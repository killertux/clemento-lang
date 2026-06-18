// ClementoLang runtime allocator: a fixed-size-class slab/free-list pool used
// under the language's reference counting. Recycles freed nodes instead of
// returning them to the OS, avoiding per-tiny-object malloc/free overhead.
//
// Layout of every allocation: [ size_t header ][ payload ... ]
//   - header stores the *padded* payload size, so clem_free(ptr) needs no size
//     argument (drop_value frees nested pointers of unknown size).
//   - small payloads are pooled per size class; freed payloads reuse their first
//     8 bytes to chain the intrusive free list.
//   - oversized payloads fall back to malloc/free (header marked LARGE).
//
// Single-threaded: the free lists and slab cursor are global and unsynchronized,
// matching the language today. When threads land this needs per-thread pools.

#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define ALIGN 8                 // our fields are <= 8-aligned (i64, ptr, i32)
#define MAX_SMALL 4096          // payloads above this bypass the pool
#define SLAB_BYTES (1 << 16)    // 64 KiB slabs
#define NUM_CLASSES (MAX_SMALL / ALIGN + 1)
#define LARGE_MARK ((size_t)-1)

static void *free_list[NUM_CLASSES];
static char *slab_cursor = 0;
static size_t slab_left = 0;

static size_t pad(size_t n) {
    if (n < ALIGN) n = ALIGN;          // room for the intrusive free pointer
    return (n + (ALIGN - 1)) & ~((size_t)(ALIGN - 1));
}

void *clem_alloc(size_t size) {
    size_t padded = pad(size);

    if (padded > MAX_SMALL) {
        size_t *header = (size_t *)malloc(sizeof(size_t) + padded);
        *header = LARGE_MARK;
        return (void *)(header + 1);
    }

    size_t class = padded / ALIGN;
    void *payload = free_list[class];
    if (payload) {
        free_list[class] = *(void **)payload;   // pop; header already set
        return payload;
    }

    size_t block = sizeof(size_t) + padded;
    if (slab_left < block) {
        size_t slab_size = block > SLAB_BYTES ? block : SLAB_BYTES;
        slab_cursor = (char *)malloc(slab_size);
        slab_left = slab_size;
    }
    size_t *header = (size_t *)slab_cursor;
    *header = padded;
    slab_cursor += block;
    slab_left -= block;
    return (void *)(header + 1);
}

void clem_free(void *ptr) {
    if (!ptr) return;
    size_t *header = ((size_t *)ptr) - 1;
    size_t padded = *header;
    if (padded == LARGE_MARK) {
        free(header);
        return;
    }
    size_t class = padded / ALIGN;
    *(void **)ptr = free_list[class];        // push (payload chains the list)
    free_list[class] = ptr;
}

// ---------------------------------------------------------------------------
// FFI string marshalling: Clemento `String` (= `List<Char>`) <-> C `char*`.
//
// These let C glue code (and the `ffi::to_cstr`/`ffi::from_cstr` builtins) move
// text across the boundary. They hard-code the heap layout the compiler emits
// for `List<Char>`, so they MUST stay in sync with `base_custom_type()` and
// `std/list.clem`:
//
//   node = packed { uint64_t rc; uint8_t tag; <payload> }   // header = 9 bytes
//     tag 0 = Empty  (no payload)
//     tag 1 = List   (payload: packed { void* next; int32_t element })
//
// `element` is a Unicode scalar (code point). Fields are read/written with
// memcpy because the packed layout leaves them unaligned.
// ---------------------------------------------------------------------------

#define LIST_TAG_EMPTY 0
#define LIST_TAG_CONS  1
#define HEADER_SIZE    9                    // packed { u64 rc; u8 tag }
#define CONS_NEXT_OFF  HEADER_SIZE          // payload field 0: void* next
#define CONS_ELEM_OFF  (HEADER_SIZE + 8)    // payload field 1: int32_t element

// --- Generic node helpers (any custom type) ------------------------------
// Build and read any Clemento heap value from C. The variant `tag` follows the
// declaration order in the type's .clem file, e.g.
//   Boolean = False(0) True(1)
//   Option  = Some(0)  None(1)
//   Result  = Ok(0)    Err(1)
//   List    = Empty(0) List(1)
// The payload — the variant's fields, packed in declaration order — starts at
// `clem_payload(node)`. Write/read fields there with memcpy at their offsets.
void *clem_new(uint8_t tag, size_t payload_size) {
    char *node = (char *)clem_alloc(HEADER_SIZE + payload_size);
    uint64_t rc = 1;
    memcpy(node, &rc, 8);
    memcpy(node + 8, &tag, 1);
    return node;
}

uint8_t clem_tag(const void *node) {
    uint8_t tag;
    memcpy(&tag, (const char *)node + 8, 1);
    return tag;
}

void *clem_payload(void *node) {
    return (char *)node + HEADER_SIZE;
}

// List<Char> payload accessors, used by the string helpers below.
static void *cons_next(const void *node) {
    void *next;
    memcpy(&next, (const char *)node + CONS_NEXT_OFF, sizeof(void *));
    return next;
}

static int32_t cons_elem(const void *node) {
    int32_t elem;
    memcpy(&elem, (const char *)node + CONS_ELEM_OFF, sizeof(int32_t));
    return elem;
}

static void *make_empty(void) { return clem_new(LIST_TAG_EMPTY, 0); }

static void *make_cons(void *next, int32_t elem) {
    void *node = clem_new(LIST_TAG_CONS, sizeof(void *) + sizeof(int32_t));
    char *p = (char *)clem_payload(node);
    memcpy(p, &next, sizeof(void *));
    memcpy(p + sizeof(void *), &elem, sizeof(int32_t));
    return node;
}

// Encode a single Unicode scalar as UTF-8 into `out` (must hold >= 4 bytes);
// returns the number of bytes written.
static int utf8_encode(int32_t cp, unsigned char *out) {
    if (cp < 0x80) {
        out[0] = (unsigned char)cp;
        return 1;
    } else if (cp < 0x800) {
        out[0] = (unsigned char)(0xC0 | (cp >> 6));
        out[1] = (unsigned char)(0x80 | (cp & 0x3F));
        return 2;
    } else if (cp < 0x10000) {
        out[0] = (unsigned char)(0xE0 | (cp >> 12));
        out[1] = (unsigned char)(0x80 | ((cp >> 6) & 0x3F));
        out[2] = (unsigned char)(0x80 | (cp & 0x3F));
        return 3;
    } else {
        out[0] = (unsigned char)(0xF0 | (cp >> 18));
        out[1] = (unsigned char)(0x80 | ((cp >> 12) & 0x3F));
        out[2] = (unsigned char)(0x80 | ((cp >> 6) & 0x3F));
        out[3] = (unsigned char)(0x80 | (cp & 0x3F));
        return 4;
    }
}

// Build a Clemento `String` (List<Char>) from a NUL-terminated UTF-8 C string.
// Returns an owned value (refcount 1); decode is forward, then we cons back to
// front so the list head holds the first code point.
void *clem_string_from_cstr(const char *s) {
    size_t len = s ? strlen(s) : 0;

    // Decode UTF-8 into a temporary array of code points.
    int32_t *cps = (int32_t *)malloc((len + 1) * sizeof(int32_t));
    size_t n = 0;
    for (size_t i = 0; i < len;) {
        unsigned char c = (unsigned char)s[i];
        int32_t cp;
        int extra;
        if (c < 0x80)        { cp = c;          extra = 0; }
        else if (c < 0xE0)   { cp = c & 0x1F;   extra = 1; }
        else if (c < 0xF0)   { cp = c & 0x0F;   extra = 2; }
        else                 { cp = c & 0x07;   extra = 3; }
        i++;
        for (int k = 0; k < extra && i < len; k++, i++) {
            cp = (cp << 6) | ((unsigned char)s[i] & 0x3F);
        }
        cps[n++] = cp;
    }

    void *acc = make_empty();
    for (size_t i = n; i > 0; i--) {
        acc = make_cons(acc, cps[i - 1]);
    }
    free(cps);
    return acc;
}

// Render a Clemento `String` (List<Char>) into a freshly malloc'd, NUL-terminated
// UTF-8 C string. The caller owns the buffer and must free() it (or hand it to
// C code that does). Does not consume/free the input list.
char *clem_string_to_cstr(const void *list) {
    // First pass: count code points.
    size_t n = 0;
    for (const void *node = list; node && clem_tag(node) == LIST_TAG_CONS;
         node = cons_next(node)) {
        n++;
    }

    // Worst case 4 bytes per code point, plus the NUL.
    char *buf = (char *)malloc(n * 4 + 1);
    size_t off = 0;
    for (const void *node = list; node && clem_tag(node) == LIST_TAG_CONS;
         node = cons_next(node)) {
        off += utf8_encode(cons_elem(node), (unsigned char *)buf + off);
    }
    buf[off] = '\0';
    return buf;
}
