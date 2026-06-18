// ClementoLang FFI header.
//
// Include this from C "glue" code that you link against a Clemento program to
// bridge between Clemento values and C. The implementations live in
// `clem_runtime.c`, which the compiler links into every binary.
//
// What crosses the FFI boundary, and how it maps to C:
//
//   Clemento type   C type        Notes
//   -------------   -----------   -------------------------------------------
//   U8/I8 .. I128   uint8_t..     scalar integers (signedness per the name)
//   F64             double        scalar
//   Char            int32_t       a Unicode scalar (code point)
//   CStr            char*         a raw, NUL-terminated C string
//   Ptr             void*         an opaque handle (e.g. FILE*)
//   String          (opaque)      a List<Char>; use the helpers below
//
// Scalars and CStr/Ptr pass through `defx` verbatim — a `defx strlen
// (CStr -> I64)` binds directly to C `size_t strlen(const char*)`.
//
// Clemento's heap types (String, List, Option, ...) are reference counted and
// pool-allocated; do NOT poke at them directly. To exchange text, convert at
// the boundary with `ffi::to_cstr` / `ffi::from_cstr` on the Clemento side, or
// call the helpers below from C.

#ifndef CLEM_H
#define CLEM_H

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

// --- Pool allocator -------------------------------------------------------
// The runtime allocator backing Clemento's reference counting. Only needed if
// you construct Clemento heap values by hand; for plain text use the string
// helpers instead. `clem_free` takes just the pointer (size is recorded in a
// header), matching how Clemento frees values.
void *clem_alloc(size_t size);
void  clem_free(void *ptr);

// --- String marshalling ---------------------------------------------------
// Convert between a Clemento `String` (an opaque List<Char> pointer) and a C
// string. `clem_string_to_cstr` returns a malloc'd buffer the caller must
// free(); `clem_string_from_cstr` returns an owned Clemento String (refcount 1)
// ready to hand back across `defx`. Both speak UTF-8.
char *clem_string_to_cstr(const void *clem_string);
void *clem_string_from_cstr(const char *s);

// --- Generic custom-type nodes --------------------------------------------
// Build and read any Clemento heap value (Boolean, Option, Result, List, your
// own `type`s). Every value is a node laid out as packed { uint64_t rc;
// uint8_t tag; <payload> }; `clem_new` sets rc=1 and the variant tag, and the
// payload starts at `clem_payload(node)`.
//
// The `tag` is the variant's index in declaration order, and the payload is the
// variant's fields packed in declaration order. For the stdlib types:
//   Boolean = False(0) True(1)                       -- no payload
//   Option  = Some(0){ value }   None(1)             -- Some holds one field
//   Result  = Ok(0){ value }     Err(1){ val }
//   List    = Empty(0)           List(1){ next, element }
// e.g. an `Option<I64>` Some(7):
//   void *o = clem_new(0, sizeof(int64_t));
//   int64_t v = 7; memcpy(clem_payload(o), &v, sizeof v);
void   *clem_new(unsigned char tag, size_t payload_size);
unsigned char clem_tag(const void *node);
void   *clem_payload(void *node);

#ifdef __cplusplus
}
#endif

#endif // CLEM_H
