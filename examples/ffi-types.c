// FFI glue for ffi-types.clem: building Clemento heap types (Boolean, Option,
// List) from C with the generic node API in clem.h.
//
// Variant tags follow declaration order in the stdlib types:
//   Boolean = False(0) True(1)
//   Option  = Some(0){ value }  None(1)
//   List    = Empty(0)          List(1){ next, element }

#include <stdint.h>
#include <string.h>

#include "clem.h"

#define BOOL_FALSE 0
#define BOOL_TRUE  1
#define OPT_SOME   0
#define OPT_NONE   1
#define LIST_EMPTY 0
#define LIST_CONS  1

// Boolean is a tag-only node (no payload).
void *is_even(int64_t n) {
    return clem_new(n % 2 == 0 ? BOOL_TRUE : BOOL_FALSE, 0);
}

// Option<I64>: None for divide-by-zero, otherwise Some(a / b). The Some payload
// is a single i64 field at the start of the payload.
void *safe_div(int64_t a, int64_t b) {
    if (b == 0) {
        return clem_new(OPT_NONE, 0);
    }
    void *node = clem_new(OPT_SOME, sizeof(int64_t));
    int64_t quotient = a / b;
    memcpy(clem_payload(node), &quotient, sizeof(int64_t));
    return node;
}

// List<I64> holding [1, 2, ..., n]. The List payload is packed { void* next;
// int64_t element }, so we cons back-to-front: the head ends up holding 1.
void *range(int64_t n) {
    void *acc = clem_new(LIST_EMPTY, 0);
    for (int64_t i = n; i >= 1; i--) {
        void *node = clem_new(LIST_CONS, sizeof(void *) + sizeof(int64_t));
        char *payload = (char *)clem_payload(node);
        memcpy(payload, &acc, sizeof(void *));
        memcpy(payload + sizeof(void *), &i, sizeof(int64_t));
        acc = node;
    }
    return acc;
}
