// FFI glue for ffi-string.clem, demonstrating the clem.h C API.
//
// `shout` receives a C string (produced by `ffi::to_cstr`, which hands us
// ownership of the malloc'd buffer), uppercases it in place, and returns a
// freshly built Clemento String via `clem_string_from_cstr`.

#include <ctype.h>
#include <stdlib.h>

#include "clem.h"

void *shout(char *s) {
    for (char *p = s; *p; p++) {
        *p = (char)toupper((unsigned char)*p);
    }
    void *result = clem_string_from_cstr(s);
    free(s); // we own the buffer `to_cstr` handed over
    return result;
}

// Returns a borrowed C string. The Clemento side turns it into an owned String
// with `ffi::from_cstr`, so we must NOT free this static buffer.
const char *banner(void) {
    return "clem ffi";
}
