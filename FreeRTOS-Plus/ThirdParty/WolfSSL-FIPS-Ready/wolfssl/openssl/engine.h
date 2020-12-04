/* engine.h for libcurl */

#include <wolfssl/openssl/err.h>

#undef HAVE_OPENSSL_ENGINE_H

#define ENGINE_load_builtin_engines() /*ENGINE_load_builtin_engines not needed*/

