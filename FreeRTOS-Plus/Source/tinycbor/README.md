# Overview

This is a copy of [intel/tinycbor](https://github.com/intel/tinycbor), except for the deviations listed herein.

**The current version in this subdirectory is 0.5.2. As part of future updates, please merge/reapply the modifications described below.**

## Excluded "Cbor To Json"

Three files are excluded: cborjson.h, cbortojson.c, open_memstream.c. 

- They are not required by FreeRTOS.
- They don't compile with "make" in the Espressif build environment.
- Not every compiler defines "FILE" data type.

## Modified "compilersupport_p.h"

1. Disable optimization for TI.

```
#if !defined(__TI_COMPILER_VERSION__) || __TI_COMPILER_VERSION__ < 18000000
```

2. Comment out function mappint to standard ntohs or htons.

```
//#  include <netinet/in.h>
//#  define cbor_ntohs        ntohs
//#  define cbor_htons        htons
```

3. Implement default cbor_ntohll with cbor_ntohl, instead of undefined ntohl.

```
define ntohll(x)       ((cbor_ntohl((uint32_t)(x)) * UINT64_C(0x100000000)) + (cbor_ntohl((x) >> 32)))
```

4. Add IAR compiler support.

This code is copied from [ARMmbed/tinycbor](https://github.com/ARMmbed/tinycbor/blob/master/src/compilersupport_p.h)

```
#elif defined(__ICCARM__)
#  if __LITTLE_ENDIAN__ == 1
#    include <intrinsics.h>
#    define ntohll(x)       ((__REV((uint32_t)(x)) * UINT64_C(0x100000000)) + (__REV((x) >> 32)))
#    define htonll          ntohll
#    define cbor_ntohl     __REV
#    define cbor_htonl     __REV
#    define cbor_ntohs     __REVSH
#    define cbor_htons     __REVSH
#  else
#    define cbor_ntohll
#    define cbor_htonll
#    define cbor_ntohl
#    define cbor_htonl
#    define cbor_ntohs
#    define cbor_htons
#  endif
```

## Modified "cborvalidation.c"

Initialize local variable in function validate_floating_point; otherwise it is a may-not-be-initialized error when compiling with "make" on ESP.
```
// In function: validate_floating_point(CborValue *it, CborType type, uint32_t flags)
float valf = 0.0;
```
