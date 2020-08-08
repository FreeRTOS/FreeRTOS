# Microchip/Atmel ATECC508A/ATECC608A Support

Support for ATECC508A using these methods:
* TLS: Using the PK callbacks and reference ATECC508A callbacks. See Coding section below. Requires options `HAVE_PK_CALLBACKS` and `WOLFSSL_ATECC_PKCB or WOLFSSL_ATECC508A`
* wolfCrypt: Native wc_ecc_* API's using the `./configure CFLAGS="-DWOLFSSL_ATECC508A"` or `#define WOLFSSL_ATECC508A`.

## Dependency

Requires the Microchip CryptoAuthLib. The examples in `wolfcrypt/src/port/atmel/atmel.c` make calls to the `atcatls_*` API's.


## Building

### Build Options

* `HAVE_PK_CALLBACKS`: Option for enabling wolfSSL's PK callback support for TLS.
* `WOLFSSL_ATECC508A`: Enables support for initializing the CryptoAuthLib and setting up the encryption key used for the I2C communication.
* `WOLFSSL_ATECC_PKCB`: Enables support for the reference PK callbacks without init.
* `WOLFSSL_ATMEL`: Enables ASF hooks seeding random data using the `atmel_get_random_number` function.
* `WOLFSSL_ATMEL_TIME`: Enables the built-in `atmel_get_curr_time_and_date` function get getting time from ASF RTC. 
* `ATECC_GET_ENC_KEY`: Macro to define your own function for getting the encryption key.
* `ATECC_SLOT_I2C_ENC`: Macro for the default encryption key slot. Can also get via the slot callback with `ATMEL_SLOT_ENCKEY`.
* `ATECC_MAX_SLOT`: Macro for the maximum dynamically allocated slots.

### Build Command Examples

`./configure --enable-pkcallbacks CFLAGS="-DWOLFSSL_ATECC_PKCB"`
`#define HAVE_PK_CALLBACKS`
`#define WOLFSSL_ATECC_PKCB`

or 

`./configure CFLAGS="-DWOLFSSL_ATECC508A"`
`#define WOLFSSL_ATECC508A`


## Coding

Setup the PK callbacks for TLS using:

```
/* Setup PK Callbacks for ATECC508A */
WOLFSSL_CTX* ctx;
wolfSSL_CTX_SetEccKeyGenCb(ctx, atcatls_create_key_cb);
wolfSSL_CTX_SetEccVerifyCb(ctx, atcatls_verify_signature_cb);
wolfSSL_CTX_SetEccSignCb(ctx, atcatls_sign_certificate_cb);
wolfSSL_CTX_SetEccSharedSecretCb(ctx, atcatls_create_pms_cb);
```

The reference ATECC508A PK callback functions are located in the `wolfcrypt/src/port/atmel/atmel.c` file.


Adding a custom context to the callbacks:

```
/* Setup PK Callbacks context */
WOLFSSL* ssl;
void* myOwnCtx;
wolfSSL_SetEccKeyGenCtx(ssl, myOwnCtx);
wolfSSL_SetEccVerifyCtx(ssl, myOwnCtx);
wolfSSL_SetEccSignCtx(ssl, myOwnCtx);
wolfSSL_SetEccSharedSecretCtx(ssl, myOwnCtx);
```

## Benchmarks

Supports ECC SECP256R1 (NIST P-256)

### TLS

TLS Establishment Times:

* Hardware accelerated ATECC508A: 2.342 seconds average
* Software only: 13.422 seconds average

The TLS connection establishment time is 5.73 times faster with the ATECC508A.

### Cryptographic ECC

Software only implementation (SAMD21 48Mhz Cortex-M0, Fast Math TFM-ASM):

`EC-DHE   key generation  3123.000 milliseconds, avg over 5 iterations, 1.601 ops/sec`
`EC-DHE   key agreement   3117.000 milliseconds, avg over 5 iterations, 1.604 ops/sec`
`EC-DSA   sign   time     1997.000 milliseconds, avg over 5 iterations, 2.504 ops/sec`
`EC-DSA   verify time     5057.000 milliseconds, avg over 5 iterations, 0.988 ops/sec`

ATECC508A HW accelerated implementation:
`EC-DHE   key generation  144.400 milliseconds, avg over 5 iterations, 34.722 ops/sec`
`EC-DHE   key agreement   134.200 milliseconds, avg over 5 iterations, 37.313 ops/sec`
`EC-DSA   sign   time     293.400 milliseconds, avg over 5 iterations, 17.065 ops/sec`
`EC-DSA   verify time     208.400 milliseconds, avg over 5 iterations, 24.038 ops/sec`


For details see our [wolfSSL Atmel ATECC508A](https://wolfssl.com/wolfSSL/wolfssl-atmel.html) page.
