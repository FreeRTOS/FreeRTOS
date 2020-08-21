*** Description ***

The wolfSSL embedded SSL library (formerly CyaSSL) is a lightweight SSL/TLS
library written in ANSI C and targeted for embedded, RTOS, and
resource-constrained environments - primarily because of its small size, speed,
and feature set.  It is commonly used in standard operating environments as well
because of its royalty-free pricing and excellent cross platform support.
wolfSSL supports industry standards up to the current TLS 1.3 and DTLS 1.2
levels, is up to 20 times smaller than OpenSSL, and offers progressive ciphers
such as ChaCha20, Curve25519, NTRU, and Blake2b. User benchmarking and feedback
reports dramatically better performance when using wolfSSL over OpenSSL.

wolfSSL is powered by the wolfCrypt library. Two versions of the wolfCrypt
cryptography library have been FIPS 140-2 validated (Certificate #2425 and
certificate #3389). For additional information, visit the wolfCrypt FIPS FAQ
(https://www.wolfssl.com/license/fips/) or contact fips@wolfssl.com

*** Why choose wolfSSL? ***

There are many reasons to choose wolfSSL as your embedded SSL solution. Some of
the top reasons include size (typical footprint sizes range from 20-100 kB),
support for the newest standards (SSL 3.0, TLS 1.0, TLS 1.1, TLS 1.2, TLS 1.3,
DTLS 1.0, and DTLS 1.2), current and progressive cipher support (including
stream ciphers), multi-platform, royalty free, and an OpenSSL compatibility API
to ease porting into existing applications which have previously used the
OpenSSL package. For a complete feature list, see chapter 4 of the wolfSSL
manual. (https://www.wolfssl.com/docs/wolfssl-manual/ch4/)

*** Notes, Please read ***

Note 1)
wolfSSL as of 3.6.6 no longer enables SSLv3 by default.  wolfSSL also no longer
supports static key cipher suites with PSK, RSA, or ECDH. This means if you
plan to use TLS cipher suites you must enable DH (DH is on by default), or
enable ECC (ECC is on by default), or you must enable static key cipher suites
with

    WOLFSSL_STATIC_DH
    WOLFSSL_STATIC_RSA
      or
    WOLFSSL_STATIC_PSK

though static key cipher suites are deprecated and will be removed from future
versions of TLS.  They also lower your security by removing PFS.  Since current
NTRU suites available do not use ephemeral keys, WOLFSSL_STATIC_RSA needs to be
used in order to build with NTRU suites.

When compiling ssl.c, wolfSSL will now issue a compiler error if no cipher
suites are available. You can remove this error by defining
WOLFSSL_ALLOW_NO_SUITES in the event that you desire that, i.e., you're not
using TLS cipher suites.

Note 2)
wolfSSL takes a different approach to certificate verification than OpenSSL
does. The default policy for the client is to verify the server, this means
that if you don't load CAs to verify the server you'll get a connect error,
no signer error to confirm failure (-188).

If you want to mimic OpenSSL behavior of having SSL_connect succeed even if
verifying the server fails and reducing security you can do this by calling:

    wolfSSL_CTX_set_verify(ctx, SSL_VERIFY_NONE, 0);

before calling wolfSSL_new();. Though it's not recommended.

Note 3)
The enum values SHA, SHA256, SHA384, SHA512 are no longer available when
wolfSSL is built with --enable-opensslextra (OPENSSL_EXTRA) or with the macro
NO_OLD_SHA_NAMES. These names get mapped to the OpenSSL API for a single call
hash function. Instead the name WC_SHA, WC_SHA256, WC_SHA384 and WC_SHA512
should be used for the enum name.

*** end Notes ***


# wolfSSL Release 4.4.0 (04/22/2020)

If you have questions about this release, feel free to contact us on our
info@ address.

Release 4.4.0 of wolfSSL embedded TLS has bug fixes and new features including:

## New Feature Additions

* Hexagon support.
* DSP builds to offload ECC verify operations.
* Certificate Manager callback support.
* New APIs for running updates to ChaCha20/Poly1305 AEAD.
* Support for use with Apache.
* Add support for IBM s390x.
* PKCS8 support for ED25519.
* OpenVPN support.
* Add P384 curve support to SP.
* Add BIO and EVP API.
* Add AES-OFB mode.
* Add AES-CFB mode.
* Add Curve448, X448, and Ed448.
* Add Renesas Synergy S7G2 build and hardware acceleration.

## Fixes

* Fix for RSA public encrypt / private sign with RSA key sizes over 2048-bit.
* Correct misspellings.
* Secure renegotiation fix.
* Fix memory leak when using ATECC and non-SECP256R1 curves for sign, verify,
  or shared secret.
* Fix for K64 MMCAU with `WOLFSSL_SMALL_STACK_CACHE`.
* Fix the RSA verify only build.
* Fix in SP C implementation for small stack.
* Fix using the auth key id extension is set, hash might not be present.
* Fix when flattening certificate structure to include the subject alt names.
* Fixes for building with ECC sign/verify only.
* Fix for ECC and no cache resistance.
* Fix memory leak in DSA.
* Fix build on minGW.
* Fix `PemToDer()` call in `ProcessBuffer()` to set more than ECC.
* Fix for using RSA without SHA-512.
* Add some close tags to the echoserver HTTP example output.
* Miscellaneous fixes and updates for static analysis reports.
* Fixes for time structure support.
* Fixes for VxWorks support.
* Fixes for Async crypto support.
* Fix cache resist compile to work with SP C code.
* Fixes for Curve25519 x64 asm.
* Fix for SP x64 div.
* Fix for DTLS edge case where CCS and Finished come out of order and the
  retransmit pool gets flushed.
* Fix for infinite loop in SHA-1 with small inputs. Thanks to Peter W.
* Fix for FIPS Hmac where `wc_HmacInit()` isn't used. `wc_HmacSetKey()` needs
  to initialize the Hmac structure. Type is set to NONE, and checked against
  NONE, not 0.
* Fixes for SP RSA private operations.
* Fixes for Xilinx SDK and Zynq UltraScale+ MPSoC
* Fix leak when building with HAVE_AESGCM and NO_AES_DECRYPT. Thanks G.G.
* Fixes for building ECC without ASN.
* Fix for async TLSv1.3 issues.
* Fix `wc_KeyPemToDer()` with PKCS1 and empty key.
* Omit `-fomit-frame-pointer` from CFLAGS in configure.ac.

## Improvements/Optimizations

* Qt 5.12 and 5.13 support.
* Added more digest types to Cryptocell RSA sign/verify.
* Some memory usage improvements.
* Speed improvements for mp_rand.
* Improvements to CRL and OCSP support.
* Refactor Poly1305 AEAD/MAC to reduce duplicate code.
* Add blinding to RSA key gen.
* Improvements to blinding.
* Improvement and expansion of OpenSSL Compatibility Layer.
* Improvements to ChaCha20.
* Improvements to X.509 processing.
* Improvements to ECC support.
* Improvement in detecting 64-bit support.
* Refactor to combine duplicate ECC parameter parsing code.
* Improve keyFormat to be set by algId and let later key parsing produce fail.
* Add test cases for 3072-bit and 4096-bit RSA keys.
* Improve signature wrapper and DH test cases.
* Improvements to the configure.ac script.
* Added constant time RSA q modinv p.
* Improve performance of SP Intel 64-bit asm.
* Added a few more functions to the ABI list.
* Improve TLS bidirectional shutdown behavior.
* OpenSSH 8.1 support.
* Improve performance of RSA/DH operations on x64.
* Add support for PKCS7/CMS Enveloped data with fragmented encrypted content.
* Example linker description for FIPS builds to enforce object ordering.
* C# wrapper improvements. Added TLS client example and TLSv1.3 methods.
* Allow setting MTU in DTLS.
* Improve PKCS12 create for outputting encrypted bundles.
* Constant time EC map to affine for private operations.
* Improve performance of RSA public key ops with TFM.
* Smaller table version of AES encrypt/decrypt.
* Support IAR with position independent code (ROPI).
* Improve speed of AArch64 assembly.
* Support AES-CTR with AES-NI.
* Support AES-CTR on esp32.
* Add a no malloc option for small SP math.

## This release of wolfSSL includes fixes for 2 security vulnerabilities.

* For fast math, use a constant time modular inverse when mapping to affine
  when operation involves a private key - keygen, calc shared secret, sign.
  Thank you to Alejandro Cabrera Aldaya, Cesar Pereida García and
  Billy Bob Brumley from the Network and Information Security Group (NISEC)
  at Tampere University for the report.

* Change constant time and cache resistant ECC mulmod. Ensure points being
  operated on change to make constant time. Thank you to Pietro Borrello at
  Sapienza University of Rome.

For additional vulnerability information visit the vulnerability page at
https://www.wolfssl.com/docs/security-vulnerabilities/

See INSTALL file for build instructions.
More info can be found on-line at https://wolfssl.com/wolfSSL/Docs.html



*** Resources ***


[wolfSSL Website](https://www.wolfssl.com/)

[wolfSSL Wiki](https://github.com/wolfSSL/wolfssl/wiki)

[FIPS FAQ](https://wolfssl.com/license/fips)

[wolfSSL Documents](https://wolfssl.com/wolfSSL/Docs.html)

[wolfSSL Manual](https://wolfssl.com/wolfSSL/Docs-wolfssl-manual-toc.html)

[wolfSSL API Reference]
(https://wolfssl.com/wolfSSL/Docs-wolfssl-manual-17-wolfssl-api-reference.html)

[wolfCrypt API Reference]
(https://wolfssl.com/wolfSSL/Docs-wolfssl-manual-18-wolfcrypt-api-reference.html)

[TLS 1.3](https://www.wolfssl.com/docs/tls13/)

[wolfSSL Vulnerabilities]
(https://www.wolfssl.com/docs/security-vulnerabilities/)
