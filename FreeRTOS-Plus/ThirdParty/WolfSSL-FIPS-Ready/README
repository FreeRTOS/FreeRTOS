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


# wolfSSL Release 4.5.0 (August 19, 2020)

If you have questions about this release, feel free to contact us on our
info@ address.

Release 4.5.0 of wolfSSL embedded TLS has bug fixes and new features including:

## New Feature Additions

* Added Xilinx Vitis 2019.2 example and README updates
* TLS v1.3 is now enabled by default
* Building FIPS 140-2 code and test on Solaris
* Secure renegotiation with DTLS 1.2
* Update RSA calls for hardware acceleration with Xilsecure
* Additional OpenSSL compatibility layer functions added
* Cypress PSoC6 wolfCrypt driver added
* Added STM32CubeIDE support
* Added certificate parsing and inspection to C# wrapper layer
* TLS v1.3 sniffer support added
* TSIP v1.09 for target board GR-ROSE support added
* Added support for the "X72N Envision Kit" evaluation board
* Support for ECC nonblocking using the configure options
  "--enable-ecc=nonblock --enable-sp=yes,nonblock CFLAGS=-DWOLFSSL_PUBLIC_MP"
* Added wc_curve25519_make_pub function to generate a public key given the
  private one

## Fixes

* PIC32MZ hardware cache and large hashes fix
* AES-GCM use with EVP layer in compatibility layer code
* Fix for RSA_LOW_MEM with ARM build of SP code
* Sanity check on tag length with AES-CCM to conform with RFC 3610
* Fixes for 32 and 64 bit software implementations of SP code when
  WOLFSSL_SP_CACHE_RESISTANT is defined
* GCC warning fixes for GCC 9 and later
* Sanity check on HKDF expand length to conform with RFC 5869
* Fixes for STM32 CubeMX HAL with AES-GCM
* Fixed point cache look up table (LUT) implementation fixes
* Fix for ARM 32bit SP code when calling div word
* Fix for potential out of bounds read when parsing CRLs
* Fix for potential out of bounds read with RSA unpadding
* AES-CCM optimized counter fix
* Updates to Xcode projects for new files and features
* Fix for adding CRL’s to a WOLFSSL_X509_STORE structure
* FIPSv2 build with opensslall build fixes
* Fixes for CryptoCell use with ECC and signature wrappers
* Fix for mod calculation with SP code dealing with 3072 bit keys
* Fix for handling certificates with multiple OU’s in name
* Fix for SP math implementation of sp_add_d and add a sanity check on
  rshb range
* Fix for sanity check on padding with DES3 conversion of PEM to DER
* Sanity check for potential out of bounds read with fp_read_radix_16
* Additional checking of ECC scalars.
* Fixing the FIPS Ready build w.r.t. ecc.c.
* When processing certificate names with OpenSSL compatibility layer
  enabled, unknown name item types were getting handled as having NID 0,
  and failing. Added a couple more items to what is handled correctly,
  and ignoring anything that is an unknown type.

## Improvements/Optimizations

* TLS 1.3 certificate verify update to handle 8192 bit RSA keys
* wpa_supplicant support with reduced code size option
* TLS 1.3 alerts encrypted when possible
* Many minor coverity fixes added
* Error checking when parsing PKCS12 DER
* IAR warning in test.c resolved
* ATECC608A improvements for use with Harmony 3 and PIC32 MZ
* Support for AES-GCM and wc_SignatureVerifyHash with static memory and no
  malloc’s
* Enable SNI by default with JNI/JSSE builds
* NetBSD GCC compiler warnings resolved
* Additional test cases and code coverage added including curve25519 and
  curve448 tests
* Option for user defined mutexes with WOLFSSL_USER_MUTEX
* Sniffer API’s for loading buffer directly
* Fixes and improvements from going through the DO-178 process were added
* Doxygen updates and fixes for auto documentation generation
* Changed the configure option for FIPS Ready builds to be
  `--enable-fips=ready`.

## This release of wolfSSL includes fixes for 6 security vulnerabilities.

wolfSSL version 4.5.0 contains 6 vulnerability fixes: 2 fixes for TLS 1.3,
2 side channel attack mitigations, 1 fix for a potential private key leak
in a specific use case, 1 fix for DTLS.

* In earlier versions of wolfSSL there exists a potential man in the middle
  attack on TLS 1.3 clients. Malicious attackers with a privileged network
  position can impersonate TLS 1.3 servers and bypass authentication. Users
  that have applications with client side code and have TLS 1.3 turned on,
  should update to the latest version of wolfSSL. Users that do not have
  TLS 1.3 turned on, or that are server side only, are NOT affected by this
  report. Thanks to Gerald Doussot from NCC group for the report.
* Denial of service attack on TLS 1.3 servers from repetitively sending
  ChangeCipherSpecs messages. This denial of service results from the
  relatively low effort of sending a ChangeCipherSpecs message versus the
  effort of the server to process that message. Users with TLS 1.3 servers are
  recommended to update to the most recent version of wolfSSL which limits the
  number of TLS 1.3 ChangeCipherSpecs that can be received in order to avoid
  this DoS attack. CVE-2020-12457 was reserved for the report. Thanks to
  Lenny Wang of Tencent Security Xuanwu LAB.
* Potential cache timing attacks on public key operations in builds that are
  not using SP (single precision). Users that have a system where malicious
  agents could execute code on the system, are not using the SP build with
  wolfSSL, and are doing private key operations on the system (such as signing
  with a private key) are recommended to regenerate private keys and update to
  the most recent version of wolfSSL. CVE-2020-15309 is reserved for this
  issue. Thanks to Ida Bruhns from Universität zu Lübeck for the report.
* When using SGX with EC scalar multiplication the possibility of side-channel
  attacks are present. To mitigate the risk of side channel attacks wolfSSL’s
  single precision EC operations should be used instead. Release 4.5.0 turns
  this on be default now with SGX builds and in previous versions of wolfSSL
  this can be turned on by using the WOLFSSL_SP macros. Thank you to
  Alejandro Cabrera Aldaya, Cesar Pereida García and Billy Bob Brumley from
  the Network and Information Security Group (NISEC) at Tampere University for
  the report.
* Leak of private key in the case that PEM format private keys are bundled in
  with PEM certificates into a single file. This is due to the
  misclassification of certificate type versus private key type when parsing
  through the PEM file. To be affected, wolfSSL would need to have been built
  with OPENSSL_EXTRA (--enable-opensslextra). Some build variants such as
  --enable-all and --enable-opensslall also turn on this code path, checking
  wolfssl/options.h for OPENSSL_EXTRA will show if the macro was used with the
  build. If having built with the opensslextra enable option and having placed
  PEM certificates with PEM private keys in the same file when loading up the
  certificate file, then we recommend updating wolfSSL for this use case and
  also recommend regenerating any private keys in the file.
* During the handshake, clear application_data messages in epoch 0 are
  processed and returned to the application. Fixed by dropping received
  application_data messages in epoch 0. Thank you to Paul Fiterau of Uppsala
  University and Robert Merget of Ruhr-University Bochum for the report.

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
