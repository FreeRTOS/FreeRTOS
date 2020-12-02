Directories:

+ Utilities/backoff_algorithm contains a utility that calculates an
  exponential back off time, with some jitter.  It is used to ensure fleets of
  IoT devices that become disconnected don't all try and reconnect at the same
  time.

+ Utilities/logging contains header files for use with the core libraries logging
  macros.  See https://www.FreeRTOS.org/logging.html.

+ Utililties/mbedtls_freertos contains a few FreeRTOS specifics required by
  mbedTLS.


