## Background
This folder contains two files:

### mbedtls_utils.c

The convert_pem_to_der() function defined in mbedtls_utils.c is used by the PKCS #11 tests and the dev_mode_key_provisioning demo. This function is copied from the pem2der.c file that can be found in the mbedtls/programs/util/ directory of the mbedTLS library. Copying this function is required since the pem2der.c file has a main function and could not be used.

The PKI_RSA_RSASSA_PKCS1_v15_Encode() function defined in mbedtls_utils.c is used in the PKCS #11 tests. It's a  modified version of the rsa_rsassa_pkcs1_v15_encode() function that is defined in the mbedTLS library file rsa.c that can be found in the mbedtls/library/ directory. Copying and modifying this function is required because the test code needs changes that are specific to this repo and should not be moved upstream.

### mbedtls_error.h/.c files

These provide 2 utility functions, `mbedtls_strerror_highlevel` and `mbedtls_strerror_lowlevel`, to convert the high-level and low-level codes embedded in a mbed TLS return codes, respectively. 

The difference between these utilities and the mbedTLS provided `mbedtls_strerror` utility is that the former enable string-conversion of error codes with constant strings (that is efficient for resource-constrained microcontroller platforms), while the latter involves a string-copy operation in a caller-provided buffer.
