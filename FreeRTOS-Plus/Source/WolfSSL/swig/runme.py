# file: runme.py

import wolfssl

print ""
print "Trying to connect to the example server -d..."

wolfssl.wolfSSL_Init()
#wolfssl.wolfSSL_Debugging_ON()
ctx = wolfssl.wolfSSL_CTX_new(wolfssl.wolfTLSv1_2_client_method())
if ctx == None:
    print "Couldn't get SSL CTX for TLSv1.2"
    exit(-1)

ret = wolfssl.wolfSSL_CTX_load_verify_locations(ctx, "../certs/ca-cert.pem", None)
if ret != wolfssl.SSL_SUCCESS:
    print "Couldn't do SSL_CTX_load_verify_locations "
    print "error string = ", ret
    exit(-1)

ssl = wolfssl.wolfSSL_new(ctx)
ret = wolfssl.wolfSSL_swig_connect(ssl, "localhost", 11111)

if ret != wolfssl.SSL_SUCCESS:
    print "Couldn't do SSL connect"
    err    = wolfssl.wolfSSL_get_error(ssl, 0)
    if ret == -2:
        print "tcp error, is example server running?"
    else:
        print "error string = ", wolfssl.wolfSSL_error_string(err)
    exit(-1)

print "...Connected"
written = wolfssl.wolfSSL_write(ssl, "hello from python\r\n", 19)

if written > 0:
    print "Wrote ", written, " bytes"

byteArray = wolfssl.byteArray(100)
readBytes = wolfssl.wolfSSL_read(ssl, byteArray, 100)

print "server reply: ", wolfssl.cdata(byteArray, readBytes)

