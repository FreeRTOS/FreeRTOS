# file: runme.py

import cyassl 

print ""
print "Trying to connect to the echo server..."

cyassl.CyaSSL_Init()
#cyassl.CyaSSL_Debugging_ON()
ctx = cyassl.CyaSSL_CTX_new(cyassl.CyaTLSv1_client_method())
if ctx == None:
    print "Couldn't get SSL CTX for TLSv1"
    exit(-1)

ret = cyassl.CyaSSL_CTX_load_verify_locations(ctx, "../certs/ca-cert.pem", None)
if ret != cyassl.SSL_SUCCESS:
    print "Couldn't do SSL_CTX_load_verify_locations "
    print "error string = ", ret 
    exit(-1)

ssl = cyassl.CyaSSL_new(ctx)
ret = cyassl.CyaSSL_swig_connect(ssl, "localhost", 11111)

if ret != cyassl.SSL_SUCCESS:
    print "Couldn't do SSL connect"
    err    = cyassl.CyaSSL_get_error(ssl, 0)
    print "error string = ", cyassl.CyaSSL_error_string(err)
    exit(-1)

print "...Connected"
written = cyassl.CyaSSL_write(ssl, "hello from python\r\n", 19)

if written > 0:
    print "Wrote ", written, " bytes"

byteArray = cyassl.byteArray(100)
readBytes = cyassl.CyaSSL_read(ssl, byteArray, 100)

print "server reply: ", cyassl.cdata(byteArray, readBytes) 

