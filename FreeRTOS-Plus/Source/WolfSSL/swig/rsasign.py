# file: rsasign.py

import wolfssl


# start Random Number Generator
rng = wolfssl.GetRng()
if rng == None:
    print "Couldn't get an RNG"
    exit(-1)

# load RSA private key in DER format
key = wolfssl.GetRsaPrivateKey("../certs/client-key.der")
if key == None:
    print "Couldn't load DER private key file"
    exit(-1)

# Make byte Arrays and fill input
signOutput = wolfssl.byteArray(128)   # 128 allows 1024 bit private key
signStr    = wolfssl.byteArray(25)    # input can't be larger then key size
                                     # 64 for 512 bit 128 for 1024 bit
wolfssl.FillSignStr(signStr, "Everybody gets Friday off", 25)

# Do RSA Sign
signedSize = wolfssl.RsaSSL_Sign(signStr, 25, signOutput, 128, key, rng)

# Show output
print "Signed Size = ", signedSize, " signed array = ", wolfssl.cdata(signOutput, signedSize)

# let's verify this worked
signVerify = wolfssl.byteArray(signedSize)
verifySize = wolfssl.RsaSSL_Verify(signOutput, signedSize, signVerify, signedSize, key)

print "Verify Size = ", verifySize, " verify array = ", wolfssl.cdata(signVerify, verifySize)

