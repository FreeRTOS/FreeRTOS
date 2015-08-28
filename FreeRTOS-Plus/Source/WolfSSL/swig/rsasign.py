# file: rsasign.py

import cyassl 


# start Random Number Generator
rng = cyassl.GetRng()
if rng == None:
    print "Couldn't get an RNG"
    exit(-1)

# load RSA private key in DER format
key = cyassl.GetRsaPrivateKey("../certs/client-key.der")
if key == None:
    print "Couldn't load DER private key file"
    exit(-1)

# Make byte Arrays and fill input
signOutput = cyassl.byteArray(128)   # 128 allows 1024 bit private key
signStr    = cyassl.byteArray(25)    # input can't be larger then key size
                                     # 64 for 512 bit 128 for 1024 bit
cyassl.FillSignStr(signStr, "Everybody gets Friday off", 25)

# Do RSA Sign
signedSize = cyassl.RsaSSL_Sign(signStr, 25, signOutput, 128, key, rng) 

# Show output 
print "Signed Size = ", signedSize, " signed array = ", cyassl.cdata(signOutput, signedSize)

# let's verify this worked
signVerify = cyassl.byteArray(signedSize)
verifySize = cyassl.RsaSSL_Verify(signOutput, signedSize, signVerify, signedSize, key)

print "Verify Size = ", verifySize, " verify array = ", cyassl.cdata(signVerify, verifySize)

