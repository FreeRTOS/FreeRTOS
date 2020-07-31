#!/bin/bash

# run from wolfssl root

rm ./certs/ecc/*.old
rm ./certs/ecc/index.txt*
rm ./certs/ecc/serial
rm ./certs/ecc/crlnumber

touch ./certs/ecc/index.txt
echo 1000 > ./certs/ecc/serial
echo 2000 > ./certs/ecc/crlnumber

# generate ECC 256-bit CA
openssl ecparam -out ./certs/ca-ecc-key.par -name prime256v1
openssl req -config ./certs/ecc/wolfssl.cnf -extensions v3_ca -x509 -nodes -newkey ec:./certs/ca-ecc-key.par -keyout ./certs/ca-ecc-key.pem -out ./certs/ca-ecc-cert.pem -sha256 \
	-days 7300 -batch -subj "/C=US/ST=Washington/L=Seattle/O=wolfSSL/OU=Development/CN=www.wolfssl.com/emailAddress=info@wolfssl.com"

openssl x509 -in ./certs/ca-ecc-cert.pem -inform PEM -out ./certs/ca-ecc-cert.der -outform DER
openssl ec -in ./certs/ca-ecc-key.pem -inform PEM -out ./certs/ca-ecc-key.der -outform DER

rm ./certs/ca-ecc-key.par

# Gen CA CRL
openssl ca -config ./certs/ecc/wolfssl.cnf -gencrl -crldays 1000 -out ./certs/crl/caEccCrl.pem -keyfile ./certs/ca-ecc-key.pem -cert ./certs/ca-ecc-cert.pem



# Generate ECC 256-bit server cert
openssl req -config ./certs/ecc/wolfssl.cnf -sha256 -new -key ./certs/ecc-key.pem -out ./certs/server-ecc-req.pem -subj "/C=US/ST=Washington/L=Seattle/O=Eliptic/OU=ECC/CN=www.wolfssl.com/emailAddress=info@wolfssl.com/"
openssl x509 -req -in ./certs/server-ecc-req.pem -CA ./certs/ca-ecc-cert.pem -CAkey ./certs/ca-ecc-key.pem -CAcreateserial -out ./certs/server-ecc.pem -sha256

# Sign server certificate
openssl ca -config ./certs/ecc/wolfssl.cnf -extensions server_cert -days 3650 -notext -md sha256 -in ./certs/server-ecc-req.pem -out ./certs/server-ecc.pem
openssl x509 -in ./certs/server-ecc.pem -outform der -out ./certs/server-ecc.der

rm ./certs/server-ecc-req.pem 



# generate ECC 384-bit CA
openssl ecparam -out ./certs/ca-ecc384-key.par -name secp384r1
openssl req -config ./certs/ecc/wolfssl_384.cnf -extensions v3_ca -x509 -nodes -newkey ec:./certs/ca-ecc384-key.par -keyout ./certs/ca-ecc384-key.pem -out ./certs/ca-ecc384-cert.pem -sha384 \
	-days 7300 -batch -subj "/C=US/ST=Washington/L=Seattle/O=wolfSSL/OU=Development/CN=www.wolfssl.com/emailAddress=info@wolfssl.com"

openssl x509 -in ./certs/ca-ecc384-cert.pem -inform PEM -out ./certs/ca-ecc384-cert.der -outform DER
openssl ec -in ./certs/ca-ecc384-key.pem -inform PEM -out ./certs/ca-ecc384-key.der -outform DER

rm ./certs/ca-ecc384-key.par

# Gen CA CRL
openssl ca -config ./certs/ecc/wolfssl_384.cnf -gencrl -crldays 1000 -out ./certs/crl/caEcc384Crl.pem -keyfile ./certs/ca-ecc384-key.pem -cert ./certs/ca-ecc384-cert.pem



# Generate ECC 384-bit server cert
openssl ecparam -out ./certs/server-ecc384-key.par -name secp384r1
openssl req -config ./certs/ecc/wolfssl_384.cnf -sha384 -x509 -nodes -newkey ec:./certs/server-ecc384-key.par -keyout ./certs/server-ecc384-key.pem -out ./certs/server-ecc384-req.pem \
	-subj "/C=US/ST=Washington/L=Seattle/O=Eliptic/OU=ECC384Srv/CN=www.wolfssl.com/emailAddress=info@wolfssl.com/"
openssl req -config ./certs/ecc/wolfssl_384.cnf -sha384 -new -key ./certs/server-ecc384-key.pem -out ./certs/server-ecc384-req.pem \
	-subj "/C=US/ST=Washington/L=Seattle/O=Eliptic/OU=ECC384Srv/CN=www.wolfssl.com/emailAddress=info@wolfssl.com/"
openssl ec -in ./certs/server-ecc384-key.pem -inform PEM -out ./certs/server-ecc384-key.der -outform DER

# Sign server certificate
openssl ca -config ./certs/ecc/wolfssl_384.cnf -extensions server_cert -days 10950 -notext -md sha384 -in ./certs/server-ecc384-req.pem -out ./certs/server-ecc384-cert.pem
openssl x509 -in ./certs/server-ecc384-cert.pem -outform der -out ./certs/server-ecc384-cert.der

rm ./certs/server-ecc384-req.pem 
rm ./certs/server-ecc384-key.par

# Generate ECC 384-bit client cert
openssl ecparam -out ./certs/client-ecc384-key.par -name secp384r1
openssl req -config ./certs/ecc/wolfssl_384.cnf -sha384 -x509 -nodes -newkey ec:./certs/client-ecc384-key.par -keyout ./certs/client-ecc384-key.pem -out ./certs/client-ecc384-req.pem \
	-subj "/C=US/ST=Washington/L=Seattle/O=Eliptic/OU=ECC384Cli/CN=www.wolfssl.com/emailAddress=info@wolfssl.com/"
openssl req -config ./certs/ecc/wolfssl_384.cnf -sha384 -new -key ./certs/client-ecc384-key.pem -out ./certs/client-ecc384-req.pem \
	-subj "/C=US/ST=Washington/L=Seattle/O=Eliptic/OU=ECC384Clit/CN=www.wolfssl.com/emailAddress=info@wolfssl.com/"
openssl ec -in ./certs/client-ecc384-key.pem -inform PEM -out ./certs/client-ecc384-key.der -outform DER

# Sign client certificate
openssl ca -config ./certs/ecc/wolfssl_384.cnf -extensions usr_cert -days 10950 -notext -md sha384 -in ./certs/client-ecc384-req.pem -out ./certs/client-ecc384-cert.pem
openssl x509 -in ./certs/client-ecc384-cert.pem -outform der -out ./certs/client-ecc384-cert.der

rm ./certs/client-ecc384-req.pem 
rm ./certs/client-ecc384-key.par


# Also manually need to:
# 1. Copy ./certs/server-ecc.der into ./certs/test/server-cert-ecc-badsig.der `cp ./certs/server-ecc.der ./certs/test/server-cert-ecc-badsig.der`
# 2. Modify last byte so its invalidates signature in ./certs/test/server-cert-ecc-badsig.der
# 3. Covert bad cert to pem `openssl x509 -inform der -in ./certs/test/server-cert-ecc-badsig.der -outform pem -out ./certs/test/server-cert-ecc-badsig.pem`
# 4. Update AKID's for CA's in test.c certext_test() function akid_ecc.
