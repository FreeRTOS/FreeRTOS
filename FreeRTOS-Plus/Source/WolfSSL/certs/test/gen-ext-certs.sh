#!/bin/sh

TMP="/tmp/`basename $0`"

gen_cert() {
    openssl req -x509 -keyform DER -key certs/server-key.der \
      -days 1000 -new -outform DER -out $OUT -config $CONFIG \
        >$TMP 2>&1

    if [ "$?" = "0" -a -f $OUT ]; then
        echo "Created: $OUT"
    else
        cat $TMP
        echo "Failed:  $OUT"
    fi

    rm $TMP
}

OUT=certs/test/cert-ext-nc.der
KEYFILE=certs/test/cert-ext-nc-key.der
CONFIG=certs/test/cert-ext-nc.cfg
tee >$CONFIG <<EOF
[ req ]
distinguished_name = req_distinguished_name
prompt             = no
x509_extensions    = v3_ca

[ req_distinguished_name ]
C             = AU
ST            = Queensland
L             = Brisbane
O             = wolfSSL Inc
OU            = Engineering
CN            = www.wolfssl.com
emailAddress  = support@wolfsssl.com

[ v3_ca ]
subjectKeyIdentifier = hash
authorityKeyIdentifier = keyid:always,issuer
basicConstraints = critical, CA:true, pathlen:0
keyUsage = critical, digitalSignature, cRLSign, keyCertSign
nameConstraints = critical,permitted;email:.wolfssl.com
nsComment       = "Testing name constraints"

EOF
gen_cert

OUT=certs/test/cert-ext-ia.der
KEYFILE=certs/test/cert-ext-ia-key.der
CONFIG=certs/test/cert-ext-ia.cfg
tee >$CONFIG <<EOF
[ req ]
distinguished_name = req_distinguished_name
prompt             = no
x509_extensions    = v3_ca

[ req_distinguished_name ]
C             = AU
ST            = Queensland
L             = Brisbane
O             = wolfSSL Inc
OU            = Engineering
CN            = www.wolfssl.com
emailAddress  = support@wolfsssl.com

[ v3_ca ]
inhibitAnyPolicy = critical,1
nsComment        = "Testing inhibit any"

EOF
gen_cert

OUT=certs/test/cert-ext-nct.der
KEYFILE=certs/test/cert-ext-mct-key.der
CONFIG=certs/test/cert-ext-nct.cfg
tee >$CONFIG <<EOF
[ req ]
distinguished_name = req_distinguished_name
prompt             = no
x509_extensions    = v3_ca

[ req_distinguished_name ]
C             = AU
ST            = Queensland
L             = Brisbane
O             = wolfSSL Inc
OU            = Engineering
CN            = www.wolfssl.com
emailAddress  = support@wolfsssl.com

[ v3_ca ]
nsCertType       = critical,server
nsComment        = "Testing Netscape Certificate Type"

EOF
gen_cert

