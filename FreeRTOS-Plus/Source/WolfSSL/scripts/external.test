#!/bin/sh

# external.test

server=www.wolfssl.com
ca=./certs/wolfssl-website-ca.pem

[ ! -x ./examples/client/client ] && echo -e "\n\nClient doesn't exist" && exit 1

# www.wolfssl.com isn't using RFC 8446 yet but the draft instead.
./examples/client/client -v 3 2>&1 | grep -- 'Bad SSL version'
if [ $? -ne 0 ]; then

    # cloudflare seems to change CAs quickly, disabled by default
    if test -n "$WOLFSSL_EXTERNAL_TEST"; then
        echo "WOLFSSL_EXTERNAL_TEST set, running test..."
    else
        echo "WOLFSSL_EXTERNAL_TEST NOT set, won't run"
        exit 0
    fi

    # is our desired server there?
    ./scripts/ping.test $server 2
    RESULT=$?
    [ $RESULT -ne 0 ] && exit 0

    # client test against the server
    ./examples/client/client -X -C -h $server -p 443 -g -A $ca
    RESULT=$?
    [ $RESULT -ne 0 ] && echo -e "\n\nClient connection failed" && exit 1

fi

exit 0
