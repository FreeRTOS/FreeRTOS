#!/bin/sh

# ocsp.test

server=www.globalsign.com
ca=certs/external/ca-globalsign-root.pem

[ ! -x ./examples/client/client ] && printf '\n\n%s\n' "Client doesn't exist" \
                                  && exit 1

./examples/client/client -v 3 2>&1 | grep -- 'Bad SSL version'
if [ $? -eq 0 ]; then
    echo "TLS 1.2 or lower required"
    echo "Skipped"
    exit 0
fi

GL_UNREACHABLE=0
# Global Sign now requires server name indication extension to work, check
# enabled prior to testing
OUTPUT=$(eval "./examples/client/client -S check")
if [ "$OUTPUT" = "SNI is: ON" ]; then
    printf '\n\n%s\n\n' "SNI is on, proceed with globalsign test"

    # is our desired server there?
    ./scripts/ping.test $server 2
    RESULT=$?
    if [ $RESULT -ne 0 ]; then
        GL_UNREACHABLE=1
    fi

    if [ $RESULT -eq 0 ]; then
        # client test against the server
        ./examples/client/client -X -C -h $server -p 443 -A $ca -g -o -N -v d -S $server
        GL_RESULT=$?
        [ $GL_RESULT -ne 0 ] && printf '\n\n%s\n' "Client connection failed"
    else
        GL_RESULT=1
    fi
else
    printf '\n\n%s\n\n' "SNI disabled, skipping globalsign test"
    GL_RESULT=0
fi

server=www.google.com
ca=certs/external/ca-google-root.pem

# is our desired server there?
./scripts/ping.test $server 2
RESULT=$?
if [ $RESULT -eq 0 ]; then
    # client test against the server
    ./examples/client/client -X -C -h $server -p 443 -A $ca -g -o -N
    GR_RESULT=$?
    [ $GR_RESULT -ne 0 ] && printf '\n\n%s\n' "Client connection failed"
else
    GR_RESULT=1
fi

if test -n "$WOLFSSL_OCSP_TEST"; then
    # check that both passed
    if [ $GL_RESULT -eq 0 ] && [ $GR_RESULT -eq 0 ]; then
        printf '\n\n%s\n' "Both OCSP connection to globalsign and google passed"
        printf '%s\n' "Test Passed!"
        exit 0
    elif [ $GL_UNREACHABLE -eq 1 ] && [ $GR_RESULT -eq 0 ]; then
         printf '%s\n' "Global Sign is currently unreachable. Logging it but if"
         printf '%s\n' "this continues to occur should be investigated"
        exit 0
    else
        # Unlike other environment variables the intent of WOLFSSL_OCSP_TEST
        # is to indicate a requirement for both tests to pass. If variable is
        # set and either tests fail then whole case fails. Do not set the
        # variable if either case passing is to be considered a success.
        printf '\n\n%s\n' "One of the OCSP connections to either globalsign or"
        printf '%s\n' "google failed, however since WOLFSSL_OCSP_TEST is set"
        printf '%s\n' "the test is considered to have failed"
        printf '%s\n' "Test Failed!"
        exit 1
    fi
else
    # if environment variable is not set then just need one to pass
    if [ $GL_RESULT -ne 0 ] && [ $GR_RESULT -ne 0 ]; then
        printf '\n\n%s\n' "Both OCSP connection to globalsign and google failed"
        printf '%s\n' "Test Failed!"
        exit 1
    else
        printf '\n\n%s\n' "WOLFSSL_OCSP_TEST NOT set, and 1 of the tests passed"
        printf '%s\n' "Test Passed!"
        exit 0
    fi
fi
