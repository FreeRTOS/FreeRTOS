#!/bin/sh

#crl.test

revocation_code="-361"
exit_code=1
counter=0
# need a unique resume port since may run the same time as testsuite
# use server port zero hack to get one
crl_port=0
#no_pid tells us process was never started if -1
no_pid=-1
#server_pid captured on startup, stores the id of the server process
server_pid=$no_pid
# let's use absolute path to a local dir (make distcheck may be in sub dir)
# also let's add some randomness by adding pid in case multiple 'make check's
# per source tree
ready_file=`pwd`/wolfssl_crl_ready$$

remove_ready_file() {
    if test -e $ready_file; then
        echo -e "removing existing ready file"
        rm $ready_file
    fi
}

# trap this function so if user aborts with ^C or other kill signal we still
# get an exit that will in turn clean up the file system
abort_trap() {
    echo "script aborted"

    if  [ $server_pid != $no_pid ]
    then
        echo "killing server"
        kill -9 $server_pid
    fi

    exit_code=2 #different exit code in case of user interrupt

    echo "got abort signal, exiting with $exit_code"
    exit $exit_code
}
trap abort_trap INT TERM


# trap this function so that if we exit on an error the file system will still
# be restored and the other tests may still pass. Never call this function
# instead use "exit <some value>" and this function will run automatically
restore_file_system() {
    remove_ready_file
}
trap restore_file_system EXIT

run_test() {
    echo -e "\nStarting example server for crl test...\n"

    remove_ready_file

    # starts the server on crl_port, -R generates ready file to be used as a
    # mutex lock, -c loads the revoked certificate. We capture the processid
    # into the variable server_pid
    ./examples/server/server -R $ready_file -p $crl_port \
             -c certs/server-revoked-cert.pem -k certs/server-revoked-key.pem &
    server_pid=$!

    while [ ! -s $ready_file -a "$counter" -lt 20 ]; do
        echo -e "waiting for ready file..."
        sleep 0.1
        counter=$((counter+ 1))
    done

    if test -e $ready_file; then
        echo -e "found ready file, starting client..."
    else
        echo -e "NO ready file ending test..."
        exit 1
    fi

    # get created port 0 ephemeral port
    crl_port=`cat $ready_file`

    # starts client on crl_port and captures the output from client
    capture_out=$(./examples/client/client -p $crl_port 2>&1)
    client_result=$?

    wait $server_pid
    server_result=$?

    case  "$capture_out" in
    *$revocation_code*)
        # only exit with zero on detection of the expected error code
        echo ""
        echo "Successful Revocation!!!!"
        echo ""
        exit_code=0
        echo "exiting with $exit_code"
        exit $exit_code
        ;;
    *)
        echo ""
        echo "Certificate was not revoked saw this instead: $capture_out"
        echo ""
        echo "configure with --enable-crl and run this script again"
        echo ""
    esac
}


######### begin program #########

# run the test
run_test

# If we get to this exit, exit_code will be a 1 signaling failure
echo "exiting with $exit_code certificate was not revoked"
exit $exit_code
########## end program ##########

