#!/bin/sh
#
#
# Our valgrind "error" wrapper.

valgrind --leak-check=full -q "$@" 2> valgrind.tmp

result="$?"

# verify no errors

output="`cat valgrind.tmp`"

if [ "$output" != "" ]; then
    cat valgrind.tmp >&2
    result=1
fi

rm valgrind.tmp

exit $result

