#!/bin/sh

indent \
    --declaration-indentation16 \
    --procnames-start-lines \
    --blank-lines-after-declarations \
    --blank-lines-after-procedures \
    --break-before-boolean-operator \
    --braces-after-if-line \
    --braces-after-struct-decl-line \
    --brace-indent0 \
    --case-indentation0 \
    --no-space-after-function-call-names \
    --no-space-after-for \
    --no-space-after-if \
    --no-space-after-while \
    --no-space-after-casts \
    --space-after-parentheses \
    --dont-format-comments \
    --indent-level4 \
    --honour-newlines \
    --no-tabs \
    --line-length100 \
    $@
    
