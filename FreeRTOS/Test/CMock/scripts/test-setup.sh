#!/bin/bash

echo "Setting up test environment..."
git -C FreeRTOS submodule update --init --recursive
RC=$?
echo "Done"
exit $RC
