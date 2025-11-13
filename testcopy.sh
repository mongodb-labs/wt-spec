#!/bin/bash

# Copy locallly generated test files to remote WiredTiger build directory.
for file in model_tests/model_tests*.py; do
    scp "$file" mongo-dev-workstation:/home/ubuntu/wiredtiger/test/suite/ &
done
wait