#!/bin/bash

set -ex

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SRC="$1"; shift
DST="$1"; shift

cd "$DST"
make clean cleanall -k
git clean -xfd
make V=1 VERBOSE=1 "$@" | tee log
