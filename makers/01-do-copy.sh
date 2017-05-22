#!/bin/bash

set -ex

SRC="$1"
DST="$2"

rm -rf "$DST"
cp -a "$SRC" "$DST"
