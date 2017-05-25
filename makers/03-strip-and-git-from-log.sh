#!/bin/bash

set -x

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SRC="$1"
DST="$2"

cd "$DST"
FILES="$(grep -o '^[^ ]*coqc.*\([^ ]*\.v\)' log | grep -o '[^ ]*$')"
VFILES="$(echo "$FILES" | grep '\.v$')"
OTHERFILES="$(echo "$FILES" | grep -v '\.v$')"
echo "$OTHERFILES"
FILES="$(echo "$VFILES"; (echo "$OTHERFILES" | sed s'/^\(.*)$/\1.v/g'))"
echo "$FILES"
HEADER="$(cat _CoqProject | grep -v '\.\(v\|ml\|ml4\|mllib\|mli\)$')"
(echo "$HEADER"; echo "$FILES") > _CoqProject
rm -rf .gitignore .git
echo "$FILES" | tr '\n' '\0' | xargs -0 git add
git add _CoqProject
git add .dir-locals.el || true
git commit -am "Add project $DST"
cd ..
rm -rf "$DST"
git reset --hard
