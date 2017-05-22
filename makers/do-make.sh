#!/bin/bash

set -ex

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SRC="$1"
DST="$2"

"$DIR/01-do-copy.sh" "$@"
"$DIR/02-make-log.sh" "$@"
"$DIR/03-strip-and-git-from-log.sh" "$@"
