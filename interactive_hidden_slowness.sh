#!/bin/bash

"$COQBIN"coqtop -emacs < interactive_hidden_slowness.v 2>&1 | ./insert-timings.sh
