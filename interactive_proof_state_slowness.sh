#!/bin/bash

"$COQBIN"coqtop -emacs < interactive_proof_state_slowness.v 2>&1 | ./insert-timings.sh
