Require Import Crypto.Specific.GF25519Reflective.Reified.LadderStep.

Time Definition rladderstepW_pkg' := Eval vm_compute in rladderstepW_pkg.
Time Definition rladderstepW_pkg'' := Eval native_compute in rladderstepW_pkg.
