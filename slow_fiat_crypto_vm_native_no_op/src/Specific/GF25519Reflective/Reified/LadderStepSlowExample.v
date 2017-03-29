Require Import Crypto.Specific.GF25519Reflective.Reified.LadderStep.

Time Definition rladderstepW_pkg' := Eval vm_compute in rladderstepW_pkg. (* 17.662 secs (17.54u,0.127s) *)
Time Definition rladderstepW_pkg'' := Eval native_compute in rladderstepW_pkg. (* 231.37 secs (16.58u,0.103s) *)
