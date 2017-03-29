Require Import Crypto.Specific.GF25519Reflective.Reified.AddCoordinates.

Time Definition radd_coordinatesW_pkg' := Eval vm_compute in radd_coordinatesW_pkg. (* 15.087 secs (14.939u,0.151s) *)
Time Definition radd_coordinatesW_pkg'' := Eval native_compute in radd_coordinatesW_pkg. (* 210.191 secs (15.544u,0.099s) *)
