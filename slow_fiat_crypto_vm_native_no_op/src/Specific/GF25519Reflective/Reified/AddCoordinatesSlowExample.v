Require Import Crypto.Specific.GF25519Reflective.Reified.AddCoordinates.

Time Definition radd_coordinatesW_pkg' := Eval vm_compute in radd_coordinatesW_pkg.
Time Definition radd_coordinatesW_pkg'' := Eval native_compute in radd_coordinatesW_pkg.
