Fixpoint slower (n:nat) (x:nat) : nat :=
  match n with
  | O => x
  | S n' => let x := x + x in slower n' x
  end.

Local Opaque plus.

Time Definition slow0 := Eval cbv iota beta delta in slower 0.
Time Definition slow1 := Eval cbv iota beta delta in slower 1.
Time Definition slow2 := Eval cbv iota beta delta in slower 2.
Time Definition slow3 := Eval cbv iota beta delta in slower 3.
Time Definition slow4 := Eval cbv iota beta delta in slower 4.
Time Definition slow5 := Eval cbv iota beta delta in slower 5.
Time Definition slow6 := Eval cbv iota beta delta in slower 6.
Time Definition slow7 := Eval cbv iota beta delta in slower 7.
Time Definition slow8 := Eval cbv iota beta delta in slower 8.
Time Definition slow9 := Eval cbv iota beta delta in slower 9.
Time Definition slow10 := Eval cbv iota beta delta in slower 10.
Time Definition slow11 := Eval cbv iota beta delta in slower 11.
Time Definition slow12 := Eval cbv iota beta delta in slower 12.
Time Definition slow13 := Eval cbv iota beta delta in slower 13.
Time Definition slow14 := Eval cbv iota beta delta in slower 14.
Time Definition slow15 := Eval cbv iota beta delta in slower 15.
Time Definition slow16 := Eval cbv iota beta delta in slower 16.
Time Definition slow17 := Eval cbv iota beta delta in slower 17.
Time Definition slow18 := Eval cbv iota beta delta in slower 18.
Time Definition slow19 := Eval cbv iota beta delta in slower 19.
Time Definition slow20 := Eval cbv iota beta delta in slower 20.
Time Definition slow21 := Eval cbv iota beta delta in slower 21.
Time Definition slow22 := Eval cbv iota beta delta in slower 22.
Time Definition slow23 := Eval cbv iota beta delta in slower 23.
Time Definition slow24 := Eval cbv iota beta delta in slower 24.
Time Definition slow25 := Eval cbv iota beta delta in slower 25.
Time Definition slow26 := Eval cbv iota beta delta in slower 26.
