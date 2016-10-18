Require Import Coq.ZArith.ZArith.
Require Import Crypto.Specific.X86.Core.
Require Import Crypto.BoundedArithmetic.Interface.

Local Coercion Z.of_nat : nat >-> Z.

Section x86.
  Local Notation n := 64%nat.
  Context (ops : x86.instructions n).
  Definition barrett_reduce64'1 :=
    fun x : (x86.W * x86.W * (x86.W * x86.W) * (x86.W * x86.W * (x86.W * x86.W)))%type =>
      let y :=
  (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 6346243789798364141,
  @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 1503914060200516822,
  (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
  @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 1152921504606846976)) in
let y0 :=
  (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 11508512988225646668,
  @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 12431087832907484326,
  (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 18446744073709551615,
  @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 4611686018427387903)) in
let y1 :=
  (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
  @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
  (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
  @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0)) in
let y2 :=
  let y2 :=
    let (_, y2) :=
      let (xs, x0) := let (x0, _) := x in x0 in
      let (ys, y2) :=
        let (x1, _) :=
          let y2 :=
            let (_, y2) :=
              let y2 :=
                let y2 := x in
                let (high1, high2) := let (_, y3) := y2 in y3 in
                let (_, low2) := let (x1, _) := y2 in x1 in
                (let (high3, high4) := high1 in
                 let (_, low4) := low2 in
                 (let (_, y3) :=
                    @shrdf (@x86.W (Z.of_nat 64) ops) (@x86.shrdf (Z.of_nat 64) ops) high3 low4
                      58 in
                  y3,
                 let (_, y3) :=
                   @shrdf (@x86.W (Z.of_nat 64) ops) (@x86.shrdf (Z.of_nat 64) ops) high4 high3
                     58 in
                 y3),
                let (high3, high4) := high2 in
                let (_, low4) := high1 in
                (let (_, y3) :=
                   @shrdf (@x86.W (Z.of_nat 64) ops) (@x86.shrdf (Z.of_nat 64) ops) high3 low4 58 in
                 y3,
                let (_, y3) :=
                  @shrdf (@x86.W (Z.of_nat 64) ops) (@x86.shrdf (Z.of_nat 64) ops) high4 high3 58 in
                y3)) in
              let y3 := y0 in
              let y4 :=
                (let y4 := let (x1, _) := y2 in x1 in
                 let y5 := let (x1, _) := y3 in x1 in
                 let y6 :=
                   (let (_, y6) :=
                      @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                        (let (x1, _) := y4 in x1) (let (x1, _) := y5 in x1) in
                    y6,
                   let (_, y6) :=
                     @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                       (let (_, y6) := y4 in y6) (let (_, y6) := y5 in y6) in
                   y6) in
                 let y7 :=
                   let (_, y7) :=
                     @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                       (let (_, y7) := y4 in y7) (let (x1, _) := y5 in x1) in
                   y7 in
                 let (_, out) :=
                   let (xs0, x1) := y6 in
                   let (carry, zs) :=
                     let (xs1, x2) := xs0 in
                     let (ys, y8) :=
                       let (r1, _) := y7 in
                       (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                       let (_, y8) :=
                         @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                       y8) in
                     let (carry, zs) :=
                       @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                     let (carry0, z) :=
                       @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y8 carry in
                     (carry0, (zs, z)) in
                   let (carry0, z) :=
                     let (xs1, x2) := x1 in
                     let (ys, y8) :=
                       let (_, r2) := y7 in
                       (let (_, y8) :=
                          @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                        y8, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                     let (carry0, zs0) :=
                       @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                     let (carry1, z) :=
                       @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y8 carry0 in
                     (carry1, (zs0, z)) in
                   (carry0, (zs, z)) in
                 let y8 :=
                   let (_, y8) :=
                     @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                       (let (_, y8) := y5 in y8) (let (x1, _) := y4 in x1) in
                   y8 in
                 let (_, out0) :=
                   let (xs0, x1) := out in
                   let (carry, zs) :=
                     let (xs1, x2) := xs0 in
                     let (ys, y9) :=
                       let (r1, _) := y8 in
                       (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                       let (_, y9) :=
                         @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                       y9) in
                     let (carry, zs) :=
                       @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                     let (carry0, z) :=
                       @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y9 carry in
                     (carry0, (zs, z)) in
                   let (carry0, z) :=
                     let (xs1, x2) := x1 in
                     let (ys, y9) :=
                       let (_, r2) := y8 in
                       (let (_, y9) :=
                          @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                        y9, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                     let (carry0, zs0) :=
                       @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                     let (carry1, z) :=
                       @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y9 carry0 in
                     (carry1, (zs0, z)) in
                   (carry0, (zs, z)) in
                 out0,
                let y4 := let (_, y4) := y2 in y4 in
                let y5 := let (_, y5) := y3 in y5 in
                let y6 :=
                  (let (_, y6) :=
                     @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                       (let (x1, _) := y4 in x1) (let (x1, _) := y5 in x1) in
                   y6,
                  let (_, y6) :=
                    @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                      (let (_, y6) := y4 in y6) (let (_, y6) := y5 in y6) in
                  y6) in
                let y7 :=
                  let (_, y7) :=
                    @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                      (let (_, y7) := y4 in y7) (let (x1, _) := y5 in x1) in
                  y7 in
                let (_, out) :=
                  let (xs0, x1) := y6 in
                  let (carry, zs) :=
                    let (xs1, x2) := xs0 in
                    let (ys, y8) :=
                      let (r1, _) := y7 in
                      (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                      let (_, y8) :=
                        @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                      y8) in
                    let (carry, zs) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                    let (carry0, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y8 carry in
                    (carry0, (zs, z)) in
                  let (carry0, z) :=
                    let (xs1, x2) := x1 in
                    let (ys, y8) :=
                      let (_, r2) := y7 in
                      (let (_, y8) :=
                         @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                       y8, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                    let (carry0, zs0) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                    let (carry1, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y8 carry0 in
                    (carry1, (zs0, z)) in
                  (carry0, (zs, z)) in
                let y8 :=
                  let (_, y8) :=
                    @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                      (let (_, y8) := y5 in y8) (let (x1, _) := y4 in x1) in
                  y8 in
                let (_, out0) :=
                  let (xs0, x1) := out in
                  let (carry, zs) :=
                    let (xs1, x2) := xs0 in
                    let (ys, y9) :=
                      let (r1, _) := y8 in
                      (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                      let (_, y9) :=
                        @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                      y9) in
                    let (carry, zs) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                    let (carry0, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y9 carry in
                    (carry0, (zs, z)) in
                  let (carry0, z) :=
                    let (xs1, x2) := x1 in
                    let (ys, y9) :=
                      let (_, r2) := y8 in
                      (let (_, y9) :=
                         @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                       y9, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                    let (carry0, zs0) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                    let (carry1, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y9 carry0 in
                    (carry1, (zs0, z)) in
                  (carry0, (zs, z)) in
                out0) in
              let y5 :=
                let y5 := let (_, y5) := y2 in y5 in
                let y6 := let (x1, _) := y3 in x1 in
                let y7 :=
                  (let (_, y7) :=
                     @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                       (let (x1, _) := y5 in x1) (let (x1, _) := y6 in x1) in
                   y7,
                  let (_, y7) :=
                    @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                      (let (_, y7) := y5 in y7) (let (_, y7) := y6 in y7) in
                  y7) in
                let y8 :=
                  let (_, y8) :=
                    @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                      (let (_, y8) := y5 in y8) (let (x1, _) := y6 in x1) in
                  y8 in
                let (_, out) :=
                  let (xs0, x1) := y7 in
                  let (carry, zs) :=
                    let (xs1, x2) := xs0 in
                    let (ys, y9) :=
                      let (r1, _) := y8 in
                      (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                      let (_, y9) :=
                        @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                      y9) in
                    let (carry, zs) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                    let (carry0, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y9 carry in
                    (carry0, (zs, z)) in
                  let (carry0, z) :=
                    let (xs1, x2) := x1 in
                    let (ys, y9) :=
                      let (_, r2) := y8 in
                      (let (_, y9) :=
                         @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                       y9, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                    let (carry0, zs0) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                    let (carry1, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y9 carry0 in
                    (carry1, (zs0, z)) in
                  (carry0, (zs, z)) in
                let y9 :=
                  let (_, y9) :=
                    @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                      (let (_, y9) := y6 in y9) (let (x1, _) := y5 in x1) in
                  y9 in
                let (_, out0) :=
                  let (xs0, x1) := out in
                  let (carry, zs) :=
                    let (xs1, x2) := xs0 in
                    let (ys, y10) :=
                      let (r1, _) := y9 in
                      (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                      let (_, y10) :=
                        @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                      y10) in
                    let (carry, zs) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                    let (carry0, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y10 carry in
                    (carry0, (zs, z)) in
                  let (carry0, z) :=
                    let (xs1, x2) := x1 in
                    let (ys, y10) :=
                      let (_, r2) := y9 in
                      (let (_, y10) :=
                         @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                       y10, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                    let (carry0, zs0) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                    let (carry1, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y10 carry0 in
                    (carry1, (zs0, z)) in
                  (carry0, (zs, z)) in
                out0 in
              let (_, out) :=
                let (xs0, x1) := y4 in
                let (carry, zs) :=
                  let (xs1, x2) := xs0 in
                  let (ys, y6) :=
                    let (r1, _) := y5 in
                    (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                    @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                    let (r3, r4) := r1 in (r3, r4)) in
                  let (carry, zs) :=
                    let (xs2, x3) := xs1 in
                    let (ys0, y7) := ys in
                    let (carry, zs) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 false in
                    let (carry0, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y7 carry in
                    (carry0, (zs, z)) in
                  let (carry0, z) :=
                    let (xs2, x3) := x2 in
                    let (ys0, y7) := y6 in
                    let (carry0, zs0) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 carry in
                    let (carry1, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y7 carry0 in
                    (carry1, (zs0, z)) in
                  (carry0, (zs, z)) in
                let (carry0, z) :=
                  let (xs1, x2) := x1 in
                  let (ys, y6) :=
                    let (_, r2) := y5 in
                    (let (r3, r4) := r2 in (r3, r4),
                    (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                    @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0)) in
                  let (carry0, zs0) :=
                    let (xs2, x3) := xs1 in
                    let (ys0, y7) := ys in
                    let (carry0, zs0) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 carry in
                    let (carry1, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y7 carry0 in
                    (carry1, (zs0, z)) in
                  let (carry1, z) :=
                    let (xs2, x3) := x2 in
                    let (ys0, y7) := y6 in
                    let (carry1, zs1) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 carry0 in
                    let (carry2, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y7 carry1 in
                    (carry2, (zs1, z)) in
                  (carry1, (zs0, z)) in
                (carry0, (zs, z)) in
              let y6 :=
                let y6 := let (_, y6) := y3 in y6 in
                let y7 := let (x1, _) := y2 in x1 in
                let y8 :=
                  (let (_, y8) :=
                     @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                       (let (x1, _) := y6 in x1) (let (x1, _) := y7 in x1) in
                   y8,
                  let (_, y8) :=
                    @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                      (let (_, y8) := y6 in y8) (let (_, y8) := y7 in y8) in
                  y8) in
                let y9 :=
                  let (_, y9) :=
                    @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                      (let (_, y9) := y6 in y9) (let (x1, _) := y7 in x1) in
                  y9 in
                let (_, out0) :=
                  let (xs0, x1) := y8 in
                  let (carry, zs) :=
                    let (xs1, x2) := xs0 in
                    let (ys, y10) :=
                      let (r1, _) := y9 in
                      (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                      let (_, y10) :=
                        @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                      y10) in
                    let (carry, zs) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                    let (carry0, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y10 carry in
                    (carry0, (zs, z)) in
                  let (carry0, z) :=
                    let (xs1, x2) := x1 in
                    let (ys, y10) :=
                      let (_, r2) := y9 in
                      (let (_, y10) :=
                         @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                       y10, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                    let (carry0, zs0) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                    let (carry1, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y10 carry0 in
                    (carry1, (zs0, z)) in
                  (carry0, (zs, z)) in
                let y10 :=
                  let (_, y10) :=
                    @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                      (let (_, y10) := y7 in y10) (let (x1, _) := y6 in x1) in
                  y10 in
                let (_, out1) :=
                  let (xs0, x1) := out0 in
                  let (carry, zs) :=
                    let (xs1, x2) := xs0 in
                    let (ys, y11) :=
                      let (r1, _) := y10 in
                      (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                      let (_, y11) :=
                        @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                      y11) in
                    let (carry, zs) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                    let (carry0, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y11 carry in
                    (carry0, (zs, z)) in
                  let (carry0, z) :=
                    let (xs1, x2) := x1 in
                    let (ys, y11) :=
                      let (_, r2) := y10 in
                      (let (_, y11) :=
                         @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                       y11, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                    let (carry0, zs0) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                    let (carry1, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y11 carry0 in
                    (carry1, (zs0, z)) in
                  (carry0, (zs, z)) in
                out1 in
              let (_, out0) :=
                let (xs0, x1) := out in
                let (carry, zs) :=
                  let (xs1, x2) := xs0 in
                  let (ys, y7) :=
                    let (r1, _) := y6 in
                    (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                    @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                    let (r3, r4) := r1 in (r3, r4)) in
                  let (carry, zs) :=
                    let (xs2, x3) := xs1 in
                    let (ys0, y8) := ys in
                    let (carry, zs) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 false in
                    let (carry0, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y8 carry in
                    (carry0, (zs, z)) in
                  let (carry0, z) :=
                    let (xs2, x3) := x2 in
                    let (ys0, y8) := y7 in
                    let (carry0, zs0) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 carry in
                    let (carry1, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y8 carry0 in
                    (carry1, (zs0, z)) in
                  (carry0, (zs, z)) in
                let (carry0, z) :=
                  let (xs1, x2) := x1 in
                  let (ys, y7) :=
                    let (_, r2) := y6 in
                    (let (r3, r4) := r2 in (r3, r4),
                    (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                    @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0)) in
                  let (carry0, zs0) :=
                    let (xs2, x3) := xs1 in
                    let (ys0, y8) := ys in
                    let (carry0, zs0) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 carry in
                    let (carry1, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y8 carry0 in
                    (carry1, (zs0, z)) in
                  let (carry1, z) :=
                    let (xs2, x3) := x2 in
                    let (ys0, y8) := y7 in
                    let (carry1, zs1) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 carry0 in
                    let (carry2, z) :=
                      @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y8 carry1 in
                    (carry2, (zs1, z)) in
                  (carry1, (zs0, z)) in
                (carry0, (zs, z)) in
              out0 in
            y2 in
          let y3 := y in
          let y4 :=
            (let y4 := let (x1, _) := y2 in x1 in
             let y5 := let (x1, _) := y3 in x1 in
             let y6 :=
               (let (_, y6) :=
                  @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                    (let (x1, _) := y4 in x1) (let (x1, _) := y5 in x1) in
                y6,
               let (_, y6) :=
                 @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                   (let (_, y6) := y4 in y6) (let (_, y6) := y5 in y6) in
               y6) in
             let y7 :=
               let (_, y7) :=
                 @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                   (let (_, y7) := y4 in y7) (let (x1, _) := y5 in x1) in
               y7 in
             let (_, out) :=
               let (xs0, x1) := y6 in
               let (carry, zs) :=
                 let (xs1, x2) := xs0 in
                 let (ys, y8) :=
                   let (r1, _) := y7 in
                   (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                   let (_, y8) :=
                     @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                   y8) in
                 let (carry, zs) :=
                   @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                 let (carry0, z) :=
                   @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y8 carry in
                 (carry0, (zs, z)) in
               let (carry0, z) :=
                 let (xs1, x2) := x1 in
                 let (ys, y8) :=
                   let (_, r2) := y7 in
                   (let (_, y8) :=
                      @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                    y8, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                 let (carry0, zs0) :=
                   @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                 let (carry1, z) :=
                   @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y8 carry0 in
                 (carry1, (zs0, z)) in
               (carry0, (zs, z)) in
             let y8 :=
               let (_, y8) :=
                 @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                   (let (_, y8) := y5 in y8) (let (x1, _) := y4 in x1) in
               y8 in
             let (_, out0) :=
               let (xs0, x1) := out in
               let (carry, zs) :=
                 let (xs1, x2) := xs0 in
                 let (ys, y9) :=
                   let (r1, _) := y8 in
                   (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                   let (_, y9) :=
                     @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                   y9) in
                 let (carry, zs) :=
                   @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                 let (carry0, z) :=
                   @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y9 carry in
                 (carry0, (zs, z)) in
               let (carry0, z) :=
                 let (xs1, x2) := x1 in
                 let (ys, y9) :=
                   let (_, r2) := y8 in
                   (let (_, y9) :=
                      @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                    y9, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                 let (carry0, zs0) :=
                   @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                 let (carry1, z) :=
                   @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y9 carry0 in
                 (carry1, (zs0, z)) in
               (carry0, (zs, z)) in
             out0,
            let y4 := let (_, y4) := y2 in y4 in
            let y5 := let (_, y5) := y3 in y5 in
            let y6 :=
              (let (_, y6) :=
                 @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                   (let (x1, _) := y4 in x1) (let (x1, _) := y5 in x1) in
               y6,
              let (_, y6) :=
                @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                  (let (_, y6) := y4 in y6) (let (_, y6) := y5 in y6) in
              y6) in
            let y7 :=
              let (_, y7) :=
                @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                  (let (_, y7) := y4 in y7) (let (x1, _) := y5 in x1) in
              y7 in
            let (_, out) :=
              let (xs0, x1) := y6 in
              let (carry, zs) :=
                let (xs1, x2) := xs0 in
                let (ys, y8) :=
                  let (r1, _) := y7 in
                  (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                  let (_, y8) :=
                    @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                  y8) in
                let (carry, zs) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                let (carry0, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y8 carry in
                (carry0, (zs, z)) in
              let (carry0, z) :=
                let (xs1, x2) := x1 in
                let (ys, y8) :=
                  let (_, r2) := y7 in
                  (let (_, y8) :=
                     @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                   y8, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                let (carry0, zs0) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                let (carry1, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y8 carry0 in
                (carry1, (zs0, z)) in
              (carry0, (zs, z)) in
            let y8 :=
              let (_, y8) :=
                @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                  (let (_, y8) := y5 in y8) (let (x1, _) := y4 in x1) in
              y8 in
            let (_, out0) :=
              let (xs0, x1) := out in
              let (carry, zs) :=
                let (xs1, x2) := xs0 in
                let (ys, y9) :=
                  let (r1, _) := y8 in
                  (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                  let (_, y9) :=
                    @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                  y9) in
                let (carry, zs) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                let (carry0, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y9 carry in
                (carry0, (zs, z)) in
              let (carry0, z) :=
                let (xs1, x2) := x1 in
                let (ys, y9) :=
                  let (_, r2) := y8 in
                  (let (_, y9) :=
                     @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                   y9, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                let (carry0, zs0) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                let (carry1, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y9 carry0 in
                (carry1, (zs0, z)) in
              (carry0, (zs, z)) in
            out0) in
          let y5 :=
            let y5 := let (_, y5) := y2 in y5 in
            let y6 := let (x1, _) := y3 in x1 in
            let y7 :=
              (let (_, y7) :=
                 @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                   (let (x1, _) := y5 in x1) (let (x1, _) := y6 in x1) in
               y7,
              let (_, y7) :=
                @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                  (let (_, y7) := y5 in y7) (let (_, y7) := y6 in y7) in
              y7) in
            let y8 :=
              let (_, y8) :=
                @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                  (let (_, y8) := y5 in y8) (let (x1, _) := y6 in x1) in
              y8 in
            let (_, out) :=
              let (xs0, x1) := y7 in
              let (carry, zs) :=
                let (xs1, x2) := xs0 in
                let (ys, y9) :=
                  let (r1, _) := y8 in
                  (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                  let (_, y9) :=
                    @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                  y9) in
                let (carry, zs) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                let (carry0, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y9 carry in
                (carry0, (zs, z)) in
              let (carry0, z) :=
                let (xs1, x2) := x1 in
                let (ys, y9) :=
                  let (_, r2) := y8 in
                  (let (_, y9) :=
                     @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                   y9, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                let (carry0, zs0) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                let (carry1, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y9 carry0 in
                (carry1, (zs0, z)) in
              (carry0, (zs, z)) in
            let y9 :=
              let (_, y9) :=
                @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                  (let (_, y9) := y6 in y9) (let (x1, _) := y5 in x1) in
              y9 in
            let (_, out0) :=
              let (xs0, x1) := out in
              let (carry, zs) :=
                let (xs1, x2) := xs0 in
                let (ys, y10) :=
                  let (r1, _) := y9 in
                  (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                  let (_, y10) :=
                    @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                  y10) in
                let (carry, zs) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                let (carry0, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y10 carry in
                (carry0, (zs, z)) in
              let (carry0, z) :=
                let (xs1, x2) := x1 in
                let (ys, y10) :=
                  let (_, r2) := y9 in
                  (let (_, y10) :=
                     @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                   y10, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                let (carry0, zs0) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                let (carry1, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y10 carry0 in
                (carry1, (zs0, z)) in
              (carry0, (zs, z)) in
            out0 in
          let (_, out) :=
            let (xs0, x1) := y4 in
            let (carry, zs) :=
              let (xs1, x2) := xs0 in
              let (ys, y6) :=
                let (r1, _) := y5 in
                (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                let (r3, r4) := r1 in (r3, r4)) in
              let (carry, zs) :=
                let (xs2, x3) := xs1 in
                let (ys0, y7) := ys in
                let (carry, zs) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 false in
                let (carry0, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y7 carry in
                (carry0, (zs, z)) in
              let (carry0, z) :=
                let (xs2, x3) := x2 in
                let (ys0, y7) := y6 in
                let (carry0, zs0) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 carry in
                let (carry1, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y7 carry0 in
                (carry1, (zs0, z)) in
              (carry0, (zs, z)) in
            let (carry0, z) :=
              let (xs1, x2) := x1 in
              let (ys, y6) :=
                let (_, r2) := y5 in
                (let (r3, r4) := r2 in (r3, r4),
                (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0)) in
              let (carry0, zs0) :=
                let (xs2, x3) := xs1 in
                let (ys0, y7) := ys in
                let (carry0, zs0) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 carry in
                let (carry1, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y7 carry0 in
                (carry1, (zs0, z)) in
              let (carry1, z) :=
                let (xs2, x3) := x2 in
                let (ys0, y7) := y6 in
                let (carry1, zs1) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 carry0 in
                let (carry2, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y7 carry1 in
                (carry2, (zs1, z)) in
              (carry1, (zs0, z)) in
            (carry0, (zs, z)) in
          let y6 :=
            let y6 := let (_, y6) := y3 in y6 in
            let y7 := let (x1, _) := y2 in x1 in
            let y8 :=
              (let (_, y8) :=
                 @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                   (let (x1, _) := y6 in x1) (let (x1, _) := y7 in x1) in
               y8,
              let (_, y8) :=
                @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                  (let (_, y8) := y6 in y8) (let (_, y8) := y7 in y8) in
              y8) in
            let y9 :=
              let (_, y9) :=
                @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                  (let (_, y9) := y6 in y9) (let (x1, _) := y7 in x1) in
              y9 in
            let (_, out0) :=
              let (xs0, x1) := y8 in
              let (carry, zs) :=
                let (xs1, x2) := xs0 in
                let (ys, y10) :=
                  let (r1, _) := y9 in
                  (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                  let (_, y10) :=
                    @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                  y10) in
                let (carry, zs) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                let (carry0, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y10 carry in
                (carry0, (zs, z)) in
              let (carry0, z) :=
                let (xs1, x2) := x1 in
                let (ys, y10) :=
                  let (_, r2) := y9 in
                  (let (_, y10) :=
                     @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                   y10, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                let (carry0, zs0) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                let (carry1, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y10 carry0 in
                (carry1, (zs0, z)) in
              (carry0, (zs, z)) in
            let y10 :=
              let (_, y10) :=
                @muldwf (@x86.W (Z.of_nat 64) ops) (@x86.muldwf (Z.of_nat 64) ops)
                  (let (_, y10) := y7 in y10) (let (x1, _) := y6 in x1) in
              y10 in
            let (_, out1) :=
              let (xs0, x1) := out0 in
              let (carry, zs) :=
                let (xs1, x2) := xs0 in
                let (ys, y11) :=
                  let (r1, _) := y10 in
                  (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                  let (_, y11) :=
                    @shlf (@x86.W (Z.of_nat 64) ops) (@x86.shlf (Z.of_nat 64) ops) r1 0 in
                  y11) in
                let (carry, zs) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys false in
                let (carry0, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y11 carry in
                (carry0, (zs, z)) in
              let (carry0, z) :=
                let (xs1, x2) := x1 in
                let (ys, y11) :=
                  let (_, r2) := y10 in
                  (let (_, y11) :=
                     @shrf (@x86.W (Z.of_nat 64) ops) (@x86.shrf (Z.of_nat 64) ops) r2 0 in
                   y11, @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0) in
                let (carry0, zs0) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs1 ys carry in
                let (carry1, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x2 y11 carry0 in
                (carry1, (zs0, z)) in
              (carry0, (zs, z)) in
            out1 in
          let (_, out0) :=
            let (xs0, x1) := out in
            let (carry, zs) :=
              let (xs1, x2) := xs0 in
              let (ys, y7) :=
                let (r1, _) := y6 in
                (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                let (r3, r4) := r1 in (r3, r4)) in
              let (carry, zs) :=
                let (xs2, x3) := xs1 in
                let (ys0, y8) := ys in
                let (carry, zs) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 false in
                let (carry0, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y8 carry in
                (carry0, (zs, z)) in
              let (carry0, z) :=
                let (xs2, x3) := x2 in
                let (ys0, y8) := y7 in
                let (carry0, zs0) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 carry in
                let (carry1, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y8 carry0 in
                (carry1, (zs0, z)) in
              (carry0, (zs, z)) in
            let (carry0, z) :=
              let (xs1, x2) := x1 in
              let (ys, y7) :=
                let (_, r2) := y6 in
                (let (r3, r4) := r2 in (r3, r4),
                (@ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0,
                @ldi (@x86.W (Z.of_nat 64) ops) (@x86.ldi (Z.of_nat 64) ops) 0)) in
              let (carry0, zs0) :=
                let (xs2, x3) := xs1 in
                let (ys0, y8) := ys in
                let (carry0, zs0) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 carry in
                let (carry1, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y8 carry0 in
                (carry1, (zs0, z)) in
              let (carry1, z) :=
                let (xs2, x3) := x2 in
                let (ys0, y8) := y7 in
                let (carry1, zs1) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) xs2 ys0 carry0 in
                let (carry2, z) :=
                  @adc (@x86.W (Z.of_nat 64) ops) (@x86.adc (Z.of_nat 64) ops) x3 y8 carry1 in
                (carry2, (zs1, z)) in
              (carry1, (zs0, z)) in
            (carry0, (zs, z)) in
          out0 in
        x1 in
      let (carry, zs) :=
        let (xs0, x1) := xs in
        let (ys0, y3) := ys in
        let (carry, zs) :=
          @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) xs0 ys0 false in
        let (carry0, z) :=
          @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) x1 y3 carry in
        (carry0, (zs, z)) in
      let (carry0, z) :=
        let (xs0, x1) := x0 in
        let (ys0, y3) := y2 in
        let (carry0, zs0) :=
          @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) xs0 ys0 carry in
        let (carry1, z) :=
          @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) x1 y3 carry0 in
        (carry1, (zs0, z)) in
      (carry0, (zs, z)) in
    y2 in
  let (CF, _) :=
    let (xs, x0) := y2 in
    let (ys, y3) := y in
    let (carry, zs) :=
      let (xs0, x1) := xs in
      let (ys0, y4) := ys in
      let (carry, zs) :=
        @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) xs0 ys0 false in
      let (carry0, z) :=
        @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) x1 y4 carry in
      (carry0, (zs, z)) in
    let (carry0, z) :=
      let (xs0, x1) := x0 in
      let (ys0, y4) := y3 in
      let (carry0, zs0) :=
        @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) xs0 ys0 carry in
      let (carry1, z) :=
        @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) x1 y4 carry0 in
      (carry1, (zs0, z)) in
    (carry0, (zs, z)) in
  let (_, y3) :=
    let (xs, x0) := y2 in
    let (ys, y3) :=
      let (x1, x2) := y1 in
      let (y3, y4) := y in
      (let (x3, x4) := x1 in
       let (y5, y6) := y3 in
       (@selc (@x86.W (Z.of_nat 64) ops) (@x86.selc (Z.of_nat 64) ops) CF x3 y5,
       @selc (@x86.W (Z.of_nat 64) ops) (@x86.selc (Z.of_nat 64) ops) CF x4 y6),
      let (x3, x4) := x2 in
      let (y5, y6) := y4 in
      (@selc (@x86.W (Z.of_nat 64) ops) (@x86.selc (Z.of_nat 64) ops) CF x3 y5,
      @selc (@x86.W (Z.of_nat 64) ops) (@x86.selc (Z.of_nat 64) ops) CF x4 y6)) in
    let (carry, zs) :=
      let (xs0, x1) := xs in
      let (ys0, y4) := ys in
      let (carry, zs) :=
        @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) xs0 ys0 false in
      let (carry0, z) :=
        @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) x1 y4 carry in
      (carry0, (zs, z)) in
    let (carry0, z) :=
      let (xs0, x1) := x0 in
      let (ys0, y4) := y3 in
      let (carry0, zs0) :=
        @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) xs0 ys0 carry in
      let (carry1, z) :=
        @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) x1 y4 carry0 in
      (carry1, (zs0, z)) in
    (carry0, (zs, z)) in
  y3 in
let (CF, _) :=
  let (xs, x0) := y2 in
  let (ys, y3) := y in
  let (carry, zs) :=
    let (xs0, x1) := xs in
    let (ys0, y4) := ys in
    let (carry, zs) :=
      @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) xs0 ys0 false in
    let (carry0, z) :=
      @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) x1 y4 carry in
    (carry0, (zs, z)) in
  let (carry0, z) :=
    let (xs0, x1) := x0 in
    let (ys0, y4) := y3 in
    let (carry0, zs0) :=
      @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) xs0 ys0 carry in
    let (carry1, z) :=
      @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) x1 y4 carry0 in
    (carry1, (zs0, z)) in
  (carry0, (zs, z)) in
let (_, y3) :=
  let (xs, x0) := y2 in
  let (ys, y3) :=
    let (x1, x2) := y1 in
    let (y3, y4) := y in
    (let (x3, x4) := x1 in
     let (y5, y6) := y3 in
     (@selc (@x86.W (Z.of_nat 64) ops) (@x86.selc (Z.of_nat 64) ops) CF x3 y5,
     @selc (@x86.W (Z.of_nat 64) ops) (@x86.selc (Z.of_nat 64) ops) CF x4 y6),
    let (x3, x4) := x2 in
    let (y5, y6) := y4 in
    (@selc (@x86.W (Z.of_nat 64) ops) (@x86.selc (Z.of_nat 64) ops) CF x3 y5,
    @selc (@x86.W (Z.of_nat 64) ops) (@x86.selc (Z.of_nat 64) ops) CF x4 y6)) in
  let (carry, zs) :=
    let (xs0, x1) := xs in
    let (ys0, y4) := ys in
    let (carry, zs) :=
      @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) xs0 ys0 false in
    let (carry0, z) :=
      @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) x1 y4 carry in
    (carry0, (zs, z)) in
  let (carry0, z) :=
    let (xs0, x1) := x0 in
    let (ys0, y4) := y3 in
    let (carry0, zs0) :=
      @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) xs0 ys0 carry in
    let (carry1, z) :=
      @subc (@x86.W (Z.of_nat 64) ops) (@x86.subc (Z.of_nat 64) ops) x1 y4 carry0 in
    (carry1, (zs0, z)) in
  (carry0, (zs, z)) in
y3.
  Definition rexpression : Syntax.Expr base_type (interp_base_type _) op (Arrow TW (Arrow TW (Arrow TW (Arrow TW (Arrow TW (Arrow TW (Arrow TW (Arrow TW (Tbase TW))))))))).
  Proof.
    Typeclasses eauto := debug.
    Time try let v := (eval cbv beta delta [barrett_reduce64'1] in (fun a b c d e f g h => barrett_reduce64'1 (((a, b), (c, d)), ((e, f), (g, h))))) in
             let v := Reify v in
             exact v.
  Defined.
End x86.
