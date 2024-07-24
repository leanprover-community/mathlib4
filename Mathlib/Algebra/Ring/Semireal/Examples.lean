/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser
-/

import Mathlib.Algebra.Ring.Semireal.Defs
import Mathlib.Algebra.Ring.Hom.Defs

/-!
We construct instances of semireal rings. One method to show that a commutative ring `R` is semireal
is to construct a ring homomorphism `f : R →+* S` to a semireal ring `S` (see theorem
`maps_to_semireal_implies_semireal`).

In that case, `R` is non-trivial because `f (1 : R) = (1 : S) ≠ (0 : S)`, so `(1 : R) ≠ (0 : R)`
(see lemma `maps_to_nonzero_implies_non_zero`). And `(-1 : R)` is not a sum of squares in `R`,
because the image under `f` of a sum of squares in `R` is a sum of squares in `S` and `f (-1 : R) =
(-1 : S)` but `(-1 : S)` is not a sum of squares in `S` (see lemma `is_SumSq_mapsto_isSumSq`).
-/

theorem maps_to_nonzero_implies_non_zero {R S : Type} [Semiring R] [Semiring S] :
    (R →+* S) → (0 : S) ≠ 1 → (0 : R) ≠ 1 := by
  intro f
  apply mt
  intro one_R_eq_zero
  rw [← f.map_zero, ← f.map_one]
  apply congrArg f
  exact one_R_eq_zero

theorem is_SumSq_mapsto_isSumSq {R S : Type} [Semiring R] [Semiring S]
    (f : R →+* S) (x : R) : isSumSq x → isSumSq (f x) := by
  intro hx
  induction hx with
  | zero =>
    rewrite [f.map_zero]
    exact isSumSq.zero
  | sq_add y S _ ihfS =>
    have aux : f (y * y + S) = f y * f y + f S :=
      calc
        f ( y * y + S) = f (y * y) + f S := by rw [RingHom.map_add]
        _              = f y * f y + f S := by rw [RingHom.map_mul]
    rw [aux]
    exact isSumSq.sq_add (f y) (f S) ihfS

theorem maps_to_semireal_implies_semireal (R S : Type) [CommRing R] [CommRing S] :
    (R →+* S) → isSemireal S → isSemireal R := by
  intro f hS
  constructor
  · exact maps_to_nonzero_implies_non_zero f hS.non_trivial
  · apply mt
    apply is_SumSq_mapsto_isSumSq f (-1 : R)
    have aux : f (-1 : R) = -1 :=
      calc
        f (-1 : R) = -(f 1) := RingHom.map_neg f 1
        _          = -1     := by rw [f.map_one]
    rw [aux]
    exact hS.neg_one_not_SumSq

/-
We now use theorem `maps_to_semireal_implies_semireal` to construct new instances of semireal
*rings*. Namely:

- If `R` is a commutative ring whose total ring of fraction `qf R` is semireal, then `R` is semireal
(because there is a ring homomorphism `R →+* qf R`). This happens for instance if `R` is a domain
and `qf R` is a linearly ordered field (e.g. for `R = ℤ`).
- If `R` is a semireal ring, then the polynomial ring `R[X]` is semireal (using for instance the
evaluation morphism `P ↦ P 0`). In particular, if `F` is a linearly ordered field, then the ring
`F[X]` is semireal.
-/

-- WIP

#lint
