/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Oliver Nash
-/

import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Algebra.Algebra.Defs

/-!
# Algebra instances for actions by ℚ and theorems about them

-/

namespace RingHom

variable {R S : Type*}

-- Porting note: changed `[Ring R] [Ring S]` to `[Semiring R] [Semiring S]`
-- otherwise, Lean failed to find a `Subsingleton (ℚ →+* S)` instance
@[simp]
theorem map_rat_algebraMap [Semiring R] [Semiring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S)
    (r : ℚ) : f (algebraMap ℚ R r) = algebraMap ℚ S r :=
  RingHom.ext_iff.1 (Subsingleton.elim (f.comp (algebraMap ℚ R)) (algebraMap ℚ S)) r
#align ring_hom.map_rat_algebra_map RingHom.map_rat_algebraMap

end RingHom

section Rat

instance algebraRat {α} [DivisionRing α] [CharZero α] : Algebra ℚ α where
  smul := (· • ·)
  smul_def' := Rat.smul_def
  toRingHom := Rat.castHom α
  commutes' := Rat.cast_commute
#align algebra_rat algebraRat

/-- The rational numbers are an algebra over the non-negative rationals. -/
instance : Algebra NNRat ℚ :=
  NNRat.coeHom.toAlgebra

/-- The two `Algebra ℚ ℚ` instances should coincide. -/
example : algebraRat = Algebra.id ℚ :=
  rfl

@[simp] theorem algebraMap_rat_rat : algebraMap ℚ ℚ = RingHom.id ℚ := rfl
#align algebra_map_rat_rat algebraMap_rat_rat

instance algebra_rat_subsingleton {α} [Semiring α] : Subsingleton (Algebra ℚ α) :=
  ⟨fun x y => Algebra.algebra_ext x y <| RingHom.congr_fun <| Subsingleton.elim _ _⟩
#align algebra_rat_subsingleton algebra_rat_subsingleton

end Rat

