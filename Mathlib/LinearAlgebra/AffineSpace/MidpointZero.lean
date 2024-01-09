/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.CharP.Invertible
import Mathlib.LinearAlgebra.AffineSpace.Midpoint

#align_import linear_algebra.affine_space.midpoint_zero from "leanprover-community/mathlib"@"78261225eb5cedc61c5c74ecb44e5b385d13b733"

/-!
# Midpoint of a segment for characteristic zero

We collect lemmas that require that the underlying ring has characteristic zero.

## Tags

midpoint
-/


open AffineMap AffineEquiv

theorem lineMap_inv_two {R : Type*} {V P : Type*} [DivisionRing R] [CharZero R] [AddCommGroup V]
    [Module R V] [AddTorsor V P] (a b : P) : lineMap a b (2⁻¹ : R) = midpoint R a b :=
  rfl
#align line_map_inv_two lineMap_inv_two

theorem lineMap_one_half {R : Type*} {V P : Type*} [DivisionRing R] [CharZero R] [AddCommGroup V]
    [Module R V] [AddTorsor V P] (a b : P) : lineMap a b (1 / 2 : R) = midpoint R a b := by
  rw [one_div, lineMap_inv_two]
#align line_map_one_half lineMap_one_half

theorem homothety_invOf_two {R : Type*} {V P : Type*} [CommRing R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [AddTorsor V P] (a b : P) :
    homothety a (⅟ 2 : R) b = midpoint R a b :=
  rfl
#align homothety_inv_of_two homothety_invOf_two

theorem homothety_inv_two {k : Type*} {V P : Type*} [Field k] [CharZero k] [AddCommGroup V]
    [Module k V] [AddTorsor V P] (a b : P) : homothety a (2⁻¹ : k) b = midpoint k a b :=
  rfl
#align homothety_inv_two homothety_inv_two

theorem homothety_one_half {k : Type*} {V P : Type*} [Field k] [CharZero k] [AddCommGroup V]
    [Module k V] [AddTorsor V P] (a b : P) : homothety a (1 / 2 : k) b = midpoint k a b := by
  rw [one_div, homothety_inv_two]
#align homothety_one_half homothety_one_half

@[simp]
theorem pi_midpoint_apply {k ι : Type*} {V : ι → Type*} {P : ι → Type*} [Field k]
    [Invertible (2 : k)] [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, AddTorsor (V i) (P i)] (f g : ∀ i, P i) (i : ι) :
    midpoint k f g i = midpoint k (f i) (g i) :=
  rfl
#align pi_midpoint_apply pi_midpoint_apply
