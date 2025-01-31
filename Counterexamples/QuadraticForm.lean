/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# `QuadraticForm R M` and `Subtype LinearMap.IsSymm` are distinct notions in characteristic 2

The main result of this file is `LinearMap.BilinForm.not_injOn_toQuadraticForm_isSymm`.

The counterexample we use is $B (x, y) (x', y') ↦ xy' + x'y$ where `x y x' y' : ZMod 2`.
-/


variable (F : Type*) [CommRing F]

open LinearMap
open LinearMap.BilinForm
open LinearMap (BilinForm)
open LinearMap.BilinMap

namespace Counterexample


/-- The bilinear form we will use as a counterexample, over some field `F` of characteristic two. -/
def B : BilinForm F (F × F) :=
  (mul F F).compl₁₂ (fst _ _ _) (snd _ _ _) + (mul F F).compl₁₂ (snd _ _ _) (fst _ _ _)

@[simp]
theorem B_apply (x y : F × F) : B F x y = x.1 * y.2 + x.2 * y.1 :=
  rfl

theorem isSymm_B : (B F).IsSymm := fun x y => by simp [mul_comm, add_comm]

theorem isAlt_B [CharP F 2] : (B F).IsAlt := fun x => by
  simp [mul_comm, CharTwo.add_self_eq_zero (x.1 * x.2)]

theorem B_ne_zero [Nontrivial F] : B F ≠ 0 := fun h => by
  simpa using LinearMap.congr_fun₂ h (1, 0) (1, 1)

/-- `LinearMap.BilinForm.toQuadraticForm` is not injective on symmetric bilinear forms.

This disproves a weaker version of `QuadraticForm.associated_left_inverse`.
-/
theorem LinearMap.BilinForm.not_injOn_toQuadraticForm_isSymm.{u} :
    ¬∀ {R M : Type u} [CommSemiring R] [AddCommMonoid M], ∀ [Module R M],
      Set.InjOn (toQuadraticMap : BilinForm R M → QuadraticForm R M) {B | B.IsSymm} := by
  intro h
  let F := ULift.{u} (ZMod 2)
  apply B_ne_zero F
  apply h (isSymm_B F) isSymm_zero
  rw [toQuadraticMap_zero, toQuadraticMap_eq_zero]
  exact isAlt_B F

end Counterexample
