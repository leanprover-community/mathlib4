/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic

#align_import quadratic_form from "leanprover-community/mathlib"@"328375597f2c0dd00522d9c2e5a33b6a6128feeb"

/-!
# `QuadraticForm R M` and `Subtype LinearMap.IsSymm` are distinct notions in characteristic 2

The main result of this file is `LinearMap.BilinForm.not_injOn_toQuadraticForm_isSymm`.

The counterexample we use is $B (x, y) (x', y') ↦ xy' + x'y$ where `x y x' y' : ZMod 2`.
-/


variable (F : Type*) [Nontrivial F] [CommRing F] [CharP F 2]

open LinearMap
open LinearMap.BilinForm
open LinearMap (BilinForm)

namespace Counterexample

set_option linter.uppercaseLean3 false

/-- The bilinear form we will use as a counterexample, over some field `F` of characteristic two. -/
def B : BilinForm F (F × F) :=
  (mul F F).compl₁₂ (fst _ _ _) (snd _ _ _) + (mul F F).compl₁₂ (snd _ _ _) (fst _ _ _)
#align counterexample.B Counterexample.B

@[simp]
theorem B_apply (x y : F × F) : B F x y = x.1 * y.2 + x.2 * y.1 :=
  rfl
#align counterexample.B_apply Counterexample.B_apply

theorem isSymm_B : (B F).IsSymm := fun x y => by simp [mul_comm, add_comm]
#align counterexample.is_symm_B Counterexample.isSymm_B

theorem isAlt_B : (B F).IsAlt := fun x => by simp [mul_comm, CharTwo.add_self_eq_zero (x.1 * x.2)]
#align counterexample.is_alt_B Counterexample.isAlt_B

theorem B_ne_zero : B F ≠ 0 := fun h => by simpa using LinearMap.congr_fun₂ h (1, 0) (1, 1)
#align counterexample.B_ne_zero Counterexample.B_ne_zero

/-- `LinearMap.BilinForm.toQuadraticForm` is not injective on symmetric bilinear forms.

This disproves a weaker version of `QuadraticForm.associated_left_inverse`.
-/
theorem LinearMap.BilinForm.not_injOn_toQuadraticForm_isSymm.{u} :
    ¬∀ {R M : Type u} [CommSemiring R] [AddCommMonoid M], ∀ [Module R M],
      Set.InjOn (toQuadraticForm : BilinForm R M → QuadraticForm R M) {B | B.IsSymm} := by
  intro h
  let F := ULift.{u} (ZMod 2)
  apply B_ne_zero F
  apply h (isSymm_B F) isSymm_zero
  rw [toQuadraticForm_zero, toQuadraticForm_eq_zero]
  exact isAlt_B F
#align counterexample.bilin_form.not_inj_on_to_quadratic_form_is_symm Counterexample.LinearMap.BilinForm.not_injOn_toQuadraticForm_isSymm

end Counterexample
