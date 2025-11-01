/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change for the dual of a module

* `Module.Dual.congr` : equivalent modules have equivalent duals.

If `f : Module.Dual R V` and `Algebra R A`, then

* `Module.Dual.baseChange A f` is the element
of `Module.Dual A (A ⊗[R] V)` deduced by base change.

* `Module.Dual.baseChangeHom` is the `R`-linear map
given by `Module.Dual.baseChange`.

-/

universe u v

namespace Module.Dual

open TensorProduct LinearEquiv

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  (A : Type*) [CommSemiring A] [Algebra R A]

/-- Equivalent modules have equivalent duals. -/
def congr (e : V ≃ₗ[R] W) :
    Module.Dual R V ≃ₗ[R] Module.Dual R W :=
  LinearEquiv.congrLeft R R e

/-- `LinearMap.baseChange` for `Module.Dual`. -/
def baseChange (f : Module.Dual R V) :
    Module.Dual A (A ⊗[R] V) :=
  (AlgebraTensorModule.rid R A A).toLinearMap.comp (LinearMap.baseChange A f)

@[simp]
theorem baseChange_apply_tmul (f : Module.Dual R V) (a : A) (v : V) :
    f.baseChange A (a ⊗ₜ v) = (f v) • a := by
  simp [baseChange]

/-- `Module.Dual.baseChange` as a linear map. -/
def baseChangeHom :
    Module.Dual R V →ₗ[R] Module.Dual A (A ⊗[R] V) where
  toFun := Module.Dual.baseChange A
  map_add' := by unfold Module.Dual.baseChange; aesop
  map_smul' r x := by
    ext
    unfold Module.Dual.baseChange
    simp [LinearMap.baseChange_smul, ← TensorProduct.tmul_smul, mul_smul]

@[simp]
theorem baseChangeHom_apply (f : Module.Dual R V) :
    Module.Dual.baseChangeHom A f = f.baseChange A :=
  rfl

section group

variable {R : Type*} [CommRing R]
  {V : Type*} [AddCommGroup V] [Module R V]
  (A : Type*) [CommRing A] [Algebra R A]

theorem baseChange_sub (f g : Module.Dual R V) :
    Module.Dual.baseChange A (f - g) = Module.Dual.baseChange A f - Module.Dual.baseChange A g := by
  unfold Module.Dual.baseChange; aesop

theorem baseChange_neg (f : Module.Dual R V) :
    Module.Dual.baseChange A (-f) = -(Module.Dual.baseChange A f) := by
  unfold Module.Dual.baseChange; aesop

end group

section comp

variable (B : Type*) [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem baseChange_comp (f : Module.Dual R V) :
    ((f.baseChange A).baseChange B) =
      (Module.Dual.congr (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B V)).symm
       (f.baseChange B) := by
  ext; simp [Module.Dual.congr, congrLeft]

end comp

end Module.Dual
