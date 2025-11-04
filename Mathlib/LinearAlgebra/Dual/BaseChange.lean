/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Base change for the dual of a module

* `Module.Dual.congr` : equivalent modules have equivalent duals.

If `f : Module.Dual R V` and `Algebra R A`, then

* `Module.Dual.baseChange A f` is the element
of `Module.Dual A (A ⊗[R] V)` deduced by base change.

* `Module.Dual.baseChangeHom` is the `R`-linear map
given by `Module.Dual.baseChange`.

* `IsBaseChange.dual` : for finite free modules, taking dual commutes with base change.

## TODO

Generalize for more general modules of linear maps.

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

@[simp]
theorem baseChange_add (f g : Module.Dual R V) :
    (f + g).baseChange A = f.baseChange A + g.baseChange A := by
  unfold baseChange; aesop

@[simp]
theorem baseChange_smul (r : R) (f : Module.Dual R V) :
    (r • f).baseChange A = r • f.baseChange A := by
  unfold baseChange
  ext x
  simp [LinearMap.baseChange_smul, ← TensorProduct.tmul_smul, mul_smul]

/-- `Module.Dual.baseChange` as a linear map. -/
def baseChangeHom :
    Module.Dual R V →ₗ[R] Module.Dual A (A ⊗[R] V) where
  toFun := baseChange A
  map_add' := baseChange_add A
  map_smul' := baseChange_smul A

@[simp]
theorem baseChangeHom_apply (f : Module.Dual R V) :
    baseChangeHom A f = f.baseChange A :=
  rfl

section group

variable {R : Type*} [CommRing R]
  {V : Type*} [AddCommGroup V] [Module R V]
  (A : Type*) [CommRing A] [Algebra R A]

theorem baseChange_sub (f g : Module.Dual R V) :
    baseChange A (f - g) = baseChange A f - baseChange A g := by
  unfold baseChange; aesop

theorem baseChange_neg (f : Module.Dual R V) :
    baseChange A (-f) = -(baseChange A f) := by
  unfold baseChange; aesop

end group

section comp

variable (B : Type*) [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem baseChange_comp (f : Module.Dual R V) :
    ((f.baseChange A).baseChange B) =
      (congr (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B V)).symm
       (f.baseChange B) := by
  ext; simp [congr, congrLeft]

end comp

end Module.Dual

namespace IsBaseChange

open TensorProduct

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  {A : Type*} [CommSemiring A] [Algebra R A] [Module A W] [IsScalarTower R A W]
  {j : V →ₗ[R] W} (ibc : IsBaseChange A j)

/-- The base change of an element of the dual. -/
noncomputable def toDual (f : Module.Dual R V) :
    Module.Dual A W :=
  (f.baseChange A).congr ibc.equiv

/-- The base change of an element of the dual. -/
noncomputable def toDualHom :
    Module.Dual R V →ₗ[R] Module.Dual A W where
  toFun f := ibc.toDual f
  map_add' f g := by unfold toDual; aesop
  map_smul' r f := by unfold toDual; aesop

noncomputable def toDualBaseChangeHom :
    A ⊗[R] Module.Dual R V →ₗ[A] Module.Dual A W where
  toAddHom := (TensorProduct.lift {
    toFun a := a • ibc.toDualHom
    map_add' a b := by simp [add_smul]
    map_smul' r a := by simp }).toAddHom
  map_smul' a g := by
    induction g using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply] at hx hy
      simp [map_add, hx, hy]
    | tmul b f =>
      simp [TensorProduct.smul_tmul', mul_smul]

theorem toDualBaseChangeHom_apply_comp (f : Module.Dual R V) (v : V) :
    ibc.toDualBaseChangeHom (1 ⊗ₜ[R] f) (j v) = algebraMap R A (f v) := by
  simp [toDualBaseChangeHom, toDualHom, toDual, Module.Dual.congr, LinearEquiv.congrLeft,
        IsBaseChange.equiv_symm_apply, Algebra.algebraMap_eq_smul_one]

variable [Module.Free R V] [Module.Finite R V]

noncomputable def toDualBaseChangeLinearEquiv :
        A ⊗[R] Module.Dual R V ≃ₗ[A] Module.Dual A W := by
  apply LinearEquiv.ofBijective ibc.toDualBaseChangeHom
  classical
  let b := Module.Free.chooseBasis R V
  set ι := Module.Free.ChooseBasisIndex R V
  have ibc' : IsBaseChange A (Algebra.linearMap R A) := linearMap R A
  have ibc'_pow := ibc'.finitePow ι
  suffices ibc.toDualBaseChangeHom = (((b.constr R).symm.baseChange ..).trans ibc'_pow.equiv).trans
    ((ibc.basis b).constr A) by
    rw [this]
    apply LinearEquiv.bijective
  ext f w
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  induction w using ibc.inductionOn with
  | zero => simp
  | tmul v =>
    rw [toDualBaseChangeHom_apply_comp]
    conv_lhs => rw [← Module.Basis.sum_equivFun b v, map_sum]
    simp [LinearEquiv.baseChange, IsBaseChange.equiv_tmul,
      basis_repr_comp_apply, b.constr_symm_apply]
  | smul a w h => simp [h]
  | add x y hx hy => simp [map_add, hx, hy]

theorem dual : IsBaseChange A (ibc.toDualHom) := by
  apply of_equiv (toDualBaseChangeLinearEquiv ibc)
  intro f
  simp [toDualBaseChangeLinearEquiv, toDualBaseChangeHom]

end IsBaseChange
