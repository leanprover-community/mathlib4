/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
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

@[expose] public section

namespace Module.Dual

open TensorProduct LinearEquiv

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  (A : Type*) [CommSemiring A] [Algebra R A]

/-- Equivalent modules have equivalent duals. -/
@[simps!] def congr (e : V ≃ₗ[R] W) :
    Module.Dual R V ≃ₗ[R] Module.Dual R W :=
  LinearEquiv.congrLeft R R e

/-- `LinearMap.baseChange` for `Module.Dual`. -/
def baseChange : Module.Dual R V →ₗ[R] Module.Dual A (A ⊗[R] V) :=
  (AlgebraTensorModule.rid R A A).compRight R ∘ₗ LinearMap.baseChangeHom R A V R

@[simp]
theorem baseChange_apply_tmul (f : Module.Dual R V) (a : A) (v : V) :
    f.baseChange A (a ⊗ₜ v) = (f v) • a :=
  rfl

variable {B : Type*} [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

open AlgebraTensorModule in
theorem baseChange_baseChange (f : Module.Dual R V) :
    ((f.baseChange A).baseChange B) =
      (congr (cancelBaseChange R A B B V)).symm (f.baseChange B) := by
  ext; simp [congr, congrLeft]

end Module.Dual

namespace IsBaseChange

open Module TensorProduct

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  {A : Type*} [CommSemiring A] [Algebra R A] [Module A W] [IsScalarTower R A W]
  {j : V →ₗ[R] W} (ibc : IsBaseChange A j)

/-- The base change of an element of the dual. -/
noncomputable def toDual :
    Dual R V →ₗ[R] Dual A W :=
  linearMapLeftRightHom ibc (Algebra.linearMap R A)

theorem toDual_comp_apply (f : Module.Dual R V) (v : V) :
    ibc.toDual f (j v) = algebraMap R A (f v) := by
  simp [toDual, linearMapLeftRightHom_comp_apply]

theorem toDual_apply (f : Module.Dual R V) :
    ibc.toDual f = (f.baseChange A).congr ibc.equiv := by
  apply ibc.algHom_ext
  intro v
  simp [toDual_comp_apply, Algebra.algebraMap_eq_smul_one]

/-- The linear map underlying `IsBaseChange.toDualBaseChangeLinearEquiv`. -/
noncomputable def toDualBaseChange :
    A ⊗[R] Module.Dual R V →ₗ[A] Module.Dual A W where
  toAddHom := (TensorProduct.lift {
    toFun a := a • ibc.toDual
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

theorem toDualBaseChange_tmul (a : A) (f : Dual R V) (v : V) :
    (ibc.toDualBaseChange (a ⊗ₜ[R] f)) (j v) = a * algebraMap R A (f v) := by
  simp [toDualBaseChange, toDual_comp_apply]

variable [Free R V] [Module.Finite R V]

/-- The linear equivalence underlying `IsBaseChange.dual`. -/
noncomputable def toDualBaseChangeLinearEquiv :
    A ⊗[R] Dual R V ≃ₗ[A] Dual A W := by
  apply LinearEquiv.ofBijective ibc.toDualBaseChange
  let b := Free.chooseBasis R V
  set ι := Free.ChooseBasisIndex R V
  have : Fintype ι := Free.ChooseBasisIndex.fintype R V
  have ibc' : IsBaseChange A (Algebra.linearMap R A) := linearMap R A
  have ibc'_pow := ibc'.finitePow ι
  suffices ibc.toDualBaseChange = (((b.constr R).symm.baseChange ..).trans ibc'_pow.equiv).trans
    ((ibc.basis b).constr A) by
    rw [this]
    apply LinearEquiv.bijective
  ext f w
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  induction w using ibc.inductionOn with
  | zero => simp
  | tmul v =>
    simp only [toDualBaseChange_tmul, one_mul]
    conv_lhs => rw [← Basis.sum_equivFun b v, map_sum]
    simp [LinearEquiv.baseChange, IsBaseChange.equiv_tmul,
      basis_repr_comp_apply, b.constr_symm_apply]
  | smul a w h => simp [h]
  | add x y hx hy => simp [map_add, hx, hy]

theorem dual : IsBaseChange A (ibc.toDual) := by
  apply of_equiv (toDualBaseChangeLinearEquiv ibc)
  intro f
  simp [toDualBaseChangeLinearEquiv, toDualBaseChange]

end IsBaseChange
