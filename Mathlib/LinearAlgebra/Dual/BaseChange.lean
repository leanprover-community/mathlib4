/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import Mathlib.Tactic.Conv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
/-!
# Base change for the dual of a module

* `Module.Dual.congr` : equivalent modules have equivalent duals.

If `f : Module.Dual R V` and `Algebra R A`, then

* `Module.Dual.baseChange A f` is the element
  of `Module.Dual A (A ⊗[R] V)` deduced by base change.

* `Module.Dual.baseChangeHom` is the `R`-linear map
  given by `Module.Dual.baseChange`.

* `IsBaseChange.dual` : for finite free modules, taking dual commutes with base change.

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
    Dual R V ≃ₗ[R] Dual R W := congrLeft R R e

/-- `LinearMap.baseChange` for `Module.Dual`. -/
def baseChange : Dual R V →ₗ[R] Dual A (A ⊗[R] V) :=
  (AlgebraTensorModule.rid R A A).compRight R ∘ₗ LinearMap.baseChangeHom R A V R

@[simp]
theorem baseChange_apply_tmul (f : Dual R V) (a : A) (v : V) :
    f.baseChange A (a ⊗ₜ v) = (f v) • a :=
  rfl

variable {B : Type*} [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

open AlgebraTensorModule in
theorem baseChange_baseChange (f : Dual R V) :
    (f.baseChange A).baseChange B = (congr (cancelBaseChange R A B B V)).symm (f.baseChange B) := by
  ext; simp

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

theorem toDual_comp_apply (f : Dual R V) (v : V) :
    ibc.toDual f (j v) = algebraMap R A (f v) := by
  simp [toDual, linearMapLeftRightHom_comp_apply]

theorem toDual_apply (f : Dual R V) :
    ibc.toDual f = (f.baseChange A).congr ibc.equiv := by
  apply ibc.algHom_ext
  intro v
  simp [toDual_comp_apply, Algebra.algebraMap_eq_smul_one]

set_option backward.privateInPublic true in
/-- The linear map underlying `IsBaseChange.toDualBaseChangeLinearEquiv`. -/
private noncomputable def toDualBaseChangeAux :
    A ⊗[R] Dual R V →ₗ[A] Dual A W where
  toAddHom := (TensorProduct.lift {
    toFun a := a • ibc.toDual
    map_add' a b := by simp [add_smul]
    map_smul' r a := by simp }).toAddHom
  map_smul' a g := by
    induction g using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => aesop
    | tmul b f => simp [TensorProduct.smul_tmul', mul_smul]

set_option backward.privateInPublic true in
private theorem toDualBaseChangeAux_tmul (a : A) (f : Dual R V) (v : V) :
    (ibc.toDualBaseChangeAux (a ⊗ₜ[R] f)) (j v) = a * algebraMap R A (f v) := by
  simp [toDualBaseChangeAux, toDual_comp_apply]

variable [Free R V] [Module.Finite R V]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The linear equivalence underlying `IsBaseChange.dual`. -/
noncomputable def toDualBaseChange :
    A ⊗[R] Dual R V ≃ₗ[A] Dual A W := by
  apply LinearEquiv.ofBijective ibc.toDualBaseChangeAux
  let b := Free.chooseBasis R V
  set ι := Free.ChooseBasisIndex R V
  have ibc_pow : IsBaseChange A ((Algebra.linearMap R A).compLeft ι) := (linearMap R A).finitePow ι
  suffices ibc.toDualBaseChangeAux =
      (((b.constr R).symm.baseChange ..).trans ibc_pow.equiv).trans ((ibc.basis b).constr A) from
    this ▸ LinearEquiv.bijective _
  ext f w
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  induction w using ibc.inductionOn with
  | zero => simp
  | tmul v =>
    simp only [toDualBaseChangeAux_tmul, one_mul]
    conv_lhs => rw [← Basis.sum_equivFun b v, map_sum]
    simp [LinearEquiv.baseChange, basis_repr_comp_apply]
  | smul a w h => simp [h]
  | add x y hx hy => simp [map_add, hx, hy]

theorem toDualBaseChange_tmul (a : A) (f : Dual R V) (v : V) :
    (ibc.toDualBaseChange (a ⊗ₜ[R] f)) (j v) = a * algebraMap R A (f v) :=
  toDualBaseChangeAux_tmul ibc a f v

theorem dual : IsBaseChange A (ibc.toDual) := by
  apply of_equiv (toDualBaseChange ibc)
  intro f
  simp [toDualBaseChange, toDualBaseChangeAux]

end IsBaseChange
