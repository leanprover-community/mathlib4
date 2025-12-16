/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Base change of a free module

* `IsBaseChange.basis` : the natural basis of the base change of a module with a basis

* `IsBaseChange.free` : a base change of a free module is free.

-/

@[expose] public section

namespace IsBaseChange

variable {R : Type*} [CommSemiring R]
    {S : Type*} [CommSemiring S] [Algebra R S]
    {V : Type*} [AddCommMonoid V] [Module R V]
    {W : Type*} [AddCommMonoid W] [Module R W] [Module S W] [IsScalarTower R S W]
    {ι : Type*}
    {ε : V →ₗ[R] W}

variable (b : Module.Basis ι R V) (ibc : IsBaseChange S ε)

/-- The basis of a module deduced by base change from a free module with a basis. -/
noncomputable def basis :
    Module.Basis ι S W where
  repr := (ibc.equiv.symm.trans (b.repr.baseChange R S _ _)).trans
      (finsuppPow ι (linearMap R S)).equiv

theorem basis_apply (i) : ibc.basis b i = ε (b i) := by
  simp only [basis, LinearEquiv.baseChange, Module.Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  generalize_proofs _ _ _ _ ibcRA
  have : ibcRA.equiv.symm (Finsupp.single i 1) = 1 ⊗ₜ (Finsupp.single i 1) := by
    simp [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul]
  simp [this, IsBaseChange.equiv_tmul]

theorem basis_repr_comp_apply (v i) :
    (ibc.basis b).repr (ε v) i = algebraMap R S (b.repr v i) := by
  conv_lhs => rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply,
    map_finsuppSum, map_finsuppSum]
  simp only [map_smul, Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single i]
  · rw [← IsScalarTower.algebraMap_smul S (b.repr v i) (ε (b i)),
      map_smul, ← ibc.basis_apply]
    simp [Finsupp.single_eq_same, Algebra.algebraMap_eq_smul_one]
  · intro i' _ h
    rw [← IsScalarTower.algebraMap_smul S (b.repr v i') (ε (b i')), map_smul,
      ← ibc.basis_apply]
    simp [Finsupp.single_eq_of_ne (Ne.symm h)]
  · simp

theorem basis_repr_comp (v : V) :
    (ibc.basis b).repr (ε v) =
      Finsupp.mapRange.linearMap (Algebra.linearMap R S) (b.repr v) := by
  ext i
  simp [basis_repr_comp_apply]

variable [Module.Free R V]

include ibc in
theorem free : Module.Free S W :=
  Module.Free.of_basis (ibc.basis (Module.Free.chooseBasis R V))

end IsBaseChange
