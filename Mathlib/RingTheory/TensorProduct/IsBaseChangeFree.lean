/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

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

include ibc in
theorem free [Module.Free R V] : Module.Free S W :=
  Module.Free.of_basis (ibc.basis (Module.Free.chooseBasis R V))

end IsBaseChange

section underring

namespace IsBaseChange

open TensorProduct

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  (A : Type*) [CommSemiring A] [Algebra A R]
  [Module A V] [IsScalarTower A R V]

open TensorProduct

variable {ι : Type*} (b : Module.Basis ι R V)

theorem of_basis : IsBaseChange R (Finsupp.linearCombination A b) := by
  classical
  let j := TensorProduct.finsuppScalarRight A R R ι
  refine of_equiv ?_ ?_
  · apply LinearEquiv.ofBijective (Finsupp.linearCombination R b ∘ₗ j)
    rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, j.bijective.of_comp_iff]
    simp [Function.Bijective,
        ← span_range_eq_top_iff_surjective_finsuppLinearCombination,
        ← linearIndependent_iff_injective_finsuppLinearCombination,
        Module.Basis.span_eq, b.linearIndependent]
  · intro x
    suffices (j (1 ⊗ₜ[A] x)) = x.mapRange (algebraMap A R) (by simp) by
      simp [this, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index]
    ext i
    simp [j, Algebra.algebraMap_eq_smul_one]

include A in
/-- Any finite basis of a module can express it as the base change
of a finite free module from any under-ring. -/
theorem of_fintype_basis [Fintype ι] :
    IsBaseChange R (Fintype.linearCombination A b) := by
  have : DecidableEq ι := Classical.typeDecidableEq ι
  let j : R ⊗[A] (ι → A) ≃ₗ[R] ι → R := piScalarRight A R R ι
  refine of_equiv ?_ ?_
  · apply LinearEquiv.ofBijective (Fintype.linearCombination R b ∘ₗ j)
    rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, j.bijective.of_comp_iff]
    simp [Function.Bijective,
        ← span_range_eq_top_iff_surjective_fintypeLinearCombination,
        ← linearIndependent_iff_injective_fintypeLinearCombination,
        Module.Basis.span_eq, b.linearIndependent]
  · intro x
    -- simp? [Fintype.linearCombination_apply] says:
    simp only [LinearEquiv.ofBijective_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, Fintype.linearCombination_apply]
    congr
    ext i
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    simp

variable {A b} in
theorem of_fintype_basis_eq [Fintype ι] {a : ι → A} {v : V} :
    (Fintype.linearCombination A b) a = v ↔
      algebraMap A R ∘ a = b.equivFun v := by
  rw [← LinearEquiv.symm_apply_eq]
  rw [Fintype.linearCombination_apply, b.equivFun_symm_apply]
  simp

end IsBaseChange

end underring
