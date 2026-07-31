/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Basis.Basic
public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!

# The root system base associated to a Lie algebra basis

-/

@[expose] public section

noncomputable section

namespace LieAlgebra.Basis

open AddSubmonoid Function IsKilling LieModule LieSubalgebra Matrix Set

variable {ι K L : Type*} [Fintype ι] [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] {H : LieSubalgebra K L} (b : Basis ι H)

/-- The elements `LieAlgebra.Basis.baseSupp` as roots in the sense of `LieSubalgebra.root`. -/
def baseSupp' (i : ι) :
    letI := b.isCartanSubalgebra
    H.root := by
  let := b.isCartanSubalgebra
  refine ⟨⟨b.baseSupp i, ?_⟩, ?_⟩
  · simp only [LieSubmodule.eq_bot_iff, ne_eq, not_forall]
    exact ⟨b.e i, (mem_genWeightSpace _ _ _).mpr fun x ↦ ⟨1, by simp⟩, (b.sl2 i).e_ne_zero⟩
  · simpa [Weight.IsNonZero, Weight.IsZero] using b.linearIndependent_baseSupp.ne_zero i

@[simp] lemma coe_linearMap_baseSupp' (i : ι) : b.baseSupp' i = b.baseSupp i := rfl

variable [IsTriangularizable K H L] [IsKilling K L]

lemma linearIndepOn_root_baseSupp :
    letI := b.isCartanSubalgebra
    LinearIndepOn K (rootSystem H).root (range b.baseSupp') := by
  let e : ι ≃ range b.baseSupp' := Equiv.ofInjective _ <| fun i j hij ↦
    b.linearIndependent_baseSupp.injective <| by simpa [baseSupp'] using hij
  rw [LinearIndepOn, ← linearIndependent_equiv e]
  exact b.linearIndependent_baseSupp

lemma root_mem_or_mem_neg (χ : letI := b.isCartanSubalgebra; H.root) :
    letI := b.isCartanSubalgebra
    ( (rootSystem H).root χ ∈ closure ((rootSystem H).root '' range b.baseSupp') ∨
     -(rootSystem H).root χ ∈ closure ((rootSystem H).root '' range b.baseSupp')) := by
  let := b.isCartanSubalgebra
  have (n : ι → ℕ) :
      ∑ i, n i • b.baseSupp i ∈ closure (⇑(rootSystem H).root '' range b.baseSupp') := by
    simp_rw [← Submodule.span_nat_eq_addSubmonoidClosure, Submodule.mem_toAddSubmonoid]
    exact Submodule.sum_smul_mem _ _ fun i _ ↦ Submodule.subset_span <| by simp
  let s : Set (H → K) := {0} ∪
    {f | ∃ n : ι → ℕ, n ≠ 0 ∧ f = -∑ i, n i • b.baseSupp i} ∪
    {f | ∃ n : ι → ℕ, n ≠ 0 ∧ f =  ∑ i, n i • b.baseSupp i}
  have hs : ⨆ α ∈ s, rootSpace H α = ⊤ := by
    have := b.iSup_cartan_borelLower_borelUpper_eq_top
    rw [borelLower_eq, borelUpper_eq, b.cartan_eq] at this
    rw [iSup_union, iSup_union]
    simpa [iSup_and, iSup_comm (ι := H → K)] using this
  obtain ⟨χ, hχ⟩ := χ
  change χ.toLinear ∈ _ ∨ -χ.toLinear ∈ _
  replace hs : ⇑χ ∈ s :=
    (iSupIndep_genWeightSpace K H L).mem_of_biSup_eq_top hs χ.genWeightSpace_ne_bot
  replace hs : (∃ n : ι → ℕ, n ≠ 0 ∧ χ.toLinear = -∑ i, n i • b.baseSupp i) ∨
               (∃ n : ι → ℕ, n ≠ 0 ∧ χ.toLinear = ∑ i, n i • b.baseSupp i) := by
    have hχ' : ¬ χ.IsZero := by simpa using hχ
    simp only [hχ', s, singleton_union, mem_union, mem_insert_iff, Weight.coe_eq_zero_iff,
      mem_ofPred_eq, false_or] at hs
    simpa only [← LinearMap.coe_neg, ← Weight.coe_coe, LinearMap.coe_injective.eq_iff] using hs
  refine hs.symm.imp (fun ⟨n, hn₀, hn⟩ ↦ ?_) (fun ⟨n, hn₀, hn⟩ ↦ ?_) <;> simpa [hn] using this n

/-- The distinguished root system base associated to a basis. -/
def base :
    letI := b.isCartanSubalgebra
    RootPairing.Base (rootSystem H) :=
  letI := b.isCartanSubalgebra
  .mk' (rootSystem H) (range b.baseSupp') b.linearIndepOn_root_baseSupp b.root_mem_or_mem_neg

/-- The support of `LieAlgebra.Basis.base` is in one-to-one correspondence with the indexing
set of the basis. -/
def baseSupportEquiv : ι ≃ b.base.support :=
  have : Injective b.baseSupp' :=
    fun i j hij ↦ b.linearIndependent_baseSupp.injective <| by simpa [baseSupp'] using hij
  (Equiv.ofInjective _ this).trans (Set.Finite.subtypeEquivToFinset _)

@[simp] lemma coe_baseSupportEquiv_apply (i : ι) : b.baseSupportEquiv i = b.baseSupp i := rfl

@[simp] lemma coroot_eq_h' (i : ι) :
    letI := b.isCartanSubalgebra
    coroot (b.baseSupportEquiv i) = b.h' i := by
  let := b.isCartanSubalgebra
  suffices b.h' i ∈ corootSpace (b.baseSupp' i) by
    have _i : IsAddTorsionFree L := .of_isTorsionFree K L
    exact (eq_coroot_of_mem_corootSpace_of_two (b.baseSupp' i).val this (by simp [baseSupp'])).symm
  have h_mem : ⁅b.e i, b.f i⁆ ∈ H := by
    nth_rw 1 [(b.sl2 i).lie_e_f, b.cartan_eq_lieSpan]
    exact subset_lieSpan <| mem_range_self i
  have h_eq : b.h' i = ⟨⁅b.e i, b.f i⁆, h_mem⟩ := by simp [(b.sl2 i).lie_e_f, h']
  rw [h_eq]
  have he : b.e i ∈ rootSpace H (b.baseSupp i) :=
    (mem_genWeightSpace _ _ _).mpr fun ⟨z, hz⟩ ↦ ⟨1, by simp⟩
  have hf : b.f i ∈ rootSpace H (-b.baseSupp i) :=
    (mem_genWeightSpace _ _ _).mpr fun ⟨z, hz⟩ ↦ ⟨1, by simp [← eq_neg_iff_add_eq_zero]⟩
  exact (mem_corootSpace _).mpr <| Submodule.subset_span ⟨b.e i, he, b.f i, hf, rfl⟩

lemma cartanMatrix_base_eq :
    b.base.cartanMatrix = b.A.reindex b.baseSupportEquiv b.baseSupportEquiv := by
  suffices b.base.cartanMatrix.reindex b.baseSupportEquiv.symm b.baseSupportEquiv.symm = b.A by
    rwa [← (reindex b.baseSupportEquiv b.baseSupportEquiv).symm_apply_eq]
  ext i j
  apply FaithfulSMul.algebraMap_injective ℤ K
  rw [reindex_apply, submatrix_apply, RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  simp [← Weight.coe_coe]

end LieAlgebra.Basis
