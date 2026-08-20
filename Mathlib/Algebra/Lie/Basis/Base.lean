/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Basis.Prod
public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!

# The root system base associated to a Lie algebra basis

-/

@[expose] public section

noncomputable section

namespace LieAlgebra

open AddSubmonoid Function IsKilling LieModule LieSubalgebra Matrix Set

variable {K L : Type*} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L}

namespace Basis

variable {ι : Type*} [Fintype ι] (b : Basis ι H)

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

end Basis

variable [H.IsCartanSubalgebra] [IsTriangularizable K H L]

private lemma cartan_eq_lieSpan [IsKilling K L] (b : (rootSystem H).Base) :
    H = lieSpan K L (range fun i : b.support ↦ (rootSystem H).coroot i) := by
    suffices lieSpan K H (range fun i : b.support ↦ (rootSystem H).coroot i) = ⊤ by
      refine le_antisymm ?_ ?_
      · rwa [← H.comap_lieSpan_range_eq, comap_incl_eq_top] at this
      · simp_rw [lieSpan_le, Set.range_subset_iff, Subtype.coe_prop, implies_true]
    simp_rw [← RootPairing.Base.toCoweightBasis_apply, ← LieSubalgebra.toSubmodule_inj,
      top_toSubmodule, eq_top_iff, ← b.toCoweightBasis.span_eq]
    exact submodule_span_le_lieSpan

private lemma exists_mem_rootSpace_lie_ne_zero' [IsKilling K L]
    {α β : Weight K H L} (hα : α.IsNonZero) (h_ne_bot : rootSpace H (α + β) ≠ ⊥)
    {a : L} (ha : a ∈ rootSpace H α) (ha₀ : a ≠ 0) :
    ∃ b ∈ rootSpace H β, ⁅a, b⁆ ≠ 0 := by
  obtain ⟨a', ha', b, hb, hab⟩ := exists_mem_rootSpace_lie_ne_zero hα h_ne_bot
  obtain ⟨t, rfl⟩ : ∃ t : K, t • a = a' :=
    Submodule.mem_span_singleton.mp <| by rwa [← toSubmodule_rootSpace_eq_span α hα a ha₀ ha]
  exact ⟨b, hb, by contrapose! hab; simp [hab]⟩

lemma lieSpan_range_union_eq_top_of_mem_rootSpace [IsKilling K L] (b : (rootSystem H).Base)
    (e f : b.support → L)
    (ef_sl2 : ∀ α : b.support, IsSl2Triple ((rootSystem H).coroot α : L) (e α) (f α))
    (e_mem :  ∀ α : b.support, e α ∈ rootSpace H α)
    (f_mem :  ∀ α : b.support, f α ∈ rootSpace H (-↑α)) :
    lieSpan K L (range e ∪ range f) = ⊤ := by
  set S := lieSpan K L (range e ∪ range f) with S_def
  have e_mem_S (i : b.support) : e i ∈ S := subset_lieSpan (mem_union_left _ ⟨i, rfl⟩)
  have f_mem_S (i : b.support) : f i ∈ S := subset_lieSpan (mem_union_right _ ⟨i, rfl⟩)
  suffices ∀ α : H.root, rootSpace H α ≤ S.toSubmodule by
    replace this (α : Weight K H L) (hα : α.IsNonZero) : rootSpace H α ≤ S.toSubmodule :=
      this ⟨α, by simpa⟩
    rw [eq_top_iff, ← toSubmodule_le_toSubmodule, top_toSubmodule,
      ← LieSubmodule.top_toSubmodule (L := H), ← cartan_sup_iSup_rootSpace_eq_top H]
    have H_le : H ≤ S := by
      nth_rw 1 [cartan_eq_lieSpan b, lieSpan_le]
      rintro - ⟨i, rfl⟩
      simpa only [← (ef_sl2 i).lie_e_f, SetLike.mem_coe] using lie_mem _ (e_mem_S i) (f_mem_S i)
    simpa [H_le]
  suffices h : ∀ α : H.root,
    rootSpace H α ≤ S.toSubmodule ∧ rootSpace H (-α : Weight K H L) ≤ S.toSubmodule by grind
  refine fun α ↦ b.induction_add (p := fun α ↦
    rootSpace H α ≤ S.toSubmodule ∧ rootSpace H (-α : Weight K H L) ≤ S.toSubmodule) α ?_ ?_ ?_
  · rintro β hβ
    simpa [rootSystem_reflectionPerm_self_eq_neg] using hβ.symm
  · rintro β hβ
    set β' : b.support := ⟨β, hβ⟩
    have hβp : β.val.IsNonZero := H.isNonZero_coe_root β
    have hβn : (-β.val).IsNonZero := by simpa [Weight.isNonZero_neg] using H.isNonZero_coe_root β
    simpa only [Weight.coe_coe,
      toSubmodule_rootSpace_eq_span _ hβp (e β') (ef_sl2 β').e_ne_zero (e_mem β'),
      toSubmodule_rootSpace_eq_span _ hβn (f β') (ef_sl2 β').f_ne_zero (f_mem β'),
      Submodule.span_singleton_le_iff_mem, mem_toSubmodule] using ⟨e_mem_S β', f_mem_S β'⟩
  · rintro i j k hk ⟨hip, hin⟩ hj
    constructor
    · have h_ne_bot : rootSpace H ((rootSystem H).root j + (rootSystem H).root i) ≠ ⊥ := by
        convert (k : Weight K H L).genWeightSpace_ne_bot
        rw [← LinearMap.coe_add, add_comm, ← hk, rootSystem_root_apply, Weight.coe_coe]
      obtain ⟨x, hx, hlie⟩ := exists_mem_rootSpace_lie_ne_zero'
        (H.isNonZero_coe_root j) h_ne_bot (e_mem ⟨j, hj⟩) (ef_sl2 ⟨j, hj⟩).e_ne_zero
      have hmem : ⁅e ⟨j, hj⟩, x⁆ ∈ rootSpace H ((rootSystem H).root k) := by
        rw [hk, add_comm]
        exact mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L _ _ (e_mem ⟨j, hj⟩) hx
      simpa [toSubmodule_rootSpace_eq_span _ (H.isNonZero_coe_root k) _ hlie hmem] using
        lie_mem S (e_mem_S ⟨j, hj⟩) (hip hx)
    · replace hk : ⇑k.val = ⇑i.val + ⇑j.val := by ext x; simpa using DFunLike.congr_fun hk x
      replace hk : (⇑(-i).val + ⇑(-j).val) = ⇑(-k).val := by simp [hk, -neg_add_rev, neg_add]
      have h_ne_bot : rootSpace H (⇑(-j).val + ⇑(-i).val) ≠ ⊥ := by
        rw [add_comm, hk]; exact (-k).val.genWeightSpace_ne_bot
      obtain ⟨x, hx, hlie⟩ := exists_mem_rootSpace_lie_ne_zero'
        (H.isNonZero_coe_root (-j)) h_ne_bot (f_mem ⟨j, hj⟩) (ef_sl2 ⟨j, hj⟩).f_ne_zero
      have hmem : ⁅f ⟨j, hj⟩, x⁆ ∈ rootSpace H ⇑(-k).val := by
        rw [← hk, add_comm]
        exact mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L _ _ (f_mem ⟨j, hj⟩) hx
      simpa [toSubmodule_rootSpace_eq_span _ (H.isNonZero_coe_root (-k)) _ hlie hmem,
        ← val_neg_root] using lie_mem S (f_mem_S ⟨j, hj⟩) (hin hx)

open RootPairing in
lemma exists_basis_of_base [IsKilling K L] (b : (rootSystem H).Base) :
    ∃ B : Basis b.support H, B.A = b.cartanMatrix ∧ (∀ i, B.h i = (rootSystem H).coroot i) := by
  have nonZero (α : b.support) : (α : Weight K H L).IsNonZero := by
    obtain ⟨⟨α, hα⟩, -⟩ := α
    simpa using hα
  choose h e f ef_sl2 e_mem f_mem using fun α ↦ exists_isSl2Triple_of_weight_isNonZero (nonZero α)
  have h_coroot (i : b.support) : h i = (rootSystem H).coroot i :=
    (ef_sl2 i).h_eq_coroot (nonZero i) (e_mem i) (f_mem i)
  simp_rw [h_coroot] at ef_sl2
  let B : Basis b.support H :=
    { A := b.cartanMatrix
      h i := (rootSystem H).coroot i
      e i := e i
      f i := f i
      cartan_eq_lieSpan := cartan_eq_lieSpan b
      linInd := b.linearIndepOn_coroot.map_injOn H.incl.toLinearMap <| by simp
      nondegen := b.cartanMatrix_nondegenerate
      sl2 i := ef_sl2 i
      lie_h_h := by simp [← coe_bracket, trivial_lie_zero]
      span_ef := lieSpan_range_union_eq_top_of_mem_rootSpace b e f ef_sl2 e_mem f_mem
      lie_h_e i j := by
        have : (b.cartanMatrix i j : K) = algebraMap ℤ K (b.cartanMatrix i j) := by simp
        rw [← LieSubalgebra.coe_bracket_of_module, lie_eq_smul_of_mem_rootSpace (e_mem i),
          ← Int.cast_smul_eq_zsmul K, this, Base.cartanMatrix, Base.cartanMatrixIn_def,
          algebraMap_pairingIn, rootSystem_coroot_apply, rootSystem_pairing_apply]
      lie_h_f i j := by
        have : (b.cartanMatrix i j : K) = algebraMap ℤ K (b.cartanMatrix i j) := by simp
        rw [neg_smul, ← LieSubalgebra.coe_bracket_of_module, lie_eq_smul_of_mem_rootSpace (f_mem i),
          ← Int.cast_smul_eq_zsmul K, this, Base.cartanMatrix, Base.cartanMatrixIn_def,
          algebraMap_pairingIn, rootSystem_coroot_apply, rootSystem_pairing_apply, Pi.neg_apply,
          neg_smul]
      lie_e_f_ne i j hij := by
        set χ : H → K := ⇑i.val.val - ⇑j.val.val with hχ
        suffices rootSpace H χ = ⊥ by
          have aux : ⁅e i, f j⁆ ∈ rootSpace H χ := by
            rw [hχ, sub_eq_add_neg]
            exact mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L _ _ (e_mem i) (f_mem j)
          simpa [this] using aux
        replace hij : χ ≠ 0 := by contrapose hij; rw [hχ, sub_eq_zero] at hij; aesop
        have := b.sub_notMem_range_root i.property j.property
        simp only [rootSystem_root_apply, mem_range, Subtype.exists, Finset.mem_filter,
          Finset.mem_univ, true_and, exists_prop, not_exists, not_and, ne_eq] at this
        contrapose! this
        exact ⟨⟨χ, this⟩, hij, LinearMap.ext fun x ↦ by simp [hχ]⟩ }
  exact ⟨B, rfl, by simp [B]⟩

open scoped Classical in
/-- Lie algebras with equivalent root systems are equivalent. -/
def equivOfRootSystemEquiv {L₂ : Type*} [LieRing L₂] [LieAlgebra K L₂] [FiniteDimensional K L₂]
    {H₂ : LieSubalgebra K L₂} [H₂.IsCartanSubalgebra] [IsTriangularizable K H₂ L₂]
    [IsSimple K L] [IsSimple K L₂]
    (e : (rootSystem H).Equiv (rootSystem H₂)) :
    L ≃ₗ⁅K⁆ L₂ :=
  letI b := (rootSystem H).nonempty_base.some
  letI B₁ := (exists_basis_of_base b).choose
  letI B₂ := (exists_basis_of_base (b.map e)).choose
  have hA : B₁.A.reindex (b.supportMapEquiv e) (b.supportMapEquiv e) = B₂.A := by
    have hB₁ : B₁.A = _ := (exists_basis_of_base b).choose_spec.1
    have hB₂ : B₂.A = _ := (exists_basis_of_base (b.map e)).choose_spec.1
    simp [hB₁, hB₂, b.map_equiv_cartanMatrix e]
  LieAlgebra.Basis.equivOfReindex _ _ _ hA

end LieAlgebra
