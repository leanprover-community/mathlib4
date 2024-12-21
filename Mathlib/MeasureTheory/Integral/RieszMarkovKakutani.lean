/-
Copyright (c) 2022 Jesse Reimann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Reimann, Kalle Kytölä
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.PartitionOfUnity

/-!
#  Riesz–Markov–Kakutani representation theorem

This file will prove the Riesz-Markov-Kakutani representation theorem on a locally compact
T2 space `X`. As a special case, the statements about linear functionals on bounded continuous
functions follows.

To make use of the existing API, the measure is constructed from a content `λ` on the
compact subsets of a locally compact space X, rather than the usual construction of open sets in the
literature.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/


noncomputable section

open scoped BoundedContinuousFunction NNReal ENNReal
open Set Function TopologicalSpace CompactlySupported CompactlySupportedContinuousMap
  MeasureTheory

variable {X : Type*} [TopologicalSpace X]
variable (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0)

/-! ### Construction of the content: -/

section Λ_mono

lemma Λ_mono (f₁ f₂ : C_c(X, ℝ≥0)) (h : f₁.1 ≤ f₂.1) : Λ f₁ ≤ Λ f₂ := by
  obtain ⟨g, hg⟩ := exist_add_eq f₁ f₂ h
  simp only [← hg, map_add, le_add_iff_nonneg_right, zero_le]

end Λ_mono

/-- Given a positive linear functional `Λ` on continuous compactly supported functions on `X`
with values in `ℝ≥0`, for `K ⊆ X` compact define `λ(K) = inf {Λf | 1≤f on K}`.
When `X` is a locally compact T2 space, this will be shown to be a
content, and will be shown to agree with the Riesz measure on the compact subsets `K ⊆ X`. -/
def rieszContentAux : Compacts X → ℝ≥0 := fun K =>
  sInf (Λ '' { f : C_c(X, ℝ≥0) | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x })

section RieszMonotone

variable [T2Space X] [LocallyCompactSpace X]

/-- For any compact subset `K ⊆ X`, there exist some compactly supported continuous nonnegative
functions `f` on `X` such that `f ≥ 1` on `K`. -/
theorem rieszContentAux_image_nonempty (K : Compacts X) :
    (Λ '' { f : C_c(X, ℝ≥0) | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x }).Nonempty := by
  rw [image_nonempty]
  obtain ⟨V, hVcp, hKsubintV⟩ := exists_compact_superset K.2
  have hIsCompact_closure_interior : IsCompact (closure (interior V)) := by
    apply IsCompact.of_isClosed_subset hVcp isClosed_closure
    nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hVcp)]
    exact closure_mono interior_subset
  obtain ⟨f, hsuppfsubV, hfeq1onK, hfinicc⟩ :=
    exists_tsupport_one_of_isOpen_isClosed isOpen_interior hIsCompact_closure_interior
      (IsCompact.isClosed K.2) hKsubintV
  have hfHasCompactSupport : HasCompactSupport f :=
    IsCompact.of_isClosed_subset hVcp (isClosed_tsupport f)
      (Set.Subset.trans hsuppfsubV interior_subset)
  use nnrealPart ⟨f, hfHasCompactSupport⟩
  intro x hx
  apply le_of_eq
  simp only [nnrealPart_apply, CompactlySupportedContinuousMap.coe_mk]
  rw [← Real.toNNReal_one, Real.toNNReal_eq_toNNReal_iff (zero_le_one' ℝ) (hfinicc x).1]
  exact hfeq1onK.symm hx

/-- Riesz content `λ` (associated with a positive linear functional `Λ`) is
monotone: if `K₁ ⊆ K₂` are compact subsets in `X`, then `λ(K₁) ≤ λ(K₂)`. -/
theorem rieszContentAux_mono {K₁ K₂ : Compacts X} (h : K₁ ≤ K₂) :
    rieszContentAux Λ K₁ ≤ rieszContentAux Λ K₂ :=
  csInf_le_csInf (OrderBot.bddBelow _) (rieszContentAux_image_nonempty Λ K₂)
    (image_subset Λ (setOf_subset_setOf.mpr fun _ f_hyp x x_in_K₁ => f_hyp x (h x_in_K₁)))

end RieszMonotone

section RieszSubadditive

/-- Any compactly supported continuous nonnegative `f` such that `f ≥ 1` on `K` gives an upper bound
on the content of `K`; namely `λ(K) ≤ Λ f`. -/
theorem rieszContentAux_le {K : Compacts X} {f : C_c(X, ℝ≥0)} (h : ∀ x ∈ K, (1 : ℝ≥0) ≤ f x) :
    rieszContentAux Λ K ≤ Λ f :=
  csInf_le (OrderBot.bddBelow _) ⟨f, ⟨h, rfl⟩⟩

variable [T2Space X] [LocallyCompactSpace X]

/-- The Riesz content can be approximated arbitrarily well by evaluating the positive linear
functional on test functions: for any `ε > 0`, there exists a compactly supported continuous
nonnegative function `f` on `X` such that `f ≥ 1` on `K` and such that `λ(K) ≤ Λ f < λ(K) + ε`. -/
theorem exists_lt_rieszContentAux_add_pos (K : Compacts X) {ε : ℝ≥0} (εpos : 0 < ε) :
    ∃ f : C_c(X, ℝ≥0), (∀ x ∈ K, (1 : ℝ≥0) ≤ f x) ∧ Λ f < rieszContentAux Λ K + ε := by
  --choose a test function `f` s.t. `Λf = α < λ(K) + ε`
  obtain ⟨α, ⟨⟨f, f_hyp⟩, α_hyp⟩⟩ :=
    exists_lt_of_csInf_lt (rieszContentAux_image_nonempty Λ K)
      (lt_add_of_pos_right (rieszContentAux Λ K) εpos)
  refine ⟨f, f_hyp.left, ?_⟩
  rw [f_hyp.right]
  exact α_hyp

/-- The Riesz content `λ` associated to a given positive linear functional `Λ` is
finitely subadditive: `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)` for any compact subsets `K₁, K₂ ⊆ X`. -/
theorem rieszContentAux_sup_le (K1 K2 : Compacts X) :
    rieszContentAux Λ (K1 ⊔ K2) ≤ rieszContentAux Λ K1 + rieszContentAux Λ K2 := by
  apply _root_.le_of_forall_pos_le_add
  intro ε εpos
  --get test functions s.t. `λ(Ki) ≤ Λfi ≤ λ(Ki) + ε/2, i=1,2`
  obtain ⟨f1, f_test_function_K1⟩ := exists_lt_rieszContentAux_add_pos Λ K1 (half_pos εpos)
  obtain ⟨f2, f_test_function_K2⟩ := exists_lt_rieszContentAux_add_pos Λ K2 (half_pos εpos)
  --let `f := f1 + f2` test function for the content of `K`
  have f_test_function_union : ∀ x ∈ K1 ⊔ K2, (1 : ℝ≥0) ≤ (f1 + f2) x := by
    rintro x (x_in_K1 | x_in_K2)
    · exact le_add_right (f_test_function_K1.left x x_in_K1)
    · exact le_add_left (f_test_function_K2.left x x_in_K2)
  --use that `Λf` is an upper bound for `λ(K1⊔K2)`
  apply (rieszContentAux_le Λ f_test_function_union).trans (le_of_lt _)
  rw [map_add]
  --use that `Λfi` are lower bounds for `λ(Ki) + ε/2`
  apply lt_of_lt_of_le (_root_.add_lt_add f_test_function_K1.right f_test_function_K2.right)
    (le_of_eq _)
  rw [add_assoc, add_comm (ε / 2), add_assoc, add_halves ε, add_assoc]

end RieszSubadditive


section PartitionOfUnity

variable [T2Space X] [LocallyCompactSpace X]

lemma exists_continuous_add_one_of_isCompact_nnreal
    {s₀ s₁ : Set X} {t : Set X} (s₀_compact : IsCompact s₀) (s₁_compact : IsCompact s₁)
    (t_compact : IsCompact t) (disj : Disjoint s₀ s₁) (hst : s₀ ∪ s₁ ⊆ t) :
    ∃ (f₀ f₁ : C_c(X, ℝ≥0)), EqOn f₀ 1 s₀ ∧ EqOn f₁ 1 s₁ ∧ EqOn (f₀ + f₁) 1 t := by
  set so : Fin 2 → Set X := fun j => if j = 0 then s₀ᶜ else s₁ᶜ with hso
  have soopen (j : Fin 2) :  IsOpen (so j) := by
    fin_cases j
    · simp only [hso, Fin.zero_eta, Fin.isValue, ↓reduceIte, isOpen_compl_iff]
      exact IsCompact.isClosed <| s₀_compact
    · simp only [hso, Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte, isOpen_compl_iff]
      exact IsCompact.isClosed <| s₁_compact
  have hsot : t ⊆ ⋃ j, so j := by
    rw [hso]
    simp only [Fin.isValue]
    intro x hx
    rw [mem_iUnion]
    rw [← subset_compl_iff_disjoint_right, ← compl_compl s₀, compl_subset_iff_union] at disj
    have h : x ∈ s₀ᶜ ∨ x ∈ s₁ᶜ := by
      rw [← mem_union, disj]
      trivial
    apply Or.elim h
    · intro h0
      use 0
      simp only [Fin.isValue, ↓reduceIte]
      exact h0
    · intro h1
      use 1
      simp only [Fin.isValue, one_ne_zero, ↓reduceIte]
      exact h1
  obtain ⟨f, f_supp_in_so, sum_f_one_on_t, f_in_icc, f_hcs⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact soopen t_compact hsot
  use (nnrealPart (⟨f 1, f_hcs 1⟩ : C_c(X, ℝ))),
    (nnrealPart (⟨f 0, f_hcs 0⟩ : C_c(X, ℝ)))
  simp only [Fin.isValue, CompactlySupportedContinuousMap.coe_add]
  have sum_one_x (x : X) (hx : x ∈ t) : (f 0) x + (f 1) x = 1 := by
    simpa only [Finset.sum_apply, Fin.sum_univ_two, Fin.isValue, Pi.one_apply]
      using sum_f_one_on_t hx
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [Fin.isValue, nnrealPart_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply, Real.toNNReal_eq_one]
    have : (f 0) x = 0 := by
      rw [← nmem_support]
      have : s₀ ⊆ (tsupport (f 0))ᶜ := by
        apply subset_trans _ (compl_subset_compl.mpr (f_supp_in_so 0))
        rw [hso]
        simp only [Fin.isValue, ↓reduceIte, compl_compl, subset_refl]
      apply not_mem_of_mem_compl
      exact mem_of_subset_of_mem (subset_trans this (compl_subset_compl_of_subset subset_closure))
        hx
    rw [union_subset_iff] at hst
    rw [← sum_one_x x (mem_of_subset_of_mem hst.1 hx), this]
    exact Eq.symm (AddZeroClass.zero_add ((f 1) x))
  · intro x hx
    simp only [Fin.isValue, nnrealPart_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply, Real.toNNReal_eq_one]
    have : (f 1) x = 0 := by
      rw [← nmem_support]
      have : s₁ ⊆ (tsupport (f 1))ᶜ := by
        apply subset_trans _ (compl_subset_compl.mpr (f_supp_in_so 1))
        rw [hso]
        simp only [Fin.isValue, one_ne_zero, ↓reduceIte, compl_compl, subset_refl]
      apply not_mem_of_mem_compl
      exact mem_of_subset_of_mem (subset_trans this (compl_subset_compl_of_subset subset_closure))
        hx
    rw [union_subset_iff] at hst
    rw [← sum_one_x x (mem_of_subset_of_mem hst.2 hx), this]
    exact Eq.symm (AddMonoid.add_zero ((f 0) x))
  · intro x hx
    simp only [Fin.isValue, Pi.add_apply, nnrealPart_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply]
    rw [Real.toNNReal_add_toNNReal (f_in_icc 1 x).1 (f_in_icc 0 x).1, add_comm]
    simp only [Fin.isValue, Real.toNNReal_eq_one]
    exact sum_one_x x hx

end PartitionOfUnity

section RieszContentAdditive

variable [T2Space X] [LocallyCompactSpace X]

lemma rieszContentAux_union {K₁ K₂ : TopologicalSpace.Compacts X}
    (disj : Disjoint (K₁ : Set X) K₂) :
    rieszContentAux Λ (K₁ ⊔ K₂) = rieszContentAux Λ K₁ + rieszContentAux Λ K₂ := by
  refine le_antisymm (rieszContentAux_sup_le Λ K₁ K₂) ?_
  refine le_csInf (rieszContentAux_image_nonempty Λ (K₁ ⊔ K₂)) ?_
  intro b ⟨f, ⟨hf, Λf_eq_b⟩⟩
  have hsuppf : ∀ x ∈ K₁ ⊔ K₂, x ∈ support f := by
    intro x hx
    rw [mem_support]
    exact Ne.symm (ne_of_lt <| lt_of_lt_of_le (zero_lt_one' ℝ≥0) (hf x hx))
  have hsubsuppf : (K₁ : Set X) ∪ (K₂ : Set X) ⊆ tsupport f := subset_trans hsuppf subset_closure
  obtain ⟨g₁, g₂, hg₁, hg₂, sum_g⟩ := exists_continuous_add_one_of_isCompact_nnreal K₁.isCompact'
    K₂.isCompact' f.hasCompactSupport'.isCompact disj hsubsuppf
  have f_eq_sum : f = g₁ * f + g₂ * f := by
    ext x
    simp only [CompactlySupportedContinuousMap.coe_add, CompactlySupportedContinuousMap.coe_mul,
      Pi.add_apply, Pi.mul_apply, NNReal.coe_add, NNReal.coe_mul,
      Eq.symm (RightDistribClass.right_distrib _ _ _), ← NNReal.coe_add, ← Pi.add_apply]
    by_cases h : f x = 0
    · rw [h]
      simp only [NNReal.coe_zero, NNReal.coe_add, mul_zero]
    · push_neg at h
      simp only [CompactlySupportedContinuousMap.coe_add, ContinuousMap.toFun_eq_coe,
        CompactlySupportedContinuousMap.coe_toContinuousMap] at sum_g
      rw [sum_g (mem_of_subset_of_mem subset_closure (mem_support.mpr h))]
      simp only [Pi.one_apply, NNReal.coe_one, one_mul]
  rw [← Λf_eq_b, f_eq_sum, map_add]
  have aux₁ : ∀ x ∈ K₁, 1 ≤ (g₁ * f) x := by
    intro x x_in_K₁
    simp [hg₁ x_in_K₁, hf x (mem_union_left _ x_in_K₁)]
  have aux₂ : ∀ x ∈ K₂, 1 ≤ (g₂ * f) x := by
    intro x x_in_K₂
    simp [hg₂ x_in_K₂, hf x (mem_union_right _ x_in_K₂)]
  exact add_le_add (rieszContentAux_le Λ aux₁) (rieszContentAux_le Λ aux₂)

end RieszContentAdditive

section RieszContentRegular

variable [T2Space X] [LocallyCompactSpace X]

/-- The content induced by the linear functional `Λ`. -/
noncomputable def rieszContent (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) : Content X where
  toFun := rieszContentAux Λ
  mono' := fun _ _ ↦ rieszContentAux_mono Λ
  sup_disjoint' := fun _ _ disj _ _ ↦ rieszContentAux_union Λ disj
  sup_le' := rieszContentAux_sup_le Λ

lemma rieszContent_neq_top {K : Compacts X} : rieszContent Λ K ≠ ⊤ := by
  simp only [ne_eq, ENNReal.coe_ne_top, not_false_eq_true]

lemma rieszContentRegular : (rieszContent Λ).ContentRegular := by
  intro K
  simp only [rieszContent]
  apply le_antisymm
  · apply le_iInf
    simp only [le_iInf_iff, ENNReal.coe_le_coe]
    intro K' hK'
    exact rieszContentAux_mono Λ (Set.Subset.trans hK' interior_subset)
  · rw [iInf_le_iff]
    intro b hb
    rw [rieszContentAux, ENNReal.le_coe_iff]
    have : b < ⊤ := by
      obtain ⟨F, hF⟩ := exists_compact_superset K.2
      exact lt_of_le_of_lt (le_iInf_iff.mp (hb ⟨F, hF.1⟩) hF.2) ENNReal.coe_lt_top
    use b.toNNReal
    refine ⟨Eq.symm (ENNReal.coe_toNNReal (ne_of_lt this)), ?_⟩
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_le_coe, ← NNReal.coe_le_coe]
    apply le_iff_forall_pos_le_add.mpr
    intro ε hε
    set εnn : ℝ≥0 := ⟨ε, le_of_lt hε⟩
    have εnneq : ε.toNNReal = εnn := Real.toNNReal_of_nonneg (le_of_lt hε)
    rw [← NNReal.coe_mk ε (le_of_lt hε), ← NNReal.coe_add, NNReal.coe_le_coe]
    obtain ⟨f, hfleoneonK, hfle⟩ := exists_lt_rieszContentAux_add_pos Λ K (Real.toNNReal_pos.mpr hε)
    rw [rieszContentAux, εnneq] at hfle
    apply le_of_lt (lt_of_le_of_lt _ hfle)
    rw [← NNReal.coe_le_coe]
    apply (le_iff_forall_one_lt_le_mul₀ _).mpr
    · intro α hα
      have : (Λ f) * α = Λ (α.toNNReal • f) := by
        simp only [map_smul, smul_eq_mul, NNReal.coe_mul, Real.coe_toNNReal',
          max_eq_left <| le_of_lt (lt_of_le_of_lt zero_le_one hα)]
        exact mul_comm _ _
      rw [this]
      set K' := f ⁻¹' (Ici α⁻¹.toNNReal) with hK'
      have hKK' : K.carrier ⊆ interior K' := by
        rw [subset_interior_iff]
        use f ⁻¹' (Ioi α⁻¹.toNNReal)
        refine ⟨IsOpen.preimage f.1.2 isOpen_Ioi, ?_, ?_⟩
        · intro x hx
          rw [Set.mem_preimage, Set.mem_Ioi]
          exact lt_of_lt_of_le (Real.toNNReal_lt_one.mpr (inv_lt_one_of_one_lt₀ hα))
            (hfleoneonK x hx)
        · rw [hK']
          intro x hx
          simp only [mem_preimage, mem_Ioi] at hx
          simp only [mem_preimage, mem_Ici]
          exact le_of_lt hx
      have hK'cp : IsCompact K' := by
        apply IsCompact.of_isClosed_subset f.2
        · exact IsClosed.preimage f.1.2 isClosed_Ici
        · rw [hK']
          apply Set.Subset.trans _ subset_closure
          intro x hx
          simp only [mem_preimage, mem_Ici] at hx
          simp only [mem_support]
          apply ne_of_gt
          rw [Real.toNNReal_inv] at hx
          exact (lt_of_lt_of_le
            (inv_pos_of_pos (lt_trans zero_lt_one (Real.one_lt_toNNReal.mpr hα))) hx)
      set hb' := hb ⟨K', hK'cp⟩
      simp only [Compacts.coe_mk, le_iInf_iff] at hb'
      have hbK' : b ≤ rieszContent Λ ⟨K', hK'cp⟩ := hb' hKK'
      rw [ENNReal.le_coe_iff] at hbK'
      obtain ⟨p, hp⟩ := hbK'
      simp only [hp.1, ENNReal.toNNReal_coe, NNReal.val_eq_coe, map_smul, smul_eq_mul,
        NNReal.coe_mul, Real.coe_toNNReal', ge_iff_le]
      apply le_trans (NNReal.GCongr.toReal_le_toReal hp.2)
      simp only [rieszContent]
      rw [rieszContentAux, ← Real.coe_toNNReal (α ⊔ 0) (le_max_right α 0), ← NNReal.coe_mul,
        NNReal.coe_le_coe]
      apply csInf_le
      · simp only [OrderBot.bddBelow]
      · simp only [mem_image, mem_setOf_eq]
        use α.toNNReal • f
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul,
            ← NNReal.coe_le_coe, NNReal.coe_one, NNReal.coe_mul, Real.coe_toNNReal']
          rw [← (left_eq_sup.mpr <| le_of_lt (lt_of_le_of_lt zero_le_one hα)), mul_comm]
          apply (inv_le_iff_one_le_mul₀ (lt_trans zero_lt_one hα)).mp
          rw [← Set.mem_Ici]
          simp only [mem_Ici, ge_iff_le]
          exact Real.toNNReal_le_iff_le_coe.mp hx
        · simp only [map_smul, smul_eq_mul, mul_eq_mul_right_iff]
          left
          rw [Real.toNNReal_eq_toNNReal_iff (le_of_lt (lt_of_le_of_lt zero_le_one hα))
            (le_max_right α 0), left_eq_sup]
          exact le_of_lt (lt_of_le_of_lt zero_le_one hα)
    · exact zero_le (Λ f)

end RieszContentRegular

section RieszMeasure

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- `rieszContent` is promoted to a measure. -/
def μ := (MeasureTheory.Content.measure (rieszContent Λ))

lemma leRieszMeasure_Compacts {f : C_c(X, ℝ≥0)} (hf : ∀ (x : X), f x ≤ 1) {K : Compacts X}
    (h : tsupport f ⊆ K) : ENNReal.ofReal (Λ f) ≤ (μ Λ) K := by
  simp only [μ, MeasureTheory.Content.measure_eq_content_of_regular (rieszContent Λ)
    (rieszContentRegular Λ)]
  simp only [rieszContent, ENNReal.ofReal_coe_nnreal, ENNReal.coe_le_coe]
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos Λ K hε
  apply le_of_lt (lt_of_le_of_lt _ hg.2)
  apply Λ_mono Λ
  intro x
  simp only [ContinuousMap.toFun_eq_coe, CompactlySupportedContinuousMap.coe_toContinuousMap]
  by_cases hx : x ∈ tsupport f
  · exact le_trans (hf x) (hg.1 x (Set.mem_of_subset_of_mem h hx))
  · rw [image_eq_zero_of_nmem_tsupport hx]
    exact zero_le (g x)

lemma leRieszMeasure_Opens {f : C_c(X, ℝ≥0)} (hf : ∀ (x : X), f x ≤ 1) {V : Opens X}
    (h : tsupport f ⊆ V) :
    ENNReal.ofReal (Λ f) ≤ (μ Λ) V := by
  apply le_trans _ (MeasureTheory.measure_mono h)
  rw [← TopologicalSpace.Compacts.coe_mk (tsupport f) f.2]
  apply leRieszMeasure_Compacts Λ hf
  simp only [Compacts.coe_mk]
  exact subset_rfl

end RieszMeasure
