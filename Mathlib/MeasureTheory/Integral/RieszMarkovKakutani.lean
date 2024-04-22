/-
Copyright (c) 2024 Jesse Reimann, Kalle Kytölä, Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Reimann, Kalle Kytölä, Yoh Tanimoto
-/
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.Topology.ContinuousFunction.ZeroAtInfty
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner


/-!
#  Riesz–Markov–Kakutani representation theorem

This file will prove a version of the Riesz-Markov-Kakutani representation theorem.
The theorem is first proven for locally compact Hausdorff (T2) spaces.
A large part of the file is an adaptation of the `EEReal` version by Jesse Reimann, Kalle Kytölä
to `ℝ` version.

To make use of the existing API, the measure is constructed from a content `λ` on the
compact subsets of the space X, rather than the usual construction of open sets in the literature.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/


noncomputable section

open BoundedContinuousFunction NNReal ENNReal

open Set Function TopologicalSpace ZeroAtInfty


variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] [NormalSpace X]
variable (Λ : C(X, ℝ) →ₗ[ℝ] ℝ) (hΛ : ∀ (f : C(X, ℝ)), 0 ≤ f → 0 ≤ Λ f)
-- need to restrict Λ : C₀(X, ℝ)

lemma Λ_mono {f g : C(X, ℝ)} (h : f ≤ g) : Λ f ≤ Λ g := by
  have : 0 ≤ g - f := by exact sub_nonneg.mpr h
  calc Λ f ≤ Λ f + Λ (g - f) := by exact le_add_of_nonneg_right (hΛ (g - f) this)
  _ = Λ (f + (g - f)) := by rw [← LinearMap.map_add Λ f (g - f)]
  _ = Λ g := by simp only [add_sub_cancel]


/-! ### Construction of the content: -/

lemma exists_tsupport_one_of_isOpen_isClosed [NormalSpace X] {s t : Set X}
    (hs : IsOpen s) (ht : IsClosed t) (hst : t ⊆ s) : ∃ f : C(X, ℝ), tsupport f ⊆ s ∧ EqOn f 1 t
    ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  sorry


/-- Given a positive linear functional Λ on X, for `K ⊆ X` compact define
`λ(K) = inf {Λf | 1≤f on K}`. When X is a compact Hausdorff space, this will be shown to be a
content, and will be shown to agree with the Riesz measure on the compact subsets `K ⊆ X`. -/
def rieszContentAux : Compacts X → ℝ := fun K =>
  sInf (Λ '' { f : C(X, ℝ) | HasCompactSupport f ∧ (∀ (x : X), 0 ≤ f x)
  ∧ (∀ (x : X), x ∈ K → 1 ≤ f x) })

section RieszMonotone

/-- For any compact subset `K ⊆ X`, there exist some bounded continuous nonnegative
functions f on X such that `f ≥ 1` on K. -/
theorem rieszContentAux_image_nonempty (K : Compacts X) :
    (Λ '' { f : C(X, ℝ) | HasCompactSupport f ∧ (∀ (x : X), 0 ≤ f x) ∧ (∀ (x : X),
    x ∈ K → 1 ≤ f x) }).Nonempty := by
  rw [image_nonempty]
  obtain ⟨V, hV⟩ := exists_compact_superset K.2
  obtain ⟨f, hf⟩ := exists_tsupport_one_of_isOpen_isClosed isOpen_interior (IsCompact.isClosed K.2)
    hV.2
  use f
  simp only [mem_setOf_eq]
  constructor
  · exact IsCompact.of_isClosed_subset hV.1 (isClosed_tsupport f)
      (_root_.subset_trans hf.1 interior_subset)
  constructor
  · intro x
    exact (Set.mem_Icc.mp (hf.2.2 x)).1
  · intro x hx
    apply le_of_eq
    rw [← ContinuousMap.one_apply x]
    exact (hf.2.1 hx).symm

lemma rieszContentAux_nonneg {K : Compacts X} : 0 ≤ rieszContentAux Λ K := by
  apply le_csInf
  exact rieszContentAux_image_nonempty Λ K
  intro b
  simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp]
  intro f _ hf _ hb
  rw [← hb]
  exact hΛ f hf

lemma rieszContentAux_image_BddBelow (K : Compacts X) :
    BddBelow (Λ '' { f : C(X, ℝ) | HasCompactSupport f ∧ (∀ (x : X), 0 ≤ f x)
    ∧ (∀ (x : X), x ∈ K → 1 ≤ f x) }) := by
  use 0
  intro b
  simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp]
  intro f _ hf _ hb
  rw [← hb]
  exact hΛ f hf

/-- Riesz content λ (associated with a positive linear functional Λ) is
monotone: if `K₁ ⊆ K₂` are compact subsets in X, then `λ(K₁) ≤ λ(K₂)`. -/
theorem rieszContentAux_mono {K₁ K₂ : Compacts X} (h : K₁ ≤ K₂) :
    rieszContentAux Λ K₁ ≤ rieszContentAux Λ K₂ := by
  apply csInf_le_csInf (rieszContentAux_image_BddBelow Λ hΛ K₁) (rieszContentAux_image_nonempty Λ K₂)
  simp only [image_subset_iff]
  intro f hf
  simp only [mem_setOf_eq] at hf
  simp only [mem_preimage, mem_image, mem_setOf_eq]
  use f
  constructor
  constructor
  · exact hf.1
  constructor
  · exact hf.2.1
  · intro x hx
    exact hf.2.2 x (Set.mem_of_subset_of_mem h hx)
  rfl

end RieszMonotone

section RieszSubadditive

/-- Any bounded continuous nonnegative f such that `f ≥ 1` on K gives an upper bound on the
content of K; namely `λ(K) ≤ Λ f`. -/
theorem rieszContentAux_le {K : Compacts X} {f : C(X, ℝ)}
    (h : HasCompactSupport f ∧ (∀ (x : X), 0 ≤ f x) ∧ ∀ (x : X), x ∈ K → 1 ≤ f x) :
    rieszContentAux Λ K ≤ Λ f := by
  apply csInf_le (rieszContentAux_image_BddBelow Λ hΛ K)
  simp only [mem_image, mem_setOf_eq]
  use f

/-- The Riesz content can be approximated arbitrarily well by evaluating the positive linear
functional on test functions: for any `ε > 0`, there exists a bounded continuous nonnegative
function f on X such that `f ≥ 1` on K and such that `λ(K) ≤ Λ f < λ(K) + ε`. -/
theorem exists_lt_rieszContentAux_add_pos (K : Compacts X) {ε : ℝ} (εpos : 0 < ε) :
    ∃ f : C(X, ℝ), HasCompactSupport f ∧ (∀ (x : X), 0 ≤ f x) ∧ (∀ x ∈ K, 1 ≤ f x)
    ∧ Λ f < rieszContentAux Λ K + ε := by
  --choose a test function `f` s.t. `Λf = α < λ(K) + ε`
  obtain ⟨α, ⟨⟨f, f_hyp⟩, α_hyp⟩⟩ :=
    exists_lt_of_csInf_lt (rieszContentAux_image_nonempty Λ K)
      (lt_add_of_pos_right (rieszContentAux Λ K) εpos)
  use f
  simp only [mem_setOf_eq] at f_hyp
  constructor
  · exact f_hyp.1.1
  constructor
  · exact f_hyp.1.2.1
  constructor
  · exact f_hyp.1.2.2
  · rw [f_hyp.2]
    exact α_hyp

/-- The Riesz content λ associated to a given positive linear functional Λ is
finitely subadditive: `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)` for any compact subsets `K₁, K₂ ⊆ X`. -/
theorem rieszContentAux_sup_le {K₁ K₂ : Compacts X} :
    rieszContentAux Λ (K₁ ⊔ K₂) ≤ rieszContentAux Λ K₁ + rieszContentAux Λ K₂ := by
  apply le_of_forall_pos_lt_add'
  intro ε εpos
  --get test functions s.t. `λ(Ki) ≤ Λfi ≤ λ(Ki) + ε/2, i=1,2`
  obtain ⟨f1, f_test_function_K₁⟩ := exists_lt_rieszContentAux_add_pos Λ K₁ (half_pos εpos)
  obtain ⟨f2, f_test_function_K₂⟩ := exists_lt_rieszContentAux_add_pos Λ K₂ (half_pos εpos)
  --let `f := f1 + f2` test function for the content of `K`
  have f_test_function_union : ∀ x ∈ K₁ ⊔ K₂, 1 ≤ (f1 + f2) x := by
    rintro x (x_in_K₁ | x_in_K₂)
    · simp only [ContinuousMap.add_apply]
      apply le_add_of_le_of_nonneg
      · exact f_test_function_K₁.2.2.1 x x_in_K₁
      · exact f_test_function_K₂.2.1 x
    · simp only [ContinuousMap.add_apply]
      rw [add_comm]
      apply le_add_of_le_of_nonneg
      · exact f_test_function_K₂.2.2.1 x x_in_K₂
      · exact f_test_function_K₁.2.1 x
  --use that `Λf` is an upper bound for `λ(K₁⊔K₂)`
  set f := f1 + f2 with hf
  have f_HasCompactSupport : HasCompactSupport f := by
    exact HasCompactSupport.add f_test_function_K₁.1 f_test_function_K₂.1
  have f_nonneg : ∀ (x : X), 0 ≤ f x := by
    intro x
    rw [hf]
    simp only [ContinuousMap.add_apply]
    exact add_nonneg (f_test_function_K₁.2.1 x) (f_test_function_K₂.2.1 x)
  apply lt_of_le_of_lt (rieszContentAux_le Λ hΛ
    (And.intro f_HasCompactSupport (And.intro f_nonneg f_test_function_union)))
  rw [hf]
  simp only [map_add]
  --use that `Λfi` are lower bounds for `λ(Ki) + ε/2`
  apply lt_of_lt_of_le (_root_.add_lt_add f_test_function_K₁.2.2.2 f_test_function_K₂.2.2.2)
    (le_of_eq _)
  rw [add_assoc, add_comm (ε / 2), add_assoc, add_halves ε, add_assoc]

end RieszSubadditive

section RieszAdditive

theorem rieszContentAux_eq_add [T2Space X] {K₁ K₂ : Compacts X} (h : Disjoint K₁ K₂) :
    rieszContentAux Λ (K₁ ⊔ K₂) = rieszContentAux Λ K₁ + rieszContentAux Λ K₂ := by
  apply le_antisymm
  · exact rieszContentAux_sup_le Λ hΛ
  · apply le_csInf
    · exact rieszContentAux_image_nonempty Λ (K₁ ⊔ K₂)
    · intro b hb
      obtain ⟨f, hf⟩ := hb
      simp only [mem_setOf_eq] at hf
      have hDisjoint : Disjoint K₁.carrier K₂.carrier := by
        rw [disjoint_iff]
        rw [disjoint_iff] at h
        simp only [inf_eq_inter, bot_eq_empty]
        simp only [Compacts.carrier_eq_coe]
        rw [← TopologicalSpace.Compacts.coe_inf]
        rw [← Compacts.carrier_eq_coe]
        rw [h]
        exact rfl
      obtain ⟨g, hg⟩ := exists_continuous_zero_one_of_isCompact K₁.isCompact'
        (IsCompact.isClosed K₂.isCompact') hDisjoint
      simp only [Compacts.carrier_eq_coe, mem_Icc] at hg
      have h1 : rieszContentAux Λ K₁ ≤ Λ (f * (1 - g)) := by
        apply csInf_le (rieszContentAux_image_BddBelow Λ hΛ K₁)
        simp only [mem_image, mem_setOf_eq]
        use f * (1 - g)
        constructor
        constructor
        exact HasCompactSupport.mul_right hf.1.1
        constructor
        · intro x
          simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply]
          exact mul_nonneg (hf.1.2.1 x) (unitInterval.one_minus_nonneg ⟨(g x), hg.2.2 x⟩)
        · intro x hx
          simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply]
          have hgx : g x = 0 := by
            rw [hg.1 hx]
            simp only [Pi.zero_apply]
          rw [hgx]
          simp only [sub_zero, mul_one, ge_iff_le]
          exact hf.1.2.2 x ((Set.mem_union x K₁ K₂).mpr (Or.inl hx))
        · rfl
      have h2 : rieszContentAux Λ K₂ ≤ Λ (f * g) := by
        apply csInf_le (rieszContentAux_image_BddBelow Λ hΛ K₂)
        simp only [mem_image, mem_setOf_eq]
        use f * g
        constructor
        constructor
        exact HasCompactSupport.mul_right hf.1.1
        constructor
        · intro x
          simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply]
          exact mul_nonneg (hf.1.2.1 x) (hg.2.2 x).1
        · intro x hx
          simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply]
          have hgx : g x = 1 := by
            rw [hg.2.1 hx]
            simp only [Pi.one_apply]
          rw [hgx]
          simp only [sub_zero, mul_one, ge_iff_le]
          exact hf.1.2.2 x ((Set.mem_union x K₁ K₂).mpr (Or.inr hx))
        · rfl
      have hb : b = Λ (f * (1 - g) + f * g) := by
        ring_nf
        exact (hf.2).symm
      rw [hb]
      simp only [map_add, ge_iff_le]
      exact add_le_add h1 h2

end RieszAdditive

lemma restrictNonneg (f : C(X, ℝ≥0)) : 0 ≤ f.1 := by
  intro x
  simp only [Pi.zero_apply, ContinuousMap.toFun_eq_coe, zero_le]

def continuousToReal : C(ℝ≥0, ℝ) := ⟨NNReal.toReal, NNReal.continuous_coe⟩

def ExtendToReal (f : C(X, ℝ≥0)) : C(X, ℝ) :=
  ⟨NNReal.toReal ∘ f, Continuous.comp continuousToReal.2 f.2⟩

@[simp]
theorem map_apply (f : C(X, ℝ≥0)) (x : X) : ExtendToReal f x = f x :=
  rfl

@[simp]
theorem coe_map (f : C(X, ℝ≥0)) : ExtendToReal f = fun x => (f x : ℝ) := by
  rfl

def continuousExtendToReal (f : C(X, ℝ≥0)) : C(X, ℝ) :=
  ⟨NNReal.toReal ∘ f, Continuous.comp continuousToReal.2 f.2⟩

def continuousRestrictionToNNReal (f : C(X, ℝ)) : C(X, ℝ≥0) :=
  ⟨Real.toNNReal ∘ f, Continuous.comp continuous_real_toNNReal f.2⟩

-- to Continuous?
def RestrictNonneg (Λ : C(X, ℝ) →ₗ[ℝ] ℝ)  (hΛ : ∀ (f : C(X, ℝ)), 0 ≤ f → 0 ≤ Λ f) :
  C(X, ℝ≥0) → ℝ≥0 := fun f => ⟨Λ (continuousExtendToReal f), hΛ (continuousExtendToReal f) (restrictNonneg f)⟩

def rieszContentNonneg : Compacts X → ℝ≥0 := fun K =>
  sInf (RestrictNonneg Λ hΛ '' { f : C(X, ℝ≥0) | HasCompactSupport f ∧ (∀ (x : X), 0 ≤ f x)
  ∧ (∀ (x : X), x ∈ K → 1 ≤ f x) })

theorem rieszContentNonneg_image_nonempty (K : Compacts X) :
    (RestrictNonneg Λ hΛ '' { f : C(X, ℝ≥0) | HasCompactSupport f ∧ (∀ (x : X), 0 ≤ f x) ∧
    (∀ (x : X), x ∈ K → 1 ≤ f x) }).Nonempty := by
  rw [image_nonempty]
  obtain ⟨V, hV⟩ := exists_compact_superset K.2
  obtain ⟨f, hf⟩ := exists_tsupport_one_of_isOpen_isClosed isOpen_interior (IsCompact.isClosed K.2)
    hV.2
  use (continuousRestrictionToNNReal f)
  simp only [zero_le, implies_true, true_and, mem_setOf_eq]
  constructor
  · apply HasCompactSupport.of_support_subset_isCompact hV.1
    apply Set.Subset.trans (Function.support_comp_subset Real.toNNReal_zero f)
    exact Set.Subset.trans (Set.Subset.trans subset_closure hf.1) interior_subset
  · intro x hx
    apply le_of_eq
    rw [continuousRestrictionToNNReal]
    simp only [ContinuousMap.coe_mk, comp_apply]
    rw [eq_comm, Real.toNNReal_eq_one]
    exact hf.2.1 hx

lemma rieszContentNonneg_image_BddBelow (K : Compacts X) :
    BddBelow (RestrictNonneg Λ hΛ '' { f : C(X, ℝ≥0) | HasCompactSupport f ∧ (∀ (x : X), 0 ≤ f x)
    ∧ (∀ (x : X), x ∈ K → 1 ≤ f x) }) := by
  use 0
  simp only [zero_le, implies_true, true_and]
  intro b _
  exact b.2

lemma rieszContentAux_eq_rieszContentNonneg {K : Compacts X} :
    ⟨rieszContentAux Λ K, rieszContentAux_nonneg Λ hΛ⟩ = rieszContentNonneg Λ hΛ K  := by
  apply le_antisymm
  · rw [← NNReal.coe_le_coe]
    simp only [coe_mk]
    apply (csInf_le_iff (rieszContentAux_image_BddBelow Λ hΛ K)
      (rieszContentAux_image_nonempty Λ K)).mpr
    · intro b hb
      by_cases hbzero : 0 ≤ b
      · rw [← Real.coe_toNNReal b hbzero]
        rw [NNReal.coe_le_coe]
        apply (le_csInf_iff (rieszContentNonneg_image_BddBelow Λ hΛ K) (rieszContentNonneg_image_nonempty Λ hΛ K)).mpr
        intro c hc
        simp only [zero_le, implies_true, true_and, mem_image, mem_setOf_eq] at hc
        obtain ⟨f, hf⟩ := hc
        rw [RestrictNonneg] at hf
        rw [← hf.2, Real.toNNReal_le_iff_le_coe]
        simp only [coe_mk]
        rw [mem_lowerBounds] at hb
        apply hb
        simp only [mem_image, mem_setOf_eq]
        use continuousExtendToReal f
        constructor
        constructor
        · apply HasCompactSupport.of_support_subset_isCompact hf.1.1
          rw [continuousExtendToReal]
          exact Set.Subset.trans (Function.support_comp_subset NNReal.coe_zero f) subset_closure
        constructor
        · intro x
          rw [continuousExtendToReal]
          simp only [ContinuousMap.coe_mk, comp_apply, zero_le_coe]
        · intro x hx
          rw [continuousExtendToReal]
          simp only [ContinuousMap.coe_mk, comp_apply, one_le_coe]
          exact hf.1.2 x hx
        rfl
      · push_neg at hbzero
        apply le_of_lt (lt_of_lt_of_le hbzero _)
        simp only [zero_le_coe]
  · apply (csInf_le_iff (rieszContentNonneg_image_BddBelow Λ hΛ K) (rieszContentNonneg_image_nonempty Λ hΛ K)).mpr
    intro b hb
    simp only [zero_le, implies_true, true_and] at hb
    rw [mem_lowerBounds] at hb
    rw [← NNReal.coe_le_coe]
    simp only [coe_mk]
    apply (le_csInf_iff (rieszContentAux_image_BddBelow Λ hΛ K) (rieszContentAux_image_nonempty Λ K)).mpr
    intro c hc
    simp only [mem_image, mem_setOf_eq] at hc
    obtain ⟨f, hf⟩ := hc
    have hΛfpos : 0 ≤ Λ f := by
      apply hΛ
      exact hf.1.2.1
    rw [← Real.le_toNNReal_iff_coe_le _]
    · apply hb
      rw [← hf.2]
      simp only [mem_image, mem_setOf_eq]
      use continuousRestrictionToNNReal f
      constructor
      constructor
      · rw [continuousRestrictionToNNReal]
        simp only [ContinuousMap.coe_mk]
        apply HasCompactSupport.of_support_subset_isCompact hf.1.1
        exact Set.Subset.trans (Function.support_comp_subset Real.toNNReal_zero f) subset_closure
      · intro x hx
        rw [continuousRestrictionToNNReal]
        simp only [ContinuousMap.coe_mk, comp_apply, Real.one_le_toNNReal]
        exact hf.1.2.2 x hx
      rw [RestrictNonneg, Real.toNNReal_of_nonneg hΛfpos, ← NNReal.coe_inj]
      simp only [coe_mk, coe_mk (Λ f) hΛfpos]
      rw [continuousExtendToReal, continuousRestrictionToNNReal]
      simp only [ContinuousMap.coe_mk]
      apply congr_arg
      ext x
      simp only [ContinuousMap.coe_mk, comp_apply, Real.coe_toNNReal', max_eq_left_iff]
      exact hf.1.2.1 x
    · rw [← hf.2]
      exact hΛfpos

theorem rieszContentNonneg_mono {K₁ K₂ : Compacts X} (h : K₁ ≤ K₂) :
    rieszContentNonneg Λ hΛ K₁ ≤ rieszContentNonneg Λ hΛ K₂ := by
  rw [← rieszContentAux_eq_rieszContentNonneg, ← rieszContentAux_eq_rieszContentNonneg]
  rw [← NNReal.coe_le_coe]
  simp only [coe_mk]
  exact rieszContentAux_mono Λ hΛ h

theorem rieszContentNonneg_eq_add [T2Space X] {K₁ K₂ : Compacts X} (h : Disjoint K₁ K₂) :
    rieszContentNonneg Λ hΛ (K₁ ⊔ K₂) = rieszContentNonneg Λ hΛ K₁ + rieszContentNonneg Λ hΛ K₂ := by
  rw [← rieszContentAux_eq_rieszContentNonneg, ← rieszContentAux_eq_rieszContentNonneg, ← rieszContentAux_eq_rieszContentNonneg]
  rw [← NNReal.eq_iff]
  simp only [coe_mk, NNReal.coe_add]
  exact rieszContentAux_eq_add Λ hΛ h

theorem rieszContentNonneg_sup_le {K₁ K₂ : Compacts X} :
    rieszContentNonneg Λ hΛ (K₁ ⊔ K₂) ≤ rieszContentNonneg Λ hΛ K₁ + rieszContentNonneg Λ hΛ K₂ := by
  rw [← rieszContentAux_eq_rieszContentNonneg, ← rieszContentAux_eq_rieszContentNonneg, ← rieszContentAux_eq_rieszContentNonneg]
  rw [← NNReal.coe_le_coe]
  simp only [coe_mk, NNReal.coe_add]
  exact rieszContentAux_sup_le Λ hΛ

def rieszContent : MeasureTheory.Content X where
  toFun := rieszContentNonneg Λ hΛ
  mono' := by
    intro K₁ K₂ h
    exact rieszContentNonneg_mono Λ hΛ h
  sup_disjoint' := by
    intro K₁ K₂ hDisjoint _ _
    have : Disjoint K₁ K₂ := by
        rw [disjoint_iff]
        rw [disjoint_iff] at hDisjoint
        simp only [inf_eq_inter, bot_eq_empty] at hDisjoint
        apply TopologicalSpace.Compacts.ext
        simp only [Compacts.coe_inf, Compacts.coe_bot]
        exact hDisjoint
    exact rieszContentNonneg_eq_add Λ hΛ this
  sup_le' := by
    intro K₁ K₂
    exact rieszContentNonneg_sup_le Λ hΛ

variable [MeasurableSpace X] [BorelSpace X]

def μ := (MeasureTheory.Content.measure (rieszContent Λ hΛ))

/-- The Riesz-Markov-Kakutani theorem. -/
theorem RMK : ∀ (f : C₀(X, ℝ)), ∫ (x : X), f x ∂(μ Λ hΛ) = Λ f.1 := by
 sorry
