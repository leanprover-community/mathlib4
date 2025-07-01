/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Hahn
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.Topology.Algebra.UniformMulAction

/-!
# Jordan decomposition

This file proves the existence and uniqueness of the Jordan decomposition for signed measures.
The Jordan decomposition theorem states that, given a signed measure `s`, there exists a
unique pair of mutually singular measures `μ` and `ν`, such that `s = μ - ν`.

The Jordan decomposition theorem for measures is a corollary of the Hahn decomposition theorem and
is useful for the Lebesgue decomposition theorem.

## Main definitions

* `MeasureTheory.JordanDecomposition`: a Jordan decomposition of a measurable space is a
  pair of mutually singular finite measures. We say `j` is a Jordan decomposition of a signed
  measure `s` if `s = j.posPart - j.negPart`.
* `MeasureTheory.SignedMeasure.toJordanDecomposition`: the Jordan decomposition of a
  signed measure.
* `MeasureTheory.SignedMeasure.toJordanDecompositionEquiv`: is the `Equiv` between
  `MeasureTheory.SignedMeasure` and `MeasureTheory.JordanDecomposition` formed by
  `MeasureTheory.SignedMeasure.toJordanDecomposition`.

## Main results

* `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition` : the Jordan
  decomposition theorem.
* `MeasureTheory.JordanDecomposition.toSignedMeasure_injective` : the Jordan decomposition of a
  signed measure is unique.

## Tags

Jordan decomposition theorem
-/


noncomputable section

open scoped MeasureTheory ENNReal NNReal

variable {α : Type*} [MeasurableSpace α]

namespace MeasureTheory

/-- A Jordan decomposition of a measurable space is a pair of mutually singular,
finite measures. -/
@[ext]
structure JordanDecomposition (α : Type*) [MeasurableSpace α] where
  /-- Positive part of the Jordan decomposition -/
  posPart : Measure α
  /-- Negative part of the Jordan decomposition -/
  negPart : Measure α
  [posPart_finite : IsFiniteMeasure posPart]
  [negPart_finite : IsFiniteMeasure negPart]
  mutuallySingular : posPart ⟂ₘ negPart

attribute [instance] JordanDecomposition.posPart_finite

attribute [instance] JordanDecomposition.negPart_finite

namespace JordanDecomposition

open Measure VectorMeasure

variable (j : JordanDecomposition α)

instance instZero : Zero (JordanDecomposition α) where zero := ⟨0, 0, MutuallySingular.zero_right⟩

instance instInhabited : Inhabited (JordanDecomposition α) where default := 0

instance instInvolutiveNeg : InvolutiveNeg (JordanDecomposition α) where
  neg j := ⟨j.negPart, j.posPart, j.mutuallySingular.symm⟩
  neg_neg _ := JordanDecomposition.ext rfl rfl

instance instSMul : SMul ℝ≥0 (JordanDecomposition α) where
  smul r j :=
    ⟨r • j.posPart, r • j.negPart,
      MutuallySingular.smul _ (MutuallySingular.smul _ j.mutuallySingular.symm).symm⟩

instance instSMulReal : SMul ℝ (JordanDecomposition α) where
  smul r j := if 0 ≤ r then r.toNNReal • j else -((-r).toNNReal • j)

@[simp]
theorem zero_posPart : (0 : JordanDecomposition α).posPart = 0 :=
  rfl

@[simp]
theorem zero_negPart : (0 : JordanDecomposition α).negPart = 0 :=
  rfl

@[simp]
theorem neg_posPart : (-j).posPart = j.negPart :=
  rfl

@[simp]
theorem neg_negPart : (-j).negPart = j.posPart :=
  rfl

@[simp]
theorem smul_posPart (r : ℝ≥0) : (r • j).posPart = r • j.posPart :=
  rfl

@[simp]
theorem smul_negPart (r : ℝ≥0) : (r • j).negPart = r • j.negPart :=
  rfl

theorem real_smul_def (r : ℝ) (j : JordanDecomposition α) :
    r • j = if 0 ≤ r then r.toNNReal • j else -((-r).toNNReal • j) :=
  rfl

@[simp]
theorem coe_smul (r : ℝ≥0) : (r : ℝ) • j = r • j := by
  rw [real_smul_def, if_pos (NNReal.coe_nonneg r), Real.toNNReal_coe]

theorem real_smul_nonneg (r : ℝ) (hr : 0 ≤ r) : r • j = r.toNNReal • j :=
  dif_pos hr

theorem real_smul_neg (r : ℝ) (hr : r < 0) : r • j = -((-r).toNNReal • j) :=
  dif_neg (not_le.2 hr)

theorem real_smul_posPart_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (r • j).posPart = r.toNNReal • j.posPart := by
  rw [real_smul_def, ← smul_posPart, if_pos hr]

theorem real_smul_negPart_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (r • j).negPart = r.toNNReal • j.negPart := by
  rw [real_smul_def, ← smul_negPart, if_pos hr]

theorem real_smul_posPart_neg (r : ℝ) (hr : r < 0) :
    (r • j).posPart = (-r).toNNReal • j.negPart := by
  rw [real_smul_def, ← smul_negPart, if_neg (not_le.2 hr), neg_posPart]

theorem real_smul_negPart_neg (r : ℝ) (hr : r < 0) :
    (r • j).negPart = (-r).toNNReal • j.posPart := by
  rw [real_smul_def, ← smul_posPart, if_neg (not_le.2 hr), neg_negPart]

/-- The signed measure associated with a Jordan decomposition. -/
def toSignedMeasure : SignedMeasure α :=
  j.posPart.toSignedMeasure - j.negPart.toSignedMeasure

theorem toSignedMeasure_zero : (0 : JordanDecomposition α).toSignedMeasure = 0 := by
  ext1 i hi
  rw [toSignedMeasure, toSignedMeasure_sub_apply hi, zero_posPart, zero_negPart, sub_self,
    VectorMeasure.coe_zero, Pi.zero_apply]

theorem toSignedMeasure_neg : (-j).toSignedMeasure = -j.toSignedMeasure := by
  ext1 i hi
  rw [neg_apply, toSignedMeasure, toSignedMeasure, toSignedMeasure_sub_apply hi,
    toSignedMeasure_sub_apply hi, neg_sub, neg_posPart, neg_negPart]

theorem toSignedMeasure_smul (r : ℝ≥0) : (r • j).toSignedMeasure = r • j.toSignedMeasure := by
  ext1 i hi
  rw [VectorMeasure.smul_apply, toSignedMeasure, toSignedMeasure,
    toSignedMeasure_sub_apply hi, toSignedMeasure_sub_apply hi, smul_sub, smul_posPart,
    smul_negPart, measureReal_nnreal_smul_apply, measureReal_nnreal_smul_apply]
  rfl

/-- A Jordan decomposition provides a Hahn decomposition. -/
theorem exists_compl_positive_negative :
    ∃ S : Set α,
      MeasurableSet S ∧
        j.toSignedMeasure ≤[S] 0 ∧
          0 ≤[Sᶜ] j.toSignedMeasure ∧ j.posPart S = 0 ∧ j.negPart Sᶜ = 0 := by
  obtain ⟨S, hS₁, hS₂, hS₃⟩ := j.mutuallySingular
  refine ⟨S, hS₁, ?_, ?_, hS₂, hS₃⟩
  · refine restrict_le_restrict_of_subset_le _ _ fun A hA hA₁ => ?_
    rw [toSignedMeasure, toSignedMeasure_sub_apply hA, measureReal_def,
      show j.posPart A = 0 from nonpos_iff_eq_zero.1 (hS₂ ▸ measure_mono hA₁), ENNReal.toReal_zero,
      zero_sub, neg_le, zero_apply, neg_zero]
    exact ENNReal.toReal_nonneg
  · refine restrict_le_restrict_of_subset_le _ _ fun A hA hA₁ => ?_
    rw [toSignedMeasure, toSignedMeasure_sub_apply hA, measureReal_def (μ := j.negPart),
      show j.negPart A = 0 from nonpos_iff_eq_zero.1 (hS₃ ▸ measure_mono hA₁), ENNReal.toReal_zero,
      sub_zero]
    exact ENNReal.toReal_nonneg

end JordanDecomposition

namespace SignedMeasure

open JordanDecomposition Measure Set VectorMeasure

variable {s : SignedMeasure α}

/-- Given a signed measure `s`, `s.toJordanDecomposition` is the Jordan decomposition `j`,
such that `s = j.toSignedMeasure`. This property is known as the Jordan decomposition
theorem, and is shown by
`MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition`. -/
def toJordanDecomposition (s : SignedMeasure α) : JordanDecomposition α :=
  let i := s.exists_compl_positive_negative.choose
  have hi := s.exists_compl_positive_negative.choose_spec
  { posPart := s.toMeasureOfZeroLE i hi.1 hi.2.1
    negPart := s.toMeasureOfLEZero iᶜ hi.1.compl hi.2.2
    posPart_finite := inferInstance
    negPart_finite := inferInstance
    mutuallySingular := by
      refine ⟨iᶜ, hi.1.compl, ?_, ?_⟩
      · rw [toMeasureOfZeroLE_apply _ _ hi.1 hi.1.compl]; simp
      · rw [toMeasureOfLEZero_apply _ _ hi.1.compl hi.1.compl.compl]; simp }

theorem toJordanDecomposition_spec (s : SignedMeasure α) :
    ∃ (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : 0 ≤[i] s) (hi₃ : s ≤[iᶜ] 0),
      s.toJordanDecomposition.posPart = s.toMeasureOfZeroLE i hi₁ hi₂ ∧
        s.toJordanDecomposition.negPart = s.toMeasureOfLEZero iᶜ hi₁.compl hi₃ := by
  set i := s.exists_compl_positive_negative.choose
  obtain ⟨hi₁, hi₂, hi₃⟩ := s.exists_compl_positive_negative.choose_spec
  exact ⟨i, hi₁, hi₂, hi₃, rfl, rfl⟩

/-- **The Jordan decomposition theorem**: Given a signed measure `s`, there exists a pair of
mutually singular measures `μ` and `ν` such that `s = μ - ν`. In this case, the measures `μ`
and `ν` are given by `s.toJordanDecomposition.posPart` and
`s.toJordanDecomposition.negPart` respectively.

Note that we use `MeasureTheory.JordanDecomposition.toSignedMeasure` to represent the
signed measure corresponding to
`s.toJordanDecomposition.posPart - s.toJordanDecomposition.negPart`. -/
@[simp]
theorem toSignedMeasure_toJordanDecomposition (s : SignedMeasure α) :
    s.toJordanDecomposition.toSignedMeasure = s := by
  obtain ⟨i, hi₁, hi₂, hi₃, hμ, hν⟩ := s.toJordanDecomposition_spec
  simp only [JordanDecomposition.toSignedMeasure, hμ, hν]
  ext k hk
  rw [toSignedMeasure_sub_apply hk, toMeasureOfZeroLE_real_apply _ hi₂ hi₁ hk,
    toMeasureOfLEZero_real_apply _ hi₃ hi₁.compl hk]
  simp only [sub_neg_eq_add]
  rw [← of_union _ (MeasurableSet.inter hi₁ hk) (MeasurableSet.inter hi₁.compl hk),
    Set.inter_comm i, Set.inter_comm iᶜ, Set.inter_union_compl _ _]
  exact (disjoint_compl_right.inf_left _).inf_right _

section

variable {u v w : Set α}

/-- A subset `v` of a null-set `w` has zero measure if `w` is a subset of a positive set `u`. -/
theorem subset_positive_null_set (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hw : MeasurableSet w) (hsu : 0 ≤[u] s) (hw₁ : s w = 0) (hw₂ : w ⊆ u) (hwt : v ⊆ w) :
    s v = 0 := by
  have : s v + s (w \ v) = 0 := by
    rw [← hw₁, ← of_union Set.disjoint_sdiff_right hv (hw.diff hv), Set.union_diff_self,
      Set.union_eq_self_of_subset_left hwt]
  have h₁ := nonneg_of_zero_le_restrict _ (restrict_le_restrict_subset _ _ hu hsu (hwt.trans hw₂))
  have h₂ : 0 ≤ s (w \ v) :=
    nonneg_of_zero_le_restrict _
      (restrict_le_restrict_subset _ _ hu hsu (diff_subset.trans hw₂))
  linarith

/-- A subset `v` of a null-set `w` has zero measure if `w` is a subset of a negative set `u`. -/
theorem subset_negative_null_set (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hw : MeasurableSet w) (hsu : s ≤[u] 0) (hw₁ : s w = 0) (hw₂ : w ⊆ u) (hwt : v ⊆ w) :
    s v = 0 := by
  rw [← s.neg_le_neg_iff _ hu, neg_zero] at hsu
  have := subset_positive_null_set hu hv hw hsu
  simp only [Pi.neg_apply, neg_eq_zero, coe_neg] at this
  exact this hw₁ hw₂ hwt

open scoped symmDiff

/-- If the symmetric difference of two positive sets is a null-set, then so are the differences
between the two sets. -/
theorem of_diff_eq_zero_of_symmDiff_eq_zero_positive (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hsu : 0 ≤[u] s) (hsv : 0 ≤[v] s) (hs : s (u ∆ v) = 0) : s (u \ v) = 0 ∧ s (v \ u) = 0 := by
  rw [restrict_le_restrict_iff] at hsu hsv
  on_goal 1 =>
    have a := hsu (hu.diff hv) diff_subset
    have b := hsv (hv.diff hu) diff_subset
    rw [Set.symmDiff_def,
      of_union (v := s) (Set.disjoint_of_subset_left diff_subset disjoint_sdiff_self_right)
        (hu.diff hv) (hv.diff hu)] at hs
    rw [zero_apply] at a b
    constructor
  all_goals first | linarith | assumption

/-- If the symmetric difference of two negative sets is a null-set, then so are the differences
between the two sets. -/
theorem of_diff_eq_zero_of_symmDiff_eq_zero_negative (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hsu : s ≤[u] 0) (hsv : s ≤[v] 0) (hs : s (u ∆ v) = 0) : s (u \ v) = 0 ∧ s (v \ u) = 0 := by
  rw [← s.neg_le_neg_iff _ hu, neg_zero] at hsu
  rw [← s.neg_le_neg_iff _ hv, neg_zero] at hsv
  have := of_diff_eq_zero_of_symmDiff_eq_zero_positive hu hv hsu hsv
  simp only [Pi.neg_apply, neg_eq_zero, coe_neg] at this
  exact this hs

theorem of_inter_eq_of_symmDiff_eq_zero_positive (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hw : MeasurableSet w) (hsu : 0 ≤[u] s) (hsv : 0 ≤[v] s) (hs : s (u ∆ v) = 0) :
    s (w ∩ u) = s (w ∩ v) := by
  have hwuv : s ((w ∩ u) ∆ (w ∩ v)) = 0 := by
    refine
      subset_positive_null_set (hu.union hv) ((hw.inter hu).symmDiff (hw.inter hv))
        (hu.symmDiff hv) (restrict_le_restrict_union _ _ hu hsu hv hsv) hs
        Set.symmDiff_subset_union ?_
    rw [← Set.inter_symmDiff_distrib_left]
    exact Set.inter_subset_right
  obtain ⟨huv, hvu⟩ :=
    of_diff_eq_zero_of_symmDiff_eq_zero_positive (hw.inter hu) (hw.inter hv)
      (restrict_le_restrict_subset _ _ hu hsu (w.inter_subset_right))
      (restrict_le_restrict_subset _ _ hv hsv (w.inter_subset_right)) hwuv
  rw [← of_diff_of_diff_eq_zero (hw.inter hu) (hw.inter hv) hvu, huv, zero_add]

theorem of_inter_eq_of_symmDiff_eq_zero_negative (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hw : MeasurableSet w) (hsu : s ≤[u] 0) (hsv : s ≤[v] 0) (hs : s (u ∆ v) = 0) :
    s (w ∩ u) = s (w ∩ v) := by
  rw [← s.neg_le_neg_iff _ hu, neg_zero] at hsu
  rw [← s.neg_le_neg_iff _ hv, neg_zero] at hsv
  have := of_inter_eq_of_symmDiff_eq_zero_positive hu hv hw hsu hsv
  simp only [Pi.neg_apply, neg_inj, neg_eq_zero, coe_neg] at this
  exact this hs

end

end SignedMeasure

namespace JordanDecomposition

open Measure VectorMeasure SignedMeasure Function

private theorem eq_of_posPart_eq_posPart {j₁ j₂ : JordanDecomposition α}
    (hj : j₁.posPart = j₂.posPart) (hj' : j₁.toSignedMeasure = j₂.toSignedMeasure) : j₁ = j₂ := by
  ext1
  · exact hj
  · rw [← toSignedMeasure_eq_toSignedMeasure_iff]
    unfold toSignedMeasure at hj'
    simp_rw [hj, sub_right_inj] at hj'
    exact hj'

/-- The Jordan decomposition of a signed measure is unique. -/
theorem toSignedMeasure_injective : Injective <| @JordanDecomposition.toSignedMeasure α _ := by
  /- The main idea is that two Jordan decompositions of a signed measure provide two
    Hahn decompositions for that measure. Then, from `of_symmDiff_compl_positive_negative`,
    the symmetric difference of the two Hahn decompositions has measure zero, thus, allowing us to
    show the equality of the underlying measures of the Jordan decompositions. -/
  intro j₁ j₂ hj
  -- obtain the two Hahn decompositions from the Jordan decompositions
  obtain ⟨S, hS₁, hS₂, hS₃, hS₄, hS₅⟩ := j₁.exists_compl_positive_negative
  obtain ⟨T, hT₁, hT₂, hT₃, hT₄, hT₅⟩ := j₂.exists_compl_positive_negative
  rw [← hj] at hT₂ hT₃
  -- the symmetric differences of the two Hahn decompositions have measure zero
  obtain ⟨hST₁, -⟩ :=
    of_symmDiff_compl_positive_negative hS₁.compl hT₁.compl ⟨hS₃, (compl_compl S).symm ▸ hS₂⟩
      ⟨hT₃, (compl_compl T).symm ▸ hT₂⟩
  -- it suffices to show the Jordan decompositions have the same positive parts
  refine eq_of_posPart_eq_posPart ?_ hj
  ext1 i hi
  -- we see that the positive parts of the two Jordan decompositions are equal to their
  -- associated signed measures restricted on their associated Hahn decompositions
  have hμ₁ : j₁.posPart.real i = j₁.toSignedMeasure (i ∩ Sᶜ) := by
    rw [toSignedMeasure, toSignedMeasure_sub_apply (hi.inter hS₁.compl),
      measureReal_def (μ := j₁.negPart),
      show j₁.negPart (i ∩ Sᶜ) = 0 from
        nonpos_iff_eq_zero.1 (hS₅ ▸ measure_mono Set.inter_subset_right),
      ENNReal.toReal_zero, sub_zero]
    conv_lhs => rw [← Set.inter_union_compl i S]
    rw [measureReal_union, measureReal_def,
      show j₁.posPart (i ∩ S) = 0 from
        nonpos_iff_eq_zero.1 (hS₄ ▸ measure_mono Set.inter_subset_right),
      ENNReal.toReal_zero, zero_add]
    · refine
        Set.disjoint_of_subset_left Set.inter_subset_right
          (Set.disjoint_of_subset_right Set.inter_subset_right disjoint_compl_right)
    · exact hi.inter hS₁.compl
  have hμ₂ : j₂.posPart.real i = j₂.toSignedMeasure (i ∩ Tᶜ) := by
    rw [toSignedMeasure, toSignedMeasure_sub_apply (hi.inter hT₁.compl),
      measureReal_def (μ := j₂.negPart),
      show j₂.negPart (i ∩ Tᶜ) = 0 from
        nonpos_iff_eq_zero.1 (hT₅ ▸ measure_mono Set.inter_subset_right),
      ENNReal.toReal_zero, sub_zero]
    conv_lhs => rw [← Set.inter_union_compl i T]
    rw [measureReal_union, measureReal_def,
      show j₂.posPart (i ∩ T) = 0 from
        nonpos_iff_eq_zero.1 (hT₄ ▸ measure_mono Set.inter_subset_right),
      ENNReal.toReal_zero, zero_add]
    · exact
        Set.disjoint_of_subset_left Set.inter_subset_right
          (Set.disjoint_of_subset_right Set.inter_subset_right disjoint_compl_right)
    · exact hi.inter hT₁.compl
  -- since the two signed measures associated with the Jordan decompositions are the same,
  -- and the symmetric difference of the Hahn decompositions have measure zero, the result follows
  rw [← measureReal_eq_measureReal_iff, hμ₁, hμ₂, ← hj]
  exact of_inter_eq_of_symmDiff_eq_zero_positive hS₁.compl hT₁.compl hi hS₃ hT₃ hST₁

@[simp]
theorem toJordanDecomposition_toSignedMeasure (j : JordanDecomposition α) :
    j.toSignedMeasure.toJordanDecomposition = j :=
  (@toSignedMeasure_injective _ _ j j.toSignedMeasure.toJordanDecomposition (by simp)).symm

end JordanDecomposition

namespace SignedMeasure

open JordanDecomposition

/-- `MeasureTheory.SignedMeasure.toJordanDecomposition` and
`MeasureTheory.JordanDecomposition.toSignedMeasure` form an `Equiv`. -/
@[simps apply symm_apply]
def toJordanDecompositionEquiv (α : Type*) [MeasurableSpace α] :
    SignedMeasure α ≃ JordanDecomposition α where
  toFun := toJordanDecomposition
  invFun := toSignedMeasure
  left_inv := toSignedMeasure_toJordanDecomposition
  right_inv := toJordanDecomposition_toSignedMeasure

theorem toJordanDecomposition_zero : (0 : SignedMeasure α).toJordanDecomposition = 0 := by
  apply toSignedMeasure_injective
  simp [toSignedMeasure_zero]

theorem toJordanDecomposition_neg (s : SignedMeasure α) :
    (-s).toJordanDecomposition = -s.toJordanDecomposition := by
  apply toSignedMeasure_injective
  simp [toSignedMeasure_neg]

theorem toJordanDecomposition_smul (s : SignedMeasure α) (r : ℝ≥0) :
    (r • s).toJordanDecomposition = r • s.toJordanDecomposition := by
  apply toSignedMeasure_injective
  simp [toSignedMeasure_smul]

private theorem toJordanDecomposition_smul_real_nonneg (s : SignedMeasure α) (r : ℝ)
    (hr : 0 ≤ r) : (r • s).toJordanDecomposition = r • s.toJordanDecomposition := by
  lift r to ℝ≥0 using hr
  rw [JordanDecomposition.coe_smul, ← toJordanDecomposition_smul]
  rfl

theorem toJordanDecomposition_smul_real (s : SignedMeasure α) (r : ℝ) :
    (r • s).toJordanDecomposition = r • s.toJordanDecomposition := by
  by_cases hr : 0 ≤ r
  · exact toJordanDecomposition_smul_real_nonneg s r hr
  · ext1
    · rw [real_smul_posPart_neg _ _ (not_le.1 hr),
        show r • s = -(-r • s) by rw [neg_smul, neg_neg], toJordanDecomposition_neg, neg_posPart,
        toJordanDecomposition_smul_real_nonneg, ← smul_negPart, real_smul_nonneg]
      all_goals exact Left.nonneg_neg_iff.2 (le_of_lt (not_le.1 hr))
    · rw [real_smul_negPart_neg _ _ (not_le.1 hr),
        show r • s = -(-r • s) by rw [neg_smul, neg_neg], toJordanDecomposition_neg, neg_negPart,
        toJordanDecomposition_smul_real_nonneg, ← smul_posPart, real_smul_nonneg]
      all_goals exact Left.nonneg_neg_iff.2 (le_of_lt (not_le.1 hr))

theorem toJordanDecomposition_eq {s : SignedMeasure α} {j : JordanDecomposition α}
    (h : s = j.toSignedMeasure) : s.toJordanDecomposition = j := by
  rw [h, toJordanDecomposition_toSignedMeasure]

/-- The total variation of a signed measure. -/
def totalVariation (s : SignedMeasure α) : Measure α :=
  s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart

theorem totalVariation_zero : (0 : SignedMeasure α).totalVariation = 0 := by
  simp [totalVariation, toJordanDecomposition_zero]

theorem totalVariation_neg (s : SignedMeasure α) : (-s).totalVariation = s.totalVariation := by
  simp [totalVariation, toJordanDecomposition_neg, add_comm]

theorem null_of_totalVariation_zero (s : SignedMeasure α) {i : Set α}
    (hs : s.totalVariation i = 0) : s i = 0 := by
  rw [totalVariation, Measure.coe_add, Pi.add_apply, add_eq_zero] at hs
  rw [← toSignedMeasure_toJordanDecomposition s, toSignedMeasure, VectorMeasure.coe_sub,
    Pi.sub_apply, Measure.toSignedMeasure_apply, Measure.toSignedMeasure_apply]
  by_cases hi : MeasurableSet i
  · rw [if_pos hi, if_pos hi]; simp [hs.1, hs.2, measureReal_def]
  · simp [if_neg hi]

theorem absolutelyContinuous_ennreal_iff (s : SignedMeasure α) (μ : VectorMeasure α ℝ≥0∞) :
    s ≪ᵥ μ ↔ s.totalVariation ≪ μ.ennrealToMeasure := by
  constructor <;> intro h
  · refine Measure.AbsolutelyContinuous.mk fun S hS₁ hS₂ => ?_
    obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := s.toJordanDecomposition_spec
    rw [totalVariation, Measure.add_apply, hpos, hneg, toMeasureOfZeroLE_apply _ _ _ hS₁,
      toMeasureOfLEZero_apply _ _ _ hS₁]
    rw [← VectorMeasure.AbsolutelyContinuous.ennrealToMeasure] at h
    simp [h (measure_mono_null (i.inter_subset_right) hS₂),
      h (measure_mono_null (iᶜ.inter_subset_right) hS₂)]
  · refine VectorMeasure.AbsolutelyContinuous.mk fun S hS₁ hS₂ => ?_
    rw [← VectorMeasure.ennrealToMeasure_apply hS₁] at hS₂
    exact null_of_totalVariation_zero s (h hS₂)

theorem totalVariation_absolutelyContinuous_iff (s : SignedMeasure α) (μ : Measure α) :
    s.totalVariation ≪ μ ↔
      s.toJordanDecomposition.posPart ≪ μ ∧ s.toJordanDecomposition.negPart ≪ μ := by
  constructor <;> intro h
  · constructor
    all_goals
      refine Measure.AbsolutelyContinuous.mk fun S _ hS₂ => ?_
      have := h hS₂
      rw [totalVariation, Measure.add_apply, add_eq_zero] at this
    exacts [this.1, this.2]
  · refine Measure.AbsolutelyContinuous.mk fun S _ hS₂ => ?_
    rw [totalVariation, Measure.add_apply, h.1 hS₂, h.2 hS₂, add_zero]

-- TODO: Generalize to vector measures once total variation on vector measures is defined
theorem mutuallySingular_iff (s t : SignedMeasure α) :
    s ⟂ᵥ t ↔ s.totalVariation ⟂ₘ t.totalVariation := by
  constructor
  · rintro ⟨u, hmeas, hu₁, hu₂⟩
    obtain ⟨i, hi₁, hi₂, hi₃, hipos, hineg⟩ := s.toJordanDecomposition_spec
    obtain ⟨j, hj₁, hj₂, hj₃, hjpos, hjneg⟩ := t.toJordanDecomposition_spec
    refine ⟨u, hmeas, ?_, ?_⟩
    · rw [totalVariation, Measure.add_apply, hipos, hineg, toMeasureOfZeroLE_apply _ _ _ hmeas,
        toMeasureOfLEZero_apply _ _ _ hmeas]
      simp [hu₁ _ Set.inter_subset_right]
    · rw [totalVariation, Measure.add_apply, hjpos, hjneg,
        toMeasureOfZeroLE_apply _ _ _ hmeas.compl,
        toMeasureOfLEZero_apply _ _ _ hmeas.compl]
      simp [hu₂ _ Set.inter_subset_right]
  · rintro ⟨u, hmeas, hu₁, hu₂⟩
    exact
      ⟨u, hmeas, fun t htu => null_of_totalVariation_zero _ (measure_mono_null htu hu₁),
        fun t htv => null_of_totalVariation_zero _ (measure_mono_null htv hu₂)⟩

theorem mutuallySingular_ennreal_iff (s : SignedMeasure α) (μ : VectorMeasure α ℝ≥0∞) :
    s ⟂ᵥ μ ↔ s.totalVariation ⟂ₘ μ.ennrealToMeasure := by
  constructor
  · rintro ⟨u, hmeas, hu₁, hu₂⟩
    obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := s.toJordanDecomposition_spec
    refine ⟨u, hmeas, ?_, ?_⟩
    · rw [totalVariation, Measure.add_apply, hpos, hneg, toMeasureOfZeroLE_apply _ _ _ hmeas,
        toMeasureOfLEZero_apply _ _ _ hmeas]
      simp [hu₁ _ Set.inter_subset_right]
    · rw [VectorMeasure.ennrealToMeasure_apply hmeas.compl]
      exact hu₂ _ (Set.Subset.refl _)
  · rintro ⟨u, hmeas, hu₁, hu₂⟩
    refine
      VectorMeasure.MutuallySingular.mk u hmeas
        (fun t htu _ => null_of_totalVariation_zero _ (measure_mono_null htu hu₁)) fun t htv hmt =>
        ?_
    rw [← VectorMeasure.ennrealToMeasure_apply hmt]
    exact measure_mono_null htv hu₂

theorem totalVariation_mutuallySingular_iff (s : SignedMeasure α) (μ : Measure α) :
    s.totalVariation ⟂ₘ μ ↔
      s.toJordanDecomposition.posPart ⟂ₘ μ ∧ s.toJordanDecomposition.negPart ⟂ₘ μ :=
  Measure.MutuallySingular.add_left_iff

end SignedMeasure

end MeasureTheory
