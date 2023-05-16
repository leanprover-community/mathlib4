/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying

! This file was ported from Lean 3 source module measure_theory.measure.vector_measure
! leanprover-community/mathlib commit 70a4f2197832bceab57d7f41379b2592d1110570
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.MeasureSpace
import Mathbin.Analysis.Complex.Basic

/-!

# Vector valued measures

This file defines vector valued measures, which are σ-additive functions from a set to a add monoid
`M` such that it maps the empty set and non-measurable sets to zero. In the case
that `M = ℝ`, we called the vector measure a signed measure and write `signed_measure α`.
Similarly, when `M = ℂ`, we call the measure a complex measure and write `complex_measure α`.

## Main definitions

* `measure_theory.vector_measure` is a vector valued, σ-additive function that maps the empty
  and non-measurable set to zero.
* `measure_theory.vector_measure.map` is the pushforward of a vector measure along a function.
* `measure_theory.vector_measure.restrict` is the restriction of a vector measure on some set.

## Notation

* `v ≤[i] w` means that the vector measure `v` restricted on the set `i` is less than or equal
  to the vector measure `w` restricted on `i`, i.e. `v.restrict i ≤ w.restrict i`.

## Implementation notes

We require all non-measurable sets to be mapped to zero in order for the extensionality lemma
to only compare the underlying functions for measurable sets.

We use `has_sum` instead of `tsum` in the definition of vector measures in comparison to `measure`
since this provides summablity.

## Tags

vector measure, signed measure, complex measure
-/


noncomputable section

open Classical BigOperators NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α β : Type _} {m : MeasurableSpace α}

/-- A vector measure on a measurable space `α` is a σ-additive `M`-valued function (for some `M`
an add monoid) such that the empty set and non-measurable sets are mapped to zero. -/
structure VectorMeasure (α : Type _) [MeasurableSpace α] (M : Type _) [AddCommMonoid M]
  [TopologicalSpace M] where
  measureOf' : Set α → M
  empty' : measure_of' ∅ = 0
  not_measurable' ⦃i : Set α⦄ : ¬MeasurableSet i → measure_of' i = 0
  m_Union' ⦃f : ℕ → Set α⦄ :
    (∀ i, MeasurableSet (f i)) →
      Pairwise (Disjoint on f) → HasSum (fun i => measure_of' (f i)) (measure_of' (⋃ i, f i))
#align measure_theory.vector_measure MeasureTheory.VectorMeasure

/-- A `signed_measure` is a `ℝ`-vector measure. -/
abbrev SignedMeasure (α : Type _) [MeasurableSpace α] :=
  VectorMeasure α ℝ
#align measure_theory.signed_measure MeasureTheory.SignedMeasure

/-- A `complex_measure` is a `ℂ`-vector_measure. -/
abbrev ComplexMeasure (α : Type _) [MeasurableSpace α] :=
  VectorMeasure α ℂ
#align measure_theory.complex_measure MeasureTheory.ComplexMeasure

open Set MeasureTheory

namespace VectorMeasure

section

variable {M : Type _} [AddCommMonoid M] [TopologicalSpace M]

include m

instance : CoeFun (VectorMeasure α M) fun _ => Set α → M :=
  ⟨VectorMeasure.measureOf'⟩

initialize_simps_projections VectorMeasure (measureOf' → apply)

@[simp]
theorem measure_of_eq_coe (v : VectorMeasure α M) : v.measureOf' = v :=
  rfl
#align measure_theory.vector_measure.measure_of_eq_coe MeasureTheory.VectorMeasure.measure_of_eq_coe

@[simp]
theorem empty (v : VectorMeasure α M) : v ∅ = 0 :=
  v.empty'
#align measure_theory.vector_measure.empty MeasureTheory.VectorMeasure.empty

theorem not_measurable (v : VectorMeasure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0 :=
  v.not_measurable' hi
#align measure_theory.vector_measure.not_measurable MeasureTheory.VectorMeasure.not_measurable

theorem m_iUnion (v : VectorMeasure α M) {f : ℕ → Set α} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) : HasSum (fun i => v (f i)) (v (⋃ i, f i)) :=
  v.m_Union' hf₁ hf₂
#align measure_theory.vector_measure.m_Union MeasureTheory.VectorMeasure.m_iUnion

theorem of_disjoint_iUnion_nat [T2Space M] (v : VectorMeasure α M) {f : ℕ → Set α}
    (hf₁ : ∀ i, MeasurableSet (f i)) (hf₂ : Pairwise (Disjoint on f)) :
    v (⋃ i, f i) = ∑' i, v (f i) :=
  (v.m_iUnion hf₁ hf₂).tsum_eq.symm
#align measure_theory.vector_measure.of_disjoint_Union_nat MeasureTheory.VectorMeasure.of_disjoint_iUnion_nat

theorem coe_injective : @Function.Injective (VectorMeasure α M) (Set α → M) coeFn := fun v w h =>
  by
  cases v
  cases w
  congr
#align measure_theory.vector_measure.coe_injective MeasureTheory.VectorMeasure.coe_injective

theorem ext_iff' (v w : VectorMeasure α M) : v = w ↔ ∀ i : Set α, v i = w i := by
  rw [← coe_injective.eq_iff, Function.funext_iff]
#align measure_theory.vector_measure.ext_iff' MeasureTheory.VectorMeasure.ext_iff'

theorem ext_iff (v w : VectorMeasure α M) : v = w ↔ ∀ i : Set α, MeasurableSet i → v i = w i :=
  by
  constructor
  · rintro rfl _ _
    rfl
  · rw [ext_iff']
    intro h i
    by_cases hi : MeasurableSet i
    · exact h i hi
    · simp_rw [not_measurable _ hi]
#align measure_theory.vector_measure.ext_iff MeasureTheory.VectorMeasure.ext_iff

@[ext]
theorem ext {s t : VectorMeasure α M} (h : ∀ i : Set α, MeasurableSet i → s i = t i) : s = t :=
  (ext_iff s t).2 h
#align measure_theory.vector_measure.ext MeasureTheory.VectorMeasure.ext

variable [T2Space M] {v : VectorMeasure α M} {f : ℕ → Set α}

theorem hasSum_of_disjoint_iUnion [Countable β] {f : β → Set α} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) : HasSum (fun i => v (f i)) (v (⋃ i, f i)) :=
  by
  cases nonempty_encodable β
  set g := fun i : ℕ => ⋃ (b : β) (H : b ∈ Encodable.decode₂ β i), f b with hg
  have hg₁ : ∀ i, MeasurableSet (g i) := fun _ =>
    MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _ => hf₁ b
  have hg₂ : Pairwise (Disjoint on g) := Encodable.iUnion_decode₂_disjoint_on hf₂
  have := v.of_disjoint_Union_nat hg₁ hg₂
  rw [hg, Encodable.iUnion_decode₂] at this
  have hg₃ : (fun i : β => v (f i)) = fun i => v (g (Encodable.encode i)) :=
    by
    ext
    rw [hg]
    simp only
    congr
    ext y
    simp only [exists_prop, mem_Union, Option.mem_def]
    constructor
    · intro hy
      refine' ⟨x, (Encodable.decode₂_is_partial_inv _ _).2 rfl, hy⟩
    · rintro ⟨b, hb₁, hb₂⟩
      rw [Encodable.decode₂_is_partial_inv _ _] at hb₁
      rwa [← Encodable.encode_injective hb₁]
  rw [Summable.hasSum_iff, this, ← tsum_iUnion_decode₂]
  · exact v.empty
  · rw [hg₃]
    change Summable ((fun i => v (g i)) ∘ Encodable.encode)
    rw [Function.Injective.summable_iff Encodable.encode_injective]
    · exact (v.m_Union hg₁ hg₂).Summable
    · intro x hx
      convert v.empty
      simp only [Union_eq_empty, Option.mem_def, not_exists, mem_range] at hx⊢
      intro i hi
      exact False.elim ((hx i) ((Encodable.decode₂_is_partial_inv _ _).1 hi))
#align measure_theory.vector_measure.has_sum_of_disjoint_Union MeasureTheory.VectorMeasure.hasSum_of_disjoint_iUnion

theorem of_disjoint_iUnion [Countable β] {f : β → Set α} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) : v (⋃ i, f i) = ∑' i, v (f i) :=
  (hasSum_of_disjoint_iUnion hf₁ hf₂).tsum_eq.symm
#align measure_theory.vector_measure.of_disjoint_Union MeasureTheory.VectorMeasure.of_disjoint_iUnion

theorem of_union {A B : Set α} (h : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    v (A ∪ B) = v A + v B :=
  by
  rw [union_eq_Union, of_disjoint_Union, tsum_fintype, Fintype.sum_bool, cond, cond]
  exacts[fun b => Bool.casesOn b hB hA, pairwise_disjoint_on_bool.2 h]
#align measure_theory.vector_measure.of_union MeasureTheory.VectorMeasure.of_union

theorem of_add_of_diff {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A ⊆ B) :
    v A + v (B \ A) = v B :=
  by
  rw [← of_union disjoint_sdiff_right hA (hB.diff hA), union_diff_cancel h]
  infer_instance
#align measure_theory.vector_measure.of_add_of_diff MeasureTheory.VectorMeasure.of_add_of_diff

theorem of_diff {M : Type _} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    {v : VectorMeasure α M} {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : A ⊆ B) : v (B \ A) = v B - v A :=
  by
  rw [← of_add_of_diff hA hB h, add_sub_cancel']
  infer_instance
#align measure_theory.vector_measure.of_diff MeasureTheory.VectorMeasure.of_diff

theorem of_diff_of_diff_eq_zero {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h' : v (B \ A) = 0) : v (A \ B) + v B = v A :=
  by
  symm
  calc
    v A = v (A \ B ∪ A ∩ B) := by simp only [Set.diff_union_inter]
    _ = v (A \ B) + v (A ∩ B) := by
      rw [of_union]
      · rw [disjoint_comm]
        exact Set.disjoint_of_subset_left (A.inter_subset_right B) disjoint_sdiff_self_right
      · exact hA.diff hB
      · exact hA.inter hB
    _ = v (A \ B) + v (A ∩ B ∪ B \ A) :=
      by
      rw [of_union, h', add_zero]
      · exact Set.disjoint_of_subset_left (A.inter_subset_left B) disjoint_sdiff_self_right
      · exact hA.inter hB
      · exact hB.diff hA
    _ = v (A \ B) + v B := by rw [Set.union_comm, Set.inter_comm, Set.diff_union_inter]
    
#align measure_theory.vector_measure.of_diff_of_diff_eq_zero MeasureTheory.VectorMeasure.of_diff_of_diff_eq_zero

theorem of_iUnion_nonneg {M : Type _} [TopologicalSpace M] [OrderedAddCommMonoid M]
    [OrderClosedTopology M] {v : VectorMeasure α M} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) (hf₃ : ∀ i, 0 ≤ v (f i)) : 0 ≤ v (⋃ i, f i) :=
  (v.of_disjoint_iUnion_nat hf₁ hf₂).symm ▸ tsum_nonneg hf₃
#align measure_theory.vector_measure.of_Union_nonneg MeasureTheory.VectorMeasure.of_iUnion_nonneg

theorem of_iUnion_nonpos {M : Type _} [TopologicalSpace M] [OrderedAddCommMonoid M]
    [OrderClosedTopology M] {v : VectorMeasure α M} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) (hf₃ : ∀ i, v (f i) ≤ 0) : v (⋃ i, f i) ≤ 0 :=
  (v.of_disjoint_iUnion_nat hf₁ hf₂).symm ▸ tsum_nonpos hf₃
#align measure_theory.vector_measure.of_Union_nonpos MeasureTheory.VectorMeasure.of_iUnion_nonpos

theorem of_nonneg_disjoint_union_eq_zero {s : SignedMeasure α} {A B : Set α} (h : Disjoint A B)
    (hA₁ : MeasurableSet A) (hB₁ : MeasurableSet B) (hA₂ : 0 ≤ s A) (hB₂ : 0 ≤ s B)
    (hAB : s (A ∪ B) = 0) : s A = 0 :=
  by
  rw [of_union h hA₁ hB₁] at hAB
  linarith
  infer_instance
#align measure_theory.vector_measure.of_nonneg_disjoint_union_eq_zero MeasureTheory.VectorMeasure.of_nonneg_disjoint_union_eq_zero

theorem of_nonpos_disjoint_union_eq_zero {s : SignedMeasure α} {A B : Set α} (h : Disjoint A B)
    (hA₁ : MeasurableSet A) (hB₁ : MeasurableSet B) (hA₂ : s A ≤ 0) (hB₂ : s B ≤ 0)
    (hAB : s (A ∪ B) = 0) : s A = 0 :=
  by
  rw [of_union h hA₁ hB₁] at hAB
  linarith
  infer_instance
#align measure_theory.vector_measure.of_nonpos_disjoint_union_eq_zero MeasureTheory.VectorMeasure.of_nonpos_disjoint_union_eq_zero

end

section SMul

variable {M : Type _} [AddCommMonoid M] [TopologicalSpace M]

variable {R : Type _} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

include m

/-- Given a real number `r` and a signed measure `s`, `smul r s` is the signed
measure corresponding to the function `r • s`. -/
def smul (r : R) (v : VectorMeasure α M) : VectorMeasure α M
    where
  measureOf' := r • v
  empty' := by rw [Pi.smul_apply, Empty, smul_zero]
  not_measurable' _ hi := by rw [Pi.smul_apply, v.not_measurable hi, smul_zero]
  m_Union' _ hf₁ hf₂ := HasSum.const_smul _ (v.m_iUnion hf₁ hf₂)
#align measure_theory.vector_measure.smul MeasureTheory.VectorMeasure.smul

instance : SMul R (VectorMeasure α M) :=
  ⟨smul⟩

@[simp]
theorem coe_smul (r : R) (v : VectorMeasure α M) : ⇑(r • v) = r • v :=
  rfl
#align measure_theory.vector_measure.coe_smul MeasureTheory.VectorMeasure.coe_smul

theorem smul_apply (r : R) (v : VectorMeasure α M) (i : Set α) : (r • v) i = r • v i :=
  rfl
#align measure_theory.vector_measure.smul_apply MeasureTheory.VectorMeasure.smul_apply

end SMul

section AddCommMonoid

variable {M : Type _} [AddCommMonoid M] [TopologicalSpace M]

include m

instance : Zero (VectorMeasure α M) :=
  ⟨⟨0, rfl, fun _ _ => rfl, fun _ _ _ => hasSum_zero⟩⟩

instance : Inhabited (VectorMeasure α M) :=
  ⟨0⟩

@[simp]
theorem coe_zero : ⇑(0 : VectorMeasure α M) = 0 :=
  rfl
#align measure_theory.vector_measure.coe_zero MeasureTheory.VectorMeasure.coe_zero

theorem zero_apply (i : Set α) : (0 : VectorMeasure α M) i = 0 :=
  rfl
#align measure_theory.vector_measure.zero_apply MeasureTheory.VectorMeasure.zero_apply

variable [ContinuousAdd M]

/-- The sum of two vector measure is a vector measure. -/
def add (v w : VectorMeasure α M) : VectorMeasure α M
    where
  measureOf' := v + w
  empty' := by simp
  not_measurable' _ hi := by simp [v.not_measurable hi, w.not_measurable hi]
  m_Union' f hf₁ hf₂ := HasSum.add (v.m_iUnion hf₁ hf₂) (w.m_iUnion hf₁ hf₂)
#align measure_theory.vector_measure.add MeasureTheory.VectorMeasure.add

instance : Add (VectorMeasure α M) :=
  ⟨add⟩

@[simp]
theorem coe_add (v w : VectorMeasure α M) : ⇑(v + w) = v + w :=
  rfl
#align measure_theory.vector_measure.coe_add MeasureTheory.VectorMeasure.coe_add

theorem add_apply (v w : VectorMeasure α M) (i : Set α) : (v + w) i = v i + w i :=
  rfl
#align measure_theory.vector_measure.add_apply MeasureTheory.VectorMeasure.add_apply

instance : AddCommMonoid (VectorMeasure α M) :=
  Function.Injective.addCommMonoid _ coe_injective coe_zero coe_add fun _ _ => coe_smul _ _

/-- `coe_fn` is an `add_monoid_hom`. -/
@[simps]
def coeFnAddMonoidHom : VectorMeasure α M →+ Set α → M
    where
  toFun := coeFn
  map_zero' := coe_zero
  map_add' := coe_add
#align measure_theory.vector_measure.coe_fn_add_monoid_hom MeasureTheory.VectorMeasure.coeFnAddMonoidHom

end AddCommMonoid

section AddCommGroup

variable {M : Type _} [AddCommGroup M] [TopologicalSpace M] [TopologicalAddGroup M]

include m

/-- The negative of a vector measure is a vector measure. -/
def neg (v : VectorMeasure α M) : VectorMeasure α M
    where
  measureOf' := -v
  empty' := by simp
  not_measurable' _ hi := by simp [v.not_measurable hi]
  m_Union' f hf₁ hf₂ := HasSum.neg <| v.m_iUnion hf₁ hf₂
#align measure_theory.vector_measure.neg MeasureTheory.VectorMeasure.neg

instance : Neg (VectorMeasure α M) :=
  ⟨neg⟩

@[simp]
theorem coe_neg (v : VectorMeasure α M) : ⇑(-v) = -v :=
  rfl
#align measure_theory.vector_measure.coe_neg MeasureTheory.VectorMeasure.coe_neg

theorem neg_apply (v : VectorMeasure α M) (i : Set α) : (-v) i = -v i :=
  rfl
#align measure_theory.vector_measure.neg_apply MeasureTheory.VectorMeasure.neg_apply

/-- The difference of two vector measure is a vector measure. -/
def sub (v w : VectorMeasure α M) : VectorMeasure α M
    where
  measureOf' := v - w
  empty' := by simp
  not_measurable' _ hi := by simp [v.not_measurable hi, w.not_measurable hi]
  m_Union' f hf₁ hf₂ := HasSum.sub (v.m_iUnion hf₁ hf₂) (w.m_iUnion hf₁ hf₂)
#align measure_theory.vector_measure.sub MeasureTheory.VectorMeasure.sub

instance : Sub (VectorMeasure α M) :=
  ⟨sub⟩

@[simp]
theorem coe_sub (v w : VectorMeasure α M) : ⇑(v - w) = v - w :=
  rfl
#align measure_theory.vector_measure.coe_sub MeasureTheory.VectorMeasure.coe_sub

theorem sub_apply (v w : VectorMeasure α M) (i : Set α) : (v - w) i = v i - w i :=
  rfl
#align measure_theory.vector_measure.sub_apply MeasureTheory.VectorMeasure.sub_apply

instance : AddCommGroup (VectorMeasure α M) :=
  Function.Injective.addCommGroup _ coe_injective coe_zero coe_add coe_neg coe_sub
    (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

end AddCommGroup

section DistribMulAction

variable {M : Type _} [AddCommMonoid M] [TopologicalSpace M]

variable {R : Type _} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

include m

instance [ContinuousAdd M] : DistribMulAction R (VectorMeasure α M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

end DistribMulAction

section Module

variable {M : Type _} [AddCommMonoid M] [TopologicalSpace M]

variable {R : Type _} [Semiring R] [Module R M] [ContinuousConstSMul R M]

include m

instance [ContinuousAdd M] : Module R (VectorMeasure α M) :=
  Function.Injective.module R coeFnAddMonoidHom coe_injective coe_smul

end Module

end VectorMeasure

namespace Measure

include m

/-- A finite measure coerced into a real function is a signed measure. -/
@[simps]
def toSignedMeasure (μ : Measure α) [hμ : FiniteMeasure μ] : SignedMeasure α
    where
  measureOf' := fun i : Set α => if MeasurableSet i then (μ.measureOf i).toReal else 0
  empty' := by simp [μ.empty]
  not_measurable' _ hi := if_neg hi
  m_Union' := by
    intro _ hf₁ hf₂
    rw [μ.m_Union hf₁ hf₂, ENNReal.tsum_toReal_eq, if_pos (MeasurableSet.iUnion hf₁),
      Summable.hasSum_iff]
    · congr
      ext n
      rw [if_pos (hf₁ n)]
    · refine' @summable_of_nonneg_of_le _ (ENNReal.toReal ∘ μ ∘ f) _ _ _ _
      · intro
        split_ifs
        exacts[ENNReal.toReal_nonneg, le_rfl]
      · intro
        split_ifs
        exacts[le_rfl, ENNReal.toReal_nonneg]
      exact summable_measure_to_real hf₁ hf₂
    · intro a ha
      apply ne_of_lt hμ.measure_univ_lt_top
      rw [eq_top_iff, ← ha, outer_measure.measure_of_eq_coe, coe_to_outer_measure]
      exact measure_mono (Set.subset_univ _)
#align measure_theory.measure.to_signed_measure MeasureTheory.Measure.toSignedMeasure

theorem toSignedMeasure_apply_measurable {μ : Measure α} [FiniteMeasure μ] {i : Set α}
    (hi : MeasurableSet i) : μ.toSignedMeasure i = (μ i).toReal :=
  if_pos hi
#align measure_theory.measure.to_signed_measure_apply_measurable MeasureTheory.Measure.toSignedMeasure_apply_measurable

-- Without this lemma, `singular_part_neg` in `measure_theory.decomposition.lebesgue` is
-- extremely slow
theorem toSignedMeasure_congr {μ ν : Measure α} [FiniteMeasure μ] [FiniteMeasure ν] (h : μ = ν) :
    μ.toSignedMeasure = ν.toSignedMeasure := by
  congr
  exact h
#align measure_theory.measure.to_signed_measure_congr MeasureTheory.Measure.toSignedMeasure_congr

theorem toSignedMeasure_eq_toSignedMeasure_iff {μ ν : Measure α} [FiniteMeasure μ]
    [FiniteMeasure ν] : μ.toSignedMeasure = ν.toSignedMeasure ↔ μ = ν :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · ext1 i hi
    have : μ.to_signed_measure i = ν.to_signed_measure i := by rw [h]
    rwa [to_signed_measure_apply_measurable hi, to_signed_measure_apply_measurable hi,
        ENNReal.toReal_eq_toReal] at this <;>
      · exact measure_ne_top _ _
  · congr
    assumption
#align measure_theory.measure.to_signed_measure_eq_to_signed_measure_iff MeasureTheory.Measure.toSignedMeasure_eq_toSignedMeasure_iff

@[simp]
theorem toSignedMeasure_zero : (0 : Measure α).toSignedMeasure = 0 :=
  by
  ext (i hi)
  simp
#align measure_theory.measure.to_signed_measure_zero MeasureTheory.Measure.toSignedMeasure_zero

@[simp]
theorem toSignedMeasure_add (μ ν : Measure α) [FiniteMeasure μ] [FiniteMeasure ν] :
    (μ + ν).toSignedMeasure = μ.toSignedMeasure + ν.toSignedMeasure :=
  by
  ext (i hi)
  rw [to_signed_measure_apply_measurable hi, add_apply,
    ENNReal.toReal_add (ne_of_lt (measure_lt_top _ _)) (ne_of_lt (measure_lt_top _ _)),
    vector_measure.add_apply, to_signed_measure_apply_measurable hi,
    to_signed_measure_apply_measurable hi]
  all_goals infer_instance
#align measure_theory.measure.to_signed_measure_add MeasureTheory.Measure.toSignedMeasure_add

@[simp]
theorem toSignedMeasure_smul (μ : Measure α) [FiniteMeasure μ] (r : ℝ≥0) :
    (r • μ).toSignedMeasure = r • μ.toSignedMeasure :=
  by
  ext (i hi)
  rw [to_signed_measure_apply_measurable hi, vector_measure.smul_apply,
    to_signed_measure_apply_measurable hi, coe_smul, Pi.smul_apply, ENNReal.toReal_smul]
#align measure_theory.measure.to_signed_measure_smul MeasureTheory.Measure.toSignedMeasure_smul

/-- A measure is a vector measure over `ℝ≥0∞`. -/
@[simps]
def toEnnrealVectorMeasure (μ : Measure α) : VectorMeasure α ℝ≥0∞
    where
  measureOf' := fun i : Set α => if MeasurableSet i then μ i else 0
  empty' := by simp [μ.empty]
  not_measurable' _ hi := if_neg hi
  m_Union' _ hf₁ hf₂ := by
    rw [Summable.hasSum_iff ENNReal.summable]
    · rw [if_pos (MeasurableSet.iUnion hf₁), MeasureTheory.measure_iUnion hf₂ hf₁]
      exact tsum_congr fun n => if_pos (hf₁ n)
#align measure_theory.measure.to_ennreal_vector_measure MeasureTheory.Measure.toEnnrealVectorMeasure

theorem toEnnrealVectorMeasure_apply_measurable {μ : Measure α} {i : Set α} (hi : MeasurableSet i) :
    μ.toEnnrealVectorMeasure i = μ i :=
  if_pos hi
#align measure_theory.measure.to_ennreal_vector_measure_apply_measurable MeasureTheory.Measure.toEnnrealVectorMeasure_apply_measurable

@[simp]
theorem toEnnrealVectorMeasure_zero : (0 : Measure α).toEnnrealVectorMeasure = 0 :=
  by
  ext (i hi)
  simp
#align measure_theory.measure.to_ennreal_vector_measure_zero MeasureTheory.Measure.toEnnrealVectorMeasure_zero

@[simp]
theorem toEnnrealVectorMeasure_add (μ ν : Measure α) :
    (μ + ν).toEnnrealVectorMeasure = μ.toEnnrealVectorMeasure + ν.toEnnrealVectorMeasure :=
  by
  refine' MeasureTheory.VectorMeasure.ext fun i hi => _
  rw [to_ennreal_vector_measure_apply_measurable hi, add_apply, vector_measure.add_apply,
    to_ennreal_vector_measure_apply_measurable hi, to_ennreal_vector_measure_apply_measurable hi]
#align measure_theory.measure.to_ennreal_vector_measure_add MeasureTheory.Measure.toEnnrealVectorMeasure_add

theorem toSignedMeasure_sub_apply {μ ν : Measure α} [FiniteMeasure μ] [FiniteMeasure ν] {i : Set α}
    (hi : MeasurableSet i) :
    (μ.toSignedMeasure - ν.toSignedMeasure) i = (μ i).toReal - (ν i).toReal := by
  rw [vector_measure.sub_apply, to_signed_measure_apply_measurable hi,
    measure.to_signed_measure_apply_measurable hi, sub_eq_add_neg]
#align measure_theory.measure.to_signed_measure_sub_apply MeasureTheory.Measure.toSignedMeasure_sub_apply

end Measure

namespace VectorMeasure

open Measure

section

/-- A vector measure over `ℝ≥0∞` is a measure. -/
def ennrealToMeasure {m : MeasurableSpace α} (v : VectorMeasure α ℝ≥0∞) : Measure α :=
  ofMeasurable (fun s _ => v s) v.Empty fun f hf₁ hf₂ => v.of_disjoint_iUnion_nat hf₁ hf₂
#align measure_theory.vector_measure.ennreal_to_measure MeasureTheory.VectorMeasure.ennrealToMeasure

theorem ennrealToMeasure_apply {m : MeasurableSpace α} {v : VectorMeasure α ℝ≥0∞} {s : Set α}
    (hs : MeasurableSet s) : ennrealToMeasure v s = v s := by
  rw [ennreal_to_measure, of_measurable_apply _ hs]
#align measure_theory.vector_measure.ennreal_to_measure_apply MeasureTheory.VectorMeasure.ennrealToMeasure_apply

/-- The equiv between `vector_measure α ℝ≥0∞` and `measure α` formed by
`measure_theory.vector_measure.ennreal_to_measure` and
`measure_theory.measure.to_ennreal_vector_measure`. -/
@[simps]
def equivMeasure [MeasurableSpace α] : VectorMeasure α ℝ≥0∞ ≃ Measure α
    where
  toFun := ennrealToMeasure
  invFun := toEnnrealVectorMeasure
  left_inv _ :=
    ext fun s hs => by
      rw [to_ennreal_vector_measure_apply_measurable hs, ennreal_to_measure_apply hs]
  right_inv _ :=
    Measure.ext fun s hs => by
      rw [ennreal_to_measure_apply hs, to_ennreal_vector_measure_apply_measurable hs]
#align measure_theory.vector_measure.equiv_measure MeasureTheory.VectorMeasure.equivMeasure

end

section

variable [MeasurableSpace α] [MeasurableSpace β]

variable {M : Type _} [AddCommMonoid M] [TopologicalSpace M]

variable (v : VectorMeasure α M)

/-- The pushforward of a vector measure along a function. -/
def map (v : VectorMeasure α M) (f : α → β) : VectorMeasure β M :=
  if hf : Measurable f then
    { measureOf' := fun s => if MeasurableSet s then v (f ⁻¹' s) else 0
      empty' := by simp
      not_measurable' := fun i hi => if_neg hi
      m_Union' := by
        intro g hg₁ hg₂
        convert v.m_Union (fun i => hf (hg₁ i)) fun i j hij => (hg₂ hij).Preimage _
        · ext i
          rw [if_pos (hg₁ i)]
        · rw [preimage_Union, if_pos (MeasurableSet.iUnion hg₁)] }
  else 0
#align measure_theory.vector_measure.map MeasureTheory.VectorMeasure.map

theorem map_not_measurable {f : α → β} (hf : ¬Measurable f) : v.map f = 0 :=
  dif_neg hf
#align measure_theory.vector_measure.map_not_measurable MeasureTheory.VectorMeasure.map_not_measurable

theorem map_apply {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    v.map f s = v (f ⁻¹' s) := by
  rw [map, dif_pos hf]
  exact if_pos hs
#align measure_theory.vector_measure.map_apply MeasureTheory.VectorMeasure.map_apply

@[simp]
theorem map_id : v.map id = v :=
  ext fun i hi => by rw [map_apply v measurable_id hi, preimage_id]
#align measure_theory.vector_measure.map_id MeasureTheory.VectorMeasure.map_id

@[simp]
theorem map_zero (f : α → β) : (0 : VectorMeasure α M).map f = 0 :=
  by
  by_cases hf : Measurable f
  · ext (i hi)
    rw [map_apply _ hf hi, zero_apply, zero_apply]
  · exact dif_neg hf
#align measure_theory.vector_measure.map_zero MeasureTheory.VectorMeasure.map_zero

section

variable {N : Type _} [AddCommMonoid N] [TopologicalSpace N]

/-- Given a vector measure `v` on `M` and a continuous add_monoid_hom `f : M → N`, `f ∘ v` is a
vector measure on `N`. -/
def mapRange (v : VectorMeasure α M) (f : M →+ N) (hf : Continuous f) : VectorMeasure α N
    where
  measureOf' s := f (v s)
  empty' := by rw [Empty, AddMonoidHom.map_zero]
  not_measurable' i hi := by rw [not_measurable v hi, AddMonoidHom.map_zero]
  m_Union' g hg₁ hg₂ := HasSum.map (v.m_iUnion hg₁ hg₂) f hf
#align measure_theory.vector_measure.map_range MeasureTheory.VectorMeasure.mapRange

@[simp]
theorem mapRange_apply {f : M →+ N} (hf : Continuous f) {s : Set α} :
    v.map_range f hf s = f (v s) :=
  rfl
#align measure_theory.vector_measure.map_range_apply MeasureTheory.VectorMeasure.mapRange_apply

@[simp]
theorem mapRange_id : v.map_range (AddMonoidHom.id M) continuous_id = v :=
  by
  ext
  rfl
#align measure_theory.vector_measure.map_range_id MeasureTheory.VectorMeasure.mapRange_id

@[simp]
theorem mapRange_zero {f : M →+ N} (hf : Continuous f) :
    mapRange (0 : VectorMeasure α M) f hf = 0 :=
  by
  ext
  simp
#align measure_theory.vector_measure.map_range_zero MeasureTheory.VectorMeasure.mapRange_zero

section ContinuousAdd

variable [ContinuousAdd M] [ContinuousAdd N]

@[simp]
theorem mapRange_add {v w : VectorMeasure α M} {f : M →+ N} (hf : Continuous f) :
    (v + w).map_range f hf = v.map_range f hf + w.map_range f hf :=
  by
  ext
  simp
#align measure_theory.vector_measure.map_range_add MeasureTheory.VectorMeasure.mapRange_add

/-- Given a continuous add_monoid_hom `f : M → N`, `map_range_hom` is the add_monoid_hom mapping the
vector measure `v` on `M` to the vector measure `f ∘ v` on `N`. -/
def mapRangeHom (f : M →+ N) (hf : Continuous f) : VectorMeasure α M →+ VectorMeasure α N
    where
  toFun v := v.map_range f hf
  map_zero' := mapRange_zero hf
  map_add' _ _ := mapRange_add hf
#align measure_theory.vector_measure.map_range_hom MeasureTheory.VectorMeasure.mapRangeHom

end ContinuousAdd

section Module

variable {R : Type _} [Semiring R] [Module R M] [Module R N]

variable [ContinuousAdd M] [ContinuousAdd N] [ContinuousConstSMul R M] [ContinuousConstSMul R N]

/-- Given a continuous linear map `f : M → N`, `map_rangeₗ` is the linear map mapping the
vector measure `v` on `M` to the vector measure `f ∘ v` on `N`. -/
def mapRangeₗ (f : M →ₗ[R] N) (hf : Continuous f) : VectorMeasure α M →ₗ[R] VectorMeasure α N
    where
  toFun v := v.map_range f.toAddMonoidHom hf
  map_add' _ _ := mapRange_add hf
  map_smul' := by
    intros
    ext
    simp
#align measure_theory.vector_measure.map_rangeₗ MeasureTheory.VectorMeasure.mapRangeₗ

end Module

end

/-- The restriction of a vector measure on some set. -/
def restrict (v : VectorMeasure α M) (i : Set α) : VectorMeasure α M :=
  if hi : MeasurableSet i then
    { measureOf' := fun s => if MeasurableSet s then v (s ∩ i) else 0
      empty' := by simp
      not_measurable' := fun i hi => if_neg hi
      m_Union' := by
        intro f hf₁ hf₂
        convert v.m_Union (fun n => (hf₁ n).inter hi)
            (hf₂.mono fun i j => Disjoint.mono inf_le_left inf_le_left)
        · ext n
          rw [if_pos (hf₁ n)]
        · rw [Union_inter, if_pos (MeasurableSet.iUnion hf₁)] }
  else 0
#align measure_theory.vector_measure.restrict MeasureTheory.VectorMeasure.restrict

theorem restrict_not_measurable {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0 :=
  dif_neg hi
#align measure_theory.vector_measure.restrict_not_measurable MeasureTheory.VectorMeasure.restrict_not_measurable

theorem restrict_apply {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) :
    v.restrict i j = v (j ∩ i) := by
  rw [restrict, dif_pos hi]
  exact if_pos hj
#align measure_theory.vector_measure.restrict_apply MeasureTheory.VectorMeasure.restrict_apply

theorem restrict_eq_self {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j)
    (hij : j ⊆ i) : v.restrict i j = v j := by
  rw [restrict_apply v hi hj, inter_eq_left_iff_subset.2 hij]
#align measure_theory.vector_measure.restrict_eq_self MeasureTheory.VectorMeasure.restrict_eq_self

@[simp]
theorem restrict_empty : v.restrict ∅ = 0 :=
  ext fun i hi => by rw [restrict_apply v MeasurableSet.empty hi, inter_empty, v.empty, zero_apply]
#align measure_theory.vector_measure.restrict_empty MeasureTheory.VectorMeasure.restrict_empty

@[simp]
theorem restrict_univ : v.restrict univ = v :=
  ext fun i hi => by rw [restrict_apply v MeasurableSet.univ hi, inter_univ]
#align measure_theory.vector_measure.restrict_univ MeasureTheory.VectorMeasure.restrict_univ

@[simp]
theorem restrict_zero {i : Set α} : (0 : VectorMeasure α M).restrict i = 0 :=
  by
  by_cases hi : MeasurableSet i
  · ext (j hj)
    rw [restrict_apply 0 hi hj]
    rfl
  · exact dif_neg hi
#align measure_theory.vector_measure.restrict_zero MeasureTheory.VectorMeasure.restrict_zero

section ContinuousAdd

variable [ContinuousAdd M]

theorem map_add (v w : VectorMeasure α M) (f : α → β) : (v + w).map f = v.map f + w.map f :=
  by
  by_cases hf : Measurable f
  · ext (i hi)
    simp [map_apply _ hf hi]
  · simp [map, dif_neg hf]
#align measure_theory.vector_measure.map_add MeasureTheory.VectorMeasure.map_add

/-- `vector_measure.map` as an additive monoid homomorphism. -/
@[simps]
def mapGm (f : α → β) : VectorMeasure α M →+ VectorMeasure β M
    where
  toFun v := v.map f
  map_zero' := map_zero f
  map_add' _ _ := map_add _ _ f
#align measure_theory.vector_measure.map_gm MeasureTheory.VectorMeasure.mapGm

theorem restrict_add (v w : VectorMeasure α M) (i : Set α) :
    (v + w).restrict i = v.restrict i + w.restrict i :=
  by
  by_cases hi : MeasurableSet i
  · ext (j hj)
    simp [restrict_apply _ hi hj]
  · simp [restrict_not_measurable _ hi]
#align measure_theory.vector_measure.restrict_add MeasureTheory.VectorMeasure.restrict_add

/-- `vector_measure.restrict` as an additive monoid homomorphism. -/
@[simps]
def restrictGm (i : Set α) : VectorMeasure α M →+ VectorMeasure α M
    where
  toFun v := v.restrict i
  map_zero' := restrict_zero
  map_add' _ _ := restrict_add _ _ i
#align measure_theory.vector_measure.restrict_gm MeasureTheory.VectorMeasure.restrictGm

end ContinuousAdd

end

section

variable [MeasurableSpace β]

variable {M : Type _} [AddCommMonoid M] [TopologicalSpace M]

variable {R : Type _} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

include m

@[simp]
theorem map_smul {v : VectorMeasure α M} {f : α → β} (c : R) : (c • v).map f = c • v.map f :=
  by
  by_cases hf : Measurable f
  · ext (i hi)
    simp [map_apply _ hf hi]
  · simp only [map, dif_neg hf]
    -- `smul_zero` does not work since we do not require `has_continuous_add`
    ext (i hi)
    simp
#align measure_theory.vector_measure.map_smul MeasureTheory.VectorMeasure.map_smul

@[simp]
theorem restrict_smul {v : VectorMeasure α M} {i : Set α} (c : R) :
    (c • v).restrict i = c • v.restrict i :=
  by
  by_cases hi : MeasurableSet i
  · ext (j hj)
    simp [restrict_apply _ hi hj]
  · simp only [restrict_not_measurable _ hi]
    -- `smul_zero` does not work since we do not require `has_continuous_add`
    ext (j hj)
    simp
#align measure_theory.vector_measure.restrict_smul MeasureTheory.VectorMeasure.restrict_smul

end

section

variable [MeasurableSpace β]

variable {M : Type _} [AddCommMonoid M] [TopologicalSpace M]

variable {R : Type _} [Semiring R] [Module R M] [ContinuousConstSMul R M] [ContinuousAdd M]

include m

/-- `vector_measure.map` as a linear map. -/
@[simps]
def mapₗ (f : α → β) : VectorMeasure α M →ₗ[R] VectorMeasure β M
    where
  toFun v := v.map f
  map_add' _ _ := map_add _ _ f
  map_smul' _ _ := map_smul _
#align measure_theory.vector_measure.mapₗ MeasureTheory.VectorMeasure.mapₗ

/-- `vector_measure.restrict` as an additive monoid homomorphism. -/
@[simps]
def restrictₗ (i : Set α) : VectorMeasure α M →ₗ[R] VectorMeasure α M
    where
  toFun v := v.restrict i
  map_add' _ _ := restrict_add _ _ i
  map_smul' _ _ := restrict_smul _
#align measure_theory.vector_measure.restrictₗ MeasureTheory.VectorMeasure.restrictₗ

end

section

variable {M : Type _} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]

include m

/-- Vector measures over a partially ordered monoid is partially ordered.

This definition is consistent with `measure.partial_order`. -/
instance : PartialOrder (VectorMeasure α M)
    where
  le v w := ∀ i, MeasurableSet i → v i ≤ w i
  le_refl v i hi := le_rfl
  le_trans u v w h₁ h₂ i hi := le_trans (h₁ i hi) (h₂ i hi)
  le_antisymm v w h₁ h₂ := ext fun i hi => le_antisymm (h₁ i hi) (h₂ i hi)

variable {u v w : VectorMeasure α M}

theorem le_iff : v ≤ w ↔ ∀ i, MeasurableSet i → v i ≤ w i :=
  Iff.rfl
#align measure_theory.vector_measure.le_iff MeasureTheory.VectorMeasure.le_iff

theorem le_iff' : v ≤ w ↔ ∀ i, v i ≤ w i :=
  by
  refine' ⟨fun h i => _, fun h i hi => h i⟩
  by_cases hi : MeasurableSet i
  · exact h i hi
  · rw [v.not_measurable hi, w.not_measurable hi]
#align measure_theory.vector_measure.le_iff' MeasureTheory.VectorMeasure.le_iff'

end

-- mathport name: vector_measure.restrict
scoped[MeasureTheory]
  notation:50 v " ≤[" i:50 "] " w:50 =>
    MeasureTheory.VectorMeasure.restrict v i ≤ MeasureTheory.VectorMeasure.restrict w i

section

variable {M : Type _} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]

variable (v w : VectorMeasure α M)

theorem restrict_le_restrict_iff {i : Set α} (hi : MeasurableSet i) :
    v ≤[i] w ↔ ∀ ⦃j⦄, MeasurableSet j → j ⊆ i → v j ≤ w j :=
  ⟨fun h j hj₁ hj₂ => restrict_eq_self v hi hj₁ hj₂ ▸ restrict_eq_self w hi hj₁ hj₂ ▸ h j hj₁,
    fun h =>
    le_iff.1 fun j hj =>
      (restrict_apply v hi hj).symm ▸
        (restrict_apply w hi hj).symm ▸ h (hj.inter hi) (Set.inter_subset_right j i)⟩
#align measure_theory.vector_measure.restrict_le_restrict_iff MeasureTheory.VectorMeasure.restrict_le_restrict_iff

theorem subset_le_of_restrict_le_restrict {i : Set α} (hi : MeasurableSet i) (hi₂ : v ≤[i] w)
    {j : Set α} (hj : j ⊆ i) : v j ≤ w j :=
  by
  by_cases hj₁ : MeasurableSet j
  · exact (restrict_le_restrict_iff _ _ hi).1 hi₂ hj₁ hj
  · rw [v.not_measurable hj₁, w.not_measurable hj₁]
#align measure_theory.vector_measure.subset_le_of_restrict_le_restrict MeasureTheory.VectorMeasure.subset_le_of_restrict_le_restrict

theorem restrict_le_restrict_of_subset_le {i : Set α}
    (h : ∀ ⦃j⦄, MeasurableSet j → j ⊆ i → v j ≤ w j) : v ≤[i] w :=
  by
  by_cases hi : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi).2 h
  · rw [restrict_not_measurable v hi, restrict_not_measurable w hi]
    exact le_rfl
#align measure_theory.vector_measure.restrict_le_restrict_of_subset_le MeasureTheory.VectorMeasure.restrict_le_restrict_of_subset_le

theorem restrict_le_restrict_subset {i j : Set α} (hi₁ : MeasurableSet i) (hi₂ : v ≤[i] w)
    (hij : j ⊆ i) : v ≤[j] w :=
  restrict_le_restrict_of_subset_le v w fun k hk₁ hk₂ =>
    subset_le_of_restrict_le_restrict v w hi₁ hi₂ (Set.Subset.trans hk₂ hij)
#align measure_theory.vector_measure.restrict_le_restrict_subset MeasureTheory.VectorMeasure.restrict_le_restrict_subset

theorem le_restrict_empty : v ≤[∅] w := by
  intro j hj
  rw [restrict_empty, restrict_empty]
#align measure_theory.vector_measure.le_restrict_empty MeasureTheory.VectorMeasure.le_restrict_empty

theorem le_restrict_univ_iff_le : v ≤[univ] w ↔ v ≤ w :=
  by
  constructor
  · intro h s hs
    have := h s hs
    rwa [restrict_apply _ MeasurableSet.univ hs, inter_univ, restrict_apply _ MeasurableSet.univ hs,
      inter_univ] at this
  · intro h s hs
    rw [restrict_apply _ MeasurableSet.univ hs, inter_univ, restrict_apply _ MeasurableSet.univ hs,
      inter_univ]
    exact h s hs
#align measure_theory.vector_measure.le_restrict_univ_iff_le MeasureTheory.VectorMeasure.le_restrict_univ_iff_le

end

section

variable {M : Type _} [TopologicalSpace M] [OrderedAddCommGroup M] [TopologicalAddGroup M]

variable (v w : VectorMeasure α M)

theorem neg_le_neg {i : Set α} (hi : MeasurableSet i) (h : v ≤[i] w) : -w ≤[i] -v :=
  by
  intro j hj₁
  rw [restrict_apply _ hi hj₁, restrict_apply _ hi hj₁, neg_apply, neg_apply]
  refine' neg_le_neg _
  rw [← restrict_apply _ hi hj₁, ← restrict_apply _ hi hj₁]
  exact h j hj₁
#align measure_theory.vector_measure.neg_le_neg MeasureTheory.VectorMeasure.neg_le_neg

@[simp]
theorem neg_le_neg_iff {i : Set α} (hi : MeasurableSet i) : -w ≤[i] -v ↔ v ≤[i] w :=
  ⟨fun h => neg_neg v ▸ neg_neg w ▸ neg_le_neg _ _ hi h, fun h => neg_le_neg _ _ hi h⟩
#align measure_theory.vector_measure.neg_le_neg_iff MeasureTheory.VectorMeasure.neg_le_neg_iff

end

section

variable {M : Type _} [TopologicalSpace M] [OrderedAddCommMonoid M] [OrderClosedTopology M]

variable (v w : VectorMeasure α M) {i j : Set α}

theorem restrict_le_restrict_iUnion {f : ℕ → Set α} (hf₁ : ∀ n, MeasurableSet (f n))
    (hf₂ : ∀ n, v ≤[f n] w) : v ≤[⋃ n, f n] w :=
  by
  refine' restrict_le_restrict_of_subset_le v w fun a ha₁ ha₂ => _
  have ha₃ : (⋃ n, a ∩ disjointed f n) = a := by
    rwa [← inter_Union, iUnion_disjointed, inter_eq_left_iff_subset]
  have ha₄ : Pairwise (Disjoint on fun n => a ∩ disjointed f n) :=
    (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  rw [← ha₃, v.of_disjoint_Union_nat _ ha₄, w.of_disjoint_Union_nat _ ha₄]
  refine' tsum_le_tsum (fun n => (restrict_le_restrict_iff v w (hf₁ n)).1 (hf₂ n) _ _) _ _
  · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
  · exact Set.Subset.trans (Set.inter_subset_right _ _) (disjointed_subset _ _)
  · refine' (v.m_Union (fun n => _) _).Summable
    · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
    · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  · refine' (w.m_Union (fun n => _) _).Summable
    · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
    · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  · intro n
    exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
  · exact fun n => ha₁.inter (MeasurableSet.disjointed hf₁ n)
#align measure_theory.vector_measure.restrict_le_restrict_Union MeasureTheory.VectorMeasure.restrict_le_restrict_iUnion

theorem restrict_le_restrict_countable_iUnion [Countable β] {f : β → Set α}
    (hf₁ : ∀ b, MeasurableSet (f b)) (hf₂ : ∀ b, v ≤[f b] w) : v ≤[⋃ b, f b] w :=
  by
  cases nonempty_encodable β
  rw [← Encodable.iUnion_decode₂]
  refine' restrict_le_restrict_Union v w _ _
  · intro n
    measurability
  · intro n
    cases' Encodable.decode₂ β n with b
    · simp
    · simp [hf₂ b]
#align measure_theory.vector_measure.restrict_le_restrict_countable_Union MeasureTheory.VectorMeasure.restrict_le_restrict_countable_iUnion

theorem restrict_le_restrict_union (hi₁ : MeasurableSet i) (hi₂ : v ≤[i] w) (hj₁ : MeasurableSet j)
    (hj₂ : v ≤[j] w) : v ≤[i ∪ j] w := by
  rw [union_eq_Union]
  refine' restrict_le_restrict_countable_Union v w _ _
  · measurability
  · rintro (_ | _) <;> simpa
#align measure_theory.vector_measure.restrict_le_restrict_union MeasureTheory.VectorMeasure.restrict_le_restrict_union

end

section

variable {M : Type _} [TopologicalSpace M] [OrderedAddCommMonoid M]

variable (v w : VectorMeasure α M) {i j : Set α}

theorem nonneg_of_zero_le_restrict (hi₂ : 0 ≤[i] v) : 0 ≤ v i :=
  by
  by_cases hi₁ : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
  · rw [v.not_measurable hi₁]
#align measure_theory.vector_measure.nonneg_of_zero_le_restrict MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict

theorem nonpos_of_restrict_le_zero (hi₂ : v ≤[i] 0) : v i ≤ 0 :=
  by
  by_cases hi₁ : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
  · rw [v.not_measurable hi₁]
#align measure_theory.vector_measure.nonpos_of_restrict_le_zero MeasureTheory.VectorMeasure.nonpos_of_restrict_le_zero

theorem zero_le_restrict_not_measurable (hi : ¬MeasurableSet i) : 0 ≤[i] v :=
  by
  rw [restrict_zero, restrict_not_measurable _ hi]
  exact le_rfl
#align measure_theory.vector_measure.zero_le_restrict_not_measurable MeasureTheory.VectorMeasure.zero_le_restrict_not_measurable

theorem restrict_le_zero_of_not_measurable (hi : ¬MeasurableSet i) : v ≤[i] 0 :=
  by
  rw [restrict_zero, restrict_not_measurable _ hi]
  exact le_rfl
#align measure_theory.vector_measure.restrict_le_zero_of_not_measurable MeasureTheory.VectorMeasure.restrict_le_zero_of_not_measurable

theorem measurable_of_not_zero_le_restrict (hi : ¬0 ≤[i] v) : MeasurableSet i :=
  Not.imp_symm (zero_le_restrict_not_measurable _) hi
#align measure_theory.vector_measure.measurable_of_not_zero_le_restrict MeasureTheory.VectorMeasure.measurable_of_not_zero_le_restrict

theorem measurable_of_not_restrict_le_zero (hi : ¬v ≤[i] 0) : MeasurableSet i :=
  Not.imp_symm (restrict_le_zero_of_not_measurable _) hi
#align measure_theory.vector_measure.measurable_of_not_restrict_le_zero MeasureTheory.VectorMeasure.measurable_of_not_restrict_le_zero

theorem zero_le_restrict_subset (hi₁ : MeasurableSet i) (hij : j ⊆ i) (hi₂ : 0 ≤[i] v) : 0 ≤[j] v :=
  restrict_le_restrict_of_subset_le _ _ fun k hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)
#align measure_theory.vector_measure.zero_le_restrict_subset MeasureTheory.VectorMeasure.zero_le_restrict_subset

theorem restrict_le_zero_subset (hi₁ : MeasurableSet i) (hij : j ⊆ i) (hi₂ : v ≤[i] 0) : v ≤[j] 0 :=
  restrict_le_restrict_of_subset_le _ _ fun k hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)
#align measure_theory.vector_measure.restrict_le_zero_subset MeasureTheory.VectorMeasure.restrict_le_zero_subset

end

section

variable {M : Type _} [TopologicalSpace M] [LinearOrderedAddCommMonoid M]

variable (v w : VectorMeasure α M) {i j : Set α}

include m

theorem exists_pos_measure_of_not_restrict_le_zero (hi : ¬v ≤[i] 0) :
    ∃ j : Set α, MeasurableSet j ∧ j ⊆ i ∧ 0 < v j :=
  by
  have hi₁ : MeasurableSet i := measurable_of_not_restrict_le_zero _ hi
  rw [restrict_le_restrict_iff _ _ hi₁] at hi
  push_neg  at hi
  obtain ⟨j, hj₁, hj₂, hj⟩ := hi
  exact ⟨j, hj₁, hj₂, hj⟩
#align measure_theory.vector_measure.exists_pos_measure_of_not_restrict_le_zero MeasureTheory.VectorMeasure.exists_pos_measure_of_not_restrict_le_zero

end

section

variable {M : Type _} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]
  [CovariantClass M M (· + ·) (· ≤ ·)] [ContinuousAdd M]

include m

instance covariant_add_le :
    CovariantClass (VectorMeasure α M) (VectorMeasure α M) (· + ·) (· ≤ ·) :=
  ⟨fun u v w h i hi => add_le_add_left (h i hi) _⟩
#align measure_theory.vector_measure.covariant_add_le MeasureTheory.VectorMeasure.covariant_add_le

end

section

variable {L M N : Type _}

variable [AddCommMonoid L] [TopologicalSpace L] [AddCommMonoid M] [TopologicalSpace M]
  [AddCommMonoid N] [TopologicalSpace N]

include m

/-- A vector measure `v` is absolutely continuous with respect to a measure `μ` if for all sets
`s`, `μ s = 0`, we have `v s = 0`. -/
def AbsolutelyContinuous (v : VectorMeasure α M) (w : VectorMeasure α N) :=
  ∀ ⦃s : Set α⦄, w s = 0 → v s = 0
#align measure_theory.vector_measure.absolutely_continuous MeasureTheory.VectorMeasure.AbsolutelyContinuous

-- mathport name: vector_measure.absolutely_continuous
scoped[MeasureTheory] infixl:50 " ≪ᵥ " => MeasureTheory.VectorMeasure.AbsolutelyContinuous

open MeasureTheory

namespace AbsolutelyContinuous

variable {v : VectorMeasure α M} {w : VectorMeasure α N}

theorem mk (h : ∀ ⦃s : Set α⦄, MeasurableSet s → w s = 0 → v s = 0) : v ≪ᵥ w :=
  by
  intro s hs
  by_cases hmeas : MeasurableSet s
  · exact h hmeas hs
  · exact not_measurable v hmeas
#align measure_theory.vector_measure.absolutely_continuous.mk MeasureTheory.VectorMeasure.AbsolutelyContinuous.mk

theorem eq {w : VectorMeasure α M} (h : v = w) : v ≪ᵥ w := fun s hs => h.symm ▸ hs
#align measure_theory.vector_measure.absolutely_continuous.eq MeasureTheory.VectorMeasure.AbsolutelyContinuous.eq

@[refl]
theorem refl (v : VectorMeasure α M) : v ≪ᵥ v :=
  eq rfl
#align measure_theory.vector_measure.absolutely_continuous.refl MeasureTheory.VectorMeasure.AbsolutelyContinuous.refl

@[trans]
theorem trans {u : VectorMeasure α L} {v : VectorMeasure α M} {w : VectorMeasure α N} (huv : u ≪ᵥ v)
    (hvw : v ≪ᵥ w) : u ≪ᵥ w := fun _ hs => huv <| hvw hs
#align measure_theory.vector_measure.absolutely_continuous.trans MeasureTheory.VectorMeasure.AbsolutelyContinuous.trans

theorem zero (v : VectorMeasure α N) : (0 : VectorMeasure α M) ≪ᵥ v := fun s _ =>
  VectorMeasure.zero_apply s
#align measure_theory.vector_measure.absolutely_continuous.zero MeasureTheory.VectorMeasure.AbsolutelyContinuous.zero

theorem negLeft {M : Type _} [AddCommGroup M] [TopologicalSpace M] [TopologicalAddGroup M]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : -v ≪ᵥ w := fun s hs => by
  rw [neg_apply, h hs, neg_zero]
#align measure_theory.vector_measure.absolutely_continuous.neg_left MeasureTheory.VectorMeasure.AbsolutelyContinuous.negLeft

theorem negRight {N : Type _} [AddCommGroup N] [TopologicalSpace N] [TopologicalAddGroup N]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : v ≪ᵥ -w :=
  by
  intro s hs
  rw [neg_apply, neg_eq_zero] at hs
  exact h hs
#align measure_theory.vector_measure.absolutely_continuous.neg_right MeasureTheory.VectorMeasure.AbsolutelyContinuous.negRight

theorem add [ContinuousAdd M] {v₁ v₂ : VectorMeasure α M} {w : VectorMeasure α N} (hv₁ : v₁ ≪ᵥ w)
    (hv₂ : v₂ ≪ᵥ w) : v₁ + v₂ ≪ᵥ w := fun s hs => by rw [add_apply, hv₁ hs, hv₂ hs, zero_add]
#align measure_theory.vector_measure.absolutely_continuous.add MeasureTheory.VectorMeasure.AbsolutelyContinuous.add

theorem sub {M : Type _} [AddCommGroup M] [TopologicalSpace M] [TopologicalAddGroup M]
    {v₁ v₂ : VectorMeasure α M} {w : VectorMeasure α N} (hv₁ : v₁ ≪ᵥ w) (hv₂ : v₂ ≪ᵥ w) :
    v₁ - v₂ ≪ᵥ w := fun s hs => by rw [sub_apply, hv₁ hs, hv₂ hs, zero_sub, neg_zero]
#align measure_theory.vector_measure.absolutely_continuous.sub MeasureTheory.VectorMeasure.AbsolutelyContinuous.sub

theorem smul {R : Type _} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M] {r : R}
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : r • v ≪ᵥ w := fun s hs => by
  rw [smul_apply, h hs, smul_zero]
#align measure_theory.vector_measure.absolutely_continuous.smul MeasureTheory.VectorMeasure.AbsolutelyContinuous.smul

theorem map [MeasureSpace β] (h : v ≪ᵥ w) (f : α → β) : v.map f ≪ᵥ w.map f :=
  by
  by_cases hf : Measurable f
  · refine' mk fun s hs hws => _
    rw [map_apply _ hf hs] at hws⊢
    exact h hws
  · intro s hs
    rw [map_not_measurable v hf, zero_apply]
#align measure_theory.vector_measure.absolutely_continuous.map MeasureTheory.VectorMeasure.AbsolutelyContinuous.map

theorem ennrealToMeasure {μ : VectorMeasure α ℝ≥0∞} :
    (∀ ⦃s : Set α⦄, μ.ennrealToMeasure s = 0 → v s = 0) ↔ v ≪ᵥ μ :=
  by
  constructor <;> intro h
  · refine' mk fun s hmeas hs => h _
    rw [← hs, ennreal_to_measure_apply hmeas]
  · intro s hs
    by_cases hmeas : MeasurableSet s
    · rw [ennreal_to_measure_apply hmeas] at hs
      exact h hs
    · exact not_measurable v hmeas
#align measure_theory.vector_measure.absolutely_continuous.ennreal_to_measure MeasureTheory.VectorMeasure.AbsolutelyContinuous.ennrealToMeasure

end AbsolutelyContinuous

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » «expr ᶜ»(s)) -/
/-- Two vector measures `v` and `w` are said to be mutually singular if there exists a measurable
set `s`, such that for all `t ⊆ s`, `v t = 0` and for all `t ⊆ sᶜ`, `w t = 0`.

We note that we do not require the measurability of `t` in the definition since this makes it easier
to use. This is equivalent to the definition which requires measurability. To prove
`mutually_singular` with the measurability condition, use
`measure_theory.vector_measure.mutually_singular.mk`. -/
def MutuallySingular (v : VectorMeasure α M) (w : VectorMeasure α N) : Prop :=
  ∃ s : Set α, MeasurableSet s ∧ (∀ (t) (_ : t ⊆ s), v t = 0) ∧ ∀ (t) (_ : t ⊆ sᶜ), w t = 0
#align measure_theory.vector_measure.mutually_singular MeasureTheory.VectorMeasure.MutuallySingular

-- mathport name: vector_measure.mutually_singular
scoped[MeasureTheory] infixl:60 " ⟂ᵥ " => MeasureTheory.VectorMeasure.MutuallySingular

namespace MutuallySingular

variable {v v₁ v₂ : VectorMeasure α M} {w w₁ w₂ : VectorMeasure α N}

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » «expr ᶜ»(s)) -/
theorem mk (s : Set α) (hs : MeasurableSet s) (h₁ : ∀ (t) (_ : t ⊆ s), MeasurableSet t → v t = 0)
    (h₂ : ∀ (t) (_ : t ⊆ sᶜ), MeasurableSet t → w t = 0) : v ⟂ᵥ w :=
  by
  refine' ⟨s, hs, fun t hst => _, fun t hst => _⟩ <;> by_cases ht : MeasurableSet t
  · exact h₁ t hst ht
  · exact not_measurable v ht
  · exact h₂ t hst ht
  · exact not_measurable w ht
#align measure_theory.vector_measure.mutually_singular.mk MeasureTheory.VectorMeasure.MutuallySingular.mk

theorem symm (h : v ⟂ᵥ w) : w ⟂ᵥ v :=
  let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨sᶜ, hmeas.compl, hs₂, fun t ht => hs₁ _ (compl_compl s ▸ ht : t ⊆ s)⟩
#align measure_theory.vector_measure.mutually_singular.symm MeasureTheory.VectorMeasure.MutuallySingular.symm

theorem zeroRight : v ⟂ᵥ (0 : VectorMeasure α N) :=
  ⟨∅, MeasurableSet.empty, fun t ht => (subset_empty_iff.1 ht).symm ▸ v.Empty, fun _ _ =>
    zero_apply _⟩
#align measure_theory.vector_measure.mutually_singular.zero_right MeasureTheory.VectorMeasure.MutuallySingular.zeroRight

theorem zeroLeft : (0 : VectorMeasure α M) ⟂ᵥ w :=
  zeroRight.symm
#align measure_theory.vector_measure.mutually_singular.zero_left MeasureTheory.VectorMeasure.MutuallySingular.zeroLeft

theorem addLeft [T2Space N] [ContinuousAdd M] (h₁ : v₁ ⟂ᵥ w) (h₂ : v₂ ⟂ᵥ w) : v₁ + v₂ ⟂ᵥ w :=
  by
  obtain ⟨u, hmu, hu₁, hu₂⟩ := h₁
  obtain ⟨v, hmv, hv₁, hv₂⟩ := h₂
  refine' mk (u ∩ v) (hmu.inter hmv) (fun t ht hmt => _) fun t ht hmt => _
  · rw [add_apply, hu₁ _ (subset_inter_iff.1 ht).1, hv₁ _ (subset_inter_iff.1 ht).2, zero_add]
  · rw [compl_inter] at ht
    rw [(_ : t = uᶜ ∩ t ∪ vᶜ \ uᶜ ∩ t),
      of_union _ (hmu.compl.inter hmt) ((hmv.compl.diff hmu.compl).inter hmt), hu₂, hv₂, add_zero]
    · exact subset.trans (inter_subset_left _ _) (diff_subset _ _)
    · exact inter_subset_left _ _
    · infer_instance
    · exact disjoint_sdiff_self_right.mono (inter_subset_left _ _) (inter_subset_left _ _)
    · apply subset.antisymm <;> intro x hx
      · by_cases hxu' : x ∈ uᶜ
        · exact Or.inl ⟨hxu', hx⟩
        rcases ht hx with (hxu | hxv)
        exacts[False.elim (hxu' hxu), Or.inr ⟨⟨hxv, hxu'⟩, hx⟩]
      · rcases hx with ⟨⟩ <;> exact hx.2
#align measure_theory.vector_measure.mutually_singular.add_left MeasureTheory.VectorMeasure.MutuallySingular.addLeft

theorem addRight [T2Space M] [ContinuousAdd N] (h₁ : v ⟂ᵥ w₁) (h₂ : v ⟂ᵥ w₂) : v ⟂ᵥ w₁ + w₂ :=
  (addLeft h₁.symm h₂.symm).symm
#align measure_theory.vector_measure.mutually_singular.add_right MeasureTheory.VectorMeasure.MutuallySingular.addRight

theorem smulRight {R : Type _} [Semiring R] [DistribMulAction R N] [ContinuousConstSMul R N] (r : R)
    (h : v ⟂ᵥ w) : v ⟂ᵥ r • w :=
  let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨s, hmeas, hs₁, fun t ht => by simp only [coe_smul, Pi.smul_apply, hs₂ t ht, smul_zero]⟩
#align measure_theory.vector_measure.mutually_singular.smul_right MeasureTheory.VectorMeasure.MutuallySingular.smulRight

theorem smulLeft {R : Type _} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M] (r : R)
    (h : v ⟂ᵥ w) : r • v ⟂ᵥ w :=
  (smulRight r h.symm).symm
#align measure_theory.vector_measure.mutually_singular.smul_left MeasureTheory.VectorMeasure.MutuallySingular.smulLeft

theorem negLeft {M : Type _} [AddCommGroup M] [TopologicalSpace M] [TopologicalAddGroup M]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ⟂ᵥ w) : -v ⟂ᵥ w :=
  by
  obtain ⟨u, hmu, hu₁, hu₂⟩ := h
  refine' ⟨u, hmu, fun s hs => _, hu₂⟩
  rw [neg_apply v s, neg_eq_zero]
  exact hu₁ s hs
#align measure_theory.vector_measure.mutually_singular.neg_left MeasureTheory.VectorMeasure.MutuallySingular.negLeft

theorem negRight {N : Type _} [AddCommGroup N] [TopologicalSpace N] [TopologicalAddGroup N]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ⟂ᵥ w) : v ⟂ᵥ -w :=
  h.symm.neg_left.symm
#align measure_theory.vector_measure.mutually_singular.neg_right MeasureTheory.VectorMeasure.MutuallySingular.negRight

@[simp]
theorem neg_left_iff {M : Type _} [AddCommGroup M] [TopologicalSpace M] [TopologicalAddGroup M]
    {v : VectorMeasure α M} {w : VectorMeasure α N} : -v ⟂ᵥ w ↔ v ⟂ᵥ w :=
  ⟨fun h => neg_neg v ▸ h.neg_left, negLeft⟩
#align measure_theory.vector_measure.mutually_singular.neg_left_iff MeasureTheory.VectorMeasure.MutuallySingular.neg_left_iff

@[simp]
theorem neg_right_iff {N : Type _} [AddCommGroup N] [TopologicalSpace N] [TopologicalAddGroup N]
    {v : VectorMeasure α M} {w : VectorMeasure α N} : v ⟂ᵥ -w ↔ v ⟂ᵥ w :=
  ⟨fun h => neg_neg w ▸ h.neg_right, negRight⟩
#align measure_theory.vector_measure.mutually_singular.neg_right_iff MeasureTheory.VectorMeasure.MutuallySingular.neg_right_iff

end MutuallySingular

section Trim

omit m

/-- Restriction of a vector measure onto a sub-σ-algebra. -/
@[simps]
def trim {m n : MeasurableSpace α} (v : VectorMeasure α M) (hle : m ≤ n) : @VectorMeasure α m M _ _
    where
  measureOf' i := if measurable_set[m] i then v i else 0
  empty' := by rw [if_pos MeasurableSet.empty, v.empty]
  not_measurable' i hi := by rw [if_neg hi]
  m_Union' f hf₁ hf₂ :=
    by
    have hf₁' : ∀ k, measurable_set[n] (f k) := fun k => hle _ (hf₁ k)
    convert v.m_Union hf₁' hf₂
    · ext n
      rw [if_pos (hf₁ n)]
    · rw [if_pos (@MeasurableSet.iUnion _ _ m _ _ hf₁)]
#align measure_theory.vector_measure.trim MeasureTheory.VectorMeasure.trim

variable {n : MeasurableSpace α} {v : VectorMeasure α M}

theorem trim_eq_self : v.trim le_rfl = v := by
  ext1 i hi
  exact if_pos hi
#align measure_theory.vector_measure.trim_eq_self MeasureTheory.VectorMeasure.trim_eq_self

@[simp]
theorem zero_trim (hle : m ≤ n) : (0 : VectorMeasure α M).trim hle = 0 :=
  by
  ext1 i hi
  exact if_pos hi
#align measure_theory.vector_measure.zero_trim MeasureTheory.VectorMeasure.zero_trim

theorem trim_measurableSet_eq (hle : m ≤ n) {i : Set α} (hi : measurable_set[m] i) :
    v.trim hle i = v i :=
  if_pos hi
#align measure_theory.vector_measure.trim_measurable_set_eq MeasureTheory.VectorMeasure.trim_measurableSet_eq

theorem restrict_trim (hle : m ≤ n) {i : Set α} (hi : measurable_set[m] i) :
    @VectorMeasure.restrict α m M _ _ (v.trim hle) i = (v.restrict i).trim hle :=
  by
  ext (j hj)
  rw [restrict_apply, trim_measurable_set_eq hle hj, restrict_apply, trim_measurable_set_eq]
  all_goals measurability
#align measure_theory.vector_measure.restrict_trim MeasureTheory.VectorMeasure.restrict_trim

end Trim

end

end VectorMeasure

namespace SignedMeasure

open VectorMeasure

open MeasureTheory

include m

/-- The underlying function for `signed_measure.to_measure_of_zero_le`. -/
def toMeasureOfZeroLe' (s : SignedMeasure α) (i : Set α) (hi : 0 ≤[i] s) (j : Set α)
    (hj : MeasurableSet j) : ℝ≥0∞ :=
  @coe ℝ≥0 ℝ≥0∞ _ ⟨s.restrict i j, le_trans (by simp) (hi j hj)⟩
#align measure_theory.signed_measure.to_measure_of_zero_le' MeasureTheory.SignedMeasure.toMeasureOfZeroLe'

/-- Given a signed measure `s` and a positive measurable set `i`, `to_measure_of_zero_le`
provides the measure, mapping measurable sets `j` to `s (i ∩ j)`. -/
def toMeasureOfZeroLe (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : 0 ≤[i] s) :
    Measure α :=
  Measure.ofMeasurable (s.toMeasureOfZeroLe' i hi₂)
    (by
      simp_rw [to_measure_of_zero_le', s.restrict_apply hi₁ MeasurableSet.empty, Set.empty_inter i,
        s.empty]
      rfl)
    (by
      intro f hf₁ hf₂
      have h₁ : ∀ n, MeasurableSet (i ∩ f n) := fun n => hi₁.inter (hf₁ n)
      have h₂ : Pairwise (Disjoint on fun n : ℕ => i ∩ f n) :=
        by
        intro n m hnm
        exact ((hf₂ hnm).inf_left' i).inf_right' i
      simp only [to_measure_of_zero_le', s.restrict_apply hi₁ (MeasurableSet.iUnion hf₁),
        Set.inter_comm, Set.inter_iUnion, s.of_disjoint_Union_nat h₁ h₂, ENNReal.some_eq_coe,
        id.def]
      have h : ∀ n, 0 ≤ s (i ∩ f n) := fun n =>
        s.nonneg_of_zero_le_restrict (s.zero_le_restrict_subset hi₁ (inter_subset_left _ _) hi₂)
      rw [NNReal.coe_tsum_of_nonneg h, ENNReal.coe_tsum]
      · refine' tsum_congr fun n => _
        simp_rw [s.restrict_apply hi₁ (hf₁ n), Set.inter_comm]
      · exact (NNReal.summable_mk h).2 (s.m_Union h₁ h₂).Summable)
#align measure_theory.signed_measure.to_measure_of_zero_le MeasureTheory.SignedMeasure.toMeasureOfZeroLe

variable (s : SignedMeasure α) {i j : Set α}

theorem toMeasureOfZeroLe_apply (hi : 0 ≤[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) :
    s.toMeasureOfZeroLe i hi₁ hi j =
      @coe ℝ≥0 ℝ≥0∞ _
        ⟨s (i ∩ j),
          nonneg_of_zero_le_restrict s
            (zero_le_restrict_subset s hi₁ (Set.inter_subset_left _ _) hi)⟩ :=
  by
  simp_rw [to_measure_of_zero_le, measure.of_measurable_apply _ hj₁, to_measure_of_zero_le',
    s.restrict_apply hi₁ hj₁, Set.inter_comm]
#align measure_theory.signed_measure.to_measure_of_zero_le_apply MeasureTheory.SignedMeasure.toMeasureOfZeroLe_apply

/-- Given a signed measure `s` and a negative measurable set `i`, `to_measure_of_le_zero`
provides the measure, mapping measurable sets `j` to `-s (i ∩ j)`. -/
def toMeasureOfLeZero (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : s ≤[i] 0) :
    Measure α :=
  toMeasureOfZeroLe (-s) i hi₁ <| @neg_zero (VectorMeasure α ℝ) _ ▸ neg_le_neg _ _ hi₁ hi₂
#align measure_theory.signed_measure.to_measure_of_le_zero MeasureTheory.SignedMeasure.toMeasureOfLeZero

theorem toMeasureOfLeZero_apply (hi : s ≤[i] 0) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) :
    s.toMeasureOfLeZero i hi₁ hi j =
      @coe ℝ≥0 ℝ≥0∞ _
        ⟨-s (i ∩ j),
          neg_apply s (i ∩ j) ▸
            nonneg_of_zero_le_restrict _
              (zero_le_restrict_subset _ hi₁ (Set.inter_subset_left _ _)
                (@neg_zero (VectorMeasure α ℝ) _ ▸ neg_le_neg _ _ hi₁ hi))⟩ :=
  by
  erw [to_measure_of_zero_le_apply]
  · simp
  · assumption
#align measure_theory.signed_measure.to_measure_of_le_zero_apply MeasureTheory.SignedMeasure.toMeasureOfLeZero_apply

/-- `signed_measure.to_measure_of_zero_le` is a finite measure. -/
instance toMeasureOfZeroLe_finite (hi : 0 ≤[i] s) (hi₁ : MeasurableSet i) :
    FiniteMeasure (s.toMeasureOfZeroLe i hi₁ hi)
    where measure_univ_lt_top :=
    by
    rw [to_measure_of_zero_le_apply s hi hi₁ MeasurableSet.univ]
    exact ENNReal.coe_lt_top
#align measure_theory.signed_measure.to_measure_of_zero_le_finite MeasureTheory.SignedMeasure.toMeasureOfZeroLe_finite

/-- `signed_measure.to_measure_of_le_zero` is a finite measure. -/
instance toMeasureOfLeZero_finite (hi : s ≤[i] 0) (hi₁ : MeasurableSet i) :
    FiniteMeasure (s.toMeasureOfLeZero i hi₁ hi)
    where measure_univ_lt_top :=
    by
    rw [to_measure_of_le_zero_apply s hi hi₁ MeasurableSet.univ]
    exact ENNReal.coe_lt_top
#align measure_theory.signed_measure.to_measure_of_le_zero_finite MeasureTheory.SignedMeasure.toMeasureOfLeZero_finite

theorem toMeasureOfZeroLe_toSignedMeasure (hs : 0 ≤[univ] s) :
    (s.toMeasureOfZeroLe univ MeasurableSet.univ hs).toSignedMeasure = s :=
  by
  ext (i hi)
  simp [measure.to_signed_measure_apply_measurable hi, to_measure_of_zero_le_apply _ _ _ hi]
#align measure_theory.signed_measure.to_measure_of_zero_le_to_signed_measure MeasureTheory.SignedMeasure.toMeasureOfZeroLe_toSignedMeasure

theorem toMeasureOfLeZero_toSignedMeasure (hs : s ≤[univ] 0) :
    (s.toMeasureOfLeZero univ MeasurableSet.univ hs).toSignedMeasure = -s :=
  by
  ext (i hi)
  simp [measure.to_signed_measure_apply_measurable hi, to_measure_of_le_zero_apply _ _ _ hi]
#align measure_theory.signed_measure.to_measure_of_le_zero_to_signed_measure MeasureTheory.SignedMeasure.toMeasureOfLeZero_toSignedMeasure

end SignedMeasure

namespace Measure

open VectorMeasure

variable (μ : Measure α) [FiniteMeasure μ]

theorem zero_le_toSignedMeasure : 0 ≤ μ.toSignedMeasure :=
  by
  rw [← le_restrict_univ_iff_le]
  refine' restrict_le_restrict_of_subset_le _ _ fun j hj₁ _ => _
  simp only [measure.to_signed_measure_apply_measurable hj₁, coe_zero, Pi.zero_apply,
    ENNReal.toReal_nonneg, vector_measure.coe_zero]
#align measure_theory.measure.zero_le_to_signed_measure MeasureTheory.Measure.zero_le_toSignedMeasure

theorem toSignedMeasure_toMeasureOfZeroLe :
    μ.toSignedMeasure.toMeasureOfZeroLe univ MeasurableSet.univ
        ((le_restrict_univ_iff_le _ _).2 (zero_le_toSignedMeasure μ)) =
      μ :=
  by
  refine' measure.ext fun i hi => _
  lift μ i to ℝ≥0 using (measure_lt_top _ _).Ne with m hm
  simp [signed_measure.to_measure_of_zero_le_apply _ _ _ hi,
    measure.to_signed_measure_apply_measurable hi, ← hm]
#align measure_theory.measure.to_signed_measure_to_measure_of_zero_le MeasureTheory.Measure.toSignedMeasure_toMeasureOfZeroLe

end Measure

end MeasureTheory

