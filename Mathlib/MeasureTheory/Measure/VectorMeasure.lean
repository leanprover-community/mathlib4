/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.Complex.Basic

#align_import measure_theory.measure.vector_measure from "leanprover-community/mathlib"@"70a4f2197832bceab57d7f41379b2592d1110570"

/-!

# Vector valued measures

This file defines vector valued measures, which are σ-additive functions from a set to an add monoid
`M` such that it maps the empty set and non-measurable sets to zero. In the case
that `M = ℝ`, we called the vector measure a signed measure and write `SignedMeasure α`.
Similarly, when `M = ℂ`, we call the measure a complex measure and write `ComplexMeasure α`.

## Main definitions

* `MeasureTheory.VectorMeasure` is a vector valued, σ-additive function that maps the empty
  and non-measurable set to zero.
* `MeasureTheory.VectorMeasure.map` is the pushforward of a vector measure along a function.
* `MeasureTheory.VectorMeasure.restrict` is the restriction of a vector measure on some set.

## Notation

* `v ≤[i] w` means that the vector measure `v` restricted on the set `i` is less than or equal
  to the vector measure `w` restricted on `i`, i.e. `v.restrict i ≤ w.restrict i`.

## Implementation notes

We require all non-measurable sets to be mapped to zero in order for the extensionality lemma
to only compare the underlying functions for measurable sets.

We use `HasSum` instead of `tsum` in the definition of vector measures in comparison to `Measure`
since this provides summability.

## Tags

vector measure, signed measure, complex measure
-/


noncomputable section

open Classical BigOperators NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α β : Type*} {m : MeasurableSpace α}

/-- A vector measure on a measurable space `α` is a σ-additive `M`-valued function (for some `M`
an add monoid) such that the empty set and non-measurable sets are mapped to zero. -/
structure VectorMeasure (α : Type*) [MeasurableSpace α] (M : Type*) [AddCommMonoid M]
  [TopologicalSpace M] where
  measureOf' : Set α → M
  empty' : measureOf' ∅ = 0
  not_measurable' ⦃i : Set α⦄ : ¬MeasurableSet i → measureOf' i = 0
  m_iUnion' ⦃f : ℕ → Set α⦄ : (∀ i, MeasurableSet (f i)) → Pairwise (Disjoint on f) →
    HasSum (fun i => measureOf' (f i)) (measureOf' (⋃ i, f i))
#align measure_theory.vector_measure MeasureTheory.VectorMeasure
#align measure_theory.vector_measure.measure_of' MeasureTheory.VectorMeasure.measureOf'
#align measure_theory.vector_measure.empty' MeasureTheory.VectorMeasure.empty'
#align measure_theory.vector_measure.not_measurable' MeasureTheory.VectorMeasure.not_measurable'
#align measure_theory.vector_measure.m_Union' MeasureTheory.VectorMeasure.m_iUnion'

/-- A `SignedMeasure` is an `ℝ`-vector measure. -/
abbrev SignedMeasure (α : Type*) [MeasurableSpace α] :=
  VectorMeasure α ℝ
#align measure_theory.signed_measure MeasureTheory.SignedMeasure

/-- A `ComplexMeasure` is a `ℂ`-vector measure. -/
abbrev ComplexMeasure (α : Type*) [MeasurableSpace α] :=
  VectorMeasure α ℂ
#align measure_theory.complex_measure MeasureTheory.ComplexMeasure

open Set MeasureTheory

namespace VectorMeasure

section

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

attribute [coe] VectorMeasure.measureOf'

instance instCoeFun : CoeFun (VectorMeasure α M) fun _ => Set α → M :=
  ⟨VectorMeasure.measureOf'⟩
#align measure_theory.vector_measure.has_coe_to_fun MeasureTheory.VectorMeasure.instCoeFun

initialize_simps_projections VectorMeasure (measureOf' → apply)

#noalign measure_theory.vector_measure.measure_of_eq_coe

@[simp]
theorem empty (v : VectorMeasure α M) : v ∅ = 0 :=
  v.empty'
#align measure_theory.vector_measure.empty MeasureTheory.VectorMeasure.empty

theorem not_measurable (v : VectorMeasure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0 :=
  v.not_measurable' hi
#align measure_theory.vector_measure.not_measurable MeasureTheory.VectorMeasure.not_measurable

theorem m_iUnion (v : VectorMeasure α M) {f : ℕ → Set α} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) : HasSum (fun i => v (f i)) (v (⋃ i, f i)) :=
  v.m_iUnion' hf₁ hf₂
#align measure_theory.vector_measure.m_Union MeasureTheory.VectorMeasure.m_iUnion

theorem of_disjoint_iUnion_nat [T2Space M] (v : VectorMeasure α M) {f : ℕ → Set α}
    (hf₁ : ∀ i, MeasurableSet (f i)) (hf₂ : Pairwise (Disjoint on f)) :
    v (⋃ i, f i) = ∑' i, v (f i) :=
  (v.m_iUnion hf₁ hf₂).tsum_eq.symm
#align measure_theory.vector_measure.of_disjoint_Union_nat MeasureTheory.VectorMeasure.of_disjoint_iUnion_nat

theorem coe_injective : @Function.Injective (VectorMeasure α M) (Set α → M) (⇑) := fun v w h => by
  cases v
  -- ⊢ { measureOf' := measureOf'✝, empty' := empty'✝, not_measurable' := not_measu …
  cases w
  -- ⊢ { measureOf' := measureOf'✝¹, empty' := empty'✝¹, not_measurable' := not_mea …
  congr
  -- 🎉 no goals
#align measure_theory.vector_measure.coe_injective MeasureTheory.VectorMeasure.coe_injective

theorem ext_iff' (v w : VectorMeasure α M) : v = w ↔ ∀ i : Set α, v i = w i := by
  rw [← coe_injective.eq_iff, Function.funext_iff]
  -- 🎉 no goals
#align measure_theory.vector_measure.ext_iff' MeasureTheory.VectorMeasure.ext_iff'

theorem ext_iff (v w : VectorMeasure α M) : v = w ↔ ∀ i : Set α, MeasurableSet i → v i = w i := by
  constructor
  -- ⊢ v = w → ∀ (i : Set α), MeasurableSet i → ↑v i = ↑w i
  · rintro rfl _ _
    -- ⊢ ↑v i✝ = ↑v i✝
    rfl
    -- 🎉 no goals
  · rw [ext_iff']
    -- ⊢ (∀ (i : Set α), MeasurableSet i → ↑v i = ↑w i) → ∀ (i : Set α), ↑v i = ↑w i
    intro h i
    -- ⊢ ↑v i = ↑w i
    by_cases hi : MeasurableSet i
    -- ⊢ ↑v i = ↑w i
    · exact h i hi
      -- 🎉 no goals
    · simp_rw [not_measurable _ hi]
      -- 🎉 no goals
#align measure_theory.vector_measure.ext_iff MeasureTheory.VectorMeasure.ext_iff

@[ext]
theorem ext {s t : VectorMeasure α M} (h : ∀ i : Set α, MeasurableSet i → s i = t i) : s = t :=
  (ext_iff s t).2 h
#align measure_theory.vector_measure.ext MeasureTheory.VectorMeasure.ext

variable [T2Space M] {v : VectorMeasure α M} {f : ℕ → Set α}

theorem hasSum_of_disjoint_iUnion [Countable β] {f : β → Set α} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) : HasSum (fun i => v (f i)) (v (⋃ i, f i)) := by
  cases nonempty_encodable β
  -- ⊢ HasSum (fun i => ↑v (f i)) (↑v (⋃ (i : β), f i))
  set g := fun i : ℕ => ⋃ (b : β) (_ : b ∈ Encodable.decode₂ β i), f b with hg
  -- ⊢ HasSum (fun i => ↑v (f i)) (↑v (⋃ (i : β), f i))
  have hg₁ : ∀ i, MeasurableSet (g i) :=
    fun _ => MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _ => hf₁ b
  have hg₂ : Pairwise (Disjoint on g) := Encodable.iUnion_decode₂_disjoint_on hf₂
  -- ⊢ HasSum (fun i => ↑v (f i)) (↑v (⋃ (i : β), f i))
  have := v.of_disjoint_iUnion_nat hg₁ hg₂
  -- ⊢ HasSum (fun i => ↑v (f i)) (↑v (⋃ (i : β), f i))
  rw [hg, Encodable.iUnion_decode₂] at this
  -- ⊢ HasSum (fun i => ↑v (f i)) (↑v (⋃ (i : β), f i))
  have hg₃ : (fun i : β => v (f i)) = fun i => v (g (Encodable.encode i)) := by
    ext x
    rw [hg]
    simp only
    congr
    ext y
    simp only [exists_prop, Set.mem_iUnion, Option.mem_def]
    constructor
    · intro hy
      refine' ⟨x, (Encodable.decode₂_is_partial_inv _ _).2 rfl, hy⟩
    · rintro ⟨b, hb₁, hb₂⟩
      rw [Encodable.decode₂_is_partial_inv _ _] at hb₁
      rwa [← Encodable.encode_injective hb₁]
  rw [Summable.hasSum_iff, this, ← tsum_iUnion_decode₂]
  -- ⊢ ↑v ∅ = 0
  · exact v.empty
    -- 🎉 no goals
  · rw [hg₃]
    -- ⊢ Summable fun i => ↑v (g (Encodable.encode i))
    change Summable ((fun i => v (g i)) ∘ Encodable.encode)
    -- ⊢ Summable ((fun i => ↑v (g i)) ∘ Encodable.encode)
    rw [Function.Injective.summable_iff Encodable.encode_injective]
    -- ⊢ Summable fun i => ↑v (g i)
    · exact (v.m_iUnion hg₁ hg₂).summable
      -- 🎉 no goals
    · intro x hx
      -- ⊢ ↑v (g x) = 0
      convert v.empty
      -- ⊢ g x = ∅
      simp only [Set.iUnion_eq_empty, Option.mem_def, not_exists, Set.mem_range] at hx ⊢
      -- ⊢ ∀ (i : β), Encodable.decode₂ β x = Option.some i → f i = ∅
      intro i hi
      -- ⊢ f i = ∅
      exact False.elim ((hx i) ((Encodable.decode₂_is_partial_inv _ _).1 hi))
      -- 🎉 no goals
#align measure_theory.vector_measure.has_sum_of_disjoint_Union MeasureTheory.VectorMeasure.hasSum_of_disjoint_iUnion

theorem of_disjoint_iUnion [Countable β] {f : β → Set α} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) : v (⋃ i, f i) = ∑' i, v (f i) :=
  (hasSum_of_disjoint_iUnion hf₁ hf₂).tsum_eq.symm
#align measure_theory.vector_measure.of_disjoint_Union MeasureTheory.VectorMeasure.of_disjoint_iUnion

theorem of_union {A B : Set α} (h : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    v (A ∪ B) = v A + v B := by
  rw [Set.union_eq_iUnion, of_disjoint_iUnion, tsum_fintype, Fintype.sum_bool, cond, cond]
  -- ⊢ ∀ (i : Bool), MeasurableSet (bif i then A else B)
  exacts [fun b => Bool.casesOn b hB hA, pairwise_disjoint_on_bool.2 h]
  -- 🎉 no goals
#align measure_theory.vector_measure.of_union MeasureTheory.VectorMeasure.of_union

theorem of_add_of_diff {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A ⊆ B) :
    v A + v (B \ A) = v B := by
  rw [← of_union (@Set.disjoint_sdiff_right _ A B) hA (hB.diff hA), Set.union_diff_cancel h]
  -- 🎉 no goals
#align measure_theory.vector_measure.of_add_of_diff MeasureTheory.VectorMeasure.of_add_of_diff

theorem of_diff {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    {v : VectorMeasure α M} {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : A ⊆ B) : v (B \ A) = v B - v A := by
  rw [← of_add_of_diff hA hB h, add_sub_cancel']
  -- 🎉 no goals
#align measure_theory.vector_measure.of_diff MeasureTheory.VectorMeasure.of_diff

theorem of_diff_of_diff_eq_zero {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h' : v (B \ A) = 0) : v (A \ B) + v B = v A := by
  symm
  -- ⊢ ↑v A = ↑v (A \ B) + ↑v B
  calc
    v A = v (A \ B ∪ A ∩ B) := by simp only [Set.diff_union_inter]
    _ = v (A \ B) + v (A ∩ B) := by
      rw [of_union]
      · rw [disjoint_comm]
        exact Set.disjoint_of_subset_left (A.inter_subset_right B) disjoint_sdiff_self_right
      · exact hA.diff hB
      · exact hA.inter hB
    _ = v (A \ B) + v (A ∩ B ∪ B \ A) := by
      rw [of_union, h', add_zero]
      · exact Set.disjoint_of_subset_left (A.inter_subset_left B) disjoint_sdiff_self_right
      · exact hA.inter hB
      · exact hB.diff hA
    _ = v (A \ B) + v B := by rw [Set.union_comm, Set.inter_comm, Set.diff_union_inter]
#align measure_theory.vector_measure.of_diff_of_diff_eq_zero MeasureTheory.VectorMeasure.of_diff_of_diff_eq_zero

theorem of_iUnion_nonneg {M : Type*} [TopologicalSpace M] [OrderedAddCommMonoid M]
    [OrderClosedTopology M] {v : VectorMeasure α M} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) (hf₃ : ∀ i, 0 ≤ v (f i)) : 0 ≤ v (⋃ i, f i) :=
  (v.of_disjoint_iUnion_nat hf₁ hf₂).symm ▸ tsum_nonneg hf₃
#align measure_theory.vector_measure.of_Union_nonneg MeasureTheory.VectorMeasure.of_iUnion_nonneg

theorem of_iUnion_nonpos {M : Type*} [TopologicalSpace M] [OrderedAddCommMonoid M]
    [OrderClosedTopology M] {v : VectorMeasure α M} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) (hf₃ : ∀ i, v (f i) ≤ 0) : v (⋃ i, f i) ≤ 0 :=
  (v.of_disjoint_iUnion_nat hf₁ hf₂).symm ▸ tsum_nonpos hf₃
#align measure_theory.vector_measure.of_Union_nonpos MeasureTheory.VectorMeasure.of_iUnion_nonpos

theorem of_nonneg_disjoint_union_eq_zero {s : SignedMeasure α} {A B : Set α} (h : Disjoint A B)
    (hA₁ : MeasurableSet A) (hB₁ : MeasurableSet B) (hA₂ : 0 ≤ s A) (hB₂ : 0 ≤ s B)
    (hAB : s (A ∪ B) = 0) : s A = 0 := by
  rw [of_union h hA₁ hB₁] at hAB
  -- ⊢ ↑s A = 0
  linarith
  -- 🎉 no goals
#align measure_theory.vector_measure.of_nonneg_disjoint_union_eq_zero MeasureTheory.VectorMeasure.of_nonneg_disjoint_union_eq_zero

theorem of_nonpos_disjoint_union_eq_zero {s : SignedMeasure α} {A B : Set α} (h : Disjoint A B)
    (hA₁ : MeasurableSet A) (hB₁ : MeasurableSet B) (hA₂ : s A ≤ 0) (hB₂ : s B ≤ 0)
    (hAB : s (A ∪ B) = 0) : s A = 0 := by
  rw [of_union h hA₁ hB₁] at hAB
  -- ⊢ ↑s A = 0
  linarith
  -- 🎉 no goals
#align measure_theory.vector_measure.of_nonpos_disjoint_union_eq_zero MeasureTheory.VectorMeasure.of_nonpos_disjoint_union_eq_zero

end

section SMul

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

variable {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

/-- Given a real number `r` and a signed measure `s`, `smul r s` is the signed
measure corresponding to the function `r • s`. -/
def smul (r : R) (v : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := r • ⇑v
  empty' := by rw [Pi.smul_apply, empty, smul_zero]
               -- 🎉 no goals
  not_measurable' _ hi := by rw [Pi.smul_apply, v.not_measurable hi, smul_zero]
                             -- 🎉 no goals
  m_iUnion' _ hf₁ hf₂ := by exact HasSum.const_smul _ (v.m_iUnion hf₁ hf₂)
                            -- 🎉 no goals
#align measure_theory.vector_measure.smul MeasureTheory.VectorMeasure.smul

instance instSMul : SMul R (VectorMeasure α M) :=
  ⟨smul⟩
#align measure_theory.vector_measure.has_smul MeasureTheory.VectorMeasure.instSMul

@[simp]
theorem coe_smul (r : R) (v : VectorMeasure α M) : ⇑(r • v) = r • ⇑v := rfl
#align measure_theory.vector_measure.coe_smul MeasureTheory.VectorMeasure.coe_smul

theorem smul_apply (r : R) (v : VectorMeasure α M) (i : Set α) : (r • v) i = r • v i := rfl
#align measure_theory.vector_measure.smul_apply MeasureTheory.VectorMeasure.smul_apply

end SMul

section AddCommMonoid

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

instance instZero : Zero (VectorMeasure α M) :=
  ⟨⟨0, rfl, fun _ _ => rfl, fun _ _ _ => hasSum_zero⟩⟩
#align measure_theory.vector_measure.has_zero MeasureTheory.VectorMeasure.instZero

instance instInhabited : Inhabited (VectorMeasure α M) :=
  ⟨0⟩
#align measure_theory.vector_measure.inhabited MeasureTheory.VectorMeasure.instInhabited

@[simp]
theorem coe_zero : ⇑(0 : VectorMeasure α M) = 0 := rfl
#align measure_theory.vector_measure.coe_zero MeasureTheory.VectorMeasure.coe_zero

theorem zero_apply (i : Set α) : (0 : VectorMeasure α M) i = 0 := rfl
#align measure_theory.vector_measure.zero_apply MeasureTheory.VectorMeasure.zero_apply

variable [ContinuousAdd M]

/-- The sum of two vector measure is a vector measure. -/
def add (v w : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := v + w
  empty' := by simp
               -- 🎉 no goals
  not_measurable' _ hi := by rw [Pi.add_apply, v.not_measurable hi, w.not_measurable hi, add_zero]
                             -- 🎉 no goals
  m_iUnion' f hf₁ hf₂ := HasSum.add (v.m_iUnion hf₁ hf₂) (w.m_iUnion hf₁ hf₂)
#align measure_theory.vector_measure.add MeasureTheory.VectorMeasure.add

instance instAdd : Add (VectorMeasure α M) :=
  ⟨add⟩
#align measure_theory.vector_measure.has_add MeasureTheory.VectorMeasure.instAdd

@[simp]
theorem coe_add (v w : VectorMeasure α M) : ⇑(v + w) = v + w := rfl
#align measure_theory.vector_measure.coe_add MeasureTheory.VectorMeasure.coe_add

theorem add_apply (v w : VectorMeasure α M) (i : Set α) : (v + w) i = v i + w i := rfl
#align measure_theory.vector_measure.add_apply MeasureTheory.VectorMeasure.add_apply

instance instAddCommMonoid : AddCommMonoid (VectorMeasure α M) :=
  Function.Injective.addCommMonoid _ coe_injective coe_zero coe_add fun _ _ => coe_smul _ _
#align measure_theory.vector_measure.add_comm_monoid MeasureTheory.VectorMeasure.instAddCommMonoid

/-- `(⇑)` is an `AddMonoidHom`. -/
@[simps]
def coeFnAddMonoidHom : VectorMeasure α M →+ Set α → M where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add
#align measure_theory.vector_measure.coe_fn_add_monoid_hom MeasureTheory.VectorMeasure.coeFnAddMonoidHom

end AddCommMonoid

section AddCommGroup

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [TopologicalAddGroup M]

/-- The negative of a vector measure is a vector measure. -/
def neg (v : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := -v
  empty' := by simp
               -- 🎉 no goals
  not_measurable' _ hi := by rw [Pi.neg_apply, neg_eq_zero, v.not_measurable hi]
                             -- 🎉 no goals
  m_iUnion' f hf₁ hf₂ := HasSum.neg <| v.m_iUnion hf₁ hf₂
#align measure_theory.vector_measure.neg MeasureTheory.VectorMeasure.neg

instance instNeg : Neg (VectorMeasure α M) :=
  ⟨neg⟩
#align measure_theory.vector_measure.has_neg MeasureTheory.VectorMeasure.instNeg

@[simp]
theorem coe_neg (v : VectorMeasure α M) : ⇑(-v) = -v := rfl
#align measure_theory.vector_measure.coe_neg MeasureTheory.VectorMeasure.coe_neg

theorem neg_apply (v : VectorMeasure α M) (i : Set α) : (-v) i = -v i := rfl
#align measure_theory.vector_measure.neg_apply MeasureTheory.VectorMeasure.neg_apply

/-- The difference of two vector measure is a vector measure. -/
def sub (v w : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := v - w
  empty' := by simp
               -- 🎉 no goals
  not_measurable' _ hi := by rw [Pi.sub_apply, v.not_measurable hi, w.not_measurable hi, sub_zero]
                             -- 🎉 no goals
  m_iUnion' f hf₁ hf₂ := HasSum.sub (v.m_iUnion hf₁ hf₂) (w.m_iUnion hf₁ hf₂)
#align measure_theory.vector_measure.sub MeasureTheory.VectorMeasure.sub

instance instSub : Sub (VectorMeasure α M) :=
  ⟨sub⟩
#align measure_theory.vector_measure.has_sub MeasureTheory.VectorMeasure.instSub

@[simp]
theorem coe_sub (v w : VectorMeasure α M) : ⇑(v - w) = v - w := rfl
#align measure_theory.vector_measure.coe_sub MeasureTheory.VectorMeasure.coe_sub

theorem sub_apply (v w : VectorMeasure α M) (i : Set α) : (v - w) i = v i - w i := rfl
#align measure_theory.vector_measure.sub_apply MeasureTheory.VectorMeasure.sub_apply

instance instAddCommGroup : AddCommGroup (VectorMeasure α M) :=
  Function.Injective.addCommGroup _ coe_injective coe_zero coe_add coe_neg coe_sub
    (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _
#align measure_theory.vector_measure.add_comm_group MeasureTheory.VectorMeasure.instAddCommGroup

end AddCommGroup

section DistribMulAction

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

variable {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

instance instDistribMulAction [ContinuousAdd M] : DistribMulAction R (VectorMeasure α M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul
#align measure_theory.vector_measure.distrib_mul_action MeasureTheory.VectorMeasure.instDistribMulAction

end DistribMulAction

section Module

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

variable {R : Type*} [Semiring R] [Module R M] [ContinuousConstSMul R M]

instance instModule [ContinuousAdd M] : Module R (VectorMeasure α M) :=
  Function.Injective.module R coeFnAddMonoidHom coe_injective coe_smul
#align measure_theory.vector_measure.module MeasureTheory.VectorMeasure.instModule

end Module

end VectorMeasure

namespace Measure

/-- A finite measure coerced into a real function is a signed measure. -/
@[simps]
def toSignedMeasure (μ : Measure α) [hμ : IsFiniteMeasure μ] : SignedMeasure α where
  measureOf' := fun i : Set α => if MeasurableSet i then (μ.measureOf i).toReal else 0
  empty' := by simp [μ.empty]
               -- 🎉 no goals
  not_measurable' _ hi := if_neg hi
  m_iUnion' f hf₁ hf₂ := by
    simp only
    -- ⊢ HasSum (fun i => if MeasurableSet (f i) then ENNReal.toReal (↑↑μ (f i)) else …
    rw [μ.m_iUnion hf₁ hf₂, ENNReal.tsum_toReal_eq, if_pos (MeasurableSet.iUnion hf₁),
      Summable.hasSum_iff]
    · congr
      -- ⊢ (fun b => if MeasurableSet (f b) then ENNReal.toReal (↑↑μ (f b)) else 0) = f …
      ext n
      -- ⊢ (if MeasurableSet (f n) then ENNReal.toReal (↑↑μ (f n)) else 0) = ENNReal.to …
      rw [if_pos (hf₁ n)]
      -- 🎉 no goals
    · refine' @summable_of_nonneg_of_le _ (ENNReal.toReal ∘ μ ∘ f) _ _ _ _
      · intro
        -- ⊢ 0 ≤ if MeasurableSet (f b✝) then ENNReal.toReal (↑↑μ (f b✝)) else 0
        split_ifs
        -- ⊢ 0 ≤ ENNReal.toReal (↑↑μ (f b✝))
        exacts [ENNReal.toReal_nonneg, le_rfl]
        -- 🎉 no goals
      · intro
        -- ⊢ (if MeasurableSet (f b✝) then ENNReal.toReal (↑↑μ (f b✝)) else 0) ≤ (ENNReal …
        split_ifs
        -- ⊢ ENNReal.toReal (↑↑μ (f b✝)) ≤ (ENNReal.toReal ∘ ↑↑μ ∘ f) b✝
        exacts [le_rfl, ENNReal.toReal_nonneg]
        -- 🎉 no goals
      exact summable_measure_toReal hf₁ hf₂
      -- 🎉 no goals
    · intro a ha
      -- ⊢ False
      apply ne_of_lt hμ.measure_univ_lt_top
      -- ⊢ ↑↑μ univ = ⊤
      rw [eq_top_iff, ← ha]
      -- ⊢ ↑↑μ (f a) ≤ ↑↑μ univ
      exact measure_mono (Set.subset_univ _)
      -- 🎉 no goals
#align measure_theory.measure.to_signed_measure MeasureTheory.Measure.toSignedMeasure

theorem toSignedMeasure_apply_measurable {μ : Measure α} [IsFiniteMeasure μ] {i : Set α}
    (hi : MeasurableSet i) : μ.toSignedMeasure i = (μ i).toReal :=
  if_pos hi
#align measure_theory.measure.to_signed_measure_apply_measurable MeasureTheory.Measure.toSignedMeasure_apply_measurable

-- Without this lemma, `singularPart_neg` in `MeasureTheory.Decomposition.Lebesgue` is
-- extremely slow
theorem toSignedMeasure_congr {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ = ν) : μ.toSignedMeasure = ν.toSignedMeasure := by
  congr
  -- 🎉 no goals
#align measure_theory.measure.to_signed_measure_congr MeasureTheory.Measure.toSignedMeasure_congr

theorem toSignedMeasure_eq_toSignedMeasure_iff {μ ν : Measure α} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : μ.toSignedMeasure = ν.toSignedMeasure ↔ μ = ν := by
  refine' ⟨fun h => _, fun h => _⟩
  -- ⊢ μ = ν
  · ext1 i hi
    -- ⊢ ↑↑μ i = ↑↑ν i
    have : μ.toSignedMeasure i = ν.toSignedMeasure i := by rw [h]
    -- ⊢ ↑↑μ i = ↑↑ν i
    rwa [toSignedMeasure_apply_measurable hi, toSignedMeasure_apply_measurable hi,
        ENNReal.toReal_eq_toReal] at this
      <;> exact measure_ne_top _ _
          -- 🎉 no goals
          -- 🎉 no goals
  · congr
    -- 🎉 no goals
#align measure_theory.measure.to_signed_measure_eq_to_signed_measure_iff MeasureTheory.Measure.toSignedMeasure_eq_toSignedMeasure_iff

@[simp]
theorem toSignedMeasure_zero : (0 : Measure α).toSignedMeasure = 0 := by
  ext i
  -- ⊢ ↑(toSignedMeasure 0) i = ↑0 i
  simp
  -- 🎉 no goals
#align measure_theory.measure.to_signed_measure_zero MeasureTheory.Measure.toSignedMeasure_zero

@[simp]
theorem toSignedMeasure_add (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ + ν).toSignedMeasure = μ.toSignedMeasure + ν.toSignedMeasure := by
  ext i hi
  -- ⊢ ↑(toSignedMeasure (μ + ν)) i = ↑(toSignedMeasure μ + toSignedMeasure ν) i
  rw [toSignedMeasure_apply_measurable hi, add_apply,
    ENNReal.toReal_add (ne_of_lt (measure_lt_top _ _)) (ne_of_lt (measure_lt_top _ _)),
    VectorMeasure.add_apply, toSignedMeasure_apply_measurable hi,
    toSignedMeasure_apply_measurable hi]
#align measure_theory.measure.to_signed_measure_add MeasureTheory.Measure.toSignedMeasure_add

@[simp]
theorem toSignedMeasure_smul (μ : Measure α) [IsFiniteMeasure μ] (r : ℝ≥0) :
    (r • μ).toSignedMeasure = r • μ.toSignedMeasure := by
  ext i hi
  -- ⊢ ↑(toSignedMeasure (r • μ)) i = ↑(r • toSignedMeasure μ) i
  rw [toSignedMeasure_apply_measurable hi, VectorMeasure.smul_apply,
    toSignedMeasure_apply_measurable hi, coe_smul, Pi.smul_apply, ENNReal.toReal_smul]
#align measure_theory.measure.to_signed_measure_smul MeasureTheory.Measure.toSignedMeasure_smul

/-- A measure is a vector measure over `ℝ≥0∞`. -/
@[simps]
def toENNRealVectorMeasure (μ : Measure α) : VectorMeasure α ℝ≥0∞ where
  measureOf' := fun i : Set α => if MeasurableSet i then μ i else 0
  empty' := by simp [μ.empty]
               -- 🎉 no goals
  not_measurable' _ hi := if_neg hi
  m_iUnion' _ hf₁ hf₂ := by
    simp only
    -- ⊢ HasSum (fun i => if MeasurableSet (x✝ i) then ↑↑μ (x✝ i) else 0) (if Measura …
    rw [Summable.hasSum_iff ENNReal.summable, if_pos (MeasurableSet.iUnion hf₁),
      MeasureTheory.measure_iUnion hf₂ hf₁]
    exact tsum_congr fun n => if_pos (hf₁ n)
    -- 🎉 no goals
#align measure_theory.measure.to_ennreal_vector_measure MeasureTheory.Measure.toENNRealVectorMeasure

theorem toENNRealVectorMeasure_apply_measurable {μ : Measure α} {i : Set α} (hi : MeasurableSet i) :
    μ.toENNRealVectorMeasure i = μ i :=
  if_pos hi
#align measure_theory.measure.to_ennreal_vector_measure_apply_measurable MeasureTheory.Measure.toENNRealVectorMeasure_apply_measurable

@[simp]
theorem toENNRealVectorMeasure_zero : (0 : Measure α).toENNRealVectorMeasure = 0 := by
  ext i
  -- ⊢ ↑(toENNRealVectorMeasure 0) i = ↑0 i
  simp
  -- 🎉 no goals
#align measure_theory.measure.to_ennreal_vector_measure_zero MeasureTheory.Measure.toENNRealVectorMeasure_zero

@[simp]
theorem toENNRealVectorMeasure_add (μ ν : Measure α) :
    (μ + ν).toENNRealVectorMeasure = μ.toENNRealVectorMeasure + ν.toENNRealVectorMeasure := by
  refine' MeasureTheory.VectorMeasure.ext fun i hi => _
  -- ⊢ ↑(toENNRealVectorMeasure (μ + ν)) i = ↑(toENNRealVectorMeasure μ + toENNReal …
  rw [toENNRealVectorMeasure_apply_measurable hi, add_apply, VectorMeasure.add_apply,
    toENNRealVectorMeasure_apply_measurable hi, toENNRealVectorMeasure_apply_measurable hi]
#align measure_theory.measure.to_ennreal_vector_measure_add MeasureTheory.Measure.toENNRealVectorMeasure_add

theorem toSignedMeasure_sub_apply {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {i : Set α} (hi : MeasurableSet i) :
    (μ.toSignedMeasure - ν.toSignedMeasure) i = (μ i).toReal - (ν i).toReal := by
  rw [VectorMeasure.sub_apply, toSignedMeasure_apply_measurable hi,
    Measure.toSignedMeasure_apply_measurable hi, sub_eq_add_neg]
#align measure_theory.measure.to_signed_measure_sub_apply MeasureTheory.Measure.toSignedMeasure_sub_apply

end Measure

namespace VectorMeasure

open Measure

section

/-- A vector measure over `ℝ≥0∞` is a measure. -/
def ennrealToMeasure {_ : MeasurableSpace α} (v : VectorMeasure α ℝ≥0∞) : Measure α :=
  ofMeasurable (fun s _ => v s) v.empty fun _ hf₁ hf₂ => v.of_disjoint_iUnion_nat hf₁ hf₂
#align measure_theory.vector_measure.ennreal_to_measure MeasureTheory.VectorMeasure.ennrealToMeasure

theorem ennrealToMeasure_apply {m : MeasurableSpace α} {v : VectorMeasure α ℝ≥0∞} {s : Set α}
    (hs : MeasurableSet s) : ennrealToMeasure v s = v s := by
  rw [ennrealToMeasure, ofMeasurable_apply _ hs]
  -- 🎉 no goals
#align measure_theory.vector_measure.ennreal_to_measure_apply MeasureTheory.VectorMeasure.ennrealToMeasure_apply

/-- The equiv between `VectorMeasure α ℝ≥0∞` and `Measure α` formed by
`MeasureTheory.VectorMeasure.ennrealToMeasure` and
`MeasureTheory.Measure.toENNRealVectorMeasure`. -/
@[simps]
def equivMeasure [MeasurableSpace α] : VectorMeasure α ℝ≥0∞ ≃ Measure α where
  toFun := ennrealToMeasure
  invFun := toENNRealVectorMeasure
  left_inv _ := ext fun s hs => by
    rw [toENNRealVectorMeasure_apply_measurable hs, ennrealToMeasure_apply hs]
    -- 🎉 no goals
  right_inv _ := Measure.ext fun s hs => by
    rw [ennrealToMeasure_apply hs, toENNRealVectorMeasure_apply_measurable hs]
    -- 🎉 no goals
#align measure_theory.vector_measure.equiv_measure MeasureTheory.VectorMeasure.equivMeasure

end

section

variable [MeasurableSpace α] [MeasurableSpace β]

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

variable (v : VectorMeasure α M)

/-- The pushforward of a vector measure along a function. -/
def map (v : VectorMeasure α M) (f : α → β) : VectorMeasure β M :=
  if hf : Measurable f then
    { measureOf' := fun s => if MeasurableSet s then v (f ⁻¹' s) else 0
      empty' := by simp
                   -- 🎉 no goals
      not_measurable' := fun i hi => if_neg hi
      m_iUnion' := by
        intro g hg₁ hg₂
        -- ⊢ HasSum (fun i => (fun s => if MeasurableSet s then ↑v (f ⁻¹' s) else 0) (g i …
        simp only
        -- ⊢ HasSum (fun i => if MeasurableSet (g i) then ↑v (f ⁻¹' g i) else 0) (if Meas …
        convert v.m_iUnion (fun i => hf (hg₁ i)) fun i j hij => (hg₂ hij).preimage _
        -- ⊢ (if MeasurableSet (g x✝) then ↑v (f ⁻¹' g x✝) else 0) = ↑v (f ⁻¹' g x✝)
        · rw [if_pos (hg₁ _)]
          -- 🎉 no goals
        · rw [Set.preimage_iUnion, if_pos (MeasurableSet.iUnion hg₁)] }
          -- 🎉 no goals
  else 0
#align measure_theory.vector_measure.map MeasureTheory.VectorMeasure.map

theorem map_not_measurable {f : α → β} (hf : ¬Measurable f) : v.map f = 0 :=
  dif_neg hf
#align measure_theory.vector_measure.map_not_measurable MeasureTheory.VectorMeasure.map_not_measurable

theorem map_apply {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    v.map f s = v (f ⁻¹' s) := by
  rw [map, dif_pos hf]
  -- ⊢ ↑{ measureOf' := fun s => if MeasurableSet s then ↑v (f ⁻¹' s) else 0, empty …
  exact if_pos hs
  -- 🎉 no goals
#align measure_theory.vector_measure.map_apply MeasureTheory.VectorMeasure.map_apply

@[simp]
theorem map_id : v.map id = v :=
  ext fun i hi => by rw [map_apply v measurable_id hi, Set.preimage_id]
                     -- 🎉 no goals
#align measure_theory.vector_measure.map_id MeasureTheory.VectorMeasure.map_id

@[simp]
theorem map_zero (f : α → β) : (0 : VectorMeasure α M).map f = 0 := by
  by_cases hf : Measurable f
  -- ⊢ map 0 f = 0
  · ext i hi
    -- ⊢ ↑(map 0 f) i = ↑0 i
    rw [map_apply _ hf hi, zero_apply, zero_apply]
    -- 🎉 no goals
  · exact dif_neg hf
    -- 🎉 no goals
#align measure_theory.vector_measure.map_zero MeasureTheory.VectorMeasure.map_zero

section

variable {N : Type*} [AddCommMonoid N] [TopologicalSpace N]

/-- Given a vector measure `v` on `M` and a continuous `AddMonoidHom` `f : M → N`, `f ∘ v` is a
vector measure on `N`. -/
def mapRange (v : VectorMeasure α M) (f : M →+ N) (hf : Continuous f) : VectorMeasure α N where
  measureOf' s := f (v s)
  empty' := by simp only; rw [empty, AddMonoidHom.map_zero]
               -- ⊢ ↑f (↑v ∅) = 0
                          -- 🎉 no goals
  not_measurable' i hi := by simp only; rw [not_measurable v hi, AddMonoidHom.map_zero]
                             -- ⊢ ↑f (↑v i) = 0
                                        -- 🎉 no goals
  m_iUnion' g hg₁ hg₂ := HasSum.map (v.m_iUnion hg₁ hg₂) f hf
#align measure_theory.vector_measure.map_range MeasureTheory.VectorMeasure.mapRange

@[simp]
theorem mapRange_apply {f : M →+ N} (hf : Continuous f) {s : Set α} : v.mapRange f hf s = f (v s) :=
  rfl
#align measure_theory.vector_measure.map_range_apply MeasureTheory.VectorMeasure.mapRange_apply

@[simp]
theorem mapRange_id : v.mapRange (AddMonoidHom.id M) continuous_id = v := by
  ext
  -- ⊢ ↑(mapRange v (AddMonoidHom.id M) (_ : Continuous id)) i✝ = ↑v i✝
  rfl
  -- 🎉 no goals
#align measure_theory.vector_measure.map_range_id MeasureTheory.VectorMeasure.mapRange_id

@[simp]
theorem mapRange_zero {f : M →+ N} (hf : Continuous f) :
    mapRange (0 : VectorMeasure α M) f hf = 0 := by
  ext
  -- ⊢ ↑(mapRange 0 f hf) i✝ = ↑0 i✝
  simp
  -- 🎉 no goals
#align measure_theory.vector_measure.map_range_zero MeasureTheory.VectorMeasure.mapRange_zero

section ContinuousAdd

variable [ContinuousAdd M] [ContinuousAdd N]

@[simp]
theorem mapRange_add {v w : VectorMeasure α M} {f : M →+ N} (hf : Continuous f) :
    (v + w).mapRange f hf = v.mapRange f hf + w.mapRange f hf := by
  ext
  -- ⊢ ↑(mapRange (v + w) f hf) i✝ = ↑(mapRange v f hf + mapRange w f hf) i✝
  simp
  -- 🎉 no goals
#align measure_theory.vector_measure.map_range_add MeasureTheory.VectorMeasure.mapRange_add

/-- Given a continuous `AddMonoidHom` `f : M → N`, `mapRangeHom` is the `AddMonoidHom` mapping the
vector measure `v` on `M` to the vector measure `f ∘ v` on `N`. -/
def mapRangeHom (f : M →+ N) (hf : Continuous f) : VectorMeasure α M →+ VectorMeasure α N where
  toFun v := v.mapRange f hf
  map_zero' := mapRange_zero hf
  map_add' _ _ := mapRange_add hf
#align measure_theory.vector_measure.map_range_hom MeasureTheory.VectorMeasure.mapRangeHom

end ContinuousAdd

section Module

variable {R : Type*} [Semiring R] [Module R M] [Module R N]

variable [ContinuousAdd M] [ContinuousAdd N] [ContinuousConstSMul R M] [ContinuousConstSMul R N]

/-- Given a continuous linear map `f : M → N`, `mapRangeₗ` is the linear map mapping the
vector measure `v` on `M` to the vector measure `f ∘ v` on `N`. -/
def mapRangeₗ (f : M →ₗ[R] N) (hf : Continuous f) : VectorMeasure α M →ₗ[R] VectorMeasure α N where
  toFun v := v.mapRange f.toAddMonoidHom hf
  map_add' _ _ := mapRange_add hf
  map_smul' := by
    intros
    -- ⊢ AddHom.toFun { toFun := fun v => mapRange v (LinearMap.toAddMonoidHom f) hf, …
    ext
    -- ⊢ ↑(AddHom.toFun { toFun := fun v => mapRange v (LinearMap.toAddMonoidHom f) h …
    simp
    -- 🎉 no goals
#align measure_theory.vector_measure.map_rangeₗ MeasureTheory.VectorMeasure.mapRangeₗ

end Module

end

/-- The restriction of a vector measure on some set. -/
def restrict (v : VectorMeasure α M) (i : Set α) : VectorMeasure α M :=
  if hi : MeasurableSet i then
    { measureOf' := fun s => if MeasurableSet s then v (s ∩ i) else 0
      empty' := by simp
                   -- 🎉 no goals
      not_measurable' := fun i hi => if_neg hi
      m_iUnion' := by
        intro f hf₁ hf₂
        -- ⊢ HasSum (fun i_1 => (fun s => if MeasurableSet s then ↑v (s ∩ i) else 0) (f i …
        simp only
        -- ⊢ HasSum (fun i_1 => if MeasurableSet (f i_1) then ↑v (f i_1 ∩ i) else 0) (if  …
        convert v.m_iUnion (fun n => (hf₁ n).inter hi)
            (hf₂.mono fun i j => Disjoint.mono inf_le_left inf_le_left)
        · rw [if_pos (hf₁ _)]
          -- 🎉 no goals
        · rw [Set.iUnion_inter, if_pos (MeasurableSet.iUnion hf₁)] }
          -- 🎉 no goals
  else 0
#align measure_theory.vector_measure.restrict MeasureTheory.VectorMeasure.restrict

theorem restrict_not_measurable {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0 :=
  dif_neg hi
#align measure_theory.vector_measure.restrict_not_measurable MeasureTheory.VectorMeasure.restrict_not_measurable

theorem restrict_apply {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) :
    v.restrict i j = v (j ∩ i) := by
  rw [restrict, dif_pos hi]
  -- ⊢ ↑{ measureOf' := fun s => if MeasurableSet s then ↑v (s ∩ i) else 0, empty'  …
  exact if_pos hj
  -- 🎉 no goals
#align measure_theory.vector_measure.restrict_apply MeasureTheory.VectorMeasure.restrict_apply

theorem restrict_eq_self {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j)
    (hij : j ⊆ i) : v.restrict i j = v j := by
  rw [restrict_apply v hi hj, Set.inter_eq_left_iff_subset.2 hij]
  -- 🎉 no goals
#align measure_theory.vector_measure.restrict_eq_self MeasureTheory.VectorMeasure.restrict_eq_self

@[simp]
theorem restrict_empty : v.restrict ∅ = 0 :=
  ext fun i hi => by
    rw [restrict_apply v MeasurableSet.empty hi, Set.inter_empty, v.empty, zero_apply]
    -- 🎉 no goals
#align measure_theory.vector_measure.restrict_empty MeasureTheory.VectorMeasure.restrict_empty

@[simp]
theorem restrict_univ : v.restrict Set.univ = v :=
  ext fun i hi => by rw [restrict_apply v MeasurableSet.univ hi, Set.inter_univ]
                     -- 🎉 no goals
#align measure_theory.vector_measure.restrict_univ MeasureTheory.VectorMeasure.restrict_univ

@[simp]
theorem restrict_zero {i : Set α} : (0 : VectorMeasure α M).restrict i = 0 := by
  by_cases hi : MeasurableSet i
  -- ⊢ restrict 0 i = 0
  · ext j hj
    -- ⊢ ↑(restrict 0 i) j = ↑0 j
    rw [restrict_apply 0 hi hj]
    -- ⊢ ↑0 (j ∩ i) = ↑0 j
    rfl
    -- 🎉 no goals
  · exact dif_neg hi
    -- 🎉 no goals
#align measure_theory.vector_measure.restrict_zero MeasureTheory.VectorMeasure.restrict_zero

section ContinuousAdd

variable [ContinuousAdd M]

theorem map_add (v w : VectorMeasure α M) (f : α → β) : (v + w).map f = v.map f + w.map f := by
  by_cases hf : Measurable f
  -- ⊢ map (v + w) f = map v f + map w f
  · ext i hi
    -- ⊢ ↑(map (v + w) f) i = ↑(map v f + map w f) i
    simp [map_apply _ hf hi]
    -- 🎉 no goals
  · simp [map, dif_neg hf]
    -- 🎉 no goals
#align measure_theory.vector_measure.map_add MeasureTheory.VectorMeasure.map_add

/-- `VectorMeasure.map` as an additive monoid homomorphism. -/
@[simps]
def mapGm (f : α → β) : VectorMeasure α M →+ VectorMeasure β M where
  toFun v := v.map f
  map_zero' := map_zero f
  map_add' _ _ := map_add _ _ f
#align measure_theory.vector_measure.map_gm MeasureTheory.VectorMeasure.mapGm

theorem restrict_add (v w : VectorMeasure α M) (i : Set α) :
    (v + w).restrict i = v.restrict i + w.restrict i := by
  by_cases hi : MeasurableSet i
  -- ⊢ restrict (v + w) i = restrict v i + restrict w i
  · ext j hj
    -- ⊢ ↑(restrict (v + w) i) j = ↑(restrict v i + restrict w i) j
    simp [restrict_apply _ hi hj]
    -- 🎉 no goals
  · simp [restrict_not_measurable _ hi]
    -- 🎉 no goals
#align measure_theory.vector_measure.restrict_add MeasureTheory.VectorMeasure.restrict_add

/-- `VectorMeasure.restrict` as an additive monoid homomorphism. -/
@[simps]
def restrictGm (i : Set α) : VectorMeasure α M →+ VectorMeasure α M where
  toFun v := v.restrict i
  map_zero' := restrict_zero
  map_add' _ _ := restrict_add _ _ i
#align measure_theory.vector_measure.restrict_gm MeasureTheory.VectorMeasure.restrictGm

end ContinuousAdd

end

section

variable [MeasurableSpace β]

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

variable {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

@[simp]
theorem map_smul {v : VectorMeasure α M} {f : α → β} (c : R) : (c • v).map f = c • v.map f := by
  by_cases hf : Measurable f
  -- ⊢ map (c • v) f = c • map v f
  · ext i hi
    -- ⊢ ↑(map (c • v) f) i = ↑(c • map v f) i
    simp [map_apply _ hf hi]
    -- 🎉 no goals
  · simp only [map, dif_neg hf]
    -- ⊢ 0 = c • 0
    -- `smul_zero` does not work since we do not require `ContinuousAdd`
    ext i
    -- ⊢ ↑0 i = ↑(c • 0) i
    simp
    -- 🎉 no goals
#align measure_theory.vector_measure.map_smul MeasureTheory.VectorMeasure.map_smul

@[simp]
theorem restrict_smul {v : VectorMeasure α M} {i : Set α} (c : R) :
    (c • v).restrict i = c • v.restrict i := by
  by_cases hi : MeasurableSet i
  -- ⊢ restrict (c • v) i = c • restrict v i
  · ext j hj
    -- ⊢ ↑(restrict (c • v) i) j = ↑(c • restrict v i) j
    simp [restrict_apply _ hi hj]
    -- 🎉 no goals
  · simp only [restrict_not_measurable _ hi]
    -- ⊢ 0 = c • 0
    -- `smul_zero` does not work since we do not require `ContinuousAdd`
    ext j
    -- ⊢ ↑0 j = ↑(c • 0) j
    simp
    -- 🎉 no goals
#align measure_theory.vector_measure.restrict_smul MeasureTheory.VectorMeasure.restrict_smul

end

section

variable [MeasurableSpace β]

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

variable {R : Type*} [Semiring R] [Module R M] [ContinuousConstSMul R M] [ContinuousAdd M]

/-- `VectorMeasure.map` as a linear map. -/
@[simps]
def mapₗ (f : α → β) : VectorMeasure α M →ₗ[R] VectorMeasure β M where
  toFun v := v.map f
  map_add' _ _ := map_add _ _ f
  map_smul' _ _ := map_smul _
#align measure_theory.vector_measure.mapₗ MeasureTheory.VectorMeasure.mapₗ

/-- `VectorMeasure.restrict` as an additive monoid homomorphism. -/
@[simps]
def restrictₗ (i : Set α) : VectorMeasure α M →ₗ[R] VectorMeasure α M where
  toFun v := v.restrict i
  map_add' _ _ := restrict_add _ _ i
  map_smul' _ _ := restrict_smul _
#align measure_theory.vector_measure.restrictₗ MeasureTheory.VectorMeasure.restrictₗ

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]

/-- Vector measures over a partially ordered monoid is partially ordered.

This definition is consistent with `Measure.instPartialOrder`. -/
instance instPartialOrder : PartialOrder (VectorMeasure α M) where
  le v w := ∀ i, MeasurableSet i → v i ≤ w i
  le_refl v i _ := le_rfl
  le_trans u v w h₁ h₂ i hi := le_trans (h₁ i hi) (h₂ i hi)
  le_antisymm v w h₁ h₂ := ext fun i hi => le_antisymm (h₁ i hi) (h₂ i hi)

variable {u v w : VectorMeasure α M}

theorem le_iff : v ≤ w ↔ ∀ i, MeasurableSet i → v i ≤ w i := Iff.rfl
#align measure_theory.vector_measure.le_iff MeasureTheory.VectorMeasure.le_iff

theorem le_iff' : v ≤ w ↔ ∀ i, v i ≤ w i := by
  refine' ⟨fun h i => _, fun h i _ => h i⟩
  -- ⊢ ↑v i ≤ ↑w i
  by_cases hi : MeasurableSet i
  -- ⊢ ↑v i ≤ ↑w i
  · exact h i hi
    -- 🎉 no goals
  · rw [v.not_measurable hi, w.not_measurable hi]
    -- 🎉 no goals
#align measure_theory.vector_measure.le_iff' MeasureTheory.VectorMeasure.le_iff'

end

-- mathport name: vector_measure.restrict
set_option quotPrecheck false in -- Porting note: error message suggested to do this
scoped[MeasureTheory]
  notation:50 v " ≤[" i:50 "] " w:50 =>
    MeasureTheory.VectorMeasure.restrict v i ≤ MeasureTheory.VectorMeasure.restrict w i

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]

variable (v w : VectorMeasure α M)

theorem restrict_le_restrict_iff {i : Set α} (hi : MeasurableSet i) :
    v ≤[i] w ↔ ∀ ⦃j⦄, MeasurableSet j → j ⊆ i → v j ≤ w j :=
  ⟨fun h j hj₁ hj₂ => restrict_eq_self v hi hj₁ hj₂ ▸ restrict_eq_self w hi hj₁ hj₂ ▸ h j hj₁,
    fun h => le_iff.1 fun j hj =>
      (restrict_apply v hi hj).symm ▸ (restrict_apply w hi hj).symm ▸
      h (hj.inter hi) (Set.inter_subset_right j i)⟩
#align measure_theory.vector_measure.restrict_le_restrict_iff MeasureTheory.VectorMeasure.restrict_le_restrict_iff

theorem subset_le_of_restrict_le_restrict {i : Set α} (hi : MeasurableSet i) (hi₂ : v ≤[i] w)
    {j : Set α} (hj : j ⊆ i) : v j ≤ w j := by
  by_cases hj₁ : MeasurableSet j
  -- ⊢ ↑v j ≤ ↑w j
  · exact (restrict_le_restrict_iff _ _ hi).1 hi₂ hj₁ hj
    -- 🎉 no goals
  · rw [v.not_measurable hj₁, w.not_measurable hj₁]
    -- 🎉 no goals
#align measure_theory.vector_measure.subset_le_of_restrict_le_restrict MeasureTheory.VectorMeasure.subset_le_of_restrict_le_restrict

theorem restrict_le_restrict_of_subset_le {i : Set α}
    (h : ∀ ⦃j⦄, MeasurableSet j → j ⊆ i → v j ≤ w j) : v ≤[i] w := by
  by_cases hi : MeasurableSet i
  -- ⊢ restrict v i ≤ restrict w i
  · exact (restrict_le_restrict_iff _ _ hi).2 h
    -- 🎉 no goals
  · rw [restrict_not_measurable v hi, restrict_not_measurable w hi]
    -- 🎉 no goals
#align measure_theory.vector_measure.restrict_le_restrict_of_subset_le MeasureTheory.VectorMeasure.restrict_le_restrict_of_subset_le

theorem restrict_le_restrict_subset {i j : Set α} (hi₁ : MeasurableSet i) (hi₂ : v ≤[i] w)
    (hij : j ⊆ i) : v ≤[j] w :=
  restrict_le_restrict_of_subset_le v w fun _ _ hk₂ =>
    subset_le_of_restrict_le_restrict v w hi₁ hi₂ (Set.Subset.trans hk₂ hij)
#align measure_theory.vector_measure.restrict_le_restrict_subset MeasureTheory.VectorMeasure.restrict_le_restrict_subset

theorem le_restrict_empty : v ≤[∅] w := by
  intro j _
  -- ⊢ ↑(restrict v ∅) j ≤ ↑(restrict w ∅) j
  rw [restrict_empty, restrict_empty]
  -- 🎉 no goals
#align measure_theory.vector_measure.le_restrict_empty MeasureTheory.VectorMeasure.le_restrict_empty

theorem le_restrict_univ_iff_le : v ≤[Set.univ] w ↔ v ≤ w := by
  constructor
  -- ⊢ restrict v univ ≤ restrict w univ → v ≤ w
  · intro h s hs
    -- ⊢ ↑v s ≤ ↑w s
    have := h s hs
    -- ⊢ ↑v s ≤ ↑w s
    rwa [restrict_apply _ MeasurableSet.univ hs, Set.inter_univ,
      restrict_apply _ MeasurableSet.univ hs, Set.inter_univ] at this
  · intro h s hs
    -- ⊢ ↑(restrict v univ) s ≤ ↑(restrict w univ) s
    rw [restrict_apply _ MeasurableSet.univ hs, Set.inter_univ,
      restrict_apply _ MeasurableSet.univ hs, Set.inter_univ]
    exact h s hs
    -- 🎉 no goals
#align measure_theory.vector_measure.le_restrict_univ_iff_le MeasureTheory.VectorMeasure.le_restrict_univ_iff_le

end

section

variable {M : Type*} [TopologicalSpace M] [OrderedAddCommGroup M] [TopologicalAddGroup M]

variable (v w : VectorMeasure α M)

nonrec theorem neg_le_neg {i : Set α} (hi : MeasurableSet i) (h : v ≤[i] w) : -w ≤[i] -v := by
  intro j hj₁
  -- ⊢ ↑(restrict (-w) i) j ≤ ↑(restrict (-v) i) j
  rw [restrict_apply _ hi hj₁, restrict_apply _ hi hj₁, neg_apply, neg_apply]
  -- ⊢ -↑w (j ∩ i) ≤ -↑v (j ∩ i)
  refine' neg_le_neg _
  -- ⊢ ↑v (j ∩ i) ≤ ↑w (j ∩ i)
  rw [← restrict_apply _ hi hj₁, ← restrict_apply _ hi hj₁]
  -- ⊢ ↑(restrict v i) j ≤ ↑(restrict w i) j
  exact h j hj₁
  -- 🎉 no goals
#align measure_theory.vector_measure.neg_le_neg MeasureTheory.VectorMeasure.neg_le_neg

@[simp]
theorem neg_le_neg_iff {i : Set α} (hi : MeasurableSet i) : -w ≤[i] -v ↔ v ≤[i] w :=
  ⟨fun h => neg_neg v ▸ neg_neg w ▸ neg_le_neg _ _ hi h, fun h => neg_le_neg _ _ hi h⟩
#align measure_theory.vector_measure.neg_le_neg_iff MeasureTheory.VectorMeasure.neg_le_neg_iff

end

section

variable {M : Type*} [TopologicalSpace M] [OrderedAddCommMonoid M] [OrderClosedTopology M]

variable (v w : VectorMeasure α M) {i j : Set α}

theorem restrict_le_restrict_iUnion {f : ℕ → Set α} (hf₁ : ∀ n, MeasurableSet (f n))
    (hf₂ : ∀ n, v ≤[f n] w) : v ≤[⋃ n, f n] w := by
  refine' restrict_le_restrict_of_subset_le v w fun a ha₁ ha₂ => _
  -- ⊢ ↑v a ≤ ↑w a
  have ha₃ : ⋃ n, a ∩ disjointed f n = a := by
    rwa [← Set.inter_iUnion, iUnion_disjointed, Set.inter_eq_left_iff_subset]
  have ha₄ : Pairwise (Disjoint on fun n => a ∩ disjointed f n) :=
    (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  rw [← ha₃, v.of_disjoint_iUnion_nat _ ha₄, w.of_disjoint_iUnion_nat _ ha₄]
  refine' tsum_le_tsum (fun n => (restrict_le_restrict_iff v w (hf₁ n)).1 (hf₂ n) _ _) _ _
  · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
    -- 🎉 no goals
  · exact Set.Subset.trans (Set.inter_subset_right _ _) (disjointed_subset _ _)
    -- 🎉 no goals
  · refine' (v.m_iUnion (fun n => _) _).summable
    -- ⊢ MeasurableSet (a ∩ disjointed f n)
    · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
      -- 🎉 no goals
    · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
      -- 🎉 no goals
  · refine' (w.m_iUnion (fun n => _) _).summable
    -- ⊢ MeasurableSet (a ∩ disjointed f n)
    · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
      -- 🎉 no goals
    · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
      -- 🎉 no goals
  · intro n
    -- ⊢ MeasurableSet (a ∩ disjointed f n)
    exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
    -- 🎉 no goals
  · exact fun n => ha₁.inter (MeasurableSet.disjointed hf₁ n)
    -- 🎉 no goals
#align measure_theory.vector_measure.restrict_le_restrict_Union MeasureTheory.VectorMeasure.restrict_le_restrict_iUnion

theorem restrict_le_restrict_countable_iUnion [Countable β] {f : β → Set α}
    (hf₁ : ∀ b, MeasurableSet (f b)) (hf₂ : ∀ b, v ≤[f b] w) : v ≤[⋃ b, f b] w := by
  cases nonempty_encodable β
  -- ⊢ restrict v (⋃ (b : β), f b) ≤ restrict w (⋃ (b : β), f b)
  rw [← Encodable.iUnion_decode₂]
  -- ⊢ restrict v (⋃ (i : ℕ) (b : β) (_ : b ∈ Encodable.decode₂ β i), f b) ≤ restri …
  refine' restrict_le_restrict_iUnion v w _ _
  -- ⊢ ∀ (n : ℕ), MeasurableSet (⋃ (b : β) (_ : b ∈ Encodable.decode₂ β n), f b)
  · intro n
    -- ⊢ MeasurableSet (⋃ (b : β) (_ : b ∈ Encodable.decode₂ β n), f b)
    measurability
    -- 🎉 no goals
  · intro n
    -- ⊢ restrict v (⋃ (b : β) (_ : b ∈ Encodable.decode₂ β n), f b) ≤ restrict w (⋃  …
    cases' Encodable.decode₂ β n with b
    -- ⊢ restrict v (⋃ (b : β) (_ : b ∈ none), f b) ≤ restrict w (⋃ (b : β) (_ : b ∈  …
    · simp
      -- 🎉 no goals
    · simp [hf₂ b]
      -- 🎉 no goals
#align measure_theory.vector_measure.restrict_le_restrict_countable_Union MeasureTheory.VectorMeasure.restrict_le_restrict_countable_iUnion

theorem restrict_le_restrict_union (hi₁ : MeasurableSet i) (hi₂ : v ≤[i] w) (hj₁ : MeasurableSet j)
    (hj₂ : v ≤[j] w) : v ≤[i ∪ j] w := by
  rw [Set.union_eq_iUnion]
  -- ⊢ restrict v (⋃ (b : Bool), bif b then i else j) ≤ restrict w (⋃ (b : Bool), b …
  refine' restrict_le_restrict_countable_iUnion v w _ _
  -- ⊢ ∀ (b : Bool), MeasurableSet (bif b then i else j)
  · measurability
    -- 🎉 no goals
  · rintro (_ | _) <;> simpa
    -- ⊢ restrict v (bif false then i else j) ≤ restrict w (bif false then i else j)
                       -- 🎉 no goals
                       -- 🎉 no goals
#align measure_theory.vector_measure.restrict_le_restrict_union MeasureTheory.VectorMeasure.restrict_le_restrict_union

end

section

variable {M : Type*} [TopologicalSpace M] [OrderedAddCommMonoid M]

variable (v w : VectorMeasure α M) {i j : Set α}

theorem nonneg_of_zero_le_restrict (hi₂ : 0 ≤[i] v) : 0 ≤ v i := by
  by_cases hi₁ : MeasurableSet i
  -- ⊢ 0 ≤ ↑v i
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
    -- 🎉 no goals
  · rw [v.not_measurable hi₁]
    -- 🎉 no goals
#align measure_theory.vector_measure.nonneg_of_zero_le_restrict MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict

theorem nonpos_of_restrict_le_zero (hi₂ : v ≤[i] 0) : v i ≤ 0 := by
  by_cases hi₁ : MeasurableSet i
  -- ⊢ ↑v i ≤ 0
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
    -- 🎉 no goals
  · rw [v.not_measurable hi₁]
    -- 🎉 no goals
#align measure_theory.vector_measure.nonpos_of_restrict_le_zero MeasureTheory.VectorMeasure.nonpos_of_restrict_le_zero

theorem zero_le_restrict_not_measurable (hi : ¬MeasurableSet i) : 0 ≤[i] v := by
  rw [restrict_zero, restrict_not_measurable _ hi]
  -- 🎉 no goals
#align measure_theory.vector_measure.zero_le_restrict_not_measurable MeasureTheory.VectorMeasure.zero_le_restrict_not_measurable

theorem restrict_le_zero_of_not_measurable (hi : ¬MeasurableSet i) : v ≤[i] 0 := by
  rw [restrict_zero, restrict_not_measurable _ hi]
  -- 🎉 no goals
#align measure_theory.vector_measure.restrict_le_zero_of_not_measurable MeasureTheory.VectorMeasure.restrict_le_zero_of_not_measurable

theorem measurable_of_not_zero_le_restrict (hi : ¬0 ≤[i] v) : MeasurableSet i :=
  Not.imp_symm (zero_le_restrict_not_measurable _) hi
#align measure_theory.vector_measure.measurable_of_not_zero_le_restrict MeasureTheory.VectorMeasure.measurable_of_not_zero_le_restrict

theorem measurable_of_not_restrict_le_zero (hi : ¬v ≤[i] 0) : MeasurableSet i :=
  Not.imp_symm (restrict_le_zero_of_not_measurable _) hi
#align measure_theory.vector_measure.measurable_of_not_restrict_le_zero MeasureTheory.VectorMeasure.measurable_of_not_restrict_le_zero

theorem zero_le_restrict_subset (hi₁ : MeasurableSet i) (hij : j ⊆ i) (hi₂ : 0 ≤[i] v) : 0 ≤[j] v :=
  restrict_le_restrict_of_subset_le _ _ fun _ hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)
#align measure_theory.vector_measure.zero_le_restrict_subset MeasureTheory.VectorMeasure.zero_le_restrict_subset

theorem restrict_le_zero_subset (hi₁ : MeasurableSet i) (hij : j ⊆ i) (hi₂ : v ≤[i] 0) : v ≤[j] 0 :=
  restrict_le_restrict_of_subset_le _ _ fun _ hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)
#align measure_theory.vector_measure.restrict_le_zero_subset MeasureTheory.VectorMeasure.restrict_le_zero_subset

end

section

variable {M : Type*} [TopologicalSpace M] [LinearOrderedAddCommMonoid M]

variable (v w : VectorMeasure α M) {i j : Set α}

theorem exists_pos_measure_of_not_restrict_le_zero (hi : ¬v ≤[i] 0) :
    ∃ j : Set α, MeasurableSet j ∧ j ⊆ i ∧ 0 < v j := by
  have hi₁ : MeasurableSet i := measurable_of_not_restrict_le_zero _ hi
  -- ⊢ ∃ j, MeasurableSet j ∧ j ⊆ i ∧ 0 < ↑v j
  rw [restrict_le_restrict_iff _ _ hi₁] at hi
  -- ⊢ ∃ j, MeasurableSet j ∧ j ⊆ i ∧ 0 < ↑v j
  push_neg at hi
  -- ⊢ ∃ j, MeasurableSet j ∧ j ⊆ i ∧ 0 < ↑v j
  exact hi
  -- 🎉 no goals
#align measure_theory.vector_measure.exists_pos_measure_of_not_restrict_le_zero MeasureTheory.VectorMeasure.exists_pos_measure_of_not_restrict_le_zero

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]
  [CovariantClass M M (· + ·) (· ≤ ·)] [ContinuousAdd M]

instance covariant_add_le :
    CovariantClass (VectorMeasure α M) (VectorMeasure α M) (· + ·) (· ≤ ·) :=
  ⟨fun _ _ _ h i hi => add_le_add_left (h i hi) _⟩
#align measure_theory.vector_measure.covariant_add_le MeasureTheory.VectorMeasure.covariant_add_le

end

section

variable {L M N : Type*}

variable [AddCommMonoid L] [TopologicalSpace L] [AddCommMonoid M] [TopologicalSpace M]
  [AddCommMonoid N] [TopologicalSpace N]

/-- A vector measure `v` is absolutely continuous with respect to a measure `μ` if for all sets
`s`, `μ s = 0`, we have `v s = 0`. -/
def AbsolutelyContinuous (v : VectorMeasure α M) (w : VectorMeasure α N) :=
  ∀ ⦃s : Set α⦄, w s = 0 → v s = 0
#align measure_theory.vector_measure.absolutely_continuous MeasureTheory.VectorMeasure.AbsolutelyContinuous

-- mathport name: vector_measure.absolutely_continuous
@[inherit_doc VectorMeasure.AbsolutelyContinuous]
scoped[MeasureTheory] infixl:50 " ≪ᵥ " => MeasureTheory.VectorMeasure.AbsolutelyContinuous

open MeasureTheory

namespace AbsolutelyContinuous

variable {v : VectorMeasure α M} {w : VectorMeasure α N}

theorem mk (h : ∀ ⦃s : Set α⦄, MeasurableSet s → w s = 0 → v s = 0) : v ≪ᵥ w := by
  intro s hs
  -- ⊢ ↑v s = 0
  by_cases hmeas : MeasurableSet s
  -- ⊢ ↑v s = 0
  · exact h hmeas hs
    -- 🎉 no goals
  · exact not_measurable v hmeas
    -- 🎉 no goals
#align measure_theory.vector_measure.absolutely_continuous.mk MeasureTheory.VectorMeasure.AbsolutelyContinuous.mk

theorem eq {w : VectorMeasure α M} (h : v = w) : v ≪ᵥ w :=
  fun _ hs => h.symm ▸ hs
#align measure_theory.vector_measure.absolutely_continuous.eq MeasureTheory.VectorMeasure.AbsolutelyContinuous.eq

@[refl]
theorem refl (v : VectorMeasure α M) : v ≪ᵥ v :=
  eq rfl
#align measure_theory.vector_measure.absolutely_continuous.refl MeasureTheory.VectorMeasure.AbsolutelyContinuous.refl

@[trans]
theorem trans {u : VectorMeasure α L} {v : VectorMeasure α M} {w : VectorMeasure α N} (huv : u ≪ᵥ v)
    (hvw : v ≪ᵥ w) : u ≪ᵥ w :=
  fun _ hs => huv <| hvw hs
#align measure_theory.vector_measure.absolutely_continuous.trans MeasureTheory.VectorMeasure.AbsolutelyContinuous.trans

theorem zero (v : VectorMeasure α N) : (0 : VectorMeasure α M) ≪ᵥ v :=
  fun s _ => VectorMeasure.zero_apply s
#align measure_theory.vector_measure.absolutely_continuous.zero MeasureTheory.VectorMeasure.AbsolutelyContinuous.zero

theorem neg_left {M : Type*} [AddCommGroup M] [TopologicalSpace M] [TopologicalAddGroup M]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : -v ≪ᵥ w := by
  intro s hs
  -- ⊢ ↑(-v) s = 0
  rw [neg_apply, h hs, neg_zero]
  -- 🎉 no goals
#align measure_theory.vector_measure.absolutely_continuous.neg_left MeasureTheory.VectorMeasure.AbsolutelyContinuous.neg_left

theorem neg_right {N : Type*} [AddCommGroup N] [TopologicalSpace N] [TopologicalAddGroup N]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : v ≪ᵥ -w := by
  intro s hs
  -- ⊢ ↑v s = 0
  rw [neg_apply, neg_eq_zero] at hs
  -- ⊢ ↑v s = 0
  exact h hs
  -- 🎉 no goals
#align measure_theory.vector_measure.absolutely_continuous.neg_right MeasureTheory.VectorMeasure.AbsolutelyContinuous.neg_right

theorem add [ContinuousAdd M] {v₁ v₂ : VectorMeasure α M} {w : VectorMeasure α N} (hv₁ : v₁ ≪ᵥ w)
    (hv₂ : v₂ ≪ᵥ w) : v₁ + v₂ ≪ᵥ w := by
  intro s hs
  -- ⊢ ↑(v₁ + v₂) s = 0
  rw [add_apply, hv₁ hs, hv₂ hs, zero_add]
  -- 🎉 no goals
#align measure_theory.vector_measure.absolutely_continuous.add MeasureTheory.VectorMeasure.AbsolutelyContinuous.add

theorem sub {M : Type*} [AddCommGroup M] [TopologicalSpace M] [TopologicalAddGroup M]
    {v₁ v₂ : VectorMeasure α M} {w : VectorMeasure α N} (hv₁ : v₁ ≪ᵥ w) (hv₂ : v₂ ≪ᵥ w) :
    v₁ - v₂ ≪ᵥ w := by
  intro s hs
  -- ⊢ ↑(v₁ - v₂) s = 0
  rw [sub_apply, hv₁ hs, hv₂ hs, zero_sub, neg_zero]
  -- 🎉 no goals
#align measure_theory.vector_measure.absolutely_continuous.sub MeasureTheory.VectorMeasure.AbsolutelyContinuous.sub

theorem smul {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M] {r : R}
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : r • v ≪ᵥ w := by
  intro s hs
  -- ⊢ ↑(r • v) s = 0
  rw [smul_apply, h hs, smul_zero]
  -- 🎉 no goals
#align measure_theory.vector_measure.absolutely_continuous.smul MeasureTheory.VectorMeasure.AbsolutelyContinuous.smul

theorem map [MeasureSpace β] (h : v ≪ᵥ w) (f : α → β) : v.map f ≪ᵥ w.map f := by
  by_cases hf : Measurable f
  -- ⊢ VectorMeasure.map v f ≪ᵥ VectorMeasure.map w f
  · refine' mk fun s hs hws => _
    -- ⊢ ↑(VectorMeasure.map v f) s = 0
    rw [map_apply _ hf hs] at hws ⊢
    -- ⊢ ↑v (f ⁻¹' s) = 0
    exact h hws
    -- 🎉 no goals
  · intro s _
    -- ⊢ ↑(VectorMeasure.map v f) s = 0
    rw [map_not_measurable v hf, zero_apply]
    -- 🎉 no goals
#align measure_theory.vector_measure.absolutely_continuous.map MeasureTheory.VectorMeasure.AbsolutelyContinuous.map

theorem ennrealToMeasure {μ : VectorMeasure α ℝ≥0∞} :
    (∀ ⦃s : Set α⦄, μ.ennrealToMeasure s = 0 → v s = 0) ↔ v ≪ᵥ μ := by
  constructor <;> intro h
  -- ⊢ (∀ ⦃s : Set α⦄, ↑↑(VectorMeasure.ennrealToMeasure μ) s = 0 → ↑v s = 0) → v ≪ …
                  -- ⊢ v ≪ᵥ μ
                  -- ⊢ ∀ ⦃s : Set α⦄, ↑↑(VectorMeasure.ennrealToMeasure μ) s = 0 → ↑v s = 0
  · refine' mk fun s hmeas hs => h _
    -- ⊢ ↑↑(VectorMeasure.ennrealToMeasure μ) s = 0
    rw [← hs, ennrealToMeasure_apply hmeas]
    -- 🎉 no goals
  · intro s hs
    -- ⊢ ↑v s = 0
    by_cases hmeas : MeasurableSet s
    -- ⊢ ↑v s = 0
    · rw [ennrealToMeasure_apply hmeas] at hs
      -- ⊢ ↑v s = 0
      exact h hs
      -- 🎉 no goals
    · exact not_measurable v hmeas
      -- 🎉 no goals
#align measure_theory.vector_measure.absolutely_continuous.ennreal_to_measure MeasureTheory.VectorMeasure.AbsolutelyContinuous.ennrealToMeasure

end AbsolutelyContinuous

/-- Two vector measures `v` and `w` are said to be mutually singular if there exists a measurable
set `s`, such that for all `t ⊆ s`, `v t = 0` and for all `t ⊆ sᶜ`, `w t = 0`.

We note that we do not require the measurability of `t` in the definition since this makes it easier
to use. This is equivalent to the definition which requires measurability. To prove
`MutuallySingular` with the measurability condition, use
`MeasureTheory.VectorMeasure.MutuallySingular.mk`. -/
def MutuallySingular (v : VectorMeasure α M) (w : VectorMeasure α N) : Prop :=
  ∃ s : Set α, MeasurableSet s ∧ (∀ (t) (_ : t ⊆ s), v t = 0) ∧ ∀ (t) (_ : t ⊆ sᶜ), w t = 0
#align measure_theory.vector_measure.mutually_singular MeasureTheory.VectorMeasure.MutuallySingular

-- mathport name: vector_measure.mutually_singular
@[inherit_doc VectorMeasure.MutuallySingular]
scoped[MeasureTheory] infixl:60 " ⟂ᵥ " => MeasureTheory.VectorMeasure.MutuallySingular

namespace MutuallySingular

variable {v v₁ v₂ : VectorMeasure α M} {w w₁ w₂ : VectorMeasure α N}

theorem mk (s : Set α) (hs : MeasurableSet s) (h₁ : ∀ (t) (_ : t ⊆ s), MeasurableSet t → v t = 0)
    (h₂ : ∀ (t) (_ : t ⊆ sᶜ), MeasurableSet t → w t = 0) : v ⟂ᵥ w := by
  refine' ⟨s, hs, fun t hst => _, fun t hst => _⟩ <;> by_cases ht : MeasurableSet t
  -- ⊢ ↑v t = 0
                                                      -- ⊢ ↑v t = 0
                                                      -- ⊢ ↑w t = 0
  · exact h₁ t hst ht
    -- 🎉 no goals
  · exact not_measurable v ht
    -- 🎉 no goals
  · exact h₂ t hst ht
    -- 🎉 no goals
  · exact not_measurable w ht
    -- 🎉 no goals
#align measure_theory.vector_measure.mutually_singular.mk MeasureTheory.VectorMeasure.MutuallySingular.mk

theorem symm (h : v ⟂ᵥ w) : w ⟂ᵥ v :=
  let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨sᶜ, hmeas.compl, hs₂, fun t ht => hs₁ _ (compl_compl s ▸ ht : t ⊆ s)⟩
#align measure_theory.vector_measure.mutually_singular.symm MeasureTheory.VectorMeasure.MutuallySingular.symm

theorem zero_right : v ⟂ᵥ (0 : VectorMeasure α N) :=
  ⟨∅, MeasurableSet.empty, fun _ ht => (Set.subset_empty_iff.1 ht).symm ▸ v.empty,
    fun _ _ => zero_apply _⟩
#align measure_theory.vector_measure.mutually_singular.zero_right MeasureTheory.VectorMeasure.MutuallySingular.zero_right

theorem zero_left : (0 : VectorMeasure α M) ⟂ᵥ w :=
  zero_right.symm
#align measure_theory.vector_measure.mutually_singular.zero_left MeasureTheory.VectorMeasure.MutuallySingular.zero_left

theorem add_left [T2Space N] [ContinuousAdd M] (h₁ : v₁ ⟂ᵥ w) (h₂ : v₂ ⟂ᵥ w) : v₁ + v₂ ⟂ᵥ w := by
  obtain ⟨u, hmu, hu₁, hu₂⟩ := h₁
  -- ⊢ v₁ + v₂ ⟂ᵥ w
  obtain ⟨v, hmv, hv₁, hv₂⟩ := h₂
  -- ⊢ v₁ + v₂ ⟂ᵥ w
  refine' mk (u ∩ v) (hmu.inter hmv) (fun t ht _ => _) fun t ht hmt => _
  -- ⊢ ↑(v₁ + v₂) t = 0
  · rw [add_apply, hu₁ _ (Set.subset_inter_iff.1 ht).1, hv₁ _ (Set.subset_inter_iff.1 ht).2,
      zero_add]
  · rw [Set.compl_inter] at ht
    -- ⊢ ↑w t = 0
    rw [(_ : t = uᶜ ∩ t ∪ vᶜ \ uᶜ ∩ t),
      of_union _ (hmu.compl.inter hmt) ((hmv.compl.diff hmu.compl).inter hmt), hu₂, hv₂, add_zero]
    · exact Set.Subset.trans (Set.inter_subset_left _ _) (Set.diff_subset _ _)
      -- 🎉 no goals
    · exact Set.inter_subset_left _ _
      -- 🎉 no goals
    · exact disjoint_sdiff_self_right.mono (Set.inter_subset_left _ _) (Set.inter_subset_left _ _)
      -- 🎉 no goals
    · apply Set.Subset.antisymm <;> intro x hx
      -- ⊢ t ⊆ uᶜ ∩ t ∪ vᶜ \ uᶜ ∩ t
                                    -- ⊢ x ∈ uᶜ ∩ t ∪ vᶜ \ uᶜ ∩ t
                                    -- ⊢ x ∈ t
      · by_cases hxu' : x ∈ uᶜ
        -- ⊢ x ∈ uᶜ ∩ t ∪ vᶜ \ uᶜ ∩ t
        · exact Or.inl ⟨hxu', hx⟩
          -- 🎉 no goals
        rcases ht hx with (hxu | hxv)
        -- ⊢ x ∈ uᶜ ∩ t ∪ vᶜ \ uᶜ ∩ t
        exacts [False.elim (hxu' hxu), Or.inr ⟨⟨hxv, hxu'⟩, hx⟩]
        -- 🎉 no goals
      · cases' hx with hx hx <;> exact hx.2
        -- ⊢ x ∈ t
                                 -- 🎉 no goals
                                 -- 🎉 no goals
#align measure_theory.vector_measure.mutually_singular.add_left MeasureTheory.VectorMeasure.MutuallySingular.add_left

theorem add_right [T2Space M] [ContinuousAdd N] (h₁ : v ⟂ᵥ w₁) (h₂ : v ⟂ᵥ w₂) : v ⟂ᵥ w₁ + w₂ :=
  (add_left h₁.symm h₂.symm).symm
#align measure_theory.vector_measure.mutually_singular.add_right MeasureTheory.VectorMeasure.MutuallySingular.add_right

theorem smul_right {R : Type*} [Semiring R] [DistribMulAction R N] [ContinuousConstSMul R N]
    (r : R) (h : v ⟂ᵥ w) : v ⟂ᵥ r • w :=
  let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨s, hmeas, hs₁, fun t ht => by simp only [coe_smul, Pi.smul_apply, hs₂ t ht, smul_zero]⟩
                                 -- 🎉 no goals
#align measure_theory.vector_measure.mutually_singular.smul_right MeasureTheory.VectorMeasure.MutuallySingular.smul_right

theorem smul_left {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M] (r : R)
    (h : v ⟂ᵥ w) : r • v ⟂ᵥ w :=
  (smul_right r h.symm).symm
#align measure_theory.vector_measure.mutually_singular.smul_left MeasureTheory.VectorMeasure.MutuallySingular.smul_left

theorem neg_left {M : Type*} [AddCommGroup M] [TopologicalSpace M] [TopologicalAddGroup M]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ⟂ᵥ w) : -v ⟂ᵥ w := by
  obtain ⟨u, hmu, hu₁, hu₂⟩ := h
  -- ⊢ -v ⟂ᵥ w
  refine' ⟨u, hmu, fun s hs => _, hu₂⟩
  -- ⊢ ↑(-v) s = 0
  rw [neg_apply v s, neg_eq_zero]
  -- ⊢ ↑v s = 0
  exact hu₁ s hs
  -- 🎉 no goals
#align measure_theory.vector_measure.mutually_singular.neg_left MeasureTheory.VectorMeasure.MutuallySingular.neg_left

theorem neg_right {N : Type*} [AddCommGroup N] [TopologicalSpace N] [TopologicalAddGroup N]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ⟂ᵥ w) : v ⟂ᵥ -w :=
  h.symm.neg_left.symm
#align measure_theory.vector_measure.mutually_singular.neg_right MeasureTheory.VectorMeasure.MutuallySingular.neg_right

@[simp]
theorem neg_left_iff {M : Type*} [AddCommGroup M] [TopologicalSpace M] [TopologicalAddGroup M]
    {v : VectorMeasure α M} {w : VectorMeasure α N} : -v ⟂ᵥ w ↔ v ⟂ᵥ w :=
  ⟨fun h => neg_neg v ▸ h.neg_left, neg_left⟩
#align measure_theory.vector_measure.mutually_singular.neg_left_iff MeasureTheory.VectorMeasure.MutuallySingular.neg_left_iff

@[simp]
theorem neg_right_iff {N : Type*} [AddCommGroup N] [TopologicalSpace N] [TopologicalAddGroup N]
    {v : VectorMeasure α M} {w : VectorMeasure α N} : v ⟂ᵥ -w ↔ v ⟂ᵥ w :=
  ⟨fun h => neg_neg w ▸ h.neg_right, neg_right⟩
#align measure_theory.vector_measure.mutually_singular.neg_right_iff MeasureTheory.VectorMeasure.MutuallySingular.neg_right_iff

end MutuallySingular

section Trim

/-- Restriction of a vector measure onto a sub-σ-algebra. -/
@[simps]
def trim {m n : MeasurableSpace α} (v : VectorMeasure α M) (hle : m ≤ n) :
    @VectorMeasure α m M _ _ :=
  @VectorMeasure.mk α m M _ _
    (fun i => if MeasurableSet[m] i then v i else 0)
    (by dsimp only; rw [if_pos (@MeasurableSet.empty _ m), v.empty])
        -- ⊢ (if MeasurableSet ∅ then ↑v ∅ else 0) = 0
                    -- 🎉 no goals
    (fun i hi => by dsimp only; rw [if_neg hi])
                    -- ⊢ (if MeasurableSet i then ↑v i else 0) = 0
                                -- 🎉 no goals
    (fun f hf₁ hf₂ => by
      dsimp only
      -- ⊢ HasSum (fun i => if MeasurableSet (f i) then ↑v (f i) else 0) (if Measurable …
      have hf₁' : ∀ k, MeasurableSet[n] (f k) := fun k => hle _ (hf₁ k)
      -- ⊢ HasSum (fun i => if MeasurableSet (f i) then ↑v (f i) else 0) (if Measurable …
      convert v.m_iUnion hf₁' hf₂ using 1
      -- ⊢ (fun i => if MeasurableSet (f i) then ↑v (f i) else 0) = fun i => ↑v (f i)
      · ext n
        -- ⊢ (if MeasurableSet (f n) then ↑v (f n) else 0) = ↑v (f n)
        rw [if_pos (hf₁ n)]
        -- 🎉 no goals
      · rw [if_pos (@MeasurableSet.iUnion _ _ m _ _ hf₁)])
        -- 🎉 no goals
#align measure_theory.vector_measure.trim MeasureTheory.VectorMeasure.trim

variable {n : MeasurableSpace α} {v : VectorMeasure α M}

theorem trim_eq_self : v.trim le_rfl = v := by
  ext i hi
  -- ⊢ ↑(trim v (_ : n ≤ n)) i = ↑v i
  exact if_pos hi
  -- 🎉 no goals
#align measure_theory.vector_measure.trim_eq_self MeasureTheory.VectorMeasure.trim_eq_self

@[simp]
theorem zero_trim (hle : m ≤ n) : (0 : VectorMeasure α M).trim hle = 0 := by
  ext i hi
  -- ⊢ ↑(trim 0 hle) i = ↑0 i
  exact if_pos hi
  -- 🎉 no goals
#align measure_theory.vector_measure.zero_trim MeasureTheory.VectorMeasure.zero_trim

theorem trim_measurableSet_eq (hle : m ≤ n) {i : Set α} (hi : MeasurableSet[m] i) :
    v.trim hle i = v i :=
  if_pos hi
#align measure_theory.vector_measure.trim_measurable_set_eq MeasureTheory.VectorMeasure.trim_measurableSet_eq

theorem restrict_trim (hle : m ≤ n) {i : Set α} (hi : MeasurableSet[m] i) :
    @VectorMeasure.restrict α m M _ _ (v.trim hle) i = (v.restrict i).trim hle := by
  ext j hj
  -- ⊢ ↑(restrict (trim v hle) i) j = ↑(trim (restrict v i) hle) j
  rw [@restrict_apply _ m, trim_measurableSet_eq hle hj, restrict_apply, trim_measurableSet_eq]
  all_goals measurability
  -- 🎉 no goals
#align measure_theory.vector_measure.restrict_trim MeasureTheory.VectorMeasure.restrict_trim

end Trim

end

end VectorMeasure

namespace SignedMeasure

open VectorMeasure

open MeasureTheory

/-- The underlying function for `SignedMeasure.toMeasureOfZeroLE`. -/
def toMeasureOfZeroLE' (s : SignedMeasure α) (i : Set α) (hi : 0 ≤[i] s) (j : Set α)
    (hj : MeasurableSet j) : ℝ≥0∞ :=
  ((↑) : ℝ≥0 → ℝ≥0∞) ⟨s.restrict i j, le_trans (by simp) (hi j hj)⟩
                                                   -- 🎉 no goals
#align measure_theory.signed_measure.to_measure_of_zero_le' MeasureTheory.SignedMeasure.toMeasureOfZeroLE'

/-- Given a signed measure `s` and a positive measurable set `i`, `toMeasureOfZeroLE`
provides the measure, mapping measurable sets `j` to `s (i ∩ j)`. -/
def toMeasureOfZeroLE (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : 0 ≤[i] s) :
    Measure α := by
  refine' Measure.ofMeasurable (s.toMeasureOfZeroLE' i hi₂) _ _
  -- ⊢ toMeasureOfZeroLE' s i hi₂ ∅ (_ : MeasurableSet ∅) = 0
  · simp_rw [toMeasureOfZeroLE', s.restrict_apply hi₁ MeasurableSet.empty, Set.empty_inter i,
      s.empty]
    rfl
    -- 🎉 no goals
  · intro f hf₁ hf₂
    -- ⊢ toMeasureOfZeroLE' s i hi₂ (⋃ (i : ℕ), f i) (_ : MeasurableSet (⋃ (b : ℕ), f …
    have h₁ : ∀ n, MeasurableSet (i ∩ f n) := fun n => hi₁.inter (hf₁ n)
    -- ⊢ toMeasureOfZeroLE' s i hi₂ (⋃ (i : ℕ), f i) (_ : MeasurableSet (⋃ (b : ℕ), f …
    have h₂ : Pairwise (Disjoint on fun n : ℕ => i ∩ f n) := by
      intro n m hnm
      exact ((hf₂ hnm).inf_left' i).inf_right' i
    simp only [toMeasureOfZeroLE', s.restrict_apply hi₁ (MeasurableSet.iUnion hf₁), Set.inter_comm,
      Set.inter_iUnion, s.of_disjoint_iUnion_nat h₁ h₂, ENNReal.some_eq_coe, id.def]
    have h : ∀ n, 0 ≤ s (i ∩ f n) := fun n =>
      s.nonneg_of_zero_le_restrict (s.zero_le_restrict_subset hi₁ (Set.inter_subset_left _ _) hi₂)
    rw [NNReal.coe_tsum_of_nonneg h, ENNReal.coe_tsum]
    -- ⊢ ∑' (a : ℕ), ↑{ val := ↑s (i ∩ f a), property := (_ : 0 ≤ ↑s (i ∩ f a)) } = ∑ …
    · refine' tsum_congr fun n => _
      -- ⊢ ↑{ val := ↑s (i ∩ f n), property := (_ : 0 ≤ ↑s (i ∩ f n)) } = ↑{ val := ↑(V …
      simp_rw [s.restrict_apply hi₁ (hf₁ n), Set.inter_comm]
      -- 🎉 no goals
    · exact (NNReal.summable_mk h).2 (s.m_iUnion h₁ h₂).summable
      -- 🎉 no goals
#align measure_theory.signed_measure.to_measure_of_zero_le MeasureTheory.SignedMeasure.toMeasureOfZeroLE

variable (s : SignedMeasure α) {i j : Set α}

theorem toMeasureOfZeroLE_apply (hi : 0 ≤[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) :
    s.toMeasureOfZeroLE i hi₁ hi j = ((↑) : ℝ≥0 → ℝ≥0∞) ⟨s (i ∩ j), nonneg_of_zero_le_restrict
      s (zero_le_restrict_subset s hi₁ (Set.inter_subset_left _ _) hi)⟩ := by
  simp_rw [toMeasureOfZeroLE, Measure.ofMeasurable_apply _ hj₁, toMeasureOfZeroLE',
    s.restrict_apply hi₁ hj₁, Set.inter_comm]
#align measure_theory.signed_measure.to_measure_of_zero_le_apply MeasureTheory.SignedMeasure.toMeasureOfZeroLE_apply

/-- Given a signed measure `s` and a negative measurable set `i`, `toMeasureOfLEZero`
provides the measure, mapping measurable sets `j` to `-s (i ∩ j)`. -/
def toMeasureOfLEZero (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : s ≤[i] 0) :
    Measure α :=
  toMeasureOfZeroLE (-s) i hi₁ <| @neg_zero (VectorMeasure α ℝ) _ ▸ neg_le_neg _ _ hi₁ hi₂
#align measure_theory.signed_measure.to_measure_of_le_zero MeasureTheory.SignedMeasure.toMeasureOfLEZero

theorem toMeasureOfLEZero_apply (hi : s ≤[i] 0) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) :
    s.toMeasureOfLEZero i hi₁ hi j = ((↑) : ℝ≥0 → ℝ≥0∞) ⟨-s (i ∩ j), neg_apply s (i ∩ j) ▸
      nonneg_of_zero_le_restrict _ (zero_le_restrict_subset _ hi₁ (Set.inter_subset_left _ _)
      (@neg_zero (VectorMeasure α ℝ) _ ▸ neg_le_neg _ _ hi₁ hi))⟩ := by
  erw [toMeasureOfZeroLE_apply]
  -- ⊢ ↑{ val := ↑(-s) (i ∩ j), property := (_ : 0 ≤ ↑(-s) (i ∩ j)) } = ↑{ val := - …
  · simp
    -- 🎉 no goals
  · assumption
    -- 🎉 no goals
#align measure_theory.signed_measure.to_measure_of_le_zero_apply MeasureTheory.SignedMeasure.toMeasureOfLEZero_apply

/-- `SignedMeasure.toMeasureOfZeroLE` is a finite measure. -/
instance toMeasureOfZeroLE_finite (hi : 0 ≤[i] s) (hi₁ : MeasurableSet i) :
    IsFiniteMeasure (s.toMeasureOfZeroLE i hi₁ hi) where
  measure_univ_lt_top := by
    rw [toMeasureOfZeroLE_apply s hi hi₁ MeasurableSet.univ]
    -- ⊢ ↑{ val := ↑s (i ∩ univ), property := (_ : 0 ≤ ↑s (i ∩ univ)) } < ⊤
    exact ENNReal.coe_lt_top
    -- 🎉 no goals
#align measure_theory.signed_measure.to_measure_of_zero_le_finite MeasureTheory.SignedMeasure.toMeasureOfZeroLE_finite

/-- `SignedMeasure.toMeasureOfLEZero` is a finite measure. -/
instance toMeasureOfLEZero_finite (hi : s ≤[i] 0) (hi₁ : MeasurableSet i) :
    IsFiniteMeasure (s.toMeasureOfLEZero i hi₁ hi) where
  measure_univ_lt_top := by
    rw [toMeasureOfLEZero_apply s hi hi₁ MeasurableSet.univ]
    -- ⊢ ↑{ val := -↑s (i ∩ univ), property := (_ : 0 ≤ -↑s (i ∩ univ)) } < ⊤
    exact ENNReal.coe_lt_top
    -- 🎉 no goals
#align measure_theory.signed_measure.to_measure_of_le_zero_finite MeasureTheory.SignedMeasure.toMeasureOfLEZero_finite

theorem toMeasureOfZeroLE_toSignedMeasure (hs : 0 ≤[Set.univ] s) :
    (s.toMeasureOfZeroLE Set.univ MeasurableSet.univ hs).toSignedMeasure = s := by
  ext i hi
  -- ⊢ ↑(Measure.toSignedMeasure (toMeasureOfZeroLE s univ (_ : MeasurableSet univ) …
  simp [hi, toMeasureOfZeroLE_apply _ _ _ hi]
  -- 🎉 no goals
#align measure_theory.signed_measure.to_measure_of_zero_le_to_signed_measure MeasureTheory.SignedMeasure.toMeasureOfZeroLE_toSignedMeasure

theorem toMeasureOfLEZero_toSignedMeasure (hs : s ≤[Set.univ] 0) :
    (s.toMeasureOfLEZero Set.univ MeasurableSet.univ hs).toSignedMeasure = -s := by
  ext i hi
  -- ⊢ ↑(Measure.toSignedMeasure (toMeasureOfLEZero s univ (_ : MeasurableSet univ) …
  simp [hi, toMeasureOfLEZero_apply _ _ _ hi]
  -- 🎉 no goals
#align measure_theory.signed_measure.to_measure_of_le_zero_to_signed_measure MeasureTheory.SignedMeasure.toMeasureOfLEZero_toSignedMeasure

end SignedMeasure

namespace Measure

open VectorMeasure

variable (μ : Measure α) [IsFiniteMeasure μ]

theorem zero_le_toSignedMeasure : 0 ≤ μ.toSignedMeasure := by
  rw [← le_restrict_univ_iff_le]
  -- ⊢ VectorMeasure.restrict 0 univ ≤ VectorMeasure.restrict (toSignedMeasure μ) u …
  refine' restrict_le_restrict_of_subset_le _ _ fun j hj₁ _ => _
  -- ⊢ ↑0 j ≤ ↑(toSignedMeasure μ) j
  simp only [Measure.toSignedMeasure_apply_measurable hj₁, coe_zero, Pi.zero_apply,
    ENNReal.toReal_nonneg, VectorMeasure.coe_zero]
#align measure_theory.measure.zero_le_to_signed_measure MeasureTheory.Measure.zero_le_toSignedMeasure

theorem toSignedMeasure_toMeasureOfZeroLE :
    μ.toSignedMeasure.toMeasureOfZeroLE Set.univ MeasurableSet.univ
      ((le_restrict_univ_iff_le _ _).2 (zero_le_toSignedMeasure μ)) = μ := by
  refine' Measure.ext fun i hi => _
  -- ⊢ ↑↑(SignedMeasure.toMeasureOfZeroLE (toSignedMeasure μ) univ (_ : MeasurableS …
  lift μ i to ℝ≥0 using (measure_lt_top _ _).ne with m hm
  -- ⊢ ↑↑(SignedMeasure.toMeasureOfZeroLE (toSignedMeasure μ) univ (_ : MeasurableS …
  rw [SignedMeasure.toMeasureOfZeroLE_apply _ _ _ hi, coe_eq_coe]
  -- ⊢ { val := ↑(toSignedMeasure μ) (univ ∩ i), property := (_ : 0 ≤ ↑(toSignedMea …
  congr
  -- ⊢ ↑(toSignedMeasure μ) (univ ∩ i) = ↑m
  simp [hi, ← hm]
  -- 🎉 no goals
#align measure_theory.measure.to_signed_measure_to_measure_of_zero_le MeasureTheory.Measure.toSignedMeasure_toMeasureOfZeroLE

end Measure

end MeasureTheory
