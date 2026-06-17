/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!

# Vector-valued measures

This file defines vector-valued measures, which are σ-additive functions from a set to an
additive monoid `M` such that it maps the empty set and non-measurable sets to zero. In the case
that `M = ℝ`, we called the vector measure a signed measure and write `SignedMeasure α`.
Similarly, when `M = ℂ`, we call the measure a complex measure and write `ComplexMeasure α`
(defined in `MeasureTheory/Measure/Complex`).

## Main definitions

* `MeasureTheory.VectorMeasure` is a vector-valued, σ-additive function that maps the empty
  and non-measurable sets to zero.
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

@[expose] public section


noncomputable section

open NNReal ENNReal Filter

open scoped Topology Function -- required for scoped `on` notation
namespace MeasureTheory

variable {α β : Type*} {m : MeasurableSpace α}

/-- A vector measure on a measurable space `α` is a σ-additive `M`-valued function (for some `M`
an additive monoid) such that the empty set and non-measurable sets are mapped to zero. -/
structure VectorMeasure (α : Type*) [MeasurableSpace α] (M : Type*) [AddCommMonoid M]
    [TopologicalSpace M] where
  /-- The measure of sets -/
  measureOf' : Set α → M
  /-- The empty set has measure zero -/
  empty' : measureOf' ∅ = 0
  /-- Non-measurable sets have measure zero -/
  not_measurable' ⦃i : Set α⦄ : ¬MeasurableSet i → measureOf' i = 0
  /-- The measure is σ-additive -/
  m_iUnion' ⦃f : ℕ → Set α⦄ : (∀ i, MeasurableSet (f i)) → Pairwise (Disjoint on f) →
    HasSum (fun i => measureOf' (f i)) (measureOf' (⋃ i, f i))

/-- A `SignedMeasure` is an `ℝ`-vector measure. -/
abbrev SignedMeasure (α : Type*) [MeasurableSpace α] :=
  VectorMeasure α ℝ

open Set

namespace VectorMeasure

section

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

instance : FunLike (VectorMeasure α M) (Set α) M where
  coe := VectorMeasure.measureOf'
  coe_injective v w h := by
    cases v; cases w; congr

@[simp]
theorem coe_mk (v : Set α → M) (h₁) (h₂) (h₃) : (mk v h₁ h₂ h₃ : VectorMeasure α M) = v := rfl

initialize_simps_projections VectorMeasure (measureOf' → apply)

@[simp]
theorem empty (v : VectorMeasure α M) : v ∅ = 0 :=
  v.empty'

@[simp]
theorem not_measurable (v : VectorMeasure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0 :=
  v.not_measurable' hi

theorem m_iUnion (v : VectorMeasure α M) {f : ℕ → Set α} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) : HasSum (fun i => v (f i)) (v (⋃ i, f i)) :=
  v.m_iUnion' hf₁ hf₂

@[deprecated (since := "2026-06-10")] alias coe_injective := DFunLike.coe_injective

@[deprecated (since := "2026-06-10")] alias ext_iff' := DFunLike.ext_iff

theorem ext_iff (v w : VectorMeasure α M) : v = w ↔ ∀ i : Set α, MeasurableSet i → v i = w i := by
  constructor
  · rintro rfl _ _
    rfl
  · rw [DFunLike.ext_iff]
    intro h i
    by_cases hi : MeasurableSet i
    · exact h i hi
    · simp_rw [not_measurable _ hi]

@[ext]
theorem ext {s t : VectorMeasure α M} (h : ∀ i : Set α, MeasurableSet i → s i = t i) : s = t :=
  (ext_iff s t).2 h

variable [Countable β] {v : VectorMeasure α M} {f : β → Set α}

theorem hasSum_of_disjoint_iUnion (hm : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :
    HasSum (fun i => v (f i)) (v (⋃ i, f i)) := by
  rcases Countable.exists_injective_nat β with ⟨e, he⟩
  rw [← hasSum_extend_zero he]
  convert! m_iUnion v (f := Function.extend e f fun _ ↦ ∅) _ _
  · simp only [Pi.zero_def, Function.apply_extend v, Function.comp_def, empty]
  · exact (iSup_extend_bot he _).symm
  · simp [Function.apply_extend MeasurableSet, Function.comp_def, hm]
  · exact hd.disjoint_extend_bot (he.factorsThrough _)

theorem of_if {ι : Type*} {x : ι} {B : Set ι} {A : Set α} [Decidable (x ∈ B)] :
    v (if x ∈ B then A else ∅) = indicator B (fun _ => v A) x := by
  split_ifs with h <;> simp [h]

variable [T2Space M]

theorem of_disjoint_iUnion (hm : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :
    v (⋃ i, f i) = ∑' i, v (f i) :=
  (hasSum_of_disjoint_iUnion hm hd).tsum_eq.symm

theorem of_biUnion {ι : Type*} {s : Set ι} {f : ι → Set α} (hs : s.Countable)
    (hd : s.Pairwise (Disjoint on f)) (h : ∀ b ∈ s, MeasurableSet (f b)) :
    v (⋃ b ∈ s, f b) = ∑' p : s, v (f p) := by
  haveI := hs.toEncodable
  rw [biUnion_eq_iUnion]
  apply of_disjoint_iUnion
  · exact fun x ↦ h x x.2
  · exact hd.on_injective Subtype.coe_injective fun x => x.2

theorem of_biUnion_finset {ι : Type*} {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : ∀ b ∈ s, MeasurableSet (f b)) : v (⋃ b ∈ s, f b) = ∑ p ∈ s, v (f p) := by
  rw [← Finset.sum_attach, Finset.attach_eq_univ, ← tsum_fintype (L := .unconditional s)]
  exact of_biUnion s.countable_toSet hd hm

theorem of_union {A B : Set α} (h : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    v (A ∪ B) = v A + v B := by
  rw [Set.union_eq_iUnion, of_disjoint_iUnion, tsum_fintype, Fintype.sum_bool, cond, cond]
  exacts [fun b => Bool.casesOn b hB hA, pairwise_disjoint_on_bool.2 h]

theorem of_add_of_sdiff {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A ⊆ B) :
    v A + v (B \ A) = v B := by
  rw [← of_union (@Set.disjoint_sdiff_right _ A B) hA (hB.diff hA), Set.union_sdiff_cancel h]

@[deprecated (since := "2026-06-03")] alias of_add_of_diff := of_add_of_sdiff

theorem of_sdiff {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    {v : VectorMeasure α M} {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : A ⊆ B) : v (B \ A) = v B - v A := by
  rw [← of_add_of_sdiff hA hB h, add_sub_cancel_left]

@[deprecated (since := "2026-06-03")] alias of_diff := of_sdiff

theorem of_compl {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    {v : VectorMeasure α M} {A : Set α} (hA : MeasurableSet A) :
    v Aᶜ = v univ - v A := by
  simpa [compl_eq_univ_sdiff] using of_sdiff hA .univ (v := v) (subset_univ _)

theorem of_sdiff_of_sdiff_eq_zero {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h' : v (B \ A) = 0) : v (A \ B) + v B = v A := by
  symm
  calc
    v A = v (A \ B ∪ A ∩ B) := by simp only [Set.sdiff_union_inter]
    _ = v (A \ B) + v (A ∩ B) := by
      rw [of_union]
      · rw [disjoint_comm]
        exact Set.disjoint_of_subset_left A.inter_subset_right disjoint_sdiff_self_right
      · exact hA.diff hB
      · exact hA.inter hB
    _ = v (A \ B) + v (A ∩ B ∪ B \ A) := by
      rw [of_union, h', add_zero]
      · exact Set.disjoint_of_subset_left A.inter_subset_left disjoint_sdiff_self_right
      · exact hA.inter hB
      · exact hB.diff hA
    _ = v (A \ B) + v B := by rw [Set.union_comm, Set.inter_comm, Set.sdiff_union_inter]

@[deprecated (since := "2026-06-03")] alias of_diff_of_diff_eq_zero := of_sdiff_of_sdiff_eq_zero

theorem of_iUnion_nonneg {M : Type*} [TopologicalSpace M]
    [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    [OrderClosedTopology M] {v : VectorMeasure α M} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) (hf₃ : ∀ i, 0 ≤ v (f i)) : 0 ≤ v (⋃ i, f i) :=
  (v.of_disjoint_iUnion hf₁ hf₂).symm ▸ tsum_nonneg hf₃

theorem of_iUnion_nonpos {M : Type*} [TopologicalSpace M]
    [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    [OrderClosedTopology M] {v : VectorMeasure α M} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) (hf₃ : ∀ i, v (f i) ≤ 0) : v (⋃ i, f i) ≤ 0 :=
  (v.of_disjoint_iUnion hf₁ hf₂).symm ▸ tsum_nonpos hf₃

theorem of_nonneg_disjoint_union_eq_zero {s : SignedMeasure α} {A B : Set α} (h : Disjoint A B)
    (hA₁ : MeasurableSet A) (hB₁ : MeasurableSet B) (hA₂ : 0 ≤ s A) (hB₂ : 0 ≤ s B)
    (hAB : s (A ∪ B) = 0) : s A = 0 := by
  rw [of_union h hA₁ hB₁] at hAB
  linarith

theorem of_nonpos_disjoint_union_eq_zero {s : SignedMeasure α} {A B : Set α} (h : Disjoint A B)
    (hA₁ : MeasurableSet A) (hB₁ : MeasurableSet B) (hA₂ : s A ≤ 0) (hB₂ : s B ≤ 0)
    (hAB : s (A ∪ B) = 0) : s A = 0 := by
  rw [of_union h hA₁ hB₁] at hAB
  linarith

theorem tendsto_vectorMeasure_iUnion_atTop_nat
    {s : ℕ → Set α} (hm : Monotone s) (hs : ∀ i, MeasurableSet (s i)) :
    Tendsto (fun n ↦ v (s n)) atTop (𝓝 (v (⋃ n, s n))) := by
  set t : ℕ → Set α := disjointed s
  have ht n : MeasurableSet (t n) := .disjointed (fun n ↦ hs n) n
  have : HasSum (fun n ↦ v (t n)) (v (⋃ n, s n)) := by
    rw [← iUnion_disjointed]
    apply m_iUnion _ ht (disjoint_disjointed _)
  convert! (HasSum.tendsto_sum_nat this).comp (tendsto_add_atTop_nat 1) with n
  dsimp
  rw [← of_biUnion_finset]
  · rw [biUnion_range_succ_disjointed, Monotone.partialSups_eq hm]
  · exact fun i hi j hj hij ↦ disjoint_disjointed _ hij
  · exact fun b hb ↦ ht _

theorem tendsto_vectorMeasure_iInter_atTop_nat
    {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M] [ContinuousSub M]
    {v : VectorMeasure α M} {s : ℕ → Set α} (hm : Antitone s) (hs : ∀ i, MeasurableSet (s i)) :
    Tendsto (fun n ↦ v (s n)) atTop (𝓝 (v (⋂ n, s n))) := by
  have I n : v (s n) = v univ - v (s n)ᶜ := by simp [of_compl (hs n)]
  have J : v (⋂ n, s n) = v univ - v (⋃ n, (s n)ᶜ) := by
    rw [← of_compl (MeasurableSet.iUnion (fun n ↦ (hs n).compl))]
    simp
  simp_rw [I, J]
  apply tendsto_const_nhds.sub
  exact tendsto_vectorMeasure_iUnion_atTop_nat (fun i j hij ↦ by simpa using hm hij)
    (fun i ↦ (hs i).compl)

/-- If two vector measures give the same mass to the whole space and coincide on a
generating π-system, then they coincide. -/
theorem ext_of_generateFrom
    {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M] [ContinuousSub M]
    {X : Type*} {mX : MeasurableSpace X} {μ ν : VectorMeasure X M}
    (C : Set (Set X)) (hμν : ∀ s ∈ C, μ s = ν s)
    (hA : mX = MeasurableSpace.generateFrom C) (hC : IsPiSystem C)
    (h_univ : μ Set.univ = ν Set.univ) : μ = ν := by
  ext s hs
  induction s, hs using MeasurableSpace.induction_on_inter hA hC with
  | empty => simp
  | basic t ht => exact hμν t ht
  | compl t htm iht =>
    simp [of_compl, iht, htm, h_univ]
  | iUnion f hfd hfm ihf =>
    simp [of_disjoint_iUnion, hfm, hfd, ihf]

end

section SMul

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

/-- Given a scalar `r` and a vector measure `v`, `smul r v` is the vector measure corresponding to
the set function `s : Set α => r • (v s)`. -/
@[implicit_reducible]
def smul (r : R) (v : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := r • ⇑v
  empty' := by rw [Pi.smul_apply, empty, smul_zero]
  not_measurable' _ hi := by rw [Pi.smul_apply, v.not_measurable hi, smul_zero]
  m_iUnion' _ hf₁ hf₂ := by exact HasSum.const_smul _ (v.m_iUnion hf₁ hf₂)

instance instSMul : SMul R (VectorMeasure α M) :=
  ⟨smul⟩

instance : IsSMulApply R (VectorMeasure α M) (Set α) M where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply

end SMul

section AddCommMonoid

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

instance instZero : Zero (VectorMeasure α M) :=
  ⟨⟨0, rfl, fun _ _ => rfl, fun _ _ _ => hasSum_zero⟩⟩

instance : IsZeroApply (VectorMeasure α M) (Set α) M where
  zero_apply _ := rfl

instance instInhabited : Inhabited (VectorMeasure α M) :=
  ⟨0⟩

@[nontriviality]
lemma apply_eq_zero_of_isEmpty [IsEmpty α] (μ : VectorMeasure α M) (s : Set α) :
    μ s = 0 := by
  simp [eq_empty_of_isEmpty s]

instance [IsEmpty α] : Subsingleton (VectorMeasure α M) :=
  ⟨fun μ ν => by ext; rw [apply_eq_zero_of_isEmpty, apply_eq_zero_of_isEmpty]⟩

theorem eq_zero_of_isEmpty [IsEmpty α] (μ : VectorMeasure α M) : μ = 0 :=
  Subsingleton.elim μ 0

@[deprecated (since := "2026-06-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply

variable [ContinuousAdd M]

/-- The sum of two vector measure is a vector measure. -/
def add (v w : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := v + w
  empty' := by simp
  not_measurable' _ hi := by rw [Pi.add_apply, v.not_measurable hi, w.not_measurable hi, add_zero]
  m_iUnion' _ hf₁ hf₂ := HasSum.add (v.m_iUnion hf₁ hf₂) (w.m_iUnion hf₁ hf₂)

instance instAdd : Add (VectorMeasure α M) :=
  ⟨add⟩

instance : IsAddApply (VectorMeasure α M) (Set α) M where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply

instance instAddCommMonoid : AddCommMonoid (VectorMeasure α M) :=
  fast_instance% FunLike.addCommMonoid

@[deprecated (since := "2026-06-10")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-10")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

@[deprecated (since := "2026-06-10")] alias coe_finsetSum := FunLike.coe_sum

end AddCommMonoid

section AddCommGroup

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- The negative of a vector measure is a vector measure. -/
def neg (v : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := -v
  empty' := by simp
  not_measurable' _ hi := by rw [Pi.neg_apply, neg_eq_zero, v.not_measurable hi]
  m_iUnion' _ hf₁ hf₂ := HasSum.neg <| v.m_iUnion hf₁ hf₂

instance instNeg : Neg (VectorMeasure α M) :=
  ⟨neg⟩

instance : IsNegApply (VectorMeasure α M) (Set α) M where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-06-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply

/-- The difference of two vector measure is a vector measure. -/
def sub (v w : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := v - w
  empty' := by simp
  not_measurable' _ hi := by rw [Pi.sub_apply, v.not_measurable hi, w.not_measurable hi, sub_zero]
  m_iUnion' _ hf₁ hf₂ := HasSum.sub (v.m_iUnion hf₁ hf₂) (w.m_iUnion hf₁ hf₂)

instance instSub : Sub (VectorMeasure α M) :=
  ⟨sub⟩

instance : IsSubApply (VectorMeasure α M) (Set α) M where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply

instance instAddCommGroup : AddCommGroup (VectorMeasure α M) := fast_instance% FunLike.addCommGroup

end AddCommGroup

section DistribMulAction

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

instance instDistribMulAction [ContinuousAdd M] : DistribMulAction R (VectorMeasure α M) :=
  fast_instance% FunLike.distribMulAction

end DistribMulAction

section Module

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [Module R M] [ContinuousConstSMul R M]

instance instModule [ContinuousAdd M] : Module R (VectorMeasure α M) :=
  fast_instance% FunLike.module

end Module

section Dirac

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [MeasurableSpace β]
  {x : β} {v : M} {s : Set β}

open scoped Classical in
/-- The Dirac vector measure with mass `v` at a point `x`. It gives mass `v` to measurable sets
containing `x`, and `0` otherwise. -/
def dirac (x : β) (v : M) : VectorMeasure β M where
  measureOf' s := if MeasurableSet s ∧ x ∈ s then v else 0
  empty' := by simp
  not_measurable' := by simp +contextual
  m_iUnion' f f_meas f_disj := by
    by_cases hx : x ∈ ⋃ i, f i; swap
    · simp only [mem_iUnion, not_exists] at hx
      simp [hx, hasSum_zero]
    have : MeasurableSet (⋃ i, f i) := by
      apply MeasurableSet.iUnion f_meas
    simp only [f_meas, true_and, MeasurableSet.iUnion f_meas, hx, and_self, ↓reduceIte]
    obtain ⟨j, hj⟩ : ∃ j, x ∈ f j := by simpa using hx
    nth_rewrite 2 [show v = if x ∈ f j then v else 0 by simp [hj]]
    apply hasSum_single
    intro i hi
    have : Disjoint (f i) (f j) := f_disj hi
    grind

@[simp] lemma dirac_apply_of_mem (hs : MeasurableSet s) (hx : x ∈ s) : dirac x v s = v :=
  if_pos (And.intro hs hx)

@[simp] lemma dirac_apply_of_notMem (hx : x ∉ s) : dirac x v s = 0 := by
  simp [dirac, hx]

@[simp] lemma dirac_zero : dirac x (0 : M) = 0 := by
  ext s hs
  simp [dirac]

end Dirac

end VectorMeasure

namespace Measure

open scoped Classical in
/-- A finite measure coerced into a real function is a signed measure. -/
def toSignedMeasure (μ : Measure α) [hμ : IsFiniteMeasure μ] : SignedMeasure α where
  measureOf' s := if MeasurableSet s then μ.real s else 0
  empty' := by simp
  not_measurable' _ hi := if_neg hi
  m_iUnion' f hf₁ hf₂ := by
    simp only [*, MeasurableSet.iUnion hf₁, if_true, measure_iUnion hf₂ hf₁, measureReal_def]
    rw [ENNReal.tsum_toReal_eq]
    exacts [(summable_measure_toReal hf₁ hf₂).hasSum, fun _ ↦ measure_ne_top _ _]

open scoped Classical in
@[simp]
theorem toSignedMeasure_apply (μ : Measure α) [hμ : IsFiniteMeasure μ] (i : Set α) :
    μ.toSignedMeasure i = if MeasurableSet i then μ.real i else 0 := rfl

theorem toSignedMeasure_apply_measurable {μ : Measure α} [IsFiniteMeasure μ] {i : Set α}
    (hi : MeasurableSet i) : μ.toSignedMeasure i = μ.real i :=
  if_pos hi

-- Without this lemma, `singularPart_neg` in
-- `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean` is extremely slow
theorem toSignedMeasure_congr {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ = ν) : μ.toSignedMeasure = ν.toSignedMeasure := by
  congr

theorem toSignedMeasure_eq_toSignedMeasure_iff {μ ν : Measure α} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : μ.toSignedMeasure = ν.toSignedMeasure ↔ μ = ν := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · ext1 i hi
    have : μ.toSignedMeasure i = ν.toSignedMeasure i := by rw [h]
    rwa [toSignedMeasure_apply_measurable hi, toSignedMeasure_apply_measurable hi,
        measureReal_eq_measureReal_iff] at this
  · congr

@[simp]
theorem toSignedMeasure_zero : (0 : Measure α).toSignedMeasure = 0 := by
  ext i hi
  simp [hi]

@[simp]
theorem toSignedMeasure_add (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ + ν).toSignedMeasure = μ.toSignedMeasure + ν.toSignedMeasure := by
  ext i hi
  rw [toSignedMeasure_apply_measurable hi, measureReal_add_apply,
    _root_.add_apply, toSignedMeasure_apply_measurable hi,
    toSignedMeasure_apply_measurable hi]

@[simp]
theorem toSignedMeasure_smul (μ : Measure α) [IsFiniteMeasure μ] (r : ℝ≥0) :
    (r • μ).toSignedMeasure = r • μ.toSignedMeasure := by
  ext i hi
  rw [toSignedMeasure_apply_measurable hi, _root_.smul_apply,
    toSignedMeasure_apply_measurable hi, measureReal_nnreal_smul_apply]
  rfl

open scoped Classical in
/-- A measure is a vector measure over `ℝ≥0∞`. -/
def toENNRealVectorMeasure (μ : Measure α) : VectorMeasure α ℝ≥0∞ where
  measureOf' i := if MeasurableSet i then μ i else 0
  empty' := by simp
  not_measurable' _ hi := if_neg hi
  m_iUnion' _ hf₁ hf₂ := by
    rw [Summable.hasSum_iff ENNReal.summable, if_pos (MeasurableSet.iUnion hf₁),
      MeasureTheory.measure_iUnion hf₂ hf₁]
    exact tsum_congr fun n => if_pos (hf₁ n)

open scoped Classical in
@[simp]
theorem toENNRealVectorMeasure_apply (μ : Measure α) (i : Set α) :
    μ.toENNRealVectorMeasure i = if MeasurableSet i then μ i else 0 := rfl

theorem toENNRealVectorMeasure_apply_measurable {μ : Measure α} {i : Set α} (hi : MeasurableSet i) :
    μ.toENNRealVectorMeasure i = μ i :=
  if_pos hi

@[simp]
theorem toENNRealVectorMeasure_zero : (0 : Measure α).toENNRealVectorMeasure = 0 := by
  ext i
  simp

@[simp]
theorem toENNRealVectorMeasure_add (μ ν : Measure α) :
    (μ + ν).toENNRealVectorMeasure = μ.toENNRealVectorMeasure + ν.toENNRealVectorMeasure := by
  refine MeasureTheory.VectorMeasure.ext fun i hi => ?_
  rw [toENNRealVectorMeasure_apply_measurable hi, add_apply, _root_.add_apply,
    toENNRealVectorMeasure_apply_measurable hi, toENNRealVectorMeasure_apply_measurable hi]

theorem toSignedMeasure_sub_apply {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {i : Set α} (hi : MeasurableSet i) :
    (μ.toSignedMeasure - ν.toSignedMeasure) i = μ.real i - ν.real i := by
  rw [_root_.sub_apply, toSignedMeasure_apply_measurable hi,
    Measure.toSignedMeasure_apply_measurable hi]

end Measure

namespace VectorMeasure

open Measure

section

/-- A vector measure over `ℝ≥0∞` is a measure. -/
def ennrealToMeasure {_ : MeasurableSpace α} (v : VectorMeasure α ℝ≥0∞) : Measure α :=
  ofMeasurable (fun s _ => v s) v.empty fun _ hf₁ hf₂ => v.of_disjoint_iUnion hf₁ hf₂

theorem ennrealToMeasure_apply {m : MeasurableSpace α} {v : VectorMeasure α ℝ≥0∞} {s : Set α}
    (hs : MeasurableSet s) : ennrealToMeasure v s = v s := by
  rw [ennrealToMeasure, ofMeasurable_apply _ hs]

@[simp]
theorem ennrealToMeasure_zero : ennrealToMeasure (0 : VectorMeasure α ℝ≥0∞) = 0 := by
  simp [ennrealToMeasure]

@[simp]
theorem _root_.MeasureTheory.Measure.toENNRealVectorMeasure_ennrealToMeasure
    (μ : VectorMeasure α ℝ≥0∞) :
    toENNRealVectorMeasure (ennrealToMeasure μ) = μ := ext fun s hs => by
  rw [toENNRealVectorMeasure_apply_measurable hs, ennrealToMeasure_apply hs]

@[simp]
theorem ennrealToMeasure_toENNRealVectorMeasure (μ : Measure α) :
    ennrealToMeasure (toENNRealVectorMeasure μ) = μ := Measure.ext fun s hs => by
  rw [ennrealToMeasure_apply hs, toENNRealVectorMeasure_apply_measurable hs]

/-- The equiv between `VectorMeasure α ℝ≥0∞` and `Measure α` formed by
`MeasureTheory.VectorMeasure.ennrealToMeasure` and
`MeasureTheory.Measure.toENNRealVectorMeasure`. -/
@[simps]
def equivMeasure [MeasurableSpace α] : VectorMeasure α ℝ≥0∞ ≃ Measure α where
  toFun := ennrealToMeasure
  invFun := toENNRealVectorMeasure
  left_inv := toENNRealVectorMeasure_ennrealToMeasure
  right_inv := ennrealToMeasure_toENNRealVectorMeasure

end

section

variable {mα : MeasurableSpace α} [MeasurableSpace β]
variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable (v : VectorMeasure α M)

open Classical in
/-- The pushforward of a vector measure along a function. -/
def map (v : VectorMeasure α M) (f : α → β) : VectorMeasure β M :=
  if hf : Measurable f then
    { measureOf' := fun s => if MeasurableSet s then v (f ⁻¹' s) else 0
      empty' := by simp
      not_measurable' := fun _ hi => if_neg hi
      m_iUnion' := by
        intro g hg₁ hg₂
        convert! v.m_iUnion (fun i => hf (hg₁ i)) fun i j hij => (hg₂ hij).preimage _
        · rw [if_pos (hg₁ _)]
        · rw [Set.preimage_iUnion, if_pos (MeasurableSet.iUnion hg₁)] }
  else 0

theorem map_not_measurable {f : α → β} (hf : ¬Measurable f) : v.map f = 0 :=
  dif_neg hf

theorem map_apply {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    v.map f s = v (f ⁻¹' s) := by
  rw [map, dif_pos hf]
  exact if_pos hs

@[simp]
theorem map_id : v.map id = v :=
  ext fun i hi => by rw [map_apply v measurable_id hi, Set.preimage_id]

@[simp]
theorem map_zero (f : α → β) : (0 : VectorMeasure α M).map f = 0 := by
  by_cases hf : Measurable f
  · ext i hi
    rw [map_apply _ hf hi, zero_apply, zero_apply]
  · exact dif_neg hf

section

variable {N : Type*} [AddCommMonoid N] [TopologicalSpace N]

/-- Given a vector measure `v` on `M` and a continuous `AddMonoidHom` `f : M → N`, `f ∘ v` is a
vector measure on `N`. -/
def mapRange (v : VectorMeasure α M) (f : M →+ N) (hf : Continuous f) : VectorMeasure α N where
  measureOf' s := f (v s)
  empty' := by rw [empty, AddMonoidHom.map_zero]
  not_measurable' i hi := by rw [not_measurable v hi, AddMonoidHom.map_zero]
  m_iUnion' _ hg₁ hg₂ := HasSum.map (v.m_iUnion hg₁ hg₂) f hf

@[simp]
theorem mapRange_apply {f : M →+ N} (hf : Continuous f) {s : Set α} : v.mapRange f hf s = f (v s) :=
  rfl

@[simp]
theorem mapRange_id : v.mapRange (AddMonoidHom.id M) continuous_id = v := by
  ext
  rfl

@[simp]
theorem mapRange_zero {f : M →+ N} (hf : Continuous f) :
    mapRange (0 : VectorMeasure α M) f hf = 0 := by
  ext
  simp

section ContinuousAdd

variable [ContinuousAdd M] [ContinuousAdd N]

@[simp]
theorem mapRange_add {v w : VectorMeasure α M} {f : M →+ N} (hf : Continuous f) :
    (v + w).mapRange f hf = v.mapRange f hf + w.mapRange f hf := by
  ext
  simp

/-- Given a continuous `AddMonoidHom` `f : M → N`, `mapRangeHom` is the `AddMonoidHom` mapping the
vector measure `v` on `M` to the vector measure `f ∘ v` on `N`. -/
def mapRangeHom {α : Type*} [MeasurableSpace α] (f : M →+ N) (hf : Continuous f) :
    VectorMeasure α M →+ VectorMeasure α N where
  toFun v := v.mapRange f hf
  map_zero' := mapRange_zero hf
  map_add' _ _ := mapRange_add hf

end ContinuousAdd

section Module

variable {R : Type*} [Semiring R] [Module R M] [Module R N]

variable [ContinuousConstSMul R M] [ContinuousConstSMul R N]

@[simp]
theorem mapRange_smul {v : VectorMeasure α M} {f : M →ₗ[R] N} (hf : Continuous f) {c : R} :
    (c • v).mapRange f.toAddMonoidHom hf = c • (v.mapRange f.toAddMonoidHom hf) := by
  ext; simp

variable [ContinuousAdd M] [ContinuousAdd N]

/-- Given a continuous linear map `f : M → N`, `mapRangeₗ` is the linear map mapping the
vector measure `v` on `M` to the vector measure `f ∘ v` on `N`. -/
def mapRangeₗ {α : Type*} [MeasurableSpace α] (f : M →ₗ[R] N) (hf : Continuous f) :
    VectorMeasure α M →ₗ[R] VectorMeasure α N where
  toFun v := v.mapRange f.toAddMonoidHom hf
  map_add' _ _ := mapRange_add hf
  map_smul' _ _ := mapRange_smul hf

end Module

end

open Classical in
/-- The restriction of a vector measure on some set. -/
@[no_expose] def restrict (v : VectorMeasure α M) (i : Set α) : VectorMeasure α M :=
  if hi : MeasurableSet i then
    { measureOf' := fun s => if MeasurableSet s then v (s ∩ i) else 0
      empty' := by simp
      not_measurable' := fun _ hi => if_neg hi
      m_iUnion' := by
        intro f hf₁ hf₂
        convert!
          v.m_iUnion (fun n => (hf₁ n).inter hi)
            (hf₂.mono fun i j => Disjoint.mono inf_le_left inf_le_left)
        · rw [if_pos (hf₁ _)]
        · rw [Set.iUnion_inter, if_pos (MeasurableSet.iUnion hf₁)] }
  else 0

theorem restrict_not_measurable {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0 :=
  dif_neg hi

theorem restrict_apply {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) :
    v.restrict i j = v (j ∩ i) := by
  rw [restrict, dif_pos hi]
  exact if_pos hj

theorem restrict_eq_self {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j)
    (hij : j ⊆ i) : v.restrict i j = v j := by
  rw [restrict_apply v hi hj, Set.inter_eq_left.2 hij]

@[simp]
theorem restrict_empty : v.restrict ∅ = 0 :=
  ext fun i hi => by
    rw [restrict_apply v MeasurableSet.empty hi, Set.inter_empty, v.empty, zero_apply]

@[simp]
theorem restrict_univ : v.restrict Set.univ = v :=
  ext fun i hi => by rw [restrict_apply v MeasurableSet.univ hi, Set.inter_univ]

@[simp]
theorem restrict_zero {i : Set α} : (0 : VectorMeasure α M).restrict i = 0 := by
  by_cases hi : MeasurableSet i
  · ext j hj
    rw [restrict_apply 0 hi hj, zero_apply, zero_apply]
  · exact dif_neg hi

theorem restrict_dirac {s : Set α} {x : α} {m : M} (hs : MeasurableSet s) [Decidable (x ∈ s)] :
    (dirac x m).restrict s = if x ∈ s then dirac x m else 0 := by
  classical
  ext t ht
  simp only [hs, ht, restrict_apply]
  split_ifs with has <;> simp [dirac, ht, ht.inter hs, has]

@[simp]
theorem restrict_dirac_of_mem {s : Set α} {x : α} {m : M} (hs : MeasurableSet s) (hx : x ∈ s) :
    (dirac x m).restrict s = dirac x m := by
  classical
  simp [restrict_dirac, hs, hx]

@[simp]
theorem restrict_dirac_of_notMem {s : Set α} {x : α} {m : M} (hx : x ∉ s) :
    (dirac x m).restrict s = 0 := by
  classical
  by_cases hs : MeasurableSet s
  · simp [restrict_dirac, hs, hx]
  · simp [restrict, hs]

@[simp]
theorem restrict_singleton {a : α} : v.restrict {a} = dirac a (v {a}) := by
  by_cases h : MeasurableSet {a}
  · ext s hs
    by_cases ha : a ∈ s <;> simp [*, restrict_apply]
  · simp [restrict, h]

theorem restrict_restrict {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (v.restrict t).restrict s = v.restrict (s ∩ t) := by
  ext u hu
  simp [restrict_apply, hs, hu, ht, Set.inter_assoc]

theorem restrict_map {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    (v.map f).restrict s = (v.restrict (f ⁻¹' s)).map f := by
  ext t ht
  simp [map_apply, hs, hf hs, restrict_apply, ht, hf, hf ht]

theorem restrict_toSignedMeasure {μ : Measure α} [IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s) :
    μ.toSignedMeasure.restrict s = (μ.restrict s).toSignedMeasure := by
  ext t ht
  rw [restrict_apply _ hs ht, Measure.toSignedMeasure_apply_measurable (ht.inter hs),
    Measure.toSignedMeasure_apply_measurable ht, measureReal_restrict_apply ht]

section ContinuousAdd

variable [ContinuousAdd M]

theorem map_add (v w : VectorMeasure α M) (f : α → β) : (v + w).map f = v.map f + w.map f := by
  by_cases hf : Measurable f
  · ext i hi
    simp [map_apply _ hf hi]
  · simp [map, dif_neg hf]

/-- `VectorMeasure.map` as an additive monoid homomorphism. -/
@[simps]
def mapGm {α : Type*} [MeasurableSpace α] (f : α → β) : VectorMeasure α M →+ VectorMeasure β M where
  toFun v := v.map f
  map_zero' := map_zero f
  map_add' _ _ := map_add _ _ f

@[simp]
theorem restrict_add (v w : VectorMeasure α M) (i : Set α) :
    (v + w).restrict i = v.restrict i + w.restrict i := by
  by_cases hi : MeasurableSet i
  · ext j hj
    simp [restrict_apply _ hi hj]
  · simp [restrict_not_measurable _ hi]

/-- `VectorMeasure.restrict` as an additive monoid homomorphism. -/
@[simps]
def restrictGm {α : Type*} [MeasurableSpace α] (i : Set α) :
    VectorMeasure α M →+ VectorMeasure α M where
  toFun v := v.restrict i
  map_zero' := restrict_zero
  map_add' _ _ := restrict_add _ _ i

end ContinuousAdd

section Partition

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [T2Space M] [ContinuousAdd M]
variable {v : VectorMeasure α M} {i s t : Set α}

@[simp]
theorem restrict_add_restrict_compl (hi : MeasurableSet i) :
    v.restrict i + v.restrict iᶜ = v := by
  ext A hA
  rw [_root_.add_apply, restrict_apply _ hi hA, restrict_apply _ hi.compl hA,
    ← of_union _ (hA.inter hi) (hA.inter hi.compl)]
  · simp
  · exact disjoint_compl_right.inter_right' A |>.inter_left' A

theorem restrict_inter_add_sdiff (hs : MeasurableSet s) (ht : MeasurableSet t) :
    v.restrict (s ∩ t) + v.restrict (s \ t) = v.restrict s := by
  ext u hu
  simp only [_root_.add_apply, restrict_apply, hs, hu, hs.inter ht, hs.diff ht]
  rw [← of_union (by grind) (hu.inter (hs.inter ht)) (hu.inter (hs.diff ht))]
  congr
  grind

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff := restrict_inter_add_sdiff

theorem restrict_union_add_inter (hs : MeasurableSet s) (ht : MeasurableSet t) :
    v.restrict (s ∪ t) + v.restrict (s ∩ t) = v.restrict s + v.restrict t := by
  rw [← v.restrict_inter_add_sdiff (hs.union ht) ht, union_inter_cancel_right, union_sdiff_right,
    ← v.restrict_inter_add_sdiff hs ht, add_comm, ← add_assoc, add_right_comm]

theorem restrict_union (h : Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    v.restrict (s ∪ t) = v.restrict s + v.restrict t := by
  simp [← v.restrict_union_add_inter hs ht, disjoint_iff_inter_eq_empty.mp h]

end Partition

section Sub

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

@[simp]
theorem restrict_neg (v : VectorMeasure α M) (i : Set α) :
    (-v).restrict i = -(v.restrict i) := by
  by_cases hi : MeasurableSet i
  · ext j hj; simp [restrict_apply _ hi hj]
  · simp [restrict_not_measurable _ hi]

@[simp]
theorem restrict_sub (v w : VectorMeasure α M) (i : Set α) :
    (v - w).restrict i = v.restrict i - w.restrict i := by
  simp [sub_eq_add_neg, restrict_add, restrict_neg]

end Sub

end

section

variable [MeasurableSpace β]
variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

@[simp]
theorem map_smul {v : VectorMeasure α M} {f : α → β} (c : R) : (c • v).map f = c • v.map f := by
  by_cases hf : Measurable f
  · ext i hi
    simp [map_apply _ hf hi]
  · simp only [map, dif_neg hf]
    -- `smul_zero` does not work since we do not require `ContinuousAdd`
    ext i
    simp

@[simp]
theorem restrict_smul {v : VectorMeasure α M} {i : Set α} (c : R) :
    (c • v).restrict i = c • v.restrict i := by
  by_cases hi : MeasurableSet i
  · ext j hj
    simp [restrict_apply _ hi hj]
  · simp only [restrict_not_measurable _ hi]
    -- `smul_zero` does not work since we do not require `ContinuousAdd`
    ext j
    simp

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

/-- `VectorMeasure.restrict` as an additive monoid homomorphism. -/
@[simps]
def restrictₗ (i : Set α) : VectorMeasure α M →ₗ[R] VectorMeasure α M where
  toFun v := v.restrict i
  map_add' _ _ := restrict_add _ _ i
  map_smul' _ _ := restrict_smul _

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]

/-- Vector measures over a partially ordered monoid is partially ordered.

This definition is consistent with `Measure.instPartialOrder`. -/
instance instPartialOrder : PartialOrder (VectorMeasure α M) where
  le v w := ∀ i, MeasurableSet i → v i ≤ w i
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ i hi := le_trans (h₁ i hi) (h₂ i hi)
  le_antisymm _ _ h₁ h₂ := ext fun i hi => le_antisymm (h₁ i hi) (h₂ i hi)

variable {v w : VectorMeasure α M}

theorem le_iff : v ≤ w ↔ ∀ i, MeasurableSet i → v i ≤ w i := Iff.rfl

theorem le_iff' : v ≤ w ↔ ∀ i, v i ≤ w i := by
  refine ⟨fun h i => ?_, fun h i _ => h i⟩
  by_cases hi : MeasurableSet i
  · exact h i hi
  · rw [v.not_measurable hi, w.not_measurable hi]

end

/-- `v ≤[i] w` is notation for `v.restrict i ≤ w.restrict i`. -/
scoped[MeasureTheory]
  notation3:50 v " ≤[" i:50 "] " w:50 =>
    MeasureTheory.VectorMeasure.restrict v i ≤ MeasureTheory.VectorMeasure.restrict w i

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]
variable (v w : VectorMeasure α M)

theorem restrict_le_restrict_iff {i : Set α} (hi : MeasurableSet i) :
    v ≤[i] w ↔ ∀ ⦃j⦄, MeasurableSet j → j ⊆ i → v j ≤ w j :=
  ⟨fun h j hj₁ hj₂ => restrict_eq_self v hi hj₁ hj₂ ▸ restrict_eq_self w hi hj₁ hj₂ ▸ h j hj₁,
    fun h => le_iff.1 fun _ hj =>
      (restrict_apply v hi hj).symm ▸ (restrict_apply w hi hj).symm ▸
      h (hj.inter hi) Set.inter_subset_right⟩

theorem subset_le_of_restrict_le_restrict {i : Set α} (hi : MeasurableSet i) (hi₂ : v ≤[i] w)
    {j : Set α} (hj : j ⊆ i) : v j ≤ w j := by
  by_cases hj₁ : MeasurableSet j
  · exact (restrict_le_restrict_iff _ _ hi).1 hi₂ hj₁ hj
  · rw [v.not_measurable hj₁, w.not_measurable hj₁]

theorem restrict_le_restrict_of_subset_le {i : Set α}
    (h : ∀ ⦃j⦄, MeasurableSet j → j ⊆ i → v j ≤ w j) : v ≤[i] w := by
  by_cases hi : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi).2 h
  · rw [restrict_not_measurable v hi, restrict_not_measurable w hi]

theorem restrict_le_restrict_subset {i j : Set α} (hi₁ : MeasurableSet i) (hi₂ : v ≤[i] w)
    (hij : j ⊆ i) : v ≤[j] w :=
  restrict_le_restrict_of_subset_le v w fun _ _ hk₂ =>
    subset_le_of_restrict_le_restrict v w hi₁ hi₂ (Set.Subset.trans hk₂ hij)

theorem le_restrict_empty : v ≤[∅] w := by
  simp

theorem le_restrict_univ_iff_le : v ≤[Set.univ] w ↔ v ≤ w := by
  simp

end

section

variable {M : Type*} [TopologicalSpace M]
  [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M] [IsTopologicalAddGroup M]
variable (v w : VectorMeasure α M)

nonrec theorem neg_le_neg {i : Set α} (hi : MeasurableSet i) (h : v ≤[i] w) : -w ≤[i] -v := by
  intro j hj₁
  rw [restrict_apply _ hi hj₁, restrict_apply _ hi hj₁, neg_apply, neg_apply]
  refine neg_le_neg ?_
  rw [← restrict_apply _ hi hj₁, ← restrict_apply _ hi hj₁]
  exact h j hj₁

theorem neg_le_neg_iff {i : Set α} (hi : MeasurableSet i) : -w ≤[i] -v ↔ v ≤[i] w :=
  ⟨fun h => neg_neg v ▸ neg_neg w ▸ neg_le_neg _ _ hi h, fun h => neg_le_neg _ _ hi h⟩

end

section

variable {M : Type*} [TopologicalSpace M]
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M] [OrderClosedTopology M]
variable (v w : VectorMeasure α M) {i j : Set α}

theorem restrict_le_restrict_iUnion {f : ℕ → Set α} (hf₁ : ∀ n, MeasurableSet (f n))
    (hf₂ : ∀ n, v ≤[f n] w) : v ≤[⋃ n, f n] w := by
  refine restrict_le_restrict_of_subset_le v w fun a ha₁ ha₂ => ?_
  have ha₃ : ⋃ n, a ∩ disjointed f n = a := by
    rwa [← Set.inter_iUnion, iUnion_disjointed, Set.inter_eq_left]
  have ha₄ : Pairwise (Disjoint on fun n => a ∩ disjointed f n) :=
    (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  rw [← ha₃, v.of_disjoint_iUnion _ ha₄, w.of_disjoint_iUnion _ ha₄]
  · refine Summable.tsum_le_tsum (fun n => (restrict_le_restrict_iff v w (hf₁ n)).1 (hf₂ n) ?_ ?_)
      ?_ ?_
    · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
    · exact Set.Subset.trans Set.inter_subset_right (disjointed_subset _ _)
    · refine (v.m_iUnion (fun n => ?_) ?_).summable
      · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
      · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
    · refine (w.m_iUnion (fun n => ?_) ?_).summable
      · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
      · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  · intro n
    exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
  · exact fun n => ha₁.inter (MeasurableSet.disjointed hf₁ n)

theorem restrict_le_restrict_countable_iUnion [Countable β] {f : β → Set α}
    (hf₁ : ∀ b, MeasurableSet (f b)) (hf₂ : ∀ b, v ≤[f b] w) : v ≤[⋃ b, f b] w := by
  cases nonempty_encodable β
  rw [← Encodable.iUnion_decode₂]
  refine restrict_le_restrict_iUnion v w ?_ ?_
  · intro n
    measurability
  · intro n
    rcases Encodable.decode₂ β n with - | b
    · simp
    · simp [hf₂ b]

theorem restrict_le_restrict_union (hi₁ : MeasurableSet i) (hi₂ : v ≤[i] w) (hj₁ : MeasurableSet j)
    (hj₂ : v ≤[j] w) : v ≤[i ∪ j] w := by
  rw [Set.union_eq_iUnion]
  refine restrict_le_restrict_countable_iUnion v w ?_ ?_
  · measurability
  · rintro (_ | _) <;> simpa

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]
variable (v w : VectorMeasure α M) {i j : Set α}

theorem nonneg_of_zero_le_restrict (hi₂ : 0 ≤[i] v) : 0 ≤ v i := by
  by_cases hi₁ : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
  · rw [v.not_measurable hi₁]

theorem nonpos_of_restrict_le_zero (hi₂ : v ≤[i] 0) : v i ≤ 0 := by
  by_cases hi₁ : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
  · rw [v.not_measurable hi₁]

theorem zero_le_restrict_not_measurable (hi : ¬MeasurableSet i) : 0 ≤[i] v := by
  rw [restrict_zero, restrict_not_measurable _ hi]

theorem restrict_le_zero_of_not_measurable (hi : ¬MeasurableSet i) : v ≤[i] 0 := by
  rw [restrict_zero, restrict_not_measurable _ hi]

theorem measurable_of_not_zero_le_restrict (hi : ¬0 ≤[i] v) : MeasurableSet i :=
  Not.imp_symm (zero_le_restrict_not_measurable _) hi

theorem measurable_of_not_restrict_le_zero (hi : ¬v ≤[i] 0) : MeasurableSet i :=
  Not.imp_symm (restrict_le_zero_of_not_measurable _) hi

theorem zero_le_restrict_subset (hi₁ : MeasurableSet i) (hij : j ⊆ i) (hi₂ : 0 ≤[i] v) : 0 ≤[j] v :=
  restrict_le_restrict_of_subset_le _ _ fun _ hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)

theorem restrict_le_zero_subset (hi₁ : MeasurableSet i) (hij : j ⊆ i) (hi₂ : v ≤[i] 0) : v ≤[j] 0 :=
  restrict_le_restrict_of_subset_le _ _ fun _ hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [LinearOrder M]
variable (v w : VectorMeasure α M) {i j : Set α}

theorem exists_pos_measure_of_not_restrict_le_zero (hi : ¬v ≤[i] 0) :
    ∃ j : Set α, MeasurableSet j ∧ j ⊆ i ∧ 0 < v j := by
  have hi₁ : MeasurableSet i := measurable_of_not_restrict_le_zero _ hi
  rw [restrict_le_restrict_iff _ _ hi₁] at hi
  push Not at hi
  exact hi

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]
  [AddLeftMono M] [ContinuousAdd M]

instance instAddLeftMono : AddLeftMono (VectorMeasure α M) :=
  ⟨fun _ _ _ h i hi => by simp only [_root_.add_apply]; grw [h i hi]⟩

end

section

variable {L M N : Type*}
variable [AddCommMonoid L] [TopologicalSpace L] [AddCommMonoid M] [TopologicalSpace M]
  [AddCommMonoid N] [TopologicalSpace N]

/-- A vector measure `v` is absolutely continuous with respect to a measure `μ` if for all sets
`s`, `μ s = 0`, we have `v s = 0`. -/
def AbsolutelyContinuous (v : VectorMeasure α M) (w : VectorMeasure α N) :=
  ∀ ⦃s : Set α⦄, w s = 0 → v s = 0

@[inherit_doc VectorMeasure.AbsolutelyContinuous]
scoped[MeasureTheory] infixl:50 " ≪ᵥ " => MeasureTheory.VectorMeasure.AbsolutelyContinuous

open MeasureTheory

namespace AbsolutelyContinuous

variable {v : VectorMeasure α M} {w : VectorMeasure α N}

theorem mk (h : ∀ ⦃s : Set α⦄, MeasurableSet s → w s = 0 → v s = 0) : v ≪ᵥ w := by
  intro s hs
  by_cases hmeas : MeasurableSet s
  · exact h hmeas hs
  · exact not_measurable v hmeas

theorem eq {w : VectorMeasure α M} (h : v = w) : v ≪ᵥ w :=
  fun _ hs => h.symm ▸ hs

@[refl]
theorem refl (v : VectorMeasure α M) : v ≪ᵥ v :=
  eq rfl

@[trans]
theorem trans {u : VectorMeasure α L} {v : VectorMeasure α M} {w : VectorMeasure α N} (huv : u ≪ᵥ v)
    (hvw : v ≪ᵥ w) : u ≪ᵥ w :=
  fun _ hs => huv <| hvw hs

theorem zero (v : VectorMeasure α N) : (0 : VectorMeasure α M) ≪ᵥ v :=
  fun s _ => zero_apply s

theorem neg_left {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : -v ≪ᵥ w := by
  intro s hs
  rw [neg_apply, h hs, neg_zero]

theorem neg_right {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : v ≪ᵥ -w := by
  intro s hs
  rw [neg_apply, neg_eq_zero] at hs
  exact h hs

theorem add [ContinuousAdd M] {v₁ v₂ : VectorMeasure α M} {w : VectorMeasure α N} (hv₁ : v₁ ≪ᵥ w)
    (hv₂ : v₂ ≪ᵥ w) : v₁ + v₂ ≪ᵥ w := by
  intro s hs
  rw [_root_.add_apply, hv₁ hs, hv₂ hs, zero_add]

theorem sub {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {v₁ v₂ : VectorMeasure α M} {w : VectorMeasure α N} (hv₁ : v₁ ≪ᵥ w) (hv₂ : v₂ ≪ᵥ w) :
    v₁ - v₂ ≪ᵥ w := by
  intro s hs
  rw [sub_apply, hv₁ hs, hv₂ hs, zero_sub, neg_zero]

theorem smul {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M] {r : R}
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : r • v ≪ᵥ w := by
  intro s hs
  rw [_root_.smul_apply, h hs, smul_zero]

theorem map [MeasureSpace β] (h : v ≪ᵥ w) (f : α → β) : v.map f ≪ᵥ w.map f := by
  by_cases hf : Measurable f
  · refine mk fun s hs hws => ?_
    rw [map_apply _ hf hs] at hws ⊢
    exact h hws
  · intro s _
    rw [map_not_measurable v hf, zero_apply]

theorem ennrealToMeasure {μ : VectorMeasure α ℝ≥0∞} :
    (∀ ⦃s : Set α⦄, μ.ennrealToMeasure s = 0 → v s = 0) ↔ v ≪ᵥ μ := by
  constructor <;> intro h
  · refine mk fun s hmeas hs => h ?_
    rw [← hs, ennrealToMeasure_apply hmeas]
  · intro s hs
    by_cases hmeas : MeasurableSet s
    · rw [ennrealToMeasure_apply hmeas] at hs
      exact h hs
    · exact not_measurable v hmeas

end AbsolutelyContinuous

/-- Two vector measures `v` and `w` are said to be mutually singular if there exists a measurable
set `s`, such that for all `t ⊆ s`, `v t = 0` and for all `t ⊆ sᶜ`, `w t = 0`.

We note that we do not require the measurability of `t` in the definition since this makes it easier
to use. This is equivalent to the definition which requires measurability. To prove
`MutuallySingular` with the measurability condition, use
`MeasureTheory.VectorMeasure.MutuallySingular.mk`. -/
def MutuallySingular (v : VectorMeasure α M) (w : VectorMeasure α N) : Prop :=
  ∃ s : Set α, MeasurableSet s ∧ (∀ t ⊆ s, v t = 0) ∧ ∀ t ⊆ sᶜ, w t = 0

@[inherit_doc VectorMeasure.MutuallySingular]
scoped[MeasureTheory] infixl:60 " ⟂ᵥ " => MeasureTheory.VectorMeasure.MutuallySingular

namespace MutuallySingular

variable {v v₁ v₂ : VectorMeasure α M} {w w₁ w₂ : VectorMeasure α N}

theorem mk (s : Set α) (hs : MeasurableSet s) (h₁ : ∀ t ⊆ s, MeasurableSet t → v t = 0)
    (h₂ : ∀ t ⊆ sᶜ, MeasurableSet t → w t = 0) : v ⟂ᵥ w := by
  refine ⟨s, hs, fun t hst => ?_, fun t hst => ?_⟩ <;> by_cases ht : MeasurableSet t
  · exact h₁ t hst ht
  · exact not_measurable v ht
  · exact h₂ t hst ht
  · exact not_measurable w ht

theorem symm (h : v ⟂ᵥ w) : w ⟂ᵥ v :=
  let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨sᶜ, hmeas.compl, hs₂, fun t ht => hs₁ _ (compl_compl s ▸ ht : t ⊆ s)⟩

theorem zero_right : v ⟂ᵥ (0 : VectorMeasure α N) :=
  ⟨∅, MeasurableSet.empty, fun _ ht => (Set.subset_empty_iff.1 ht).symm ▸ v.empty,
    fun _ _ => zero_apply _⟩

theorem zero_left : (0 : VectorMeasure α M) ⟂ᵥ w :=
  zero_right.symm

theorem add_left [T2Space N] [ContinuousAdd M] (h₁ : v₁ ⟂ᵥ w) (h₂ : v₂ ⟂ᵥ w) : v₁ + v₂ ⟂ᵥ w := by
  obtain ⟨u, hmu, hu₁, hu₂⟩ := h₁
  obtain ⟨v, hmv, hv₁, hv₂⟩ := h₂
  refine mk (u ∩ v) (hmu.inter hmv) (fun t ht _ => ?_) fun t ht hmt => ?_
  · rw [_root_.add_apply, hu₁ _ (Set.subset_inter_iff.1 ht).1, hv₁ _ (Set.subset_inter_iff.1 ht).2,
      zero_add]
  · rw [Set.compl_inter] at ht
    rw [(_ : t = uᶜ ∩ t ∪ vᶜ \ uᶜ ∩ t),
      of_union _ (hmu.compl.inter hmt) ((hmv.compl.diff hmu.compl).inter hmt), hu₂, hv₂, add_zero]
    · exact Set.Subset.trans Set.inter_subset_left sdiff_subset
    · exact Set.inter_subset_left
    · exact disjoint_sdiff_self_right.mono Set.inter_subset_left Set.inter_subset_left
    · apply Set.Subset.antisymm <;> intro x hx
      · by_cases hxu' : x ∈ uᶜ
        · exact Or.inl ⟨hxu', hx⟩
        rcases ht hx with (hxu | hxv)
        exacts [False.elim (hxu' hxu), Or.inr ⟨⟨hxv, hxu'⟩, hx⟩]
      · rcases hx with hx | hx <;> exact hx.2

theorem add_right [T2Space M] [ContinuousAdd N] (h₁ : v ⟂ᵥ w₁) (h₂ : v ⟂ᵥ w₂) : v ⟂ᵥ w₁ + w₂ :=
  (add_left h₁.symm h₂.symm).symm

theorem smul_right {R : Type*} [Semiring R] [DistribMulAction R N] [ContinuousConstSMul R N]
    (r : R) (h : v ⟂ᵥ w) : v ⟂ᵥ r • w :=
  let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨s, hmeas, hs₁, fun t ht => by simp only [_root_.smul_apply, hs₂ t ht, smul_zero]⟩

theorem smul_left {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M] (r : R)
    (h : v ⟂ᵥ w) : r • v ⟂ᵥ w :=
  (smul_right r h.symm).symm

theorem neg_left {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ⟂ᵥ w) : -v ⟂ᵥ w := by
  obtain ⟨u, hmu, hu₁, hu₂⟩ := h
  refine ⟨u, hmu, fun s hs => ?_, hu₂⟩
  rw [neg_apply v s, neg_eq_zero]
  exact hu₁ s hs

theorem neg_right {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ⟂ᵥ w) : v ⟂ᵥ -w :=
  h.symm.neg_left.symm

@[simp]
theorem neg_left_iff {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {v : VectorMeasure α M} {w : VectorMeasure α N} : -v ⟂ᵥ w ↔ v ⟂ᵥ w :=
  ⟨fun h => neg_neg v ▸ h.neg_left, neg_left⟩

@[simp]
theorem neg_right_iff {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    {v : VectorMeasure α M} {w : VectorMeasure α N} : v ⟂ᵥ -w ↔ v ⟂ᵥ w :=
  ⟨fun h => neg_neg w ▸ h.neg_right, neg_right⟩

end MutuallySingular

section Trim

open Classical in
/-- Restriction of a vector measure onto a sub-σ-algebra. -/
@[simps]
def trim {m n : MeasurableSpace α} (v : VectorMeasure α M) (hle : m ≤ n) :
    @VectorMeasure α m M _ _ :=
  @VectorMeasure.mk α m M _ _
    (fun i => if MeasurableSet[m] i then v i else 0)
    (by rw [if_pos (@MeasurableSet.empty _ m), v.empty])
    (fun i hi => by rw [if_neg hi])
    (fun f hf₁ hf₂ => by
      have hf₁' : ∀ k, MeasurableSet[n] (f k) := fun k => hle _ (hf₁ k)
      convert! v.m_iUnion hf₁' hf₂ using 1
      · ext n
        rw [if_pos (hf₁ n)]
      · rw [if_pos (@MeasurableSet.iUnion _ _ m _ _ hf₁)])

variable {n : MeasurableSpace α} {v : VectorMeasure α M}

theorem trim_eq_self : v.trim le_rfl = v := by
  ext i hi
  exact if_pos hi

@[simp]
theorem zero_trim (hle : m ≤ n) : (0 : VectorMeasure α M).trim hle = 0 := by
  ext i hi
  exact if_pos hi

theorem trim_measurableSet_eq (hle : m ≤ n) {i : Set α} (hi : MeasurableSet[m] i) :
    v.trim hle i = v i :=
  if_pos hi

theorem restrict_trim (hle : m ≤ n) {i : Set α} (hi : MeasurableSet[m] i) :
    @VectorMeasure.restrict α m M _ _ (v.trim hle) i = (v.restrict i).trim hle := by
  ext j hj
  rw [@restrict_apply _ m, trim_measurableSet_eq hle hj, restrict_apply, trim_measurableSet_eq]
  all_goals measurability

end Trim

end

end VectorMeasure

namespace SignedMeasure

open VectorMeasure

open MeasureTheory

/-- The underlying function for `SignedMeasure.toMeasureOfZeroLE`. -/
def toMeasureOfZeroLE' (s : SignedMeasure α) (i : Set α) (hi : 0 ≤[i] s) (j : Set α)
    (hj : MeasurableSet j) : ℝ≥0∞ :=
  ((↑) : ℝ≥0 → ℝ≥0∞) (.mk (s.restrict i j) (le_trans (by simp) (hi j hj)))

/-- Given a signed measure `s` and a positive measurable set `i`, `toMeasureOfZeroLE`
provides the measure, mapping measurable sets `j` to `s (i ∩ j)`. -/
def toMeasureOfZeroLE (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : 0 ≤[i] s) :
    Measure α := by
  refine Measure.ofMeasurable (s.toMeasureOfZeroLE' i hi₂) ?_ ?_
  · simp_rw [toMeasureOfZeroLE', s.restrict_apply hi₁ MeasurableSet.empty, Set.empty_inter i,
      s.empty]
    rfl
  · intro f hf₁ hf₂
    have h₁ : ∀ n, MeasurableSet (i ∩ f n) := fun n => hi₁.inter (hf₁ n)
    have h₂ : Pairwise (Disjoint on fun n : ℕ => i ∩ f n) := by
      intro n m hnm
      exact ((hf₂ hnm).inf_left' i).inf_right' i
    simp only [toMeasureOfZeroLE', s.restrict_apply hi₁ (MeasurableSet.iUnion hf₁), Set.inter_comm,
      Set.inter_iUnion, s.of_disjoint_iUnion h₁ h₂]
    have h : ∀ n, 0 ≤ s (i ∩ f n) := fun n =>
      s.nonneg_of_zero_le_restrict (s.zero_le_restrict_subset hi₁ Set.inter_subset_left hi₂)
    rw [NNReal.coe_tsum_of_nonneg h, ENNReal.coe_tsum]
    · refine tsum_congr fun n => ?_
      simp_rw [s.restrict_apply hi₁ (hf₁ n), Set.inter_comm]
    · exact (NNReal.summable_mk h).2 (s.m_iUnion h₁ h₂).summable

variable (s : SignedMeasure α) {i j : Set α}

theorem toMeasureOfZeroLE_apply (hi : 0 ≤[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) :
    s.toMeasureOfZeroLE i hi₁ hi j = ((↑) : ℝ≥0 → ℝ≥0∞) (.mk (s (i ∩ j)) (nonneg_of_zero_le_restrict
      s (zero_le_restrict_subset s hi₁ Set.inter_subset_left hi))) := by
  simp_rw [toMeasureOfZeroLE, Measure.ofMeasurable_apply _ hj₁, toMeasureOfZeroLE',
    s.restrict_apply hi₁ hj₁, Set.inter_comm]

theorem toMeasureOfZeroLE_real_apply (hi : 0 ≤[i] s) (hi₁ : MeasurableSet i)
    (hj₁ : MeasurableSet j) :
    (s.toMeasureOfZeroLE i hi₁ hi).real j = s (i ∩ j) := by
  simp [measureReal_def, toMeasureOfZeroLE_apply, hj₁]

/-- Given a signed measure `s` and a negative measurable set `i`, `toMeasureOfLEZero`
provides the measure, mapping measurable sets `j` to `-s (i ∩ j)`. -/
def toMeasureOfLEZero (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : s ≤[i] 0) :
    Measure α :=
  toMeasureOfZeroLE (-s) i hi₁ <| @neg_zero (VectorMeasure α ℝ) _ ▸ neg_le_neg _ _ hi₁ hi₂

theorem toMeasureOfLEZero_apply (hi : s ≤[i] 0) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) :
    s.toMeasureOfLEZero i hi₁ hi j =
    ((↑) : ℝ≥0 → ℝ≥0∞) (NNReal.mk (-s (i ∩ j)) (neg_apply s (i ∩ j) ▸
      nonneg_of_zero_le_restrict _ (zero_le_restrict_subset _ hi₁ Set.inter_subset_left
      (@neg_zero (VectorMeasure α ℝ) _ ▸ neg_le_neg _ _ hi₁ hi)))) := by
  simp [toMeasureOfLEZero, toMeasureOfZeroLE_apply _ _ _ hj₁]

theorem toMeasureOfLEZero_real_apply (hi : s ≤[i] 0) (hi₁ : MeasurableSet i)
    (hj₁ : MeasurableSet j) :
    (s.toMeasureOfLEZero i hi₁ hi).real j = -s (i ∩ j) := by
  simp [measureReal_def, toMeasureOfLEZero_apply _ hi hi₁ hj₁]

/-- `SignedMeasure.toMeasureOfZeroLE` is a finite measure. -/
instance toMeasureOfZeroLE_finite (hi : 0 ≤[i] s) (hi₁ : MeasurableSet i) :
    IsFiniteMeasure (s.toMeasureOfZeroLE i hi₁ hi) where
  measure_univ_lt_top := by
    rw [toMeasureOfZeroLE_apply s hi hi₁ MeasurableSet.univ]
    exact ENNReal.coe_lt_top

/-- `SignedMeasure.toMeasureOfLEZero` is a finite measure. -/
instance toMeasureOfLEZero_finite (hi : s ≤[i] 0) (hi₁ : MeasurableSet i) :
    IsFiniteMeasure (s.toMeasureOfLEZero i hi₁ hi) where
  measure_univ_lt_top := by
    rw [toMeasureOfLEZero_apply s hi hi₁ MeasurableSet.univ]
    exact ENNReal.coe_lt_top

theorem toMeasureOfZeroLE_toSignedMeasure (hs : 0 ≤[Set.univ] s) :
    (s.toMeasureOfZeroLE Set.univ MeasurableSet.univ hs).toSignedMeasure = s := by
  ext i hi
  simp [hi, toMeasureOfZeroLE_apply _ _ _ hi, measureReal_def]

theorem toMeasureOfLEZero_toSignedMeasure (hs : s ≤[Set.univ] 0) :
    (s.toMeasureOfLEZero Set.univ MeasurableSet.univ hs).toSignedMeasure = -s := by
  ext i hi
  simp [hi, toMeasureOfLEZero_apply _ _ _ hi, measureReal_def]

end SignedMeasure

namespace Measure

open VectorMeasure

variable (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (s : Set α)

theorem zero_le_toSignedMeasure : 0 ≤ μ.toSignedMeasure := by
  rw [← le_restrict_univ_iff_le]
  refine restrict_le_restrict_of_subset_le _ _ fun j hj₁ _ => ?_
  simp [hj₁]

theorem toSignedMeasure_toMeasureOfZeroLE :
    μ.toSignedMeasure.toMeasureOfZeroLE Set.univ MeasurableSet.univ
      ((le_restrict_univ_iff_le _ _).2 (zero_le_toSignedMeasure μ)) = μ := by
  refine Measure.ext fun i hi => ?_
  lift μ i to ℝ≥0 using (measure_lt_top _ _).ne with m hm
  rw [SignedMeasure.toMeasureOfZeroLE_apply _ _ _ hi, ENNReal.coe_inj]
  congr
  simp [hi, ← hm, measureReal_def]

theorem toSignedMeasure_restrict_eq_restrict_toSignedMeasure (hs : MeasurableSet s) :
    μ.toSignedMeasure.restrict s = (μ.restrict s).toSignedMeasure := by
  ext A hA
  simp [VectorMeasure.restrict_apply, hA, hs]

theorem toSignedMeasure_le_toSignedMeasure_iff :
    μ.toSignedMeasure ≤ ν.toSignedMeasure ↔ μ ≤ ν := by
  rw [Measure.le_iff, VectorMeasure.le_iff]
  congrm ∀ s, (hs : MeasurableSet s) → ?_
  simp_rw [toSignedMeasure_apply_measurable hs, real_def]
  apply ENNReal.toReal_le_toReal <;> finiteness

end Measure

end MeasureTheory
