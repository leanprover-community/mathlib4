/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.MeasureTheory.VectorMeasure.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Metrizable.Uniformity

/-!

# Basic API for vector measures

This file develops the basic consequences of countable additivity for vector measures, equips
vector measures with their natural algebraic structures, and defines Dirac vector measures.

## Main definitions

* `VectorMeasure.of_disjoint_iUnion` evaluates a vector measure on a disjoint countable union.
* The additive, scalar, and module structures on vector measures are defined pointwise.
* `VectorMeasure.dirac` is a Dirac vector measure.
-/

@[expose] public section

noncomputable section

open Filter

open scoped Topology Function -- required for scoped `on` notation
namespace MeasureTheory

variable {α β : Type*} {m : MeasurableSpace α}

open Set

namespace VectorMeasure

section

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

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
  have := hs.toEncodable
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
theorem ext_of_generateFrom {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
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
@[instance_reducible]
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
  ite_eq_left (And.intro hs hx)

@[simp] lemma dirac_apply_of_notMem (hx : x ∉ s) : dirac x v s = 0 := by
  simp [dirac, hx]

@[simp] lemma dirac_zero : dirac x (0 : M) = 0 := by
  ext s hs
  simp [dirac]

end Dirac

end VectorMeasure

end MeasureTheory
