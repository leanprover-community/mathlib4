/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module measure_theory.measure.haar.basic
! leanprover-community/mathlib commit fd5edc43dc4f10b85abfe544b88f82cf13c5f844
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.GroupTheory.Divisible
import Mathlib.Topology.Algebra.Group.Compact

/-!
# Haar measure

In this file we prove the existence and uniqueness (up to scalar multiples) of Haar measure
for a locally compact Hausdorff topological group.

For the construction, we follow the write-up by Jonathan Gleason,
*Existence and Uniqueness of Haar Measure*.
This is essentially the same argument as in
https://en.wikipedia.org/wiki/Haar_measure#A_construction_using_compact_subsets.

We construct the Haar measure first on compact sets. For this we define `(K : U)` as the (smallest)
number of left-translates of `U` that are needed to cover `K` (`index` in the formalization).
Then we define a function `h` on compact sets as `lim_U (K : U) / (K₀ : U)`,
where `U` becomes a smaller and smaller open neighborhood of `1`, and `K₀` is a fixed compact set
with nonempty interior. This function is `chaar` in the formalization, and we define the limit
formally using Tychonoff's theorem.

This function `h` forms a content, which we can extend to an outer measure and then a measure
(`haar_measure`).
We normalize the Haar measure so that the measure of `K₀` is `1`.
We show that for second countable spaces any left invariant Borel measure is a scalar multiple of
the Haar measure.

Note that `μ` need not coincide with `h` on compact sets, according to
[halmos1950measure, ch. X, §53 p.233]. However, we know that `h(K)` lies between `μ(Kᵒ)` and `μ(K)`,
where `ᵒ` denotes the interior.

## Main Declarations

* `haar_measure`: the Haar measure on a locally compact Hausdorff group. This is a left invariant
  regular measure. It takes as argument a compact set of the group (with non-empty interior),
  and is normalized so that the measure of the given set is 1.
* `haar_measure_self`: the Haar measure is normalized.
* `is_left_invariant_haar_measure`: the Haar measure is left invariant.
* `regular_haar_measure`: the Haar measure is a regular measure.
* `is_haar_measure_haar_measure`: the Haar measure satisfies the `is_haar_measure` typeclass, i.e.,
  it is invariant and gives finite mass to compact sets and positive mass to nonempty open sets.
* `haar` : some choice of a Haar measure, on a locally compact Hausdorff group, constructed as
  `haar_measure K` where `K` is some arbitrary choice of a compact set with nonempty interior.
* `haar_measure_unique`: Every σ-finite left invariant measure on a locally compact Hausdorff group
  is a scalar multiple of the Haar measure.

## References
* Paul Halmos (1950), Measure Theory, §53
* Jonathan Gleason, Existence and Uniqueness of Haar Measure
  - Note: step 9, page 8 contains a mistake: the last defined `μ` does not extend the `μ` on compact
    sets, see Halmos (1950) p. 233, bottom of the page. This makes some other steps (like step 11)
    invalid.
* https://en.wikipedia.org/wiki/Haar_measure
-/


noncomputable section

open Set Inv Function TopologicalSpace MeasurableSpace

open scoped NNReal Classical ENNReal Pointwise Topology

namespace MeasureTheory

namespace Measure

section Group

variable {G : Type _} [Group G]

/-! We put the internal functions in the construction of the Haar measure in a namespace,
  so that the chosen names don't clash with other declarations.
  We first define a couple of the functions before proving the properties (that require that `G`
  is a topological group). -/


namespace Haar

/-- The index or Haar covering number or ratio of `K` w.r.t. `V`, denoted `(K : V)`:
  it is the smallest number of (left) translates of `V` that is necessary to cover `K`.
  It is defined to be 0 if no finite number of translates cover `K`. -/
@[to_additive add_index "additive version of `measure_theory.measure.haar.index`"]
def index (K V : Set G) : ℕ :=
  sInf <| Finset.card '' { t : Finset G | K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V }
#align measure_theory.measure.haar.index MeasureTheory.Measure.Haar.index
#align measure_theory.measure.haar.add_index MeasureTheory.Measure.Haar.addIndex

@[to_additive add_index_empty]
theorem index_empty {V : Set G} : index ∅ V = 0 := by
  simp only [index, Nat.sInf_eq_zero]; left; use ∅
  simp only [Finset.card_empty, empty_subset, mem_set_of_eq, eq_self_iff_true, and_self_iff]
#align measure_theory.measure.haar.index_empty MeasureTheory.Measure.Haar.index_empty
#align measure_theory.measure.haar.add_index_empty MeasureTheory.Measure.Haar.add_index_empty

variable [TopologicalSpace G]

/-- `prehaar K₀ U K` is a weighted version of the index, defined as `(K : U)/(K₀ : U)`.
  In the applications `K₀` is compact with non-empty interior, `U` is open containing `1`,
  and `K` is any compact set.
  The argument `K` is a (bundled) compact set, so that we can consider `prehaar K₀ U` as an
  element of `haar_product` (below). -/
@[to_additive "additive version of `measure_theory.measure.haar.prehaar`"]
def prehaar (K₀ U : Set G) (K : Compacts G) : ℝ :=
  (index (K : Set G) U : ℝ) / index K₀ U
#align measure_theory.measure.haar.prehaar MeasureTheory.Measure.Haar.prehaar
#align measure_theory.measure.haar.add_prehaar MeasureTheory.Measure.Haar.addPrehaar

@[to_additive]
theorem prehaar_empty (K₀ : PositiveCompacts G) {U : Set G} : prehaar (K₀ : Set G) U ⊥ = 0 := by
  rw [prehaar, compacts.coe_bot, index_empty, Nat.cast_zero, zero_div]
#align measure_theory.measure.haar.prehaar_empty MeasureTheory.Measure.Haar.prehaar_empty
#align measure_theory.measure.haar.add_prehaar_empty MeasureTheory.Measure.Haar.add_prehaar_empty

@[to_additive]
theorem prehaar_nonneg (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G) :
    0 ≤ prehaar (K₀ : Set G) U K := by apply div_nonneg <;> norm_cast <;> apply zero_le
#align measure_theory.measure.haar.prehaar_nonneg MeasureTheory.Measure.Haar.prehaar_nonneg
#align measure_theory.measure.haar.add_prehaar_nonneg MeasureTheory.Measure.Haar.add_prehaar_nonneg

/-- `haar_product K₀` is the product of intervals `[0, (K : K₀)]`, for all compact sets `K`.
  For all `U`, we can show that `prehaar K₀ U ∈ haar_product K₀`. -/
@[to_additive "additive version of `measure_theory.measure.haar.haar_product`"]
def haarProduct (K₀ : Set G) : Set (Compacts G → ℝ) :=
  pi univ fun K => Icc 0 <| index (K : Set G) K₀
#align measure_theory.measure.haar.haar_product MeasureTheory.Measure.Haar.haarProduct
#align measure_theory.measure.haar.add_haar_product MeasureTheory.Measure.Haar.addHaarProduct

@[simp, to_additive]
theorem mem_prehaar_empty {K₀ : Set G} {f : Compacts G → ℝ} :
    f ∈ haarProduct K₀ ↔ ∀ K : Compacts G, f K ∈ Icc (0 : ℝ) (index (K : Set G) K₀) := by
  simp only [haar_product, pi, forall_prop_of_true, mem_univ, mem_set_of_eq]
#align measure_theory.measure.haar.mem_prehaar_empty MeasureTheory.Measure.Haar.mem_prehaar_empty
#align measure_theory.measure.haar.mem_add_prehaar_empty MeasureTheory.Measure.Haar.mem_add_prehaar_empty

/-- The closure of the collection of elements of the form `prehaar K₀ U`,
  for `U` open neighbourhoods of `1`, contained in `V`. The closure is taken in the space
  `compacts G → ℝ`, with the topology of pointwise convergence.
  We show that the intersection of all these sets is nonempty, and the Haar measure
  on compact sets is defined to be an element in the closure of this intersection. -/
@[to_additive "additive version of `measure_theory.measure.haar.cl_prehaar`"]
def clPrehaar (K₀ : Set G) (V : OpenNhdsOf (1 : G)) : Set (Compacts G → ℝ) :=
  closure <| prehaar K₀ '' { U : Set G | U ⊆ V.1 ∧ IsOpen U ∧ (1 : G) ∈ U }
#align measure_theory.measure.haar.cl_prehaar MeasureTheory.Measure.Haar.clPrehaar
#align measure_theory.measure.haar.cl_add_prehaar MeasureTheory.Measure.Haar.clAddPrehaar

variable [TopologicalGroup G]

/-!
### Lemmas about `index`
-/


/-- If `K` is compact and `V` has nonempty interior, then the index `(K : V)` is well-defined,
  there is a finite set `t` satisfying the desired properties. -/
@[to_additive add_index_defined
      "If `K` is compact and `V` has nonempty interior, then the index\n`(K : V)` is well-defined, there is a finite set `t` satisfying the desired properties."]
theorem index_defined {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty) :
    ∃ n : ℕ, n ∈ Finset.card '' { t : Finset G | K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V } := by
  rcases compact_covered_by_mul_left_translates hK hV with ⟨t, ht⟩; exact ⟨t.card, t, ht, rfl⟩
#align measure_theory.measure.haar.index_defined MeasureTheory.Measure.Haar.index_defined
#align measure_theory.measure.haar.add_index_defined MeasureTheory.Measure.Haar.add_index_defined

@[to_additive add_index_elim]
theorem index_elim {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty) :
    ∃ t : Finset G, (K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V) ∧ Finset.card t = index K V := by
  have := Nat.sInf_mem (index_defined hK hV); rwa [mem_image] at this
#align measure_theory.measure.haar.index_elim MeasureTheory.Measure.Haar.index_elim
#align measure_theory.measure.haar.add_index_elim MeasureTheory.Measure.Haar.add_index_elim

@[to_additive le_add_index_mul]
theorem le_index_mul (K₀ : PositiveCompacts G) (K : Compacts G) {V : Set G}
    (hV : (interior V).Nonempty) :
    index (K : Set G) V ≤ index (K : Set G) K₀ * index (K₀ : Set G) V := by
  obtain ⟨s, h1s, h2s⟩ := index_elim K.is_compact K₀.interior_nonempty
  obtain ⟨t, h1t, h2t⟩ := index_elim K₀.is_compact hV
  rw [← h2s, ← h2t, mul_comm]
  refine' le_trans _ Finset.card_mul_le
  apply Nat.sInf_le; refine' ⟨_, _, rfl⟩; rw [mem_set_of_eq]; refine' subset.trans h1s _
  apply Union₂_subset; intro g₁ hg₁; rw [preimage_subset_iff]; intro g₂ hg₂
  have := h1t hg₂
  rcases this with ⟨_, ⟨g₃, rfl⟩, A, ⟨hg₃, rfl⟩, h2V⟩; rw [mem_preimage, ← mul_assoc] at h2V
  exact mem_bUnion (Finset.mul_mem_mul hg₃ hg₁) h2V
#align measure_theory.measure.haar.le_index_mul MeasureTheory.Measure.Haar.le_index_mul
#align measure_theory.measure.haar.le_add_index_mul MeasureTheory.Measure.Haar.le_add_index_mul

@[to_additive add_index_pos]
theorem index_pos (K : PositiveCompacts G) {V : Set G} (hV : (interior V).Nonempty) :
    0 < index (K : Set G) V := by
  unfold index; rw [Nat.sInf_def, Nat.find_pos, mem_image]
  · rintro ⟨t, h1t, h2t⟩; rw [Finset.card_eq_zero] at h2t; subst h2t
    obtain ⟨g, hg⟩ := K.interior_nonempty
    show g ∈ (∅ : Set G); convert h1t (interior_subset hg); symm; apply bUnion_empty
  · exact index_defined K.is_compact hV
#align measure_theory.measure.haar.index_pos MeasureTheory.Measure.Haar.index_pos
#align measure_theory.measure.haar.add_index_pos MeasureTheory.Measure.Haar.add_index_pos

@[to_additive add_index_mono]
theorem index_mono {K K' V : Set G} (hK' : IsCompact K') (h : K ⊆ K') (hV : (interior V).Nonempty) :
    index K V ≤ index K' V := by
  rcases index_elim hK' hV with ⟨s, h1s, h2s⟩
  apply Nat.sInf_le; rw [mem_image]; refine' ⟨s, subset.trans h h1s, h2s⟩
#align measure_theory.measure.haar.index_mono MeasureTheory.Measure.Haar.index_mono
#align measure_theory.measure.haar.add_index_mono MeasureTheory.Measure.Haar.add_index_mono

@[to_additive add_index_union_le]
theorem index_union_le (K₁ K₂ : Compacts G) {V : Set G} (hV : (interior V).Nonempty) :
    index (K₁.1 ∪ K₂.1) V ≤ index K₁.1 V + index K₂.1 V := by
  rcases index_elim K₁.2 hV with ⟨s, h1s, h2s⟩
  rcases index_elim K₂.2 hV with ⟨t, h1t, h2t⟩
  rw [← h2s, ← h2t]
  refine' le_trans _ (Finset.card_union_le _ _)
  apply Nat.sInf_le; refine' ⟨_, _, rfl⟩; rw [mem_set_of_eq]
  apply union_subset <;> refine' subset.trans (by assumption) _ <;>
          apply bUnion_subset_bUnion_left <;>
        intro g hg <;>
      simp only [mem_def] at hg <;>
    simp only [mem_def, Multiset.mem_union, Finset.union_val, hg, or_true_iff, true_or_iff]
#align measure_theory.measure.haar.index_union_le MeasureTheory.Measure.Haar.index_union_le
#align measure_theory.measure.haar.add_index_union_le MeasureTheory.Measure.Haar.add_index_union_le

@[to_additive add_index_union_eq]
theorem index_union_eq (K₁ K₂ : Compacts G) {V : Set G} (hV : (interior V).Nonempty)
    (h : Disjoint (K₁.1 * V⁻¹) (K₂.1 * V⁻¹)) :
    index (K₁.1 ∪ K₂.1) V = index K₁.1 V + index K₂.1 V := by
  apply le_antisymm (index_union_le K₁ K₂ hV)
  rcases index_elim (K₁.2.union K₂.2) hV with ⟨s, h1s, h2s⟩; rw [← h2s]
  have :
    ∀ K : Set G,
      (K ⊆ ⋃ g ∈ s, (fun h => g * h) ⁻¹' V) →
        index K V ≤ (s.filter fun g => ((fun h : G => g * h) ⁻¹' V ∩ K).Nonempty).card := by
    intro K hK; apply Nat.sInf_le; refine' ⟨_, _, rfl⟩; rw [mem_set_of_eq]
    intro g hg; rcases hK hg with ⟨_, ⟨g₀, rfl⟩, _, ⟨h1g₀, rfl⟩, h2g₀⟩
    simp only [mem_preimage] at h2g₀
    simp only [mem_Union]; use g₀; constructor
    · simp only [Finset.mem_filter, h1g₀, true_and_iff]; use g
      simp only [hg, h2g₀, mem_inter_iff, mem_preimage, and_self_iff]
    exact h2g₀
  refine'
    le_trans
      (add_le_add (this K₁.1 <| subset.trans (subset_union_left _ _) h1s)
        (this K₂.1 <| subset.trans (subset_union_right _ _) h1s))
      _
  rw [← Finset.card_union_eq, Finset.filter_union_right]
  exact s.card_filter_le _
  apply finset.disjoint_filter.mpr
  rintro g₁ h1g₁ ⟨g₂, h1g₂, h2g₂⟩ ⟨g₃, h1g₃, h2g₃⟩
  simp only [mem_preimage] at h1g₃ h1g₂
  refine' h.le_bot (_ : g₁⁻¹ ∈ _)
  constructor <;> simp only [Set.mem_inv, Set.mem_mul, exists_exists_and_eq_and, exists_and_left]
  · refine' ⟨_, h2g₂, (g₁ * g₂)⁻¹, _, _⟩; simp only [inv_inv, h1g₂]
    simp only [mul_inv_rev, mul_inv_cancel_left]
  · refine' ⟨_, h2g₃, (g₁ * g₃)⁻¹, _, _⟩; simp only [inv_inv, h1g₃]
    simp only [mul_inv_rev, mul_inv_cancel_left]
#align measure_theory.measure.haar.index_union_eq MeasureTheory.Measure.Haar.index_union_eq
#align measure_theory.measure.haar.add_index_union_eq MeasureTheory.Measure.Haar.add_index_union_eq

@[to_additive add_left_add_index_le]
theorem mul_left_index_le {K : Set G} (hK : IsCompact K) {V : Set G} (hV : (interior V).Nonempty)
    (g : G) : index ((fun h => g * h) '' K) V ≤ index K V := by
  rcases index_elim hK hV with ⟨s, h1s, h2s⟩; rw [← h2s]
  apply Nat.sInf_le; rw [mem_image]
  refine' ⟨s.map (Equiv.mulRight g⁻¹).toEmbedding, _, Finset.card_map _⟩
  · simp only [mem_set_of_eq]; refine' subset.trans (image_subset _ h1s) _
    rintro _ ⟨g₁, ⟨_, ⟨g₂, rfl⟩, ⟨_, ⟨hg₂, rfl⟩, hg₁⟩⟩, rfl⟩
    simp only [mem_preimage] at hg₁;
    simp only [exists_prop, mem_Union, Finset.mem_map, Equiv.coe_mulRight, exists_exists_and_eq_and,
      mem_preimage, Equiv.toEmbedding_apply]
    refine' ⟨_, hg₂, _⟩; simp only [mul_assoc, hg₁, inv_mul_cancel_left]
#align measure_theory.measure.haar.mul_left_index_le MeasureTheory.Measure.Haar.mul_left_index_le
#align measure_theory.measure.haar.add_left_add_index_le MeasureTheory.Measure.Haar.add_left_add_index_le

@[to_additive is_left_invariant_add_index]
theorem is_left_invariant_index {K : Set G} (hK : IsCompact K) (g : G) {V : Set G}
    (hV : (interior V).Nonempty) : index ((fun h => g * h) '' K) V = index K V := by
  refine' le_antisymm (mul_left_index_le hK hV g) _
  convert mul_left_index_le (hK.image <| continuous_mul_left g) hV g⁻¹
  rw [image_image]; symm; convert image_id' _; ext h; apply inv_mul_cancel_left
#align measure_theory.measure.haar.is_left_invariant_index MeasureTheory.Measure.Haar.is_left_invariant_index
#align measure_theory.measure.haar.is_left_invariant_add_index MeasureTheory.Measure.Haar.is_left_invariant_add_index

/-!
### Lemmas about `prehaar`
-/


@[to_additive add_prehaar_le_add_index]
theorem prehaar_le_index (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G)
    (hU : (interior U).Nonempty) : prehaar (K₀ : Set G) U K ≤ index (K : Set G) K₀ := by
  unfold prehaar; rw [div_le_iff] <;> norm_cast
  · apply le_index_mul K₀ K hU
  · exact index_pos K₀ hU
#align measure_theory.measure.haar.prehaar_le_index MeasureTheory.Measure.Haar.prehaar_le_index
#align measure_theory.measure.haar.add_prehaar_le_add_index MeasureTheory.Measure.Haar.add_prehaar_le_add_index

@[to_additive]
theorem prehaar_pos (K₀ : PositiveCompacts G) {U : Set G} (hU : (interior U).Nonempty) {K : Set G}
    (h1K : IsCompact K) (h2K : (interior K).Nonempty) : 0 < prehaar (K₀ : Set G) U ⟨K, h1K⟩ := by
  apply div_pos <;> norm_cast; apply index_pos ⟨⟨K, h1K⟩, h2K⟩ hU; exact index_pos K₀ hU
#align measure_theory.measure.haar.prehaar_pos MeasureTheory.Measure.Haar.prehaar_pos
#align measure_theory.measure.haar.add_prehaar_pos MeasureTheory.Measure.Haar.add_prehaar_pos

@[to_additive]
theorem prehaar_mono {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty)
    {K₁ K₂ : Compacts G} (h : (K₁ : Set G) ⊆ K₂.1) :
    prehaar (K₀ : Set G) U K₁ ≤ prehaar (K₀ : Set G) U K₂ := by
  simp only [prehaar]; rw [div_le_div_right]; exact_mod_cast index_mono K₂.2 h hU
  exact_mod_cast index_pos K₀ hU
#align measure_theory.measure.haar.prehaar_mono MeasureTheory.Measure.Haar.prehaar_mono
#align measure_theory.measure.haar.add_prehaar_mono MeasureTheory.Measure.Haar.add_prehaar_mono

@[to_additive]
theorem prehaar_self {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty) :
    prehaar (K₀ : Set G) U K₀.toCompacts = 1 :=
  div_self <| ne_of_gt <| by exact_mod_cast index_pos K₀ hU
#align measure_theory.measure.haar.prehaar_self MeasureTheory.Measure.Haar.prehaar_self
#align measure_theory.measure.haar.add_prehaar_self MeasureTheory.Measure.Haar.add_prehaar_self

@[to_additive]
theorem prehaar_sup_le {K₀ : PositiveCompacts G} {U : Set G} (K₁ K₂ : Compacts G)
    (hU : (interior U).Nonempty) :
    prehaar (K₀ : Set G) U (K₁ ⊔ K₂) ≤ prehaar (K₀ : Set G) U K₁ + prehaar (K₀ : Set G) U K₂ := by
  simp only [prehaar]; rw [div_add_div_same, div_le_div_right]
  exact_mod_cast index_union_le K₁ K₂ hU; exact_mod_cast index_pos K₀ hU
#align measure_theory.measure.haar.prehaar_sup_le MeasureTheory.Measure.Haar.prehaar_sup_le
#align measure_theory.measure.haar.add_prehaar_sup_le MeasureTheory.Measure.Haar.add_prehaar_sup_le

@[to_additive]
theorem prehaar_sup_eq {K₀ : PositiveCompacts G} {U : Set G} {K₁ K₂ : Compacts G}
    (hU : (interior U).Nonempty) (h : Disjoint (K₁.1 * U⁻¹) (K₂.1 * U⁻¹)) :
    prehaar (K₀ : Set G) U (K₁ ⊔ K₂) = prehaar (K₀ : Set G) U K₁ + prehaar (K₀ : Set G) U K₂ := by
  simp only [prehaar]; rw [div_add_div_same]; congr ; exact_mod_cast index_union_eq K₁ K₂ hU h
#align measure_theory.measure.haar.prehaar_sup_eq MeasureTheory.Measure.Haar.prehaar_sup_eq
#align measure_theory.measure.haar.add_prehaar_sup_eq MeasureTheory.Measure.Haar.add_prehaar_sup_eq

@[to_additive]
theorem is_left_invariant_prehaar {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty)
    (g : G) (K : Compacts G) :
    prehaar (K₀ : Set G) U (K.map _ <| continuous_mul_left g) = prehaar (K₀ : Set G) U K := by
  simp only [prehaar, compacts.coe_map, is_left_invariant_index K.is_compact _ hU]
#align measure_theory.measure.haar.is_left_invariant_prehaar MeasureTheory.Measure.Haar.is_left_invariant_prehaar
#align measure_theory.measure.haar.is_left_invariant_add_prehaar MeasureTheory.Measure.Haar.is_left_invariant_add_prehaar

/-!
### Lemmas about `haar_product`
-/


@[to_additive]
theorem prehaar_mem_haarProduct (K₀ : PositiveCompacts G) {U : Set G} (hU : (interior U).Nonempty) :
    prehaar (K₀ : Set G) U ∈ haarProduct (K₀ : Set G) := by rintro ⟨K, hK⟩ h2K; rw [mem_Icc];
  exact ⟨prehaar_nonneg K₀ _, prehaar_le_index K₀ _ hU⟩
#align measure_theory.measure.haar.prehaar_mem_haar_product MeasureTheory.Measure.Haar.prehaar_mem_haarProduct
#align measure_theory.measure.haar.add_prehaar_mem_add_haar_product MeasureTheory.Measure.Haar.add_prehaar_mem_add_haarProduct

@[to_additive]
theorem nonempty_iInter_clPrehaar (K₀ : PositiveCompacts G) :
    (haarProduct (K₀ : Set G) ∩ ⋂ V : OpenNhdsOf (1 : G), clPrehaar K₀ V).Nonempty := by
  have : IsCompact (haar_product (K₀ : Set G)) := by apply isCompact_univ_pi; intro K;
    apply is_compact_Icc
  refine' this.inter_Inter_nonempty (cl_prehaar K₀) (fun s => isClosed_closure) fun t => _
  let V₀ := ⋂ V ∈ t, (V : open_nhds_of 1).carrier
  have h1V₀ : IsOpen V₀ := by apply isOpen_biInter; apply Finset.finite_toSet;
    rintro ⟨⟨V, hV₁⟩, hV₂⟩ h2V; exact hV₁
  have h2V₀ : (1 : G) ∈ V₀ := by simp only [mem_Inter]; rintro ⟨⟨V, hV₁⟩, hV₂⟩ h2V; exact hV₂
  refine' ⟨prehaar K₀ V₀, _⟩
  constructor
  · apply prehaar_mem_haar_product K₀; use 1; rwa [h1V₀.interior_eq]
  · simp only [mem_Inter]; rintro ⟨V, hV⟩ h2V; apply subset_closure
    apply mem_image_of_mem; rw [mem_set_of_eq]
    exact ⟨subset.trans (Inter_subset _ ⟨V, hV⟩) (Inter_subset _ h2V), h1V₀, h2V₀⟩
#align measure_theory.measure.haar.nonempty_Inter_cl_prehaar MeasureTheory.Measure.Haar.nonempty_iInter_clPrehaar
#align measure_theory.measure.haar.nonempty_Inter_cl_add_prehaar MeasureTheory.Measure.Haar.nonempty_iInter_cl_add_prehaar

/-!
### Lemmas about `chaar`
-/


/-- This is the "limit" of `prehaar K₀ U K` as `U` becomes a smaller and smaller open
  neighborhood of `(1 : G)`. More precisely, it is defined to be an arbitrary element
  in the intersection of all the sets `cl_prehaar K₀ V` in `haar_product K₀`.
  This is roughly equal to the Haar measure on compact sets,
  but it can differ slightly. We do know that
  `haar_measure K₀ (interior K) ≤ chaar K₀ K ≤ haar_measure K₀ K`. -/
@[to_additive add_chaar "additive version of `measure_theory.measure.haar.chaar`"]
def chaar (K₀ : PositiveCompacts G) (K : Compacts G) : ℝ :=
  Classical.choose (nonempty_iInter_clPrehaar K₀) K
#align measure_theory.measure.haar.chaar MeasureTheory.Measure.Haar.chaar
#align measure_theory.measure.haar.add_chaar MeasureTheory.Measure.Haar.addChaar

@[to_additive add_chaar_mem_add_haar_product]
theorem chaar_mem_haarProduct (K₀ : PositiveCompacts G) : chaar K₀ ∈ haarProduct (K₀ : Set G) :=
  (Classical.choose_spec (nonempty_iInter_clPrehaar K₀)).1
#align measure_theory.measure.haar.chaar_mem_haar_product MeasureTheory.Measure.Haar.chaar_mem_haarProduct
#align measure_theory.measure.haar.add_chaar_mem_add_haar_product MeasureTheory.Measure.Haar.add_chaar_mem_add_haarProduct

@[to_additive add_chaar_mem_cl_add_prehaar]
theorem chaar_mem_clPrehaar (K₀ : PositiveCompacts G) (V : OpenNhdsOf (1 : G)) :
    chaar K₀ ∈ clPrehaar (K₀ : Set G) V := by
  have := (Classical.choose_spec (nonempty_Inter_cl_prehaar K₀)).2; rw [mem_Inter] at this
  exact this V
#align measure_theory.measure.haar.chaar_mem_cl_prehaar MeasureTheory.Measure.Haar.chaar_mem_clPrehaar
#align measure_theory.measure.haar.add_chaar_mem_cl_add_prehaar MeasureTheory.Measure.Haar.add_chaar_mem_cl_add_prehaar

@[to_additive add_chaar_nonneg]
theorem chaar_nonneg (K₀ : PositiveCompacts G) (K : Compacts G) : 0 ≤ chaar K₀ K := by
  have := chaar_mem_haar_product K₀ K (mem_univ _); rw [mem_Icc] at this; exact this.1
#align measure_theory.measure.haar.chaar_nonneg MeasureTheory.Measure.Haar.chaar_nonneg
#align measure_theory.measure.haar.add_chaar_nonneg MeasureTheory.Measure.Haar.add_chaar_nonneg

@[to_additive add_chaar_empty]
theorem chaar_empty (K₀ : PositiveCompacts G) : chaar K₀ ⊥ = 0 := by
  let eval : (compacts G → ℝ) → ℝ := fun f => f ⊥
  have : Continuous eval := continuous_apply ⊥
  show chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)}
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⊤)
  unfold cl_prehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩; apply prehaar_empty
  · apply continuous_iff_is_closed.mp this; exact isClosed_singleton
#align measure_theory.measure.haar.chaar_empty MeasureTheory.Measure.Haar.chaar_empty
#align measure_theory.measure.haar.add_chaar_empty MeasureTheory.Measure.Haar.add_chaar_empty

@[to_additive add_chaar_self]
theorem chaar_self (K₀ : PositiveCompacts G) : chaar K₀ K₀.toCompacts = 1 := by
  let eval : (compacts G → ℝ) → ℝ := fun f => f K₀.to_compacts
  have : Continuous eval := continuous_apply _
  show chaar K₀ ∈ eval ⁻¹' {(1 : ℝ)}
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⊤)
  unfold cl_prehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩; apply prehaar_self
    rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_is_closed.mp this; exact isClosed_singleton
#align measure_theory.measure.haar.chaar_self MeasureTheory.Measure.Haar.chaar_self
#align measure_theory.measure.haar.add_chaar_self MeasureTheory.Measure.Haar.add_chaar_self

@[to_additive add_chaar_mono]
theorem chaar_mono {K₀ : PositiveCompacts G} {K₁ K₂ : Compacts G} (h : (K₁ : Set G) ⊆ K₂) :
    chaar K₀ K₁ ≤ chaar K₀ K₂ := by
  let eval : (compacts G → ℝ) → ℝ := fun f => f K₂ - f K₁
  have : Continuous eval := (continuous_apply K₂).sub (continuous_apply K₁)
  rw [← sub_nonneg]; show chaar K₀ ∈ eval ⁻¹' Ici (0 : ℝ)
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⊤)
  unfold cl_prehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩; simp only [mem_preimage, mem_Ici, eval, sub_nonneg]
    apply prehaar_mono _ h; rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_is_closed.mp this; exact isClosed_Ici
#align measure_theory.measure.haar.chaar_mono MeasureTheory.Measure.Haar.chaar_mono
#align measure_theory.measure.haar.add_chaar_mono MeasureTheory.Measure.Haar.add_chaar_mono

@[to_additive add_chaar_sup_le]
theorem chaar_sup_le {K₀ : PositiveCompacts G} (K₁ K₂ : Compacts G) :
    chaar K₀ (K₁ ⊔ K₂) ≤ chaar K₀ K₁ + chaar K₀ K₂ := by
  let eval : (compacts G → ℝ) → ℝ := fun f => f K₁ + f K₂ - f (K₁ ⊔ K₂)
  have : Continuous eval :=
    ((@continuous_add ℝ _ _ _).comp ((continuous_apply K₁).prod_mk (continuous_apply K₂))).sub
      (continuous_apply (K₁ ⊔ K₂))
  rw [← sub_nonneg]; show chaar K₀ ∈ eval ⁻¹' Ici (0 : ℝ)
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⊤)
  unfold cl_prehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩; simp only [mem_preimage, mem_Ici, eval, sub_nonneg]
    apply prehaar_sup_le; rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_is_closed.mp this; exact isClosed_Ici
#align measure_theory.measure.haar.chaar_sup_le MeasureTheory.Measure.Haar.chaar_sup_le
#align measure_theory.measure.haar.add_chaar_sup_le MeasureTheory.Measure.Haar.add_chaar_sup_le

@[to_additive add_chaar_sup_eq]
theorem chaar_sup_eq [T2Space G] {K₀ : PositiveCompacts G} {K₁ K₂ : Compacts G}
    (h : Disjoint K₁.1 K₂.1) : chaar K₀ (K₁ ⊔ K₂) = chaar K₀ K₁ + chaar K₀ K₂ := by
  rcases isCompact_isCompact_separated K₁.2 K₂.2 h with ⟨U₁, U₂, h1U₁, h1U₂, h2U₁, h2U₂, hU⟩
  rcases compact_open_separated_mul_right K₁.2 h1U₁ h2U₁ with ⟨L₁, h1L₁, h2L₁⟩
  rcases mem_nhds_iff.mp h1L₁ with ⟨V₁, h1V₁, h2V₁, h3V₁⟩
  replace h2L₁ := subset.trans (mul_subset_mul_left h1V₁) h2L₁
  rcases compact_open_separated_mul_right K₂.2 h1U₂ h2U₂ with ⟨L₂, h1L₂, h2L₂⟩
  rcases mem_nhds_iff.mp h1L₂ with ⟨V₂, h1V₂, h2V₂, h3V₂⟩
  replace h2L₂ := subset.trans (mul_subset_mul_left h1V₂) h2L₂
  let eval : (compacts G → ℝ) → ℝ := fun f => f K₁ + f K₂ - f (K₁ ⊔ K₂)
  have : Continuous eval :=
    ((@continuous_add ℝ _ _ _).comp ((continuous_apply K₁).prod_mk (continuous_apply K₂))).sub
      (continuous_apply (K₁ ⊔ K₂))
  rw [eq_comm, ← sub_eq_zero]; show chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)}
  let V := V₁ ∩ V₂
  apply
    mem_of_subset_of_mem _
      (chaar_mem_cl_prehaar K₀
        ⟨⟨V⁻¹, (h2V₁.inter h2V₂).Preimage continuous_inv⟩, by
          simp only [mem_inv, inv_one, h3V₁, h3V₂, V, mem_inter_iff, true_and_iff]⟩)
  unfold cl_prehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩
    simp only [mem_preimage, eval, sub_eq_zero, mem_singleton_iff]; rw [eq_comm]
    apply prehaar_sup_eq
    · rw [h2U.interior_eq]; exact ⟨1, h3U⟩
    · refine' disjoint_of_subset _ _ hU
      · refine' subset.trans (mul_subset_mul subset.rfl _) h2L₁
        exact subset.trans (inv_subset.mpr h1U) (inter_subset_left _ _)
      · refine' subset.trans (mul_subset_mul subset.rfl _) h2L₂
        exact subset.trans (inv_subset.mpr h1U) (inter_subset_right _ _)
  · apply continuous_iff_is_closed.mp this; exact isClosed_singleton
#align measure_theory.measure.haar.chaar_sup_eq MeasureTheory.Measure.Haar.chaar_sup_eq
#align measure_theory.measure.haar.add_chaar_sup_eq MeasureTheory.Measure.Haar.add_chaar_sup_eq

@[to_additive is_left_invariant_add_chaar]
theorem is_left_invariant_chaar {K₀ : PositiveCompacts G} (g : G) (K : Compacts G) :
    chaar K₀ (K.map _ <| continuous_mul_left g) = chaar K₀ K := by
  let eval : (compacts G → ℝ) → ℝ := fun f => f (K.map _ <| continuous_mul_left g) - f K
  have : Continuous eval := (continuous_apply (K.map _ _)).sub (continuous_apply K)
  rw [← sub_eq_zero]; show chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)}
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⊤)
  unfold cl_prehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩
    simp only [mem_singleton_iff, mem_preimage, eval, sub_eq_zero]
    apply is_left_invariant_prehaar; rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_is_closed.mp this; exact isClosed_singleton
#align measure_theory.measure.haar.is_left_invariant_chaar MeasureTheory.Measure.Haar.is_left_invariant_chaar
#align measure_theory.measure.haar.is_left_invariant_add_chaar MeasureTheory.Measure.Haar.is_left_invariant_add_chaar

variable [T2Space G]

/-- The function `chaar` interpreted in `ℝ≥0`, as a content -/
@[to_additive "additive version of `measure_theory.measure.haar.haar_content`"]
def haarContent (K₀ : PositiveCompacts G) : Content G where
  toFun K := ⟨chaar K₀ K, chaar_nonneg _ _⟩
  mono' K₁ K₂ h := by simp only [← NNReal.coe_le_coe, Subtype.coe_mk, chaar_mono, h]
  sup_disjoint' K₁ K₂ h := by simp only [chaar_sup_eq h]; rfl
  sup_le' K₁ K₂ := by simp only [← NNReal.coe_le_coe, NNReal.coe_add, Subtype.coe_mk, chaar_sup_le]
#align measure_theory.measure.haar.haar_content MeasureTheory.Measure.Haar.haarContent
#align measure_theory.measure.haar.add_haar_content MeasureTheory.Measure.Haar.addHaarContent

/-! We only prove the properties for `haar_content` that we use at least twice below. -/


@[to_additive]
theorem haarContent_apply (K₀ : PositiveCompacts G) (K : Compacts G) :
    haarContent K₀ K = show NNReal from ⟨chaar K₀ K, chaar_nonneg _ _⟩ :=
  rfl
#align measure_theory.measure.haar.haar_content_apply MeasureTheory.Measure.Haar.haarContent_apply
#align measure_theory.measure.haar.add_haar_content_apply MeasureTheory.Measure.Haar.add_haar_content_apply

/-- The variant of `chaar_self` for `haar_content` -/
@[to_additive "The variant of `add_chaar_self` for `add_haar_content`."]
theorem haarContent_self {K₀ : PositiveCompacts G} : haarContent K₀ K₀.toCompacts = 1 := by
  simp_rw [← ENNReal.coe_one, haar_content_apply, ENNReal.coe_eq_coe, chaar_self]; rfl
#align measure_theory.measure.haar.haar_content_self MeasureTheory.Measure.Haar.haarContent_self
#align measure_theory.measure.haar.add_haar_content_self MeasureTheory.Measure.Haar.add_haarContent_self

/-- The variant of `is_left_invariant_chaar` for `haar_content` -/
@[to_additive "The variant of `is_left_invariant_add_chaar` for `add_haar_content`"]
theorem is_left_invariant_haarContent {K₀ : PositiveCompacts G} (g : G) (K : Compacts G) :
    haarContent K₀ (K.map _ <| continuous_mul_left g) = haarContent K₀ K := by
  simpa only [ENNReal.coe_eq_coe, ← NNReal.coe_eq, haar_content_apply] using
    is_left_invariant_chaar g K
#align measure_theory.measure.haar.is_left_invariant_haar_content MeasureTheory.Measure.Haar.is_left_invariant_haarContent
#align measure_theory.measure.haar.is_left_invariant_add_haar_content MeasureTheory.Measure.Haar.is_left_invariant_add_haarContent

@[to_additive]
theorem haarContent_outerMeasure_self_pos {K₀ : PositiveCompacts G} :
    0 < (haarContent K₀).OuterMeasure K₀ := by
  refine' zero_lt_one.trans_le _
  rw [content.outer_measure_eq_infi]
  refine' le_iInf₂ fun U hU => le_iInf fun hK₀ => le_trans _ <| le_iSup₂ K₀.to_compacts hK₀
  exact haar_content_self.ge
#align measure_theory.measure.haar.haar_content_outer_measure_self_pos MeasureTheory.Measure.Haar.haarContent_outerMeasure_self_pos
#align measure_theory.measure.haar.add_haar_content_outer_measure_self_pos MeasureTheory.Measure.Haar.add_haarContent_outerMeasure_self_pos

end Haar

open Haar

/-!
### The Haar measure
-/


variable [TopologicalSpace G] [T2Space G] [TopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- The Haar measure on the locally compact group `G`, scaled so that `haar_measure K₀ K₀ = 1`. -/
@[to_additive
      "The Haar measure on the locally compact additive group `G`,\nscaled so that `add_haar_measure K₀ K₀ = 1`."]
def haarMeasure (K₀ : PositiveCompacts G) : Measure G :=
  ((haarContent K₀).OuterMeasure K₀)⁻¹ • (haarContent K₀).Measure
#align measure_theory.measure.haar_measure MeasureTheory.Measure.haarMeasure
#align measure_theory.measure.add_haar_measure MeasureTheory.Measure.addHaarMeasure

@[to_additive]
theorem haarMeasure_apply {K₀ : PositiveCompacts G} {s : Set G} (hs : MeasurableSet s) :
    haarMeasure K₀ s = (haarContent K₀).OuterMeasure s / (haarContent K₀).OuterMeasure K₀ := by
  change ((haar_content K₀).OuterMeasure K₀)⁻¹ * (haar_content K₀).Measure s = _
  simp only [hs, div_eq_mul_inv, mul_comm, content.measure_apply]
#align measure_theory.measure.haar_measure_apply MeasureTheory.Measure.haarMeasure_apply
#align measure_theory.measure.add_haar_measure_apply MeasureTheory.Measure.add_haarMeasure_apply

@[to_additive]
instance isMulLeftInvariant_haarMeasure (K₀ : PositiveCompacts G) :
    IsMulLeftInvariant (haarMeasure K₀) := by
  rw [← forall_measure_preimage_mul_iff]
  intro g A hA
  rw [haar_measure_apply hA, haar_measure_apply (measurable_const_mul g hA)]
  congr 1
  apply content.is_mul_left_invariant_outer_measure
  apply is_left_invariant_haar_content
#align measure_theory.measure.is_mul_left_invariant_haar_measure MeasureTheory.Measure.isMulLeftInvariant_haarMeasure
#align measure_theory.measure.is_add_left_invariant_add_haar_measure MeasureTheory.Measure.is_add_left_invariant_add_haarMeasure

@[to_additive]
theorem haarMeasure_self {K₀ : PositiveCompacts G} : haarMeasure K₀ K₀ = 1 := by
  haveI : LocallyCompactSpace G := K₀.locally_compact_space_of_group
  rw [haar_measure_apply K₀.is_compact.measurable_set, ENNReal.div_self]
  · rw [← pos_iff_ne_zero]; exact haar_content_outer_measure_self_pos
  · exact (content.outer_measure_lt_top_of_is_compact _ K₀.is_compact).Ne
#align measure_theory.measure.haar_measure_self MeasureTheory.Measure.haarMeasure_self
#align measure_theory.measure.add_haar_measure_self MeasureTheory.Measure.add_haarMeasure_self

/-- The Haar measure is regular. -/
@[to_additive "The additive Haar measure is regular."]
instance regular_haarMeasure {K₀ : PositiveCompacts G} : (haarMeasure K₀).regular := by
  haveI : LocallyCompactSpace G := K₀.locally_compact_space_of_group
  apply regular.smul
  rw [ENNReal.inv_ne_top]
  exact haar_content_outer_measure_self_pos.ne'
#align measure_theory.measure.regular_haar_measure MeasureTheory.Measure.regular_haarMeasure
#align measure_theory.measure.regular_add_haar_measure MeasureTheory.Measure.regular_add_haarMeasure

/-- The Haar measure is sigma-finite in a second countable group. -/
@[to_additive "The additive Haar measure is sigma-finite in a second countable group."]
instance sigmaFinite_haarMeasure [SecondCountableTopology G] {K₀ : PositiveCompacts G} :
    SigmaFinite (haarMeasure K₀) := by
  haveI : LocallyCompactSpace G := K₀.locally_compact_space_of_group; infer_instance
#align measure_theory.measure.sigma_finite_haar_measure MeasureTheory.Measure.sigmaFinite_haarMeasure
#align measure_theory.measure.sigma_finite_add_haar_measure MeasureTheory.Measure.sigmaFinite_add_haarMeasure

/-- The Haar measure is a Haar measure, i.e., it is invariant and gives finite mass to compact
sets and positive mass to nonempty open sets. -/
@[to_additive
      "The additive Haar measure is an additive Haar measure, i.e., it is invariant and\ngives  finite mass to compact sets and positive mass to nonempty open sets."]
instance isHaarMeasure_haarMeasure (K₀ : PositiveCompacts G) : IsHaarMeasure (haarMeasure K₀) := by
  apply
    is_haar_measure_of_is_compact_nonempty_interior (haar_measure K₀) K₀ K₀.is_compact
      K₀.interior_nonempty
  · simp only [haar_measure_self]; exact one_ne_zero
  · simp only [haar_measure_self]; exact ENNReal.coe_ne_top
#align measure_theory.measure.is_haar_measure_haar_measure MeasureTheory.Measure.isHaarMeasure_haarMeasure
#align measure_theory.measure.is_add_haar_measure_add_haar_measure MeasureTheory.Measure.is_add_haarMeasure_add_haarMeasure

/-- `haar` is some choice of a Haar measure, on a locally compact group. -/
@[reducible,
  to_additive "`add_haar` is some choice of a Haar measure, on a locally compact\nadditive group."]
def haar [LocallyCompactSpace G] : Measure G :=
  haarMeasure <| Classical.arbitrary _
#align measure_theory.measure.haar MeasureTheory.Measure.haar
#align measure_theory.measure.add_haar MeasureTheory.Measure.addHaar

section SecondCountable

variable [SecondCountableTopology G]

/-- The Haar measure is unique up to scaling. More precisely: every σ-finite left invariant measure
  is a scalar multiple of the Haar measure.
  This is slightly weaker than assuming that `μ` is a Haar measure (in particular we don't require
  `μ ≠ 0`). -/
@[to_additive
      "The additive Haar measure is unique up to scaling. More precisely: every σ-finite\nleft invariant measure is a scalar multiple of the additive Haar measure. This is slightly weaker\nthan assuming that `μ` is an additive Haar measure (in particular we don't require `μ ≠ 0`)."]
theorem haarMeasure_unique (μ : Measure G) [SigmaFinite μ] [IsMulLeftInvariant μ]
    (K₀ : PositiveCompacts G) : μ = μ K₀ • haarMeasure K₀ :=
  (measure_eq_div_smul μ (haarMeasure K₀) K₀.IsCompact.MeasurableSet
        (measure_pos_of_nonempty_interior _ K₀.interior_nonempty).ne'
        K₀.IsCompact.measure_lt_top.Ne).trans
    (by rw [haar_measure_self, div_one])
#align measure_theory.measure.haar_measure_unique MeasureTheory.Measure.haarMeasure_unique
#align measure_theory.measure.add_haar_measure_unique MeasureTheory.Measure.add_haar_measure_unique

example [LocallyCompactSpace G] (μ : Measure G) [IsHaarMeasure μ] (K₀ : PositiveCompacts G) :
    μ = μ K₀.1 • haarMeasure K₀ :=
  haarMeasure_unique μ K₀

/-- To show that an invariant σ-finite measure is regular it is sufficient to show that it is finite
  on some compact set with non-empty interior. -/
@[to_additive
      "To show that an invariant σ-finite measure is regular it is sufficient to show that\nit is finite on some compact set with non-empty interior."]
theorem regular_of_isMulLeftInvariant {μ : Measure G} [SigmaFinite μ] [IsMulLeftInvariant μ]
    {K : Set G} (hK : IsCompact K) (h2K : (interior K).Nonempty) (hμK : μ K ≠ ∞) : Regular μ := by
  rw [haar_measure_unique μ ⟨⟨K, hK⟩, h2K⟩]; exact regular.smul hμK
#align measure_theory.measure.regular_of_is_mul_left_invariant MeasureTheory.Measure.regular_of_isMulLeftInvariant
#align measure_theory.measure.regular_of_is_add_left_invariant MeasureTheory.Measure.regular_of_is_add_left_invariant

@[to_additive is_add_haar_measure_eq_smul_is_add_haar_measure]
theorem isHaarMeasure_eq_smul_isHaarMeasure [LocallyCompactSpace G] (μ ν : Measure G)
    [IsHaarMeasure μ] [IsHaarMeasure ν] : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = c • ν := by
  have K : positive_compacts G := Classical.arbitrary _
  have νpos : 0 < ν K := measure_pos_of_nonempty_interior _ K.interior_nonempty
  have νne : ν K ≠ ∞ := K.is_compact.measure_lt_top.ne
  refine' ⟨μ K / ν K, _, _, _⟩
  ·
    simp only [νne, (μ.measure_pos_of_nonempty_interior K.interior_nonempty).ne', Ne.def,
      ENNReal.div_eq_zero_iff, not_false_iff, or_self_iff]
  ·
    simp only [div_eq_mul_inv, νpos.ne', K.is_compact.measure_lt_top.Ne, or_self_iff,
      ENNReal.inv_eq_top, WithTop.mul_eq_top_iff, Ne.def, not_false_iff, and_false_iff,
      false_and_iff]
  ·
    calc
      μ = μ K • haar_measure K := haar_measure_unique μ K
      _ = (μ K / ν K) • ν K • haar_measure K := by
        rw [smul_smul, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel νpos.ne' νne, mul_one]
      _ = (μ K / ν K) • ν := by rw [← haar_measure_unique ν K]
      
#align measure_theory.measure.is_haar_measure_eq_smul_is_haar_measure MeasureTheory.Measure.isHaarMeasure_eq_smul_isHaarMeasure
#align measure_theory.measure.is_add_haar_measure_eq_smul_is_add_haar_measure MeasureTheory.Measure.is_add_haar_measure_eq_smul_is_add_haar_measure

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 90) regular_of_isHaarMeasure [LocallyCompactSpace G] (μ : Measure G)
    [IsHaarMeasure μ] : Regular μ := by
  have K : positive_compacts G := Classical.arbitrary _
  obtain ⟨c, c0, ctop, hμ⟩ : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = c • haar_measure K :=
    is_haar_measure_eq_smul_is_haar_measure μ _
  rw [hμ]
  exact regular.smul Ctop
#align measure_theory.measure.regular_of_is_haar_measure MeasureTheory.Measure.regular_of_isHaarMeasure
#align measure_theory.measure.regular_of_is_add_haar_measure MeasureTheory.Measure.regular_of_is_add_haar_measure

/-- **Steinhaus Theorem** In any locally compact group `G` with a haar measure `μ`, for any
  measurable set `E` of positive measure, the set `E / E` is a neighbourhood of `1`. -/
@[to_additive
      "**Steinhaus Theorem** In any locally compact group `G` with a haar measure `μ`,\n  for any measurable set `E` of positive measure, the set `E - E` is a neighbourhood of `0`."]
theorem div_mem_nhds_one_of_haar_pos (μ : Measure G) [IsHaarMeasure μ] [LocallyCompactSpace G]
    (E : Set G) (hE : MeasurableSet E) (hEpos : 0 < μ E) : E / E ∈ 𝓝 (1 : G) := by
  /- For any regular measure `μ` and set `E` of positive measure, we can find a compact set `K` of
       positive measure inside `E`. Further, for any outer regular measure `μ` there exists an open
       set `U` containing `K` with measure arbitrarily close to `K` (here `μ U < 2 * μ K` suffices).
       Then, we can pick an open neighborhood of `1`, say `V` such that such that `V * K` is contained
       in `U`. Now note that for any `v` in `V`, the sets `K` and `{v} * K` can not be disjoint
       because they are both of measure `μ K` (since `μ` is left regular) and also contained in `U`,
       yet we have that `μ U < 2 * μ K`. This show that `K / K` contains the neighborhood `V` of `1`,
       and therefore that it is itself such a neighborhood. -/
  obtain ⟨L, hL, hLE, hLpos, hLtop⟩ : ∃ L : Set G, MeasurableSet L ∧ L ⊆ E ∧ 0 < μ L ∧ μ L < ∞
  exact exists_subset_measure_lt_top hE hEpos
  obtain ⟨K, hKL, hK, hKpos⟩ : ∃ (K : Set G)(H : K ⊆ L), IsCompact K ∧ 0 < μ K
  exact MeasurableSet.exists_lt_isCompact_of_ne_top hL (ne_of_lt hLtop) hLpos
  have hKtop : μ K ≠ ∞ := by
    apply ne_top_of_le_ne_top (ne_of_lt hLtop)
    apply measure_mono hKL
  obtain ⟨U, hUK, hU, hμUK⟩ : ∃ (U : Set G)(H : U ⊇ K), IsOpen U ∧ μ U < μ K + μ K
  exact Set.exists_isOpen_lt_add K hKtop hKpos.ne'
  obtain ⟨V, hV1, hVKU⟩ : ∃ V ∈ 𝓝 (1 : G), V * K ⊆ U
  exact compact_open_separated_mul_left hK hU hUK
  have hv : ∀ v : G, v ∈ V → ¬Disjoint ({v} * K) K := by
    intro v hv hKv
    have hKvsub : {v} * K ∪ K ⊆ U := by
      apply Set.union_subset _ hUK
      apply subset_trans _ hVKU
      apply Set.mul_subset_mul _ (Set.Subset.refl K)
      simp only [Set.singleton_subset_iff, hv]
    replace hKvsub := @measure_mono _ _ μ _ _ hKvsub
    have hcontr := lt_of_le_of_lt hKvsub hμUK
    rw [measure_union hKv (IsCompact.measurableSet hK)] at hcontr
    have hKtranslate : μ ({v} * K) = μ K := by
      simp only [singleton_mul, image_mul_left, measure_preimage_mul]
    rw [hKtranslate, lt_self_iff_false] at hcontr
    assumption
  suffices : V ⊆ E / E; exact Filter.mem_of_superset hV1 this
  intro v hvV
  obtain ⟨x, hxK, hxvK⟩ : ∃ x : G, x ∈ {v} * K ∧ x ∈ K; exact Set.not_disjoint_iff.1 (hv v hvV)
  refine' ⟨x, v⁻¹ * x, hLE (hKL hxvK), _, _⟩
  · apply hKL.trans hLE
    simpa only [singleton_mul, image_mul_left, mem_preimage] using hxK
  · simp only [div_eq_iff_eq_mul, ← mul_assoc, mul_right_inv, one_mul]
#align measure_theory.measure.div_mem_nhds_one_of_haar_pos MeasureTheory.Measure.div_mem_nhds_one_of_haar_pos
#align measure_theory.measure.sub_mem_nhds_zero_of_add_haar_pos MeasureTheory.Measure.sub_mem_nhds_zero_of_add_haar_pos

end SecondCountable

end Group

section CommGroup

variable {G : Type _} [CommGroup G] [TopologicalSpace G] [TopologicalGroup G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (μ : Measure G) [IsHaarMeasure μ]

/-- Any Haar measure is invariant under inversion in an abelian group. -/
@[to_additive "Any additive Haar measure is invariant under negation in an abelian group."]
instance (priority := 100) IsHaarMeasure.isInvInvariant [LocallyCompactSpace G] :
    IsInvInvariant μ := by
  -- the image measure is a Haar measure. By uniqueness up to multiplication, it is of the form
  -- `c μ`. Applying again inversion, one gets the measure `c^2 μ`. But since inversion is an
  -- involution, this is also `μ`. Hence, `c^2 = 1`, which implies `c = 1`.
  constructor
  haveI : is_haar_measure (measure.map Inv.inv μ) :=
    (MulEquiv.inv G).isHaarMeasure_map μ continuous_inv continuous_inv
  obtain ⟨c, cpos, clt, hc⟩ : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ measure.map Inv.inv μ = c • μ :=
    is_haar_measure_eq_smul_is_haar_measure _ _
  have : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ := by
    simp only [hc, smul_smul, pow_two, measure.map_smul]
  have μeq : μ = c ^ 2 • μ := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at this
    · simpa only [inv_involutive, involutive.comp_self, map_id]
    all_goals infer_instance
  have K : positive_compacts G := Classical.arbitrary _
  have : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_eq_mul_right (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.is_compact.measure_lt_top.ne).1
      this
  have : c = 1 := (ENNReal.pow_strictMono two_ne_zero).Injective this
  rw [measure.inv, hc, this, one_smul]
#align measure_theory.measure.is_haar_measure.is_inv_invariant MeasureTheory.Measure.IsHaarMeasure.isInvInvariant
#align measure_theory.measure.is_add_haar_measure.is_neg_invariant MeasureTheory.Measure.IsAddHaarMeasure.is_neg_invariant

@[to_additive]
theorem measurePreserving_zpow [CompactSpace G] [RootableBy G ℤ] {n : ℤ} (hn : n ≠ 0) :
    MeasurePreserving (fun g : G => g ^ n) μ μ :=
  { Measurable := (continuous_zpow n).Measurable
    map_eq := by
      let f := @zpowGroupHom G _ n
      have hf : Continuous f := continuous_zpow n
      haveI : (μ.map f).IsHaarMeasure :=
        is_haar_measure_map μ f hf (RootableBy.surjective_pow G ℤ hn) (by simp)
      obtain ⟨C, -, -, hC⟩ := is_haar_measure_eq_smul_is_haar_measure (μ.map f) μ
      suffices C = 1 by rwa [this, one_smul] at hC
      have h_univ : (μ.map f) univ = μ univ := by
        rw [map_apply_of_ae_measurable hf.measurable.ae_measurable MeasurableSet.univ,
          preimage_univ]
      have hμ₀ : μ univ ≠ 0 := is_open_pos_measure.open_pos univ isOpen_univ univ_nonempty
      have hμ₁ : μ univ ≠ ∞ := compact_space.is_finite_measure.measure_univ_lt_top.ne
      rwa [hC, smul_apply, Algebra.id.smul_eq_mul, mul_comm, ← ENNReal.eq_div_iff hμ₀ hμ₁,
        ENNReal.div_self hμ₀ hμ₁] at h_univ }
#align measure_theory.measure.measure_preserving_zpow MeasureTheory.Measure.measurePreserving_zpow
#align measure_theory.measure.measure_preserving_zsmul MeasureTheory.Measure.measurePreserving_zsmul

@[to_additive]
theorem MeasurePreserving.zpow [CompactSpace G] [RootableBy G ℤ] {n : ℤ} (hn : n ≠ 0) {X : Type _}
    [MeasurableSpace X] {μ' : Measure X} {f : X → G} (hf : MeasurePreserving f μ' μ) :
    MeasurePreserving (fun x => f x ^ n) μ' μ :=
  (measurePreserving_zpow μ hn).comp hf
#align measure_theory.measure.measure_preserving.zpow MeasureTheory.Measure.MeasurePreserving.zpow
#align measure_theory.measure.measure_preserving.zsmul MeasureTheory.Measure.MeasurePreserving.zsmul

end CommGroup

end Measure

end MeasureTheory

