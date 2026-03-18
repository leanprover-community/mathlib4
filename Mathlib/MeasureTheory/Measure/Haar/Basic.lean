/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Measure.Content
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.Topology.Algebra.Group.Compact

/-!
# Haar measure

In this file we prove the existence of Haar measure for a locally compact Hausdorff topological
group.

We follow the write-up by Jonathan Gleason, *Existence and Uniqueness of Haar Measure*.
This is essentially the same argument as in
https://en.wikipedia.org/wiki/Haar_measure#A_construction_using_compact_subsets.

We construct the Haar measure first on compact sets. For this we define `(K : U)` as the (smallest)
number of left-translates of `U` that are needed to cover `K` (`index` in the formalization).
Then we define a function `h` on compact sets as `lim_U (K : U) / (K₀ : U)`,
where `U` becomes a smaller and smaller open neighborhood of `1`, and `K₀` is a fixed compact set
with nonempty interior. This function is `chaar` in the formalization, and we define the limit
formally using Tychonoff's theorem.

This function `h` forms a content, which we can extend to an outer measure and then a measure
(`haarMeasure`).
We normalize the Haar measure so that the measure of `K₀` is `1`.

Note that `μ` need not coincide with `h` on compact sets, according to
[halmos1950measure, ch. X, §53 p.233]. However, we know that `h(K)` lies between `μ(Kᵒ)` and `μ(K)`,
where `ᵒ` denotes the interior.

We also give a form of uniqueness of Haar measure, for σ-finite measures on second-countable
locally compact groups. For more involved statements not assuming second-countability, see
the file `Mathlib/MeasureTheory/Measure/Haar/Unique.lean`.

## Main Declarations

* `haarMeasure`: the Haar measure on a locally compact Hausdorff group. This is a left invariant
  regular measure. It takes as argument a compact set of the group (with non-empty interior),
  and is normalized so that the measure of the given set is 1.
* `haarMeasure_self`: the Haar measure is normalized.
* `isMulLeftInvariant_haarMeasure`: the Haar measure is left invariant.
* `regular_haarMeasure`: the Haar measure is a regular measure.
* `isHaarMeasure_haarMeasure`: the Haar measure satisfies the `IsHaarMeasure` typeclass, i.e.,
  it is invariant and gives finite mass to compact sets and positive mass to nonempty open sets.
* `haar` : some choice of a Haar measure, on a locally compact Hausdorff group, constructed as
  `haarMeasure K` where `K` is some arbitrary choice of a compact set with nonempty interior.
* `haarMeasure_unique`: Every σ-finite left invariant measure on a second-countable locally compact
  Hausdorff group is a scalar multiple of the Haar measure.

## References
* Paul Halmos (1950), Measure Theory, §53
* Jonathan Gleason, Existence and Uniqueness of Haar Measure
  - Note: step 9, page 8 contains a mistake: the last defined `μ` does not extend the `μ` on compact
    sets, see Halmos (1950) p. 233, bottom of the page. This makes some other steps (like step 11)
    invalid.
* https://en.wikipedia.org/wiki/Haar_measure
-/

@[expose] public section


noncomputable section

open Set Inv Function TopologicalSpace MeasurableSpace

open scoped NNReal ENNReal Pointwise Topology

namespace MeasureTheory

namespace Measure

section Group

variable {G : Type*} [Group G]

/-! We put the internal functions in the construction of the Haar measure in a namespace,
  so that the chosen names don't clash with other declarations.
  We first define a couple of the functions before proving the properties (that require that `G`
  is a topological group). -/


namespace haar

/-- The index or Haar covering number or ratio of `K` w.r.t. `V`, denoted `(K : V)`:
  it is the smallest number of (left) translates of `V` that is necessary to cover `K`.
  It is defined to be 0 if no finite number of translates cover `K`. -/
@[to_additive addIndex /-- additive version of `MeasureTheory.Measure.haar.index` -/]
noncomputable def index (K V : Set G) : ℕ :=
  sInf <| Finset.card '' { t : Finset G | K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V }

@[to_additive addIndex_empty]
theorem index_empty {V : Set G} : index ∅ V = 0 := by simp [index]

variable [TopologicalSpace G]

/-- `prehaar K₀ U K` is a weighted version of the index, defined as `(K : U)/(K₀ : U)`.
  In the applications `K₀` is compact with non-empty interior, `U` is open containing `1`,
  and `K` is any compact set.
  The argument `K` is a (bundled) compact set, so that we can consider `prehaar K₀ U` as an
  element of `haarProduct` (below). -/
@[to_additive /-- additive version of `MeasureTheory.Measure.haar.prehaar` -/]
noncomputable def prehaar (K₀ U : Set G) (K : Compacts G) : ℝ :=
  (index (K : Set G) U : ℝ) / index K₀ U

@[to_additive]
theorem prehaar_empty (K₀ : PositiveCompacts G) {U : Set G} : prehaar (K₀ : Set G) U ⊥ = 0 := by
  rw [prehaar, Compacts.coe_bot, index_empty, Nat.cast_zero, zero_div]

@[to_additive]
theorem prehaar_nonneg (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G) :
    0 ≤ prehaar (K₀ : Set G) U K := by apply div_nonneg <;> norm_cast <;> apply zero_le

/-- `haarProduct K₀` is the product of intervals `[0, (K : K₀)]`, for all compact sets `K`.
  For all `U`, we can show that `prehaar K₀ U ∈ haarProduct K₀`. -/
@[to_additive /-- additive version of `MeasureTheory.Measure.haar.haarProduct` -/]
def haarProduct (K₀ : Set G) : Set (Compacts G → ℝ) :=
  pi univ fun K => Icc 0 <| index (K : Set G) K₀

@[to_additive (attr := simp)]
theorem mem_prehaar_empty {K₀ : Set G} {f : Compacts G → ℝ} :
    f ∈ haarProduct K₀ ↔ ∀ K : Compacts G, f K ∈ Icc (0 : ℝ) (index (K : Set G) K₀) := by
  simp only [haarProduct, Set.pi, forall_prop_of_true, mem_univ, mem_setOf_eq]

/-- The closure of the collection of elements of the form `prehaar K₀ U`,
  for `U` open neighbourhoods of `1`, contained in `V`. The closure is taken in the space
  `compacts G → ℝ`, with the topology of pointwise convergence.
  We show that the intersection of all these sets is nonempty, and the Haar measure
  on compact sets is defined to be an element in the closure of this intersection. -/
@[to_additive /-- additive version of `MeasureTheory.Measure.haar.clPrehaar` -/]
def clPrehaar (K₀ : Set G) (V : OpenNhdsOf (1 : G)) : Set (Compacts G → ℝ) :=
  closure <| prehaar K₀ '' { U : Set G | U ⊆ V.1 ∧ IsOpen U ∧ (1 : G) ∈ U }

variable [IsTopologicalGroup G]

/-!
### Lemmas about `index`
-/


/-- If `K` is compact and `V` has nonempty interior, then the index `(K : V)` is well-defined,
  there is a finite set `t` satisfying the desired properties. -/
@[to_additive addIndex_defined
/-- If `K` is compact and `V` has nonempty interior, then the index `(K : V)` is well-defined,
  there is a finite set `t` satisfying the desired properties. -/]
theorem index_defined {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty) :
    ∃ n : ℕ, n ∈ Finset.card '' { t : Finset G | K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V } := by
  rcases compact_covered_by_mul_left_translates hK hV with ⟨t, ht⟩; exact ⟨t.card, t, ht, rfl⟩

@[to_additive addIndex_elim]
theorem index_elim {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty) :
    ∃ t : Finset G, (K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V) ∧ Finset.card t = index K V := by
  have := Nat.sInf_mem (index_defined hK hV); rwa [mem_image] at this

@[to_additive le_addIndex_mul]
theorem le_index_mul (K₀ : PositiveCompacts G) (K : Compacts G) {V : Set G}
    (hV : (interior V).Nonempty) :
    index (K : Set G) V ≤ index (K : Set G) K₀ * index (K₀ : Set G) V := by
  classical
  obtain ⟨s, h1s, h2s⟩ := index_elim K.isCompact K₀.interior_nonempty
  obtain ⟨t, h1t, h2t⟩ := index_elim K₀.isCompact hV
  rw [← h2s, ← h2t, mul_comm]
  refine le_trans ?_ Finset.card_mul_le
  apply Nat.sInf_le; refine ⟨_, ?_, rfl⟩; rw [mem_setOf_eq]; refine Subset.trans h1s ?_
  apply iUnion₂_subset; intro g₁ hg₁; rw [preimage_subset_iff]; intro g₂ hg₂
  have := h1t hg₂
  rcases this with ⟨_, ⟨g₃, rfl⟩, A, ⟨hg₃, rfl⟩, h2V⟩; rw [mem_preimage, ← mul_assoc] at h2V
  exact mem_biUnion (Finset.mul_mem_mul hg₃ hg₁) h2V

@[to_additive addIndex_pos]
theorem index_pos (K : PositiveCompacts G) {V : Set G} (hV : (interior V).Nonempty) :
    0 < index (K : Set G) V := by
  classical
  rw [index, Nat.sInf_def, Nat.find_pos, mem_image]
  · rintro ⟨t, h1t, h2t⟩; rw [Finset.card_eq_zero] at h2t; subst h2t
    obtain ⟨g, hg⟩ := K.interior_nonempty
    change g ∈ (∅ : Set G)
    convert h1t (interior_subset hg); symm
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
  · exact index_defined K.isCompact hV

@[to_additive addIndex_mono]
theorem index_mono {K K' V : Set G} (hK' : IsCompact K') (h : K ⊆ K') (hV : (interior V).Nonempty) :
    index K V ≤ index K' V := by
  rcases index_elim hK' hV with ⟨s, h1s, h2s⟩
  apply Nat.sInf_le; rw [mem_image]; exact ⟨s, Subset.trans h h1s, h2s⟩

@[to_additive addIndex_union_le]
theorem index_union_le (K₁ K₂ : Compacts G) {V : Set G} (hV : (interior V).Nonempty) :
    index (K₁.1 ∪ K₂.1) V ≤ index K₁.1 V + index K₂.1 V := by
  classical
  rcases index_elim K₁.2 hV with ⟨s, h1s, h2s⟩
  rcases index_elim K₂.2 hV with ⟨t, h1t, h2t⟩
  rw [← h2s, ← h2t]
  refine le_trans (Nat.sInf_le ⟨_, ?_, rfl⟩) (Finset.card_union_le _ _)
  rw [mem_setOf_eq, Finset.set_biUnion_union]
  gcongr

@[to_additive addIndex_union_eq]
theorem index_union_eq (K₁ K₂ : Compacts G) {V : Set G} (hV : (interior V).Nonempty)
    (h : Disjoint (K₁.1 * V⁻¹) (K₂.1 * V⁻¹)) :
    index (K₁.1 ∪ K₂.1) V = index K₁.1 V + index K₂.1 V := by
  classical
  apply le_antisymm (index_union_le K₁ K₂ hV)
  rcases index_elim (K₁.2.union K₂.2) hV with ⟨s, h1s, h2s⟩; rw [← h2s]
  have (K : Set G) (hK : K ⊆ ⋃ g ∈ s, (g * ·) ⁻¹' V) :
      index K V ≤ {g ∈ s | ((g * ·) ⁻¹' V ∩ K).Nonempty}.card := by
    apply Nat.sInf_le; refine ⟨_, ?_, rfl⟩; rw [mem_setOf_eq]
    intro g hg; rcases hK hg with ⟨_, ⟨g₀, rfl⟩, _, ⟨h1g₀, rfl⟩, h2g₀⟩
    simp only [mem_preimage] at h2g₀
    simp only [mem_iUnion]; use g₀; constructor; swap
    · simp only [Finset.mem_filter, h1g₀, true_and]; use g
      simp [hg, h2g₀]
    exact h2g₀
  refine
    le_trans
      (add_le_add (this K₁.1 <| Subset.trans subset_union_left h1s)
        (this K₂.1 <| Subset.trans subset_union_right h1s)) ?_
  rw [← Finset.card_union_of_disjoint, Finset.filter_union_right]
  · exact s.card_filter_le _
  apply Finset.disjoint_filter.mpr
  rintro g₁ _ ⟨g₂, h1g₂, h2g₂⟩ ⟨g₃, h1g₃, h2g₃⟩
  simp only [mem_preimage] at h1g₃ h1g₂
  refine h.le_bot (?_ : g₁⁻¹ ∈ _)
  constructor <;> simp only [Set.mem_inv, Set.mem_mul]
  · refine ⟨_, h2g₂, (g₁ * g₂)⁻¹, ?_, ?_⟩
    · simp only [inv_inv, h1g₂]
    · simp only [mul_inv_rev, mul_inv_cancel_left]
  · refine ⟨_, h2g₃, (g₁ * g₃)⁻¹, ?_, ?_⟩
    · simp only [inv_inv, h1g₃]
    · simp only [mul_inv_rev, mul_inv_cancel_left]

@[to_additive add_left_addIndex_le]
theorem mul_left_index_le {K : Set G} (hK : IsCompact K) {V : Set G} (hV : (interior V).Nonempty)
    (g : G) : index ((fun h => g * h) '' K) V ≤ index K V := by
  rcases index_elim hK hV with ⟨s, h1s, h2s⟩; rw [← h2s]
  apply Nat.sInf_le; rw [mem_image]
  refine ⟨s.map (Equiv.mulRight g⁻¹).toEmbedding, ?_, Finset.card_map _⟩
  simp only [mem_setOf_eq]; refine Subset.trans (image_mono h1s) ?_
  rintro _ ⟨g₁, ⟨_, ⟨g₂, rfl⟩, ⟨_, ⟨hg₂, rfl⟩, hg₁⟩⟩, rfl⟩
  simp only [mem_preimage] at hg₁
  simp only [exists_prop, mem_iUnion, Finset.mem_map, Equiv.coe_mulRight,
    exists_exists_and_eq_and, mem_preimage, Equiv.toEmbedding_apply]
  refine ⟨_, hg₂, ?_⟩; simp only [mul_assoc, hg₁, inv_mul_cancel_left]

@[to_additive is_left_invariant_addIndex]
theorem is_left_invariant_index {K : Set G} (hK : IsCompact K) (g : G) {V : Set G}
    (hV : (interior V).Nonempty) : index ((fun h => g * h) '' K) V = index K V := by
  refine le_antisymm (mul_left_index_le hK hV g) ?_
  convert mul_left_index_le (hK.image <| continuous_const_mul g) hV g⁻¹
  rw [image_image]; symm; convert image_id' _ with h; apply inv_mul_cancel_left

/-!
### Lemmas about `prehaar`
-/


@[to_additive add_prehaar_le_addIndex]
theorem prehaar_le_index (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G)
    (hU : (interior U).Nonempty) : prehaar (K₀ : Set G) U K ≤ index (K : Set G) K₀ := by
  unfold prehaar; rw [div_le_iff₀] <;> norm_cast
  · apply le_index_mul K₀ K hU
  · exact index_pos K₀ hU

@[to_additive]
theorem prehaar_pos (K₀ : PositiveCompacts G) {U : Set G} (hU : (interior U).Nonempty) {K : Set G}
    (h1K : IsCompact K) (h2K : (interior K).Nonempty) : 0 < prehaar (K₀ : Set G) U ⟨K, h1K⟩ := by
  apply div_pos <;> norm_cast
  · apply index_pos ⟨⟨K, h1K⟩, h2K⟩ hU
  · exact index_pos K₀ hU

@[to_additive]
theorem prehaar_mono {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty)
    {K₁ K₂ : Compacts G} (h : (K₁ : Set G) ⊆ K₂.1) :
    prehaar (K₀ : Set G) U K₁ ≤ prehaar (K₀ : Set G) U K₂ := by
  simp only [prehaar]; rw [div_le_div_iff_of_pos_right]
  · exact mod_cast index_mono K₂.2 h hU
  · exact mod_cast index_pos K₀ hU

@[to_additive]
theorem prehaar_self {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty) :
    prehaar (K₀ : Set G) U K₀.toCompacts = 1 :=
  div_self <| ne_of_gt <| mod_cast index_pos K₀ hU

@[to_additive]
theorem prehaar_sup_le {K₀ : PositiveCompacts G} {U : Set G} (K₁ K₂ : Compacts G)
    (hU : (interior U).Nonempty) :
    prehaar (K₀ : Set G) U (K₁ ⊔ K₂) ≤ prehaar (K₀ : Set G) U K₁ + prehaar (K₀ : Set G) U K₂ := by
  simp only [prehaar]; rw [← add_div, div_le_div_iff_of_pos_right]
  · exact mod_cast index_union_le K₁ K₂ hU
  · exact mod_cast index_pos K₀ hU

@[to_additive]
theorem prehaar_sup_eq {K₀ : PositiveCompacts G} {U : Set G} {K₁ K₂ : Compacts G}
    (hU : (interior U).Nonempty) (h : Disjoint (K₁.1 * U⁻¹) (K₂.1 * U⁻¹)) :
    prehaar (K₀ : Set G) U (K₁ ⊔ K₂) = prehaar (K₀ : Set G) U K₁ + prehaar (K₀ : Set G) U K₂ := by
  simp only [prehaar]; rw [← add_div]
  -- Porting note: Here was `congr`, but `to_additive` failed to generate a theorem.
  refine congr_arg (fun x : ℝ => x / index K₀ U) ?_
  exact mod_cast index_union_eq K₁ K₂ hU h

@[to_additive]
theorem is_left_invariant_prehaar {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty)
    (g : G) (K : Compacts G) :
    prehaar (K₀ : Set G) U (K.map _ <| continuous_const_mul g) = prehaar (K₀ : Set G) U K := by
  simp only [prehaar, Compacts.coe_map, is_left_invariant_index K.isCompact _ hU]

/-!
### Lemmas about `haarProduct`
-/

@[to_additive]
theorem prehaar_mem_haarProduct (K₀ : PositiveCompacts G) {U : Set G} (hU : (interior U).Nonempty) :
    prehaar (K₀ : Set G) U ∈ haarProduct (K₀ : Set G) := by
    rintro ⟨K, hK⟩ _; rw [mem_Icc]; exact ⟨prehaar_nonneg K₀ _, prehaar_le_index K₀ _ hU⟩

@[to_additive]
theorem nonempty_iInter_clPrehaar (K₀ : PositiveCompacts G) :
    (haarProduct (K₀ : Set G) ∩ ⋂ V : OpenNhdsOf (1 : G), clPrehaar K₀ V).Nonempty := by
  have : IsCompact (haarProduct (K₀ : Set G)) := by
    apply isCompact_univ_pi; intro K; apply isCompact_Icc
  refine this.inter_iInter_nonempty (clPrehaar K₀) (fun s => isClosed_closure) fun t => ?_
  let V₀ := ⋂ V ∈ t, (V : OpenNhdsOf (1 : G)).carrier
  have h1V₀ : IsOpen V₀ := isOpen_biInter_finset <| by rintro ⟨⟨V, hV₁⟩, hV₂⟩ _; exact hV₁
  have h2V₀ : (1 : G) ∈ V₀ := by simp only [V₀, mem_iInter]; rintro ⟨⟨V, hV₁⟩, hV₂⟩ _; exact hV₂
  refine ⟨prehaar K₀ V₀, ?_⟩
  constructor
  · apply prehaar_mem_haarProduct K₀; use 1; rwa [h1V₀.interior_eq]
  · simp only [mem_iInter]; rintro ⟨V, hV⟩ h2V; apply subset_closure
    apply mem_image_of_mem; rw [mem_setOf_eq]
    exact ⟨Subset.trans (iInter_subset _ ⟨V, hV⟩) (iInter_subset _ h2V), h1V₀, h2V₀⟩

/-!
### Lemmas about `chaar`
-/

/-- This is the "limit" of `prehaar K₀ U K` as `U` becomes a smaller and smaller open
  neighborhood of `(1 : G)`. More precisely, it is defined to be an arbitrary element
  in the intersection of all the sets `clPrehaar K₀ V` in `haarProduct K₀`.
  This is roughly equal to the Haar measure on compact sets,
  but it can differ slightly. We do know that
  `haarMeasure K₀ (interior K) ≤ chaar K₀ K ≤ haarMeasure K₀ K`. -/
@[to_additive addCHaar /-- additive version of `MeasureTheory.Measure.haar.chaar` -/]
noncomputable def chaar (K₀ : PositiveCompacts G) (K : Compacts G) : ℝ :=
  Classical.choose (nonempty_iInter_clPrehaar K₀) K

@[to_additive addCHaar_mem_addHaarProduct]
theorem chaar_mem_haarProduct (K₀ : PositiveCompacts G) : chaar K₀ ∈ haarProduct (K₀ : Set G) :=
  (Classical.choose_spec (nonempty_iInter_clPrehaar K₀)).1

@[to_additive addCHaar_mem_clAddPrehaar]
theorem chaar_mem_clPrehaar (K₀ : PositiveCompacts G) (V : OpenNhdsOf (1 : G)) :
    chaar K₀ ∈ clPrehaar (K₀ : Set G) V := by
  have := (Classical.choose_spec (nonempty_iInter_clPrehaar K₀)).2; rw [mem_iInter] at this
  exact this V

@[to_additive addCHaar_nonneg]
theorem chaar_nonneg (K₀ : PositiveCompacts G) (K : Compacts G) : 0 ≤ chaar K₀ K := by
  have := chaar_mem_haarProduct K₀ K (mem_univ _); rw [mem_Icc] at this; exact this.1

@[to_additive addCHaar_empty]
theorem chaar_empty (K₀ : PositiveCompacts G) : chaar K₀ ⊥ = 0 := by
  let eval : (Compacts G → ℝ) → ℝ := fun f => f ⊥
  have : Continuous eval := continuous_apply ⊥
  change chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)}
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, _, rfl⟩; apply prehaar_empty
  · apply continuous_iff_isClosed.mp this; exact isClosed_singleton

@[to_additive addCHaar_self]
theorem chaar_self (K₀ : PositiveCompacts G) : chaar K₀ K₀.toCompacts = 1 := by
  let eval : (Compacts G → ℝ) → ℝ := fun f => f K₀.toCompacts
  have : Continuous eval := continuous_apply _
  change chaar K₀ ∈ eval ⁻¹' {(1 : ℝ)}
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨_, h2U, h3U⟩, rfl⟩; apply prehaar_self
    rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_isClosed.mp this; exact isClosed_singleton

@[to_additive addCHaar_mono]
theorem chaar_mono {K₀ : PositiveCompacts G} {K₁ K₂ : Compacts G} (h : (K₁ : Set G) ⊆ K₂) :
    chaar K₀ K₁ ≤ chaar K₀ K₂ := by
  let eval : (Compacts G → ℝ) → ℝ := fun f => f K₂ - f K₁
  have : Continuous eval := (continuous_apply K₂).sub (continuous_apply K₁)
  rw [← sub_nonneg]; change chaar K₀ ∈ eval ⁻¹' Ici (0 : ℝ)
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨_, h2U, h3U⟩, rfl⟩; simp only [eval, mem_preimage, mem_Ici, sub_nonneg]
    apply prehaar_mono _ h; rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_isClosed.mp this; exact isClosed_Ici

@[to_additive addCHaar_sup_le]
theorem chaar_sup_le {K₀ : PositiveCompacts G} (K₁ K₂ : Compacts G) :
    chaar K₀ (K₁ ⊔ K₂) ≤ chaar K₀ K₁ + chaar K₀ K₂ := by
  let eval : (Compacts G → ℝ) → ℝ := fun f => f K₁ + f K₂ - f (K₁ ⊔ K₂)
  have : Continuous eval := by
    exact ((continuous_apply K₁).add (continuous_apply K₂)).sub (continuous_apply (K₁ ⊔ K₂))
  rw [← sub_nonneg]; change chaar K₀ ∈ eval ⁻¹' Ici (0 : ℝ)
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨_, h2U, h3U⟩, rfl⟩; simp only [eval, mem_preimage, mem_Ici, sub_nonneg]
    apply prehaar_sup_le; rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_isClosed.mp this; exact isClosed_Ici

@[to_additive addCHaar_sup_eq]
theorem chaar_sup_eq {K₀ : PositiveCompacts G}
    {K₁ K₂ : Compacts G} (h : Disjoint K₁.1 K₂.1) (h₂ : IsClosed K₂.1) :
    chaar K₀ (K₁ ⊔ K₂) = chaar K₀ K₁ + chaar K₀ K₂ := by
  rcases SeparatedNhds.of_isCompact_isCompact_isClosed K₁.2 K₂.2 h₂ h
    with ⟨U₁, U₂, h1U₁, h1U₂, h2U₁, h2U₂, hU⟩
  rcases compact_open_separated_mul_right K₁.2 h1U₁ h2U₁ with ⟨L₁, h1L₁, h2L₁⟩
  rcases mem_nhds_iff.mp h1L₁ with ⟨V₁, h1V₁, h2V₁, h3V₁⟩
  replace h2L₁ := Subset.trans (mul_subset_mul_left h1V₁) h2L₁
  rcases compact_open_separated_mul_right K₂.2 h1U₂ h2U₂ with ⟨L₂, h1L₂, h2L₂⟩
  rcases mem_nhds_iff.mp h1L₂ with ⟨V₂, h1V₂, h2V₂, h3V₂⟩
  replace h2L₂ := Subset.trans (mul_subset_mul_left h1V₂) h2L₂
  let eval : (Compacts G → ℝ) → ℝ := fun f => f K₁ + f K₂ - f (K₁ ⊔ K₂)
  have : Continuous eval :=
    ((continuous_apply K₁).add (continuous_apply K₂)).sub (continuous_apply (K₁ ⊔ K₂))
  rw [eq_comm, ← sub_eq_zero]; change chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)}
  let V := V₁ ∩ V₂
  apply
    mem_of_subset_of_mem _
      (chaar_mem_clPrehaar K₀
        ⟨⟨V⁻¹, (h2V₁.inter h2V₂).preimage continuous_inv⟩, by
          simp only [V, mem_inv, inv_one, h3V₁, h3V₂, mem_inter_iff, true_and]⟩)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩
    simp only [eval, mem_preimage, sub_eq_zero, mem_singleton_iff]; rw [eq_comm]
    apply prehaar_sup_eq
    · rw [h2U.interior_eq]; exact ⟨1, h3U⟩
    · refine disjoint_of_subset ?_ ?_ hU
      · refine Subset.trans (mul_subset_mul Subset.rfl ?_) h2L₁
        exact Subset.trans (inv_subset.mpr h1U) inter_subset_left
      · refine Subset.trans (mul_subset_mul Subset.rfl ?_) h2L₂
        exact Subset.trans (inv_subset.mpr h1U) inter_subset_right
  · apply continuous_iff_isClosed.mp this; exact isClosed_singleton

@[to_additive is_left_invariant_addCHaar]
theorem is_left_invariant_chaar {K₀ : PositiveCompacts G} (g : G) (K : Compacts G) :
    chaar K₀ (K.map _ <| continuous_const_mul g) = chaar K₀ K := by
  let eval : (Compacts G → ℝ) → ℝ := fun f => f (K.map _ <| continuous_const_mul g) - f K
  have : Continuous eval := (continuous_apply (K.map _ _)).sub (continuous_apply K)
  rw [← sub_eq_zero]; change chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)}
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨_, h2U, h3U⟩, rfl⟩
    simp only [eval, mem_singleton_iff, mem_preimage, sub_eq_zero]
    apply is_left_invariant_prehaar; rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_isClosed.mp this; exact isClosed_singleton

/-- The function `chaar` interpreted in `ℝ≥0`, as a content -/
@[to_additive /-- additive version of `MeasureTheory.Measure.haar.haarContent` -/]
noncomputable def haarContent (K₀ : PositiveCompacts G) : Content G where
  toFun K := ⟨chaar K₀ K, chaar_nonneg _ _⟩
  mono' K₁ K₂ h := by simp only [← NNReal.coe_le_coe, NNReal.toReal, chaar_mono, h]
  sup_disjoint' K₁ K₂ h _h₁ h₂ := by simp only [chaar_sup_eq h]; rfl
  sup_le' K₁ K₂ := by
    simp only [← NNReal.coe_le_coe, NNReal.coe_add]
    simp only [NNReal.toReal, chaar_sup_le]

/-! We only prove the properties for `haarContent` that we use at least twice below. -/


@[to_additive]
theorem haarContent_apply (K₀ : PositiveCompacts G) (K : Compacts G) :
    haarContent K₀ K = show NNReal from ⟨chaar K₀ K, chaar_nonneg _ _⟩ :=
  rfl

/-- The variant of `chaar_self` for `haarContent` -/
@[to_additive /-- The variant of `addCHaar_self` for `addHaarContent`. -/]
theorem haarContent_self {K₀ : PositiveCompacts G} : haarContent K₀ K₀.toCompacts = 1 := by
  simp_rw [← ENNReal.coe_one, haarContent_apply, ENNReal.coe_inj, chaar_self]; rfl

/-- The variant of `is_left_invariant_chaar` for `haarContent` -/
@[to_additive /-- The variant of `is_left_invariant_addCHaar` for `addHaarContent` -/]
theorem is_left_invariant_haarContent {K₀ : PositiveCompacts G} (g : G) (K : Compacts G) :
    haarContent K₀ (K.map _ <| continuous_const_mul g) = haarContent K₀ K := by
  simpa only [ENNReal.coe_inj, ← NNReal.coe_inj, haarContent_apply] using
    is_left_invariant_chaar g K

@[to_additive]
theorem haarContent_outerMeasure_self_pos (K₀ : PositiveCompacts G) :
    0 < (haarContent K₀).outerMeasure K₀ := by
  refine zero_lt_one.trans_le ?_
  rw [Content.outerMeasure_eq_iInf]
  refine le_iInf₂ fun U hU => le_iInf fun hK₀ => le_trans ?_ <| le_iSup₂ K₀.toCompacts hK₀
  exact haarContent_self.ge

@[to_additive]
theorem haarContent_outerMeasure_closure_pos (K₀ : PositiveCompacts G) :
    0 < (haarContent K₀).outerMeasure (closure K₀) :=
  (haarContent_outerMeasure_self_pos K₀).trans_le (OuterMeasure.mono _ subset_closure)

end haar

open haar

/-!
### The Haar measure
-/

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- The Haar measure on the locally compact group `G`, scaled so that `haarMeasure K₀ K₀ = 1`. -/
@[to_additive
/-- The Haar measure on the locally compact additive group `G`, scaled so that
`addHaarMeasure K₀ K₀ = 1`. -/]
noncomputable def haarMeasure (K₀ : PositiveCompacts G) : Measure G :=
  ((haarContent K₀).measure K₀)⁻¹ • (haarContent K₀).measure

@[to_additive]
theorem haarMeasure_apply {K₀ : PositiveCompacts G} {s : Set G} (hs : MeasurableSet s) :
    haarMeasure K₀ s = (haarContent K₀).outerMeasure s / (haarContent K₀).measure K₀ := by
  change ((haarContent K₀).measure K₀)⁻¹ * (haarContent K₀).measure s = _
  simp only [hs, div_eq_mul_inv, mul_comm, Content.measure_apply]

@[to_additive]
instance isMulLeftInvariant_haarMeasure (K₀ : PositiveCompacts G) :
    IsMulLeftInvariant (haarMeasure K₀) := by
  rw [← forall_measure_preimage_mul_iff]
  intro g A hA
  rw [haarMeasure_apply hA, haarMeasure_apply (measurable_const_mul g hA)]
  -- Porting note: Here was `congr 1`, but `to_additive` failed to generate a theorem.
  refine congr_arg (fun x : ℝ≥0∞ => x / (haarContent K₀).measure K₀) ?_
  apply Content.is_mul_left_invariant_outerMeasure
  apply is_left_invariant_haarContent

@[to_additive]
theorem haarMeasure_self {K₀ : PositiveCompacts G} : haarMeasure K₀ K₀ = 1 := by
  haveI : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group
  simp only [haarMeasure, coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [← K₀.isCompact.measure_closure,
    Content.measure_apply _ isClosed_closure.measurableSet, ENNReal.inv_mul_cancel]
  · exact (haarContent_outerMeasure_closure_pos K₀).ne'
  · exact (Content.outerMeasure_lt_top_of_isCompact _ K₀.isCompact.closure).ne

/-- The Haar measure is regular. -/
@[to_additive /-- The additive Haar measure is regular. -/]
instance regular_haarMeasure {K₀ : PositiveCompacts G} : (haarMeasure K₀).Regular := by
  haveI : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group
  apply Regular.smul
  rw [← K₀.isCompact.measure_closure,
    Content.measure_apply _ isClosed_closure.measurableSet, ENNReal.inv_ne_top]
  exact (haarContent_outerMeasure_closure_pos K₀).ne'

@[to_additive]
theorem haarMeasure_closure_self {K₀ : PositiveCompacts G} : haarMeasure K₀ (closure K₀) = 1 := by
  rw [K₀.isCompact.measure_closure, haarMeasure_self]

/-- The Haar measure is sigma-finite in a second countable group. -/
@[to_additive /-- The additive Haar measure is sigma-finite in a second countable group. -/]
instance sigmaFinite_haarMeasure [SecondCountableTopology G] {K₀ : PositiveCompacts G} :
    SigmaFinite (haarMeasure K₀) := by
  haveI : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group; infer_instance

/-- The Haar measure is a Haar measure, i.e., it is invariant and gives finite mass to compact
sets and positive mass to nonempty open sets. -/
@[to_additive
/-- The additive Haar measure is an additive Haar measure, i.e., it is invariant and gives finite
mass to compact sets and positive mass to nonempty open sets. -/]
instance isHaarMeasure_haarMeasure (K₀ : PositiveCompacts G) : IsHaarMeasure (haarMeasure K₀) := by
  apply
    isHaarMeasure_of_isCompact_nonempty_interior (haarMeasure K₀) K₀ K₀.isCompact
      K₀.interior_nonempty
  · simp only [haarMeasure_self]; exact one_ne_zero
  · simp only [haarMeasure_self, ne_eq, ENNReal.one_ne_top, not_false_eq_true]

/-- `haar` is some choice of a Haar measure, on a locally compact group. -/
@[to_additive
/-- `addHaar` is some choice of a Haar measure, on a locally compact additive group. -/]
noncomputable abbrev haar [LocallyCompactSpace G] : Measure G :=
  haarMeasure <| Classical.arbitrary _

/-! Steinhaus theorem: if `E` has positive measure, then `E / E` contains a neighborhood of zero.
Note that this is not true for general regular Haar measures: in `ℝ × ℝ` where the first factor
has the discrete topology, then `E = ℝ × {0}` has infinite measure for the regular Haar measure,
but `E / E` does not contain a neighborhood of zero. On the other hand, it is always true for
inner regular Haar measures (and in particular for any Haar measure on a second countable group).
-/

open Pointwise

@[to_additive]
private lemma steinhaus_mul_aux (μ : Measure G) [IsHaarMeasure μ] [μ.InnerRegularCompactLTTop]
    [LocallyCompactSpace G] (E : Set G) (hE : MeasurableSet E)
    (hEapprox : ∃ K ⊆ E, IsCompact K ∧ 0 < μ K) : E / E ∈ 𝓝 (1 : G) := by
  /- For any measure `μ` and set `E` containing a compact set `K` of positive measure, there exists
  a neighborhood `V` of the identity such that `v • K \ K` has small measure for all `v ∈ V`, say
  `< μ K`. Then `v • K` and `K` cannot be disjoint, as otherwise `μ (v • K \ K) = μ (v • K) = μ K`.
  This show that `K / K` contains the neighborhood `V` of `1`, and therefore that it is
  itself such a neighborhood. -/
  obtain ⟨K, hKE, hK, K_closed, hKpos⟩ : ∃ K ⊆ E, IsCompact K ∧ IsClosed K ∧ 0 < μ K := by
    obtain ⟨K, hKE, hK_comp, hK_meas⟩ := hEapprox
    exact ⟨closure K, hK_comp.closure_subset_measurableSet hE hKE, hK_comp.closure,
      isClosed_closure, by rwa [hK_comp.measure_closure]⟩
  filter_upwards [eventually_nhds_one_measure_smul_diff_lt hK K_closed hKpos.ne' (μ := μ)] with g hg
  obtain ⟨_, ⟨x, hxK, rfl⟩, hgxK⟩ : ∃ x ∈ g • K, x ∈ K :=
     not_disjoint_iff.1 fun hd ↦ by simp [hd.symm.sdiff_eq_right, measure_smul] at hg
  simpa using div_mem_div (hKE hgxK) (hKE hxK)

/-- **Steinhaus Theorem** for finite mass sets.

In any locally compact group `G` with a Haar measure `μ` that's inner regular on finite measure
sets, for any measurable set `E` of finite positive measure, the set `E / E` is a neighbourhood of
`1`. -/
@[to_additive
/-- **Steinhaus Theorem** for finite mass sets.

In any locally compact group `G` with a Haar measure `μ` that's inner regular on finite measure
sets, for any measurable set `E` of finite positive measure, the set `E - E` is a neighbourhood of
`0`. -/]
theorem div_mem_nhds_one_of_haar_pos_ne_top (μ : Measure G) [IsHaarMeasure μ]
    [LocallyCompactSpace G] [μ.InnerRegularCompactLTTop] (E : Set G) (hE : MeasurableSet E)
    (hEpos : 0 < μ E) (hEfin : μ E ≠ ∞) : E / E ∈ 𝓝 (1 : G) :=
  steinhaus_mul_aux μ E hE <| hE.exists_lt_isCompact_of_ne_top hEfin hEpos

/-- **Steinhaus Theorem**.

In any locally compact group `G` with an inner regular Haar measure `μ`,
for any measurable set `E` of positive measure, the set `E / E` is a neighbourhood of `1`. -/
@[to_additive
/-- **Steinhaus Theorem**.

In any locally compact group `G` with an inner regular Haar measure `μ`,
for any measurable set `E` of positive measure, the set `E - E` is a neighbourhood of `0`. -/]
theorem div_mem_nhds_one_of_haar_pos (μ : Measure G) [IsHaarMeasure μ] [LocallyCompactSpace G]
    [InnerRegular μ] (E : Set G) (hE : MeasurableSet E) (hEpos : 0 < μ E) :
    E / E ∈ 𝓝 (1 : G) := steinhaus_mul_aux μ E hE <| hE.exists_lt_isCompact hEpos

section SecondCountable_SigmaFinite
/-! In this section, we investigate uniqueness of left-invariant measures without assuming that
the measure is finite on compact sets, but assuming σ-finiteness instead. We also rely on
second-countability, to ensure that the group operations are measurable: in this case, one can
bypass all topological arguments, and conclude using uniqueness of σ-finite left-invariant measures
in measurable groups.

For more general uniqueness statements without second-countability assumptions,
see the file `Mathlib/MeasureTheory/Measure/Haar/Unique.lean`.
-/

variable [SecondCountableTopology G]

/-- **Uniqueness of left-invariant measures**: In a second-countable locally compact group, any
  σ-finite left-invariant measure is a scalar multiple of the Haar measure.
  This is slightly weaker than assuming that `μ` is a Haar measure (in particular we don't require
  `μ ≠ 0`).
  See also `isMulLeftInvariant_eq_smul_of_regular`
  for a statement not assuming second-countability. -/
@[to_additive
/-- **Uniqueness of left-invariant measures**: In a second-countable locally compact additive group,
  any σ-finite left-invariant measure is a scalar multiple of the additive Haar measure.
  This is slightly weaker than assuming that `μ` is an additive Haar measure (in particular we don't
  require `μ ≠ 0`).
  See also `isAddLeftInvariant_eq_smul_of_regular`
  for a statement not assuming second-countability. -/]
theorem haarMeasure_unique (μ : Measure G) [SigmaFinite μ] [IsMulLeftInvariant μ]
    (K₀ : PositiveCompacts G) : μ = μ K₀ • haarMeasure K₀ := by
  have A : Set.Nonempty (interior (closure (K₀ : Set G))) :=
    K₀.interior_nonempty.mono (interior_mono subset_closure)
  have := measure_eq_div_smul μ (haarMeasure K₀)
    (measure_pos_of_nonempty_interior _ A).ne' K₀.isCompact.closure.measure_ne_top
  rwa [haarMeasure_closure_self, div_one, K₀.isCompact.measure_closure] at this

/-- Let `μ` be a σ-finite left invariant measure on `G`. Then `μ` is equal to the Haar measure
defined by `K₀` iff `μ K₀ = 1`. -/
@[to_additive]
theorem haarMeasure_eq_iff (K₀ : PositiveCompacts G) (μ : Measure G) [SigmaFinite μ]
    [IsMulLeftInvariant μ] :
    haarMeasure K₀ = μ ↔ μ K₀ = 1 :=
  ⟨fun h => h.symm ▸ haarMeasure_self, fun h => by rw [haarMeasure_unique μ K₀, h, one_smul]⟩

example [LocallyCompactSpace G] (μ : Measure G) [IsHaarMeasure μ] (K₀ : PositiveCompacts G) :
    μ = μ K₀.1 • haarMeasure K₀ :=
  haarMeasure_unique μ K₀

/-- To show that an invariant σ-finite measure is regular it is sufficient to show that it is finite
  on some compact set with non-empty interior. -/
@[to_additive
/-- To show that an invariant σ-finite measure is regular it is sufficient to show that it is
  finite on some compact set with non-empty interior. -/]
theorem regular_of_isMulLeftInvariant {μ : Measure G} [SigmaFinite μ] [IsMulLeftInvariant μ]
    {K : Set G} (hK : IsCompact K) (h2K : (interior K).Nonempty) (hμK : μ K ≠ ∞) : Regular μ := by
  rw [haarMeasure_unique μ ⟨⟨K, hK⟩, h2K⟩]; exact Regular.smul hμK

end SecondCountable_SigmaFinite

end Group

end Measure

end MeasureTheory
