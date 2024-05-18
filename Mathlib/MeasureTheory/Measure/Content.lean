/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Sets.Compacts

#align_import measure_theory.measure.content from "leanprover-community/mathlib"@"d39590fc8728fbf6743249802486f8c91ffe07bc"

/-!
# Contents

In this file we work with *contents*. A content `λ` is a function from a certain class of subsets
(such as the compact subsets) to `ℝ≥0` that is
* additive: If `K₁` and `K₂` are disjoint sets in the domain of `λ`,
  then `λ(K₁ ∪ K₂) = λ(K₁) + λ(K₂)`;
* subadditive: If `K₁` and `K₂` are in the domain of `λ`, then `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)`;
* monotone: If `K₁ ⊆ K₂` are in the domain of `λ`, then `λ(K₁) ≤ λ(K₂)`.

We show that:
* Given a content `λ` on compact sets, let us define a function `λ*` on open sets, by letting
  `λ* U` be the supremum of `λ K` for `K` included in `U`. This is a countably subadditive map that
  vanishes at `∅`. In Halmos (1950) this is called the *inner content* `λ*` of `λ`, and formalized
  as `innerContent`.
* Given an inner content, we define an outer measure `μ*`, by letting `μ* E` be the infimum of
  `λ* U` over the open sets `U` containing `E`. This is indeed an outer measure. It is formalized
  as `outerMeasure`.
* Restricting this outer measure to Borel sets gives a regular measure `μ`.

We define bundled contents as `Content`.
In this file we only work on contents on compact sets, and inner contents on open sets, and both
contents and inner contents map into the extended nonnegative reals. However, in other applications
other choices can be made, and it is not a priori clear what the best interface should be.

## Main definitions

For `μ : Content G`, we define
* `μ.innerContent` : the inner content associated to `μ`.
* `μ.outerMeasure` : the outer measure associated to `μ`.
* `μ.measure`      : the Borel measure associated to `μ`.

These definitions are given for spaces which are R₁.
The resulting measure `μ.measure` is always outer regular by design.
When the space is locally compact, `μ.measure` is also regular.

## References

* Paul Halmos (1950), Measure Theory, §53
* <https://en.wikipedia.org/wiki/Content_(measure_theory)>
-/


universe u v w

noncomputable section

open Set TopologicalSpace

open NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {G : Type w} [TopologicalSpace G]

/-- A content is an additive function on compact sets taking values in `ℝ≥0`. It is a device
from which one can define a measure. -/
structure Content (G : Type w) [TopologicalSpace G] where
  toFun : Compacts G → ℝ≥0
  mono' : ∀ K₁ K₂ : Compacts G, (K₁ : Set G) ⊆ K₂ → toFun K₁ ≤ toFun K₂
  sup_disjoint' :
    ∀ K₁ K₂ : Compacts G, Disjoint (K₁ : Set G) K₂ → IsClosed (K₁ : Set G) → IsClosed (K₂ : Set G)
      → toFun (K₁ ⊔ K₂) = toFun K₁ + toFun K₂
  sup_le' : ∀ K₁ K₂ : Compacts G, toFun (K₁ ⊔ K₂) ≤ toFun K₁ + toFun K₂
#align measure_theory.content MeasureTheory.Content

instance : Inhabited (Content G) :=
  ⟨{  toFun := fun _ => 0
      mono' := by simp
      sup_disjoint' := by simp
      sup_le' := by simp }⟩

/-- Although the `toFun` field of a content takes values in `ℝ≥0`, we register a coercion to
functions taking values in `ℝ≥0∞` as most constructions below rely on taking iSups and iInfs, which
is more convenient in a complete lattice, and aim at constructing a measure. -/
instance : CoeFun (Content G) fun _ => Compacts G → ℝ≥0∞ :=
  ⟨fun μ s => μ.toFun s⟩

namespace Content

variable (μ : Content G)

theorem apply_eq_coe_toFun (K : Compacts G) : μ K = μ.toFun K :=
  rfl
#align measure_theory.content.apply_eq_coe_to_fun MeasureTheory.Content.apply_eq_coe_toFun

theorem mono (K₁ K₂ : Compacts G) (h : (K₁ : Set G) ⊆ K₂) : μ K₁ ≤ μ K₂ := by
  simp [apply_eq_coe_toFun, μ.mono' _ _ h]
#align measure_theory.content.mono MeasureTheory.Content.mono

theorem sup_disjoint (K₁ K₂ : Compacts G) (h : Disjoint (K₁ : Set G) K₂)
    (h₁ : IsClosed (K₁ : Set G)) (h₂ : IsClosed (K₂ : Set G)) :
    μ (K₁ ⊔ K₂) = μ K₁ + μ K₂ := by
  simp [apply_eq_coe_toFun, μ.sup_disjoint' _ _ h]
#align measure_theory.content.sup_disjoint MeasureTheory.Content.sup_disjoint

theorem sup_le (K₁ K₂ : Compacts G) : μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂ := by
  simp only [apply_eq_coe_toFun]
  norm_cast
  exact μ.sup_le' _ _
#align measure_theory.content.sup_le MeasureTheory.Content.sup_le

theorem lt_top (K : Compacts G) : μ K < ∞ :=
  ENNReal.coe_lt_top
#align measure_theory.content.lt_top MeasureTheory.Content.lt_top

theorem empty : μ ⊥ = 0 := by
  have := μ.sup_disjoint' ⊥ ⊥
  simpa [apply_eq_coe_toFun] using this
#align measure_theory.content.empty MeasureTheory.Content.empty

/-- Constructing the inner content of a content. From a content defined on the compact sets, we
  obtain a function defined on all open sets, by taking the supremum of the content of all compact
  subsets. -/
def innerContent (U : Opens G) : ℝ≥0∞ :=
  ⨆ (K : Compacts G) (_ : (K : Set G) ⊆ U), μ K
#align measure_theory.content.inner_content MeasureTheory.Content.innerContent

theorem le_innerContent (K : Compacts G) (U : Opens G) (h2 : (K : Set G) ⊆ U) :
    μ K ≤ μ.innerContent U :=
  le_iSup_of_le K <| le_iSup (fun _ ↦ (μ.toFun K : ℝ≥0∞)) h2
#align measure_theory.content.le_inner_content MeasureTheory.Content.le_innerContent

theorem innerContent_le (U : Opens G) (K : Compacts G) (h2 : (U : Set G) ⊆ K) :
    μ.innerContent U ≤ μ K :=
  iSup₂_le fun _ hK' => μ.mono _ _ (Subset.trans hK' h2)
#align measure_theory.content.inner_content_le MeasureTheory.Content.innerContent_le

theorem innerContent_of_isCompact {K : Set G} (h1K : IsCompact K) (h2K : IsOpen K) :
    μ.innerContent ⟨K, h2K⟩ = μ ⟨K, h1K⟩ :=
  le_antisymm (iSup₂_le fun _ hK' => μ.mono _ ⟨K, h1K⟩ hK') (μ.le_innerContent _ _ Subset.rfl)
#align measure_theory.content.inner_content_of_is_compact MeasureTheory.Content.innerContent_of_isCompact

theorem innerContent_bot : μ.innerContent ⊥ = 0 := by
  refine' le_antisymm _ (zero_le _)
  rw [← μ.empty]
  refine' iSup₂_le fun K hK => _
  have : K = ⊥ := by
    ext1
    rw [subset_empty_iff.mp hK, Compacts.coe_bot]
  rw [this]
#align measure_theory.content.inner_content_bot MeasureTheory.Content.innerContent_bot

/-- This is "unbundled", because that is required for the API of `inducedOuterMeasure`. -/
theorem innerContent_mono ⦃U V : Set G⦄ (hU : IsOpen U) (hV : IsOpen V) (h2 : U ⊆ V) :
    μ.innerContent ⟨U, hU⟩ ≤ μ.innerContent ⟨V, hV⟩ :=
  biSup_mono fun _ hK => hK.trans h2
#align measure_theory.content.inner_content_mono MeasureTheory.Content.innerContent_mono

theorem innerContent_exists_compact {U : Opens G} (hU : μ.innerContent U ≠ ∞) {ε : ℝ≥0}
    (hε : ε ≠ 0) : ∃ K : Compacts G, (K : Set G) ⊆ U ∧ μ.innerContent U ≤ μ K + ε := by
  have h'ε := ENNReal.coe_ne_zero.2 hε
  rcases le_or_lt (μ.innerContent U) ε with h | h
  · exact ⟨⊥, empty_subset _, le_add_left h⟩
  have h₂ := ENNReal.sub_lt_self hU h.ne_bot h'ε
  conv at h₂ => rhs; rw [innerContent]
  simp only [lt_iSup_iff] at h₂
  rcases h₂ with ⟨U, h1U, h2U⟩; refine' ⟨U, h1U, _⟩
  rw [← tsub_le_iff_right]; exact le_of_lt h2U
#align measure_theory.content.inner_content_exists_compact MeasureTheory.Content.innerContent_exists_compact

/-- The inner content of a supremum of opens is at most the sum of the individual inner contents. -/
theorem innerContent_iSup_nat [R1Space G] (U : ℕ → Opens G) :
    μ.innerContent (⨆ i : ℕ, U i) ≤ ∑' i : ℕ, μ.innerContent (U i) := by
  have h3 : ∀ (t : Finset ℕ) (K : ℕ → Compacts G), μ (t.sup K) ≤ t.sum fun i => μ (K i) := by
    intro t K
    refine' Finset.induction_on t _ _
    · simp only [μ.empty, nonpos_iff_eq_zero, Finset.sum_empty, Finset.sup_empty]
    · intro n s hn ih
      rw [Finset.sup_insert, Finset.sum_insert hn]
      exact le_trans (μ.sup_le _ _) (add_le_add_left ih _)
  refine' iSup₂_le fun K hK => _
  obtain ⟨t, ht⟩ :=
    K.isCompact.elim_finite_subcover _ (fun i => (U i).isOpen) (by rwa [← Opens.coe_iSup])
  rcases K.isCompact.finite_compact_cover t (SetLike.coe ∘ U) (fun i _ => (U i).isOpen) ht with
    ⟨K', h1K', h2K', h3K'⟩
  let L : ℕ → Compacts G := fun n => ⟨K' n, h1K' n⟩
  convert le_trans (h3 t L) _
  · ext1
    rw [Compacts.coe_finset_sup, Finset.sup_eq_iSup]
    exact h3K'
  refine' le_trans (Finset.sum_le_sum _) (ENNReal.sum_le_tsum t)
  intro i _
  refine' le_trans _ (le_iSup _ (L i))
  refine' le_trans _ (le_iSup _ (h2K' i))
  rfl
#align measure_theory.content.inner_content_Sup_nat MeasureTheory.Content.innerContent_iSup_nat

/-- The inner content of a union of sets is at most the sum of the individual inner contents.
  This is the "unbundled" version of `innerContent_iSup_nat`.
  It is required for the API of `inducedOuterMeasure`. -/
theorem innerContent_iUnion_nat [R1Space G] ⦃U : ℕ → Set G⦄
    (hU : ∀ i : ℕ, IsOpen (U i)) :
    μ.innerContent ⟨⋃ i : ℕ, U i, isOpen_iUnion hU⟩ ≤ ∑' i : ℕ, μ.innerContent ⟨U i, hU i⟩ := by
  have := μ.innerContent_iSup_nat fun i => ⟨U i, hU i⟩
  rwa [Opens.iSup_def] at this
#align measure_theory.content.inner_content_Union_nat MeasureTheory.Content.innerContent_iUnion_nat

theorem innerContent_comap (f : G ≃ₜ G) (h : ∀ ⦃K : Compacts G⦄, μ (K.map f f.continuous) = μ K)
    (U : Opens G) : μ.innerContent (Opens.comap f.toContinuousMap U) = μ.innerContent U := by
  refine' (Compacts.equiv f).surjective.iSup_congr _ fun K => iSup_congr_Prop image_subset_iff _
  intro hK
  simp only [Equiv.coe_fn_mk, Subtype.mk_eq_mk, Compacts.equiv]
  apply h
#align measure_theory.content.inner_content_comap MeasureTheory.Content.innerContent_comap

@[to_additive]
theorem is_mul_left_invariant_innerContent [Group G] [TopologicalGroup G]
    (h : ∀ (g : G) {K : Compacts G}, μ (K.map _ <| continuous_mul_left g) = μ K) (g : G)
    (U : Opens G) :
    μ.innerContent (Opens.comap (Homeomorph.mulLeft g).toContinuousMap U) = μ.innerContent U := by
  convert μ.innerContent_comap (Homeomorph.mulLeft g) (fun K => h g) U
#align measure_theory.content.is_mul_left_invariant_inner_content MeasureTheory.Content.is_mul_left_invariant_innerContent
#align measure_theory.content.is_add_left_invariant_inner_content MeasureTheory.Content.is_add_left_invariant_innerContent

@[to_additive]
theorem innerContent_pos_of_is_mul_left_invariant [Group G] [TopologicalGroup G]
    (h3 : ∀ (g : G) {K : Compacts G}, μ (K.map _ <| continuous_mul_left g) = μ K) (K : Compacts G)
    (hK : μ K ≠ 0) (U : Opens G) (hU : (U : Set G).Nonempty) : 0 < μ.innerContent U := by
  have : (interior (U : Set G)).Nonempty := by rwa [U.isOpen.interior_eq]
  rcases compact_covered_by_mul_left_translates K.2 this with ⟨s, hs⟩
  suffices μ K ≤ s.card * μ.innerContent U by
    exact (ENNReal.mul_pos_iff.mp <| hK.bot_lt.trans_le this).2
  have : (K : Set G) ⊆ ↑(⨆ g ∈ s, Opens.comap (Homeomorph.mulLeft g).toContinuousMap U) := by
    simpa only [Opens.iSup_def, Opens.coe_comap, Subtype.coe_mk]
  refine' (μ.le_innerContent _ _ this).trans _
  refine'
    (rel_iSup_sum μ.innerContent μ.innerContent_bot (· ≤ ·) μ.innerContent_iSup_nat _ _).trans _
  simp only [μ.is_mul_left_invariant_innerContent h3, Finset.sum_const, nsmul_eq_mul, le_refl]
#align measure_theory.content.inner_content_pos_of_is_mul_left_invariant MeasureTheory.Content.innerContent_pos_of_is_mul_left_invariant
#align measure_theory.content.inner_content_pos_of_is_add_left_invariant MeasureTheory.Content.innerContent_pos_of_is_add_left_invariant

theorem innerContent_mono' ⦃U V : Set G⦄ (hU : IsOpen U) (hV : IsOpen V) (h2 : U ⊆ V) :
    μ.innerContent ⟨U, hU⟩ ≤ μ.innerContent ⟨V, hV⟩ :=
  biSup_mono fun _ hK => hK.trans h2
#align measure_theory.content.inner_content_mono' MeasureTheory.Content.innerContent_mono'

section OuterMeasure

/-- Extending a content on compact sets to an outer measure on all sets. -/
protected def outerMeasure : OuterMeasure G :=
  inducedOuterMeasure (fun U hU => μ.innerContent ⟨U, hU⟩) isOpen_empty μ.innerContent_bot
#align measure_theory.content.outer_measure MeasureTheory.Content.outerMeasure

variable [R1Space G]

theorem outerMeasure_opens (U : Opens G) : μ.outerMeasure U = μ.innerContent U :=
  inducedOuterMeasure_eq' (fun _ => isOpen_iUnion) μ.innerContent_iUnion_nat μ.innerContent_mono U.2
#align measure_theory.content.outer_measure_opens MeasureTheory.Content.outerMeasure_opens

theorem outerMeasure_of_isOpen (U : Set G) (hU : IsOpen U) :
    μ.outerMeasure U = μ.innerContent ⟨U, hU⟩ :=
  μ.outerMeasure_opens ⟨U, hU⟩
#align measure_theory.content.outer_measure_of_is_open MeasureTheory.Content.outerMeasure_of_isOpen

theorem outerMeasure_le (U : Opens G) (K : Compacts G) (hUK : (U : Set G) ⊆ K) :
    μ.outerMeasure U ≤ μ K :=
  (μ.outerMeasure_opens U).le.trans <| μ.innerContent_le U K hUK
#align measure_theory.content.outer_measure_le MeasureTheory.Content.outerMeasure_le

theorem le_outerMeasure_compacts (K : Compacts G) : μ K ≤ μ.outerMeasure K := by
  rw [Content.outerMeasure, inducedOuterMeasure_eq_iInf]
  · exact le_iInf fun U => le_iInf fun hU => le_iInf <| μ.le_innerContent K ⟨U, hU⟩
  · exact fun U hU => isOpen_iUnion hU
  · exact μ.innerContent_iUnion_nat
  · exact μ.innerContent_mono
#align measure_theory.content.le_outer_measure_compacts MeasureTheory.Content.le_outerMeasure_compacts

theorem outerMeasure_eq_iInf (A : Set G) :
    μ.outerMeasure A = ⨅ (U : Set G) (hU : IsOpen U) (_ : A ⊆ U), μ.innerContent ⟨U, hU⟩ :=
  inducedOuterMeasure_eq_iInf _ μ.innerContent_iUnion_nat μ.innerContent_mono A
#align measure_theory.content.outer_measure_eq_infi MeasureTheory.Content.outerMeasure_eq_iInf

theorem outerMeasure_interior_compacts (K : Compacts G) : μ.outerMeasure (interior K) ≤ μ K :=
  (μ.outerMeasure_opens <| Opens.interior K).le.trans <| μ.innerContent_le _ _ interior_subset
#align measure_theory.content.outer_measure_interior_compacts MeasureTheory.Content.outerMeasure_interior_compacts

theorem outerMeasure_exists_compact {U : Opens G} (hU : μ.outerMeasure U ≠ ∞) {ε : ℝ≥0}
    (hε : ε ≠ 0) : ∃ K : Compacts G, (K : Set G) ⊆ U ∧ μ.outerMeasure U ≤ μ.outerMeasure K + ε := by
  rw [μ.outerMeasure_opens] at hU ⊢
  rcases μ.innerContent_exists_compact hU hε with ⟨K, h1K, h2K⟩
  exact ⟨K, h1K, le_trans h2K <| add_le_add_right (μ.le_outerMeasure_compacts K) _⟩
#align measure_theory.content.outer_measure_exists_compact MeasureTheory.Content.outerMeasure_exists_compact

theorem outerMeasure_exists_open {A : Set G} (hA : μ.outerMeasure A ≠ ∞) {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∃ U : Opens G, A ⊆ U ∧ μ.outerMeasure U ≤ μ.outerMeasure A + ε := by
  rcases inducedOuterMeasure_exists_set _ μ.innerContent_iUnion_nat μ.innerContent_mono hA
      (ENNReal.coe_ne_zero.2 hε) with
    ⟨U, hU, h2U, h3U⟩
  exact ⟨⟨U, hU⟩, h2U, h3U⟩
#align measure_theory.content.outer_measure_exists_open MeasureTheory.Content.outerMeasure_exists_open

theorem outerMeasure_preimage (f : G ≃ₜ G) (h : ∀ ⦃K : Compacts G⦄, μ (K.map f f.continuous) = μ K)
    (A : Set G) : μ.outerMeasure (f ⁻¹' A) = μ.outerMeasure A := by
  refine' inducedOuterMeasure_preimage _ μ.innerContent_iUnion_nat μ.innerContent_mono _
    (fun _ => f.isOpen_preimage) _
  intro s hs
  convert μ.innerContent_comap f h ⟨s, hs⟩
#align measure_theory.content.outer_measure_preimage MeasureTheory.Content.outerMeasure_preimage

theorem outerMeasure_lt_top_of_isCompact [WeaklyLocallyCompactSpace G]
    {K : Set G} (hK : IsCompact K) :
    μ.outerMeasure K < ∞ := by
  rcases exists_compact_superset hK with ⟨F, h1F, h2F⟩
  calc
    μ.outerMeasure K ≤ μ.outerMeasure (interior F) := measure_mono h2F
    _ ≤ μ ⟨F, h1F⟩ := by
      apply μ.outerMeasure_le ⟨interior F, isOpen_interior⟩ ⟨F, h1F⟩ interior_subset
    _ < ⊤ := μ.lt_top _
#align measure_theory.content.outer_measure_lt_top_of_is_compact MeasureTheory.Content.outerMeasure_lt_top_of_isCompact

@[to_additive]
theorem is_mul_left_invariant_outerMeasure [Group G] [TopologicalGroup G]
    (h : ∀ (g : G) {K : Compacts G}, μ (K.map _ <| continuous_mul_left g) = μ K) (g : G)
    (A : Set G) : μ.outerMeasure ((g * ·) ⁻¹' A) = μ.outerMeasure A := by
  convert μ.outerMeasure_preimage (Homeomorph.mulLeft g) (fun K => h g) A
#align measure_theory.content.is_mul_left_invariant_outer_measure MeasureTheory.Content.is_mul_left_invariant_outerMeasure
#align measure_theory.content.is_add_left_invariant_outer_measure MeasureTheory.Content.is_add_left_invariant_outerMeasure

theorem outerMeasure_caratheodory (A : Set G) :
    MeasurableSet[μ.outerMeasure.caratheodory] A ↔
      ∀ U : Opens G, μ.outerMeasure (U ∩ A) + μ.outerMeasure (U \ A) ≤ μ.outerMeasure U := by
  rw [Opens.forall]
  apply inducedOuterMeasure_caratheodory
  · apply innerContent_iUnion_nat
  · apply innerContent_mono'
#align measure_theory.content.outer_measure_caratheodory MeasureTheory.Content.outerMeasure_caratheodory

@[to_additive]
theorem outerMeasure_pos_of_is_mul_left_invariant [Group G] [TopologicalGroup G]
    (h3 : ∀ (g : G) {K : Compacts G}, μ (K.map _ <| continuous_mul_left g) = μ K) (K : Compacts G)
    (hK : μ K ≠ 0) {U : Set G} (h1U : IsOpen U) (h2U : U.Nonempty) : 0 < μ.outerMeasure U := by
  convert μ.innerContent_pos_of_is_mul_left_invariant h3 K hK ⟨U, h1U⟩ h2U
  exact μ.outerMeasure_opens ⟨U, h1U⟩
#align measure_theory.content.outer_measure_pos_of_is_mul_left_invariant MeasureTheory.Content.outerMeasure_pos_of_is_mul_left_invariant
#align measure_theory.content.outer_measure_pos_of_is_add_left_invariant MeasureTheory.Content.outerMeasure_pos_of_is_add_left_invariant

variable [S : MeasurableSpace G] [BorelSpace G]

/-- For the outer measure coming from a content, all Borel sets are measurable. -/
theorem borel_le_caratheodory : S ≤ μ.outerMeasure.caratheodory := by
  rw [@BorelSpace.measurable_eq G _ _]
  refine' MeasurableSpace.generateFrom_le _
  intro U hU
  rw [μ.outerMeasure_caratheodory]
  intro U'
  rw [μ.outerMeasure_of_isOpen ((U' : Set G) ∩ U) (U'.isOpen.inter hU)]
  simp only [innerContent, iSup_subtype']
  rw [Opens.coe_mk]
  haveI : Nonempty { L : Compacts G // (L : Set G) ⊆ U' ∩ U } := ⟨⟨⊥, empty_subset _⟩⟩
  rw [ENNReal.iSup_add]
  refine' iSup_le _
  rintro ⟨L, hL⟩
  let L' : Compacts G := ⟨closure L, L.isCompact.closure⟩
  suffices μ L' + μ.outerMeasure (↑U' \ U) ≤ μ.outerMeasure U' by
    have A : μ L ≤ μ L' := μ.mono _ _ subset_closure
    exact (add_le_add_right A _).trans this
  simp only [subset_inter_iff] at hL
  have hL'U : (L' : Set G) ⊆ U := IsCompact.closure_subset_of_isOpen L.2 hU hL.2
  have hL'U' : (L' : Set G) ⊆ (U' : Set G) := IsCompact.closure_subset_of_isOpen L.2 U'.2 hL.1
  have : ↑U' \ U ⊆ U' \ L' := diff_subset_diff_right hL'U
  refine' le_trans (add_le_add_left (μ.outerMeasure.mono' this) _) _
  rw [μ.outerMeasure_of_isOpen (↑U' \ L') (IsOpen.sdiff U'.2 isClosed_closure)]
  simp only [innerContent, iSup_subtype']
  rw [Opens.coe_mk]
  haveI : Nonempty { M : Compacts G // (M : Set G) ⊆ ↑U' \ closure L } := ⟨⟨⊥, empty_subset _⟩⟩
  rw [ENNReal.add_iSup]
  refine' iSup_le _
  rintro ⟨M, hM⟩
  let M' : Compacts G := ⟨closure M, M.isCompact.closure⟩
  suffices μ L' + μ M' ≤ μ.outerMeasure U' by
    have A : μ M ≤ μ M' := μ.mono _ _ subset_closure
    exact (add_le_add_left A _).trans this
  have hM' : (M' : Set G) ⊆ U' \ L' :=
    IsCompact.closure_subset_of_isOpen M.2 (IsOpen.sdiff U'.2 isClosed_closure) hM
  have : (↑(L' ⊔ M') : Set G) ⊆ U' := by
    simp only [Compacts.coe_sup, union_subset_iff, hL'U', true_and]
    exact hM'.trans (diff_subset _ _ )
  rw [μ.outerMeasure_of_isOpen (↑U') U'.2]
  refine' le_trans (ge_of_eq _) (μ.le_innerContent _ _ this)
  exact μ.sup_disjoint L' M' (subset_diff.1 hM').2.symm isClosed_closure isClosed_closure
#align measure_theory.content.borel_le_caratheodory MeasureTheory.Content.borel_le_caratheodory

/-- The measure induced by the outer measure coming from a content, on the Borel sigma-algebra. -/
protected def measure : Measure G :=
  μ.outerMeasure.toMeasure μ.borel_le_caratheodory
#align measure_theory.content.measure MeasureTheory.Content.measure

theorem measure_apply {s : Set G} (hs : MeasurableSet s) : μ.measure s = μ.outerMeasure s :=
  toMeasure_apply _ _ hs
#align measure_theory.content.measure_apply MeasureTheory.Content.measure_apply

instance outerRegular : μ.measure.OuterRegular := by
  refine ⟨fun A hA r (hr : _ < _) ↦ ?_⟩
  rw [μ.measure_apply hA, outerMeasure_eq_iInf] at hr
  simp only [iInf_lt_iff] at hr
  rcases hr with ⟨U, hUo, hAU, hr⟩
  rw [← μ.outerMeasure_of_isOpen U hUo, ← μ.measure_apply hUo.measurableSet] at hr
  exact ⟨U, hAU, hUo, hr⟩

/-- In a locally compact space, any measure constructed from a content is regular. -/
instance regular [WeaklyLocallyCompactSpace G] : μ.measure.Regular := by
  have : IsFiniteMeasureOnCompacts μ.measure := by
    refine' ⟨fun K hK => _⟩
    apply (measure_mono subset_closure).trans_lt _
    rw [measure_apply _ isClosed_closure.measurableSet]
    exact μ.outerMeasure_lt_top_of_isCompact hK.closure
  refine' ⟨fun U hU r hr => _⟩
  rw [measure_apply _ hU.measurableSet, μ.outerMeasure_of_isOpen U hU] at hr
  simp only [innerContent, lt_iSup_iff] at hr
  rcases hr with ⟨K, hKU, hr⟩
  refine' ⟨K, hKU, K.2, hr.trans_le _⟩
  exact (μ.le_outerMeasure_compacts K).trans (le_toMeasure_apply _ _ _)
#align measure_theory.content.regular MeasureTheory.Content.regular

end OuterMeasure

section RegularContents

/-- A content `μ` is called regular if for every compact set `K`,
  `μ(K) = inf {μ(K') : K ⊂ int K' ⊂ K'}`. See Paul Halmos (1950), Measure Theory, §54-/
def ContentRegular :=
  ∀ ⦃K : TopologicalSpace.Compacts G⦄,
    μ K = ⨅ (K' : TopologicalSpace.Compacts G) (_ : (K : Set G) ⊆ interior (K' : Set G)), μ K'
#align measure_theory.content.content_regular MeasureTheory.Content.ContentRegular

theorem contentRegular_exists_compact (H : ContentRegular μ) (K : TopologicalSpace.Compacts G)
    {ε : NNReal} (hε : ε ≠ 0) :
    ∃ K' : TopologicalSpace.Compacts G, K.carrier ⊆ interior K'.carrier ∧ μ K' ≤ μ K + ε := by
  by_contra hc
  simp only [not_exists, not_and, not_le] at hc
  have lower_bound_iInf : μ K + ε ≤
      ⨅ (K' : TopologicalSpace.Compacts G) (_ : (K : Set G) ⊆ interior (K' : Set G)), μ K' :=
    le_iInf fun K' => le_iInf fun K'_hyp => le_of_lt (hc K' K'_hyp)
  rw [← H] at lower_bound_iInf
  exact (lt_self_iff_false (μ K)).mp (lt_of_le_of_lt' lower_bound_iInf
    (ENNReal.lt_add_right (ne_top_of_lt (μ.lt_top K)) (ENNReal.coe_ne_zero.mpr hε)))
#align measure_theory.content.content_regular_exists_compact MeasureTheory.Content.contentRegular_exists_compact

variable [MeasurableSpace G] [R1Space G] [BorelSpace G]

/-- If `μ` is a regular content, then the measure induced by `μ` will agree with `μ`
  on compact sets. -/
theorem measure_eq_content_of_regular (H : MeasureTheory.Content.ContentRegular μ)
    (K : TopologicalSpace.Compacts G) : μ.measure ↑K = μ K := by
  refine' le_antisymm _ _
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε εpos _
    obtain ⟨K', K'_hyp⟩ := contentRegular_exists_compact μ H K (ne_bot_of_gt εpos)
    calc
      μ.measure ↑K ≤ μ.measure (interior ↑K') := measure_mono K'_hyp.1
      _ ≤ μ K' := by
        rw [μ.measure_apply (IsOpen.measurableSet isOpen_interior)]
        exact μ.outerMeasure_interior_compacts K'
      _ ≤ μ K + ε := K'_hyp.right
  · calc
    μ K ≤ μ ⟨closure K, K.2.closure⟩ := μ.mono _ _ subset_closure
    _ ≤ μ.measure (closure K) := by
      rw [μ.measure_apply (isClosed_closure.measurableSet)]
      exact μ.le_outerMeasure_compacts _
    _ = μ.measure K := Measure.OuterRegular.measure_closure_eq_of_isCompact K.2
#align measure_theory.content.measure_eq_content_of_regular MeasureTheory.Content.measure_eq_content_of_regular

end RegularContents

end Content

end MeasureTheory
