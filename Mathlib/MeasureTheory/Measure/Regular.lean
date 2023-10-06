/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris Van Doorn, Yury Kudryashov
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

#align_import measure_theory.measure.regular from "leanprover-community/mathlib"@"bf6a01357ff5684b1ebcd0f1a13be314fc82c0bf"

/-!
# Regular measures

A measure is `OuterRegular` if the measure of any measurable set `A` is the infimum of `μ U` over
all open sets `U` containing `A`.

A measure is `WeaklyRegular` if it satisfies the following properties:
* it is outer regular;
* it is inner regular for open sets with respect to closed sets: the measure of any open set `U`
  is the supremum of `μ F` over all closed sets `F` contained in `U`.

A measure is `Regular` if it satisfies the following properties:
* it is finite on compact sets;
* it is outer regular;
* it is inner regular for open sets with respect to compacts sets: the measure of any open set `U`
  is the supremum of `μ K` over all compact sets `K` contained in `U`.

A measure is `InnerRegular` if it is inner regular for measurable sets with respect to compact
sets: the measure of any measurable set `s` is the supremum of `μ K` over all compact sets
contained in `s`.

A measure is `InnerRegularCompactLTTop` if it is inner regular for measurable sets of finite
measure with respect to compact sets: the measure of any measurable set `s` is the supremum
of `μ K` over all compact sets contained in `s`.

There is a reason for this zoo of regularity classes:
* A finite measure on a metric space is always weakly regular. Therefore, in probability theory,
  weakly regular measures play a prominent role.
* In locally compact topological spaces, there are two competing notions of Radon measures: the
  ones that are regular, and the ones that are inner regular. For any of these two notions, there is
  a Riesz representation theorem, and an existence and uniqueness statement for the Haar measure in
  locally compact topological groups. The two notions coincide in sigma-compact spaces, but they
  differ in general, so it is worth having the two of them.
* Both notions of Haar measure satisfy the weaker notion `InnerRegularCompactLTTop`, so it is worth
  trying to express theorems using this weaker notion whenever possible, to make sure that it
  applies to both Haar measures simultaneously.

While traditional textbooks on measure theory on locally compact spaces emphasize regular measures,
more recent textbooks emphasize that inner regular Haar measures are better behaved than regular
Haar measures, so our notion of Haar measure will be in terms of inner regular measures. Whenever
possible, however, we will prove some statements for regular measures also.

The five conditions above are registered as typeclasses for a measure `μ`, and implications between
them are recorded as instances. For example, in a Hausdorff topological space, regularity implies
weak regularity. Also, regularity or inner regularity both imply `InnerRegularCompactLTTop`.

In order to avoid code duplication, we also define a measure `μ` to be `InnerRegularWRT` for sets
satisfying a predicate `q` with respect to sets satisfying a predicate `p` if for any set
`U ∈ {U | q U}` and a number `r < μ U` there exists `F ⊆ U` such that `p F` and `r < μ F`.

There are two main nontrivial results in the development below:
* `InnerRegularWRT.measurableSet_of_open` shows that, for an outer regular measure, inner
regularity for open sets with respect to compact sets or closed sets implies inner regularity for
all measurable sets of finite measure (with respect to compact sets or closed sets respectively).
* `InnerRegularWRT.weaklyRegular_of_finite` shows that a finite measure which is inner regular for
open sets with respect to closed sets (for instance a finite measure on a metric space) is weakly
regular.

All other results are deduced from these ones.

Here is an example showing how regularity and inner regularity may differ even on locally compact
spaces. Consider the group `ℝ × ℝ` where the first factor has the discrete topology and the second
one the usual topology. It is a locally compact Hausdorff topological group, with Haar measure equal
to Lebesgue measure on each vertical fiber. Let us consider the regular version of Haar measure.
Then the set `ℝ × {0}` has infinite measure (by outer regularity), but any compact set it contains
has zero measure (as it is finite). In fact, this set only contains subset with measure zero or
infinity. The inner regular version of Haar measure, on the other hand, gives zero mass to the
set `ℝ × {0}`.

Several authors require both regularity and inner regularity for their measures. We have opted
for the more fine grained definitions above as they apply more generally.

## Main definitions

* `MeasureTheory.Measure.OuterRegular μ`: a typeclass registering that a measure `μ` on a
  topological space is outer regular.
* `MeasureTheory.Measure.Regular μ`: a typeclass registering that a measure `μ` on a topological
  space is regular.
* `MeasureTheory.Measure.WeaklyRegular μ`: a typeclass registering that a measure `μ` on a
  topological space is weakly regular.
* `MeasureTheory.Measure.InnerRegularWRT μ p q`: a non-typeclass predicate saying that a measure `μ`
  is inner regular for sets satisfying `q` with respect to sets satisfying `p`.
* `MeasureTheory.Measure.InnerRegular μ`: a typeclass registering that a measure `μ` on a
  topological space is inner regular for measurable sets with respect to compact sets.

## Main results

### Outer regular measures

* `Set.measure_eq_iInf_isOpen` asserts that, when `μ` is outer regular, the measure of a
  set is the infimum of the measure of open sets containing it.
* `Set.exists_isOpen_lt_of_lt` asserts that, when `μ` is outer regular, for every set `s`
  and `r > μ s` there exists an open superset `U ⊇ s` of measure less than `r`.
* push forward of an outer regular measure is outer regular, and scalar multiplication of a regular
  measure by a finite number is outer regular.

### Weakly regular measures

* `IsOpen.measure_eq_iSup_isClosed` asserts that the measure of an open set is the supremum of
  the measure of closed sets it contains.
* `IsOpen.exists_lt_isClosed`: for an open set `U` and `r < μ U`, there exists a closed `F ⊆ U`
  of measure greater than `r`;
* `MeasurableSet.measure_eq_iSup_isClosed_of_ne_top` asserts that the measure of a measurable set
  of finite measure is the supremum of the measure of closed sets it contains.
*  `MeasurableSet.exists_lt_isClosed_of_ne_top` and `MeasurableSet.exists_isClosed_lt_add`:
  a measurable set of finite measure can be approximated by a closed subset (stated as
  `r < μ F` and `μ s < μ F + ε`, respectively).
* `MeasureTheory.Measure.WeaklyRegular.of_pseudoEMetricSpace_of_isFiniteMeasure` is an
  instance registering that a finite measure on a metric space is weakly regular (in fact, a pseudo
  emetric space is enough);
* `MeasureTheory.Measure.WeaklyRegular.of_pseudoEMetric_secondCountable_of_locallyFinite`
  is an instance registering that a locally finite measure on a second countable metric space (or
  even a pseudo emetric space) is weakly regular.

### Regular measures

* `IsOpen.measure_eq_iSup_isCompact` asserts that the measure of an open set is the supremum of
  the measure of compact sets it contains.
* `IsOpen.exists_lt_isCompact`: for an open set `U` and `r < μ U`, there exists a compact `K ⊆ U`
  of measure greater than `r`;
* `MeasurableSet.measure_eq_iSup_isCompact_of_ne_top` asserts that the measure of a measurable set
  of finite measure is the supremum of the measure of compact sets it contains.
*  `MeasurableSet.exists_lt_isCompact_of_ne_top` and `MeasurableSet.exists_isCompact_lt_add`:
  a measurable set of finite measure can be approximated by a compact subset (stated as
  `r < μ K` and `μ s < μ K + ε`, respectively).
* `MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure` is an
  instance registering that a locally finite measure on a `σ`-compact metric space is regular (in
  fact, an emetric space is enough).

### Inner regular measures

* `MeasurableSet.measure_eq_iSup_isCompact` asserts that the measure of a measurable set is the
  supremum of the measure of compact sets it contains.
* `MeasurableSet.exists_lt_isCompact`: for a measurable set `s` and `r < μ s`, there exists a
  compact `K ⊆ s` of measure greater than `r`;
* `MeasurableSet.measure_eq_iSup_isCompact_of_ne_top` asserts that the measure of a measurable set
  of finite measure is the supremum of the measure of compact sets it contains.

## Implementation notes

The main nontrivial statement is `MeasureTheory.Measure.InnerRegular.weaklyRegular_of_finite`,
expressing that in a finite measure space, if every open set can be approximated from inside by
closed sets, then the measure is in fact weakly regular. To prove that we show that any measurable
set can be approximated from inside by closed sets and from outside by open sets. This statement is
proved by measurable induction, starting from open sets and checking that it is stable by taking
complements (this is the point of this condition, being symmetrical between inside and outside) and
countable disjoint unions.

Once this statement is proved, one deduces results for `σ`-finite measures from this statement, by
restricting them to finite measure sets (and proving that this restriction is weakly regular, using
again the same statement).

## References

[Halmos, Measure Theory, §52][halmos1950measure]. Note that Halmos uses an unusual definition of
Borel sets (for him, they are elements of the `σ`-algebra generated by compact sets!), so his
proofs or statements do not apply directly.

[Billingsley, Convergence of Probability Measures][billingsley1999]

[Bogachev, Measure Theory, volume 2, Theorem 7.11.1][bogachev2007]
-/


open Set Filter ENNReal Topology NNReal BigOperators

namespace MeasureTheory

namespace Measure

/-- We say that a measure `μ` is *inner regular* with respect to predicates `p q : Set α → Prop`,
if for every `U` such that `q U` and `r < μ U`, there exists a subset `K ⊆ U` satisfying `p K`
of measure greater than `r`.

This definition is used to prove some facts about regular and weakly regular measures without
repeating the proofs. -/
def InnerRegularWRT {α} {_ : MeasurableSpace α} (μ : Measure α) (p q : Set α → Prop) :=
  ∀ ⦃U⦄, q U → ∀ r < μ U, ∃ K, K ⊆ U ∧ p K ∧ r < μ K
#align measure_theory.measure.inner_regular MeasureTheory.Measure.InnerRegularWRT

namespace InnerRegularWRT

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {p q : Set α → Prop} {U : Set α}
  {ε : ℝ≥0∞}

theorem measure_eq_iSup (H : InnerRegularWRT μ p q) (hU : q U) :
    μ U = ⨆ (K) (_ : K ⊆ U) (_ : p K), μ K := by
  refine'
    le_antisymm (le_of_forall_lt fun r hr => _) (iSup₂_le fun K hK => iSup_le fun _ => μ.mono hK)
  simpa only [lt_iSup_iff, exists_prop] using H hU r hr
#align measure_theory.measure.inner_regular.measure_eq_supr MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup

theorem exists_subset_lt_add (H : InnerRegularWRT μ p q) (h0 : p ∅) (hU : q U) (hμU : μ U ≠ ∞)
    (hε : ε ≠ 0) : ∃ K, K ⊆ U ∧ p K ∧ μ U < μ K + ε := by
  cases' eq_or_ne (μ U) 0 with h₀ h₀
  · refine' ⟨∅, empty_subset _, h0, _⟩
    rwa [measure_empty, h₀, zero_add, pos_iff_ne_zero]
  · rcases H hU _ (ENNReal.sub_lt_self hμU h₀ hε) with ⟨K, hKU, hKc, hrK⟩
    exact ⟨K, hKU, hKc, ENNReal.lt_add_of_sub_lt_right (Or.inl hμU) hrK⟩
#align measure_theory.measure.inner_regular.exists_subset_lt_add MeasureTheory.Measure.InnerRegularWRT.exists_subset_lt_add

theorem map {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {pa qa : Set α → Prop}
    (H : InnerRegularWRT μ pa qa) (f : α ≃ β) (hf : AEMeasurable f μ) {pb qb : Set β → Prop}
    (hAB : ∀ U, qb U → qa (f ⁻¹' U)) (hAB' : ∀ K, pa K → pb (f '' K))
    (hB₁ : ∀ K, pb K → MeasurableSet K) (hB₂ : ∀ U, qb U → MeasurableSet U) :
    InnerRegularWRT (map f μ) pb qb := by
  intro U hU r hr
  rw [map_apply_of_aemeasurable hf (hB₂ _ hU)] at hr
  rcases H (hAB U hU) r hr with ⟨K, hKU, hKc, hK⟩
  refine' ⟨f '' K, image_subset_iff.2 hKU, hAB' _ hKc, _⟩
  rwa [map_apply_of_aemeasurable hf (hB₁ _ <| hAB' _ hKc), f.preimage_image]
#align measure_theory.measure.inner_regular.map MeasureTheory.Measure.InnerRegularWRT.map

theorem smul (H : InnerRegularWRT μ p q) (c : ℝ≥0∞) : InnerRegularWRT (c • μ) p q := by
  intro U hU r hr
  rw [smul_apply, H.measure_eq_iSup hU, smul_eq_mul] at hr
  simpa only [ENNReal.mul_iSup, lt_iSup_iff, exists_prop] using hr
#align measure_theory.measure.inner_regular.smul MeasureTheory.Measure.InnerRegularWRT.smul

theorem trans {q' : Set α → Prop} (H : InnerRegularWRT μ p q) (H' : InnerRegularWRT μ q q') :
    InnerRegularWRT μ p q' := by
  intro U hU r hr
  rcases H' hU r hr with ⟨F, hFU, hqF, hF⟩; rcases H hqF _ hF with ⟨K, hKF, hpK, hrK⟩
  exact ⟨K, hKF.trans hFU, hpK, hrK⟩
#align measure_theory.measure.inner_regular.trans MeasureTheory.Measure.InnerRegularWRT.trans

end InnerRegularWRT

variable {α β : Type*} [MeasurableSpace α] [TopologicalSpace α] {μ : Measure α}

/-- A measure `μ` is outer regular if `μ(A) = inf {μ(U) | A ⊆ U open}` for a measurable set `A`.

This definition implies the same equality for any (not necessarily measurable) set, see
`Set.measure_eq_iInf_isOpen`. -/
class OuterRegular (μ : Measure α) : Prop where
  protected outerRegular :
    ∀ ⦃A : Set α⦄, MeasurableSet A → ∀ r > μ A, ∃ U, U ⊇ A ∧ IsOpen U ∧ μ U < r
#align measure_theory.measure.outer_regular MeasureTheory.Measure.OuterRegular
#align measure_theory.measure.outer_regular.outer_regular MeasureTheory.Measure.OuterRegular.outerRegular

/-- A measure `μ` is regular if
  - it is finite on all compact sets;
  - it is outer regular: `μ(A) = inf {μ(U) | A ⊆ U open}` for `A` measurable;
  - it is inner regular for open sets, using compact sets:
    `μ(U) = sup {μ(K) | K ⊆ U compact}` for `U` open. -/
class Regular (μ : Measure α) extends IsFiniteMeasureOnCompacts μ, OuterRegular μ : Prop where
  innerRegular : InnerRegularWRT μ IsCompact IsOpen
#align measure_theory.measure.regular MeasureTheory.Measure.Regular

/-- A measure `μ` is weakly regular if
  - it is outer regular: `μ(A) = inf {μ(U) | A ⊆ U open}` for `A` measurable;
  - it is inner regular for open sets, using closed sets:
    `μ(U) = sup {μ(F) | F ⊆ U closed}` for `U` open. -/
class WeaklyRegular (μ : Measure α) extends OuterRegular μ : Prop where
  protected innerRegular : InnerRegularWRT μ IsClosed IsOpen
#align measure_theory.measure.weakly_regular MeasureTheory.Measure.WeaklyRegular
#align measure_theory.measure.weakly_regular.inner_regular MeasureTheory.Measure.WeaklyRegular.innerRegular

/-- A measure `μ` is inner regular for finite measure sets with respect to compact sets:
for any measurable set `s` with finite measure, then `μ(s) = sup {μ(K) | K ⊆ s compact}`. The
main interest of this class is that it is satisfied for both natural Haar measures (the regular one
and the inner regular one). -/
class InnerRegularCompactLTTop (μ : Measure α) : Prop where
  protected innerRegular : InnerRegularWRT μ IsCompact (fun s ↦ MeasurableSet s ∧ μ s ≠ ∞)

-- see Note [lower instance priority]
/-- A regular measure is weakly regular. -/
instance (priority := 100) Regular.weaklyRegular [T2Space α] [Regular μ] : WeaklyRegular μ where
  innerRegular _U hU r hr :=
    let ⟨K, hKU, hcK, hK⟩ := Regular.innerRegular hU r hr
    ⟨K, hKU, hcK.isClosed, hK⟩
#align measure_theory.measure.regular.weakly_regular MeasureTheory.Measure.Regular.weaklyRegular

namespace OuterRegular

instance zero : OuterRegular (0 : Measure α) :=
  ⟨fun A _ _r hr => ⟨univ, subset_univ A, isOpen_univ, hr⟩⟩
#align measure_theory.measure.outer_regular.zero MeasureTheory.Measure.OuterRegular.zero

/-- Given `r` larger than the measure of a set `A`, there exists an open superset of `A` with
measure less than `r`. -/
theorem _root_.Set.exists_isOpen_lt_of_lt [OuterRegular μ] (A : Set α) (r : ℝ≥0∞) (hr : μ A < r) :
    ∃ U, U ⊇ A ∧ IsOpen U ∧ μ U < r := by
  rcases OuterRegular.outerRegular (measurableSet_toMeasurable μ A) r
      (by rwa [measure_toMeasurable]) with
    ⟨U, hAU, hUo, hU⟩
  exact ⟨U, (subset_toMeasurable _ _).trans hAU, hUo, hU⟩
#align set.exists_is_open_lt_of_lt Set.exists_isOpen_lt_of_lt

/-- For an outer regular measure, the measure of a set is the infimum of the measures of open sets
containing it. -/
theorem _root_.Set.measure_eq_iInf_isOpen (A : Set α) (μ : Measure α) [OuterRegular μ] :
    μ A = ⨅ (U : Set α) (_ : A ⊆ U) (_ : IsOpen U), μ U := by
  refine' le_antisymm (le_iInf₂ fun s hs => le_iInf fun _ => μ.mono hs) _
  refine' le_of_forall_lt' fun r hr => _
  simpa only [iInf_lt_iff, exists_prop] using A.exists_isOpen_lt_of_lt r hr
#align set.measure_eq_infi_is_open Set.measure_eq_iInf_isOpen

theorem _root_.Set.exists_isOpen_lt_add [OuterRegular μ] (A : Set α) (hA : μ A ≠ ∞) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ U, U ⊇ A ∧ IsOpen U ∧ μ U < μ A + ε :=
  A.exists_isOpen_lt_of_lt _ (ENNReal.lt_add_right hA hε)
#align set.exists_is_open_lt_add Set.exists_isOpen_lt_add

theorem _root_.Set.exists_isOpen_le_add (A : Set α) (μ : Measure α) [OuterRegular μ] {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ U, U ⊇ A ∧ IsOpen U ∧ μ U ≤ μ A + ε := by
  rcases eq_or_ne (μ A) ∞ with (H | H)
  · exact ⟨univ, subset_univ _, isOpen_univ, by simp only [H, _root_.top_add, le_top]⟩
  · rcases A.exists_isOpen_lt_add H hε with ⟨U, AU, U_open, hU⟩
    exact ⟨U, AU, U_open, hU.le⟩
#align set.exists_is_open_le_add Set.exists_isOpen_le_add

theorem _root_.MeasurableSet.exists_isOpen_diff_lt [OuterRegular μ] {A : Set α}
    (hA : MeasurableSet A) (hA' : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ U, U ⊇ A ∧ IsOpen U ∧ μ U < ∞ ∧ μ (U \ A) < ε := by
  rcases A.exists_isOpen_lt_add hA' hε with ⟨U, hAU, hUo, hU⟩
  use U, hAU, hUo, hU.trans_le le_top
  exact measure_diff_lt_of_lt_add hA hAU hA' hU
#align measurable_set.exists_is_open_diff_lt MeasurableSet.exists_isOpen_diff_lt

protected theorem map [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] (f : α ≃ₜ β) (μ : Measure α) [OuterRegular μ] :
    (Measure.map f μ).OuterRegular := by
  refine' ⟨fun A hA r hr => _⟩
  rw [map_apply f.measurable hA, ← f.image_symm] at hr
  rcases Set.exists_isOpen_lt_of_lt _ r hr with ⟨U, hAU, hUo, hU⟩
  have : IsOpen (f.symm ⁻¹' U) := hUo.preimage f.symm.continuous
  refine' ⟨f.symm ⁻¹' U, image_subset_iff.1 hAU, this, _⟩
  rwa [map_apply f.measurable this.measurableSet, f.preimage_symm, f.preimage_image]
#align measure_theory.measure.outer_regular.map MeasureTheory.Measure.OuterRegular.map

protected theorem smul (μ : Measure α) [OuterRegular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) :
    (x • μ).OuterRegular := by
  rcases eq_or_ne x 0 with (rfl | h0)
  · rw [zero_smul]
    exact OuterRegular.zero
  · refine' ⟨fun A _ r hr => _⟩
    rw [smul_apply, A.measure_eq_iInf_isOpen, smul_eq_mul] at hr
    simpa only [ENNReal.mul_iInf_of_ne h0 hx, gt_iff_lt, iInf_lt_iff, exists_prop] using hr
#align measure_theory.measure.outer_regular.smul MeasureTheory.Measure.OuterRegular.smul

end OuterRegular

/-- If a measure `μ` admits finite spanning open sets such that the restriction of `μ` to each set
is outer regular, then the original measure is outer regular as well. -/
protected theorem FiniteSpanningSetsIn.outerRegular [OpensMeasurableSpace α] {μ : Measure α}
    (s : μ.FiniteSpanningSetsIn { U | IsOpen U ∧ OuterRegular (μ.restrict U) }) :
    OuterRegular μ := by
  refine' ⟨fun A hA r hr => _⟩
  have hm : ∀ n, MeasurableSet (s.set n) := fun n => (s.set_mem n).1.measurableSet
  haveI : ∀ n, OuterRegular (μ.restrict (s.set n)) := fun n => (s.set_mem n).2
  -- Note that `A = ⋃ n, A ∩ disjointed s n`. We replace `A` with this sequence.
  obtain ⟨A, hAm, hAs, hAd, rfl⟩ :
    ∃ A' : ℕ → Set α,
      (∀ n, MeasurableSet (A' n)) ∧
        (∀ n, A' n ⊆ s.set n) ∧ Pairwise (Disjoint on A') ∧ A = ⋃ n, A' n := by
    refine'
      ⟨fun n => A ∩ disjointed s.set n, fun n => hA.inter (MeasurableSet.disjointed hm _), fun n =>
        (inter_subset_right _ _).trans (disjointed_subset _ _),
        (disjoint_disjointed s.set).mono fun k l hkl => hkl.mono inf_le_right inf_le_right, _⟩
    rw [← inter_iUnion, iUnion_disjointed, s.spanning, inter_univ]
  rcases ENNReal.exists_pos_sum_of_countable' (tsub_pos_iff_lt.2 hr).ne' ℕ with ⟨δ, δ0, hδε⟩
  rw [lt_tsub_iff_right, add_comm] at hδε
  have : ∀ n, ∃ (U : _) (_ : U ⊇ A n), IsOpen U ∧ μ U < μ (A n) + δ n := by
    intro n
    have H₁ : ∀ t, μ.restrict (s.set n) t = μ (t ∩ s.set n) := fun t => restrict_apply' (hm n)
    have Ht : μ.restrict (s.set n) (A n) ≠ ⊤ := by
      rw [H₁]
      exact ((measure_mono <| inter_subset_right _ _).trans_lt (s.finite n)).ne
    rcases(A n).exists_isOpen_lt_add Ht (δ0 n).ne' with ⟨U, hAU, hUo, hU⟩
    rw [H₁, H₁, inter_eq_self_of_subset_left (hAs _)] at hU
    exact ⟨U ∩ s.set n, subset_inter hAU (hAs _), hUo.inter (s.set_mem n).1, hU⟩
  choose U hAU hUo hU using this
  refine' ⟨⋃ n, U n, iUnion_mono hAU, isOpen_iUnion hUo, _⟩
  calc
    μ (⋃ n, U n) ≤ ∑' n, μ (U n) := measure_iUnion_le _
    _ ≤ ∑' n, (μ (A n) + δ n) := (ENNReal.tsum_le_tsum fun n => (hU n).le)
    _ = ∑' n, μ (A n) + ∑' n, δ n := ENNReal.tsum_add
    _ = μ (⋃ n, A n) + ∑' n, δ n := (congr_arg₂ (· + ·) (measure_iUnion hAd hAm).symm rfl)
    _ < r := hδε
#align measure_theory.measure.finite_spanning_sets_in.outer_regular MeasureTheory.Measure.FiniteSpanningSetsIn.outerRegular

namespace InnerRegularWRT

variable {p q : Set α → Prop} {U s : Set α} {ε r : ℝ≥0∞}

/-- If a measure is inner regular (using closed or compact sets), then every measurable set of
finite measure can be approximated by a (closed or compact) subset. -/
theorem measurableSet_of_open [OuterRegular μ] (H : InnerRegularWRT μ p IsOpen) (h0 : p ∅)
    (hd : ∀ ⦃s U⦄, p s → IsOpen U → p (s \ U)) :
    InnerRegularWRT μ p fun s => MeasurableSet s ∧ μ s ≠ ∞ := by
  rintro s ⟨hs, hμs⟩ r hr
  obtain ⟨ε, hε, hεs, rfl⟩ : ∃ (ε : _) (_ : ε ≠ 0), ε + ε ≤ μ s ∧ r = μ s - (ε + ε) := by
    use (μ s - r) / 2
    simp [*, hr.le, ENNReal.add_halves, ENNReal.sub_sub_cancel, le_add_right]
  rcases hs.exists_isOpen_diff_lt hμs hε with ⟨U, hsU, hUo, hUt, hμU⟩
  rcases (U \ s).exists_isOpen_lt_of_lt _ hμU with ⟨U', hsU', hU'o, hμU'⟩
  replace hsU' := diff_subset_comm.1 hsU'
  rcases H.exists_subset_lt_add h0 hUo hUt.ne hε with ⟨K, hKU, hKc, hKr⟩
  refine' ⟨K \ U', fun x hx => hsU' ⟨hKU hx.1, hx.2⟩, hd hKc hU'o, ENNReal.sub_lt_of_lt_add hεs _⟩
  calc
    μ s ≤ μ U := μ.mono hsU
    _ < μ K + ε := hKr
    _ ≤ μ (K \ U') + μ U' + ε := (add_le_add_right (tsub_le_iff_right.1 le_measure_diff) _)
    _ ≤ μ (K \ U') + ε + ε := by
      apply add_le_add_right; apply add_le_add_left
      exact hμU'.le
    _ = μ (K \ U') + (ε + ε) := add_assoc _ _ _
#align measure_theory.measure.inner_regular.measurable_set_of_open MeasureTheory.Measure.InnerRegularWRT.measurableSet_of_open

open Finset

/-- In a finite measure space, assume that any open set can be approximated from inside by closed
sets. Then the measure is weakly regular. -/
theorem weaklyRegular_of_finite [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (H : InnerRegularWRT μ IsClosed IsOpen) : WeaklyRegular μ := by
  have hfin : ∀ {s}, μ s ≠ ⊤ := @(measure_ne_top μ)
  suffices ∀ s, MeasurableSet s → ∀ ε, ε ≠ 0 → ∃ F, F ⊆ s ∧ ∃ U, U ⊇ s ∧
      IsClosed F ∧ IsOpen U ∧ μ s ≤ μ F + ε ∧ μ U ≤ μ s + ε by
    refine'
      { outerRegular := fun s hs r hr => _
        innerRegular := H }
    rcases exists_between hr with ⟨r', hsr', hr'r⟩
    rcases this s hs _ (tsub_pos_iff_lt.2 hsr').ne' with ⟨-, -, U, hsU, -, hUo, -, H⟩
    refine' ⟨U, hsU, hUo, _⟩
    rw [add_tsub_cancel_of_le hsr'.le] at H
    exact H.trans_lt hr'r
  refine' MeasurableSet.induction_on_open _ _ _
  /- The proof is by measurable induction: we should check that the property is true for the empty
    set, for open sets, and is stable by taking the complement and by taking countable disjoint
    unions. The point of the property we are proving is that it is stable by taking complements
    (exchanging the roles of closed and open sets and thanks to the finiteness of the measure). -/
  -- check for open set
  · intro U hU ε hε
    rcases H.exists_subset_lt_add isClosed_empty hU hfin hε with ⟨F, hsF, hFc, hF⟩
    exact ⟨F, hsF, U, Subset.rfl, hFc, hU, hF.le, le_self_add⟩
  -- check for complements
  · rintro s hs H ε hε
    rcases H ε hε with ⟨F, hFs, U, hsU, hFc, hUo, hF, hU⟩
    refine'
      ⟨Uᶜ, compl_subset_compl.2 hsU, Fᶜ, compl_subset_compl.2 hFs, hUo.isClosed_compl,
        hFc.isOpen_compl, _⟩
    simp only [measure_compl_le_add_iff, *, hUo.measurableSet, hFc.measurableSet, true_and_iff]
  -- check for disjoint unions
  · intro s hsd hsm H ε ε0
    have ε0' : ε / 2 ≠ 0 := (ENNReal.half_pos ε0).ne'
    rcases ENNReal.exists_pos_sum_of_countable' ε0' ℕ with ⟨δ, δ0, hδε⟩
    choose F hFs U hsU hFc hUo hF hU using fun n => H n (δ n) (δ0 n).ne'
    -- the approximating closed set is constructed by considering finitely many sets `s i`, which
    -- cover all the measure up to `ε/2`, approximating each of these by a closed set `F i`, and
    -- taking the union of these (finitely many) `F i`.
    have : Tendsto (fun t => (∑ k in t, μ (s k)) + ε / 2) atTop (𝓝 <| μ (⋃ n, s n) + ε / 2) := by
      rw [measure_iUnion hsd hsm]
      exact Tendsto.add ENNReal.summable.hasSum tendsto_const_nhds
    rcases(this.eventually <| lt_mem_nhds <| ENNReal.lt_add_right hfin ε0').exists with ⟨t, ht⟩
    -- the approximating open set is constructed by taking for each `s n` an approximating open set
    -- `U n` with measure at most `μ (s n) + δ n` for a summable `δ`, and taking the union of these.
    refine'
      ⟨⋃ k ∈ t, F k, iUnion_mono fun k => iUnion_subset fun _ => hFs _, ⋃ n, U n, iUnion_mono hsU,
        isClosed_biUnion_finset fun k _ => hFc k, isOpen_iUnion hUo, ht.le.trans _, _⟩
    · calc
        (∑ k in t, μ (s k)) + ε / 2 ≤ ((∑ k in t, μ (F k)) + ∑ k in t, δ k) + ε / 2 := by
          rw [← sum_add_distrib]
          exact add_le_add_right (sum_le_sum fun k _ => hF k) _
        _ ≤ (∑ k in t, μ (F k)) + ε / 2 + ε / 2 :=
          (add_le_add_right (add_le_add_left ((ENNReal.sum_le_tsum _).trans hδε.le) _) _)
        _ = μ (⋃ k ∈ t, F k) + ε := by
          rw [measure_biUnion_finset, add_assoc, ENNReal.add_halves]
          exacts [fun k _ n _ hkn => (hsd hkn).mono (hFs k) (hFs n),
            fun k _ => (hFc k).measurableSet]
    · calc
        μ (⋃ n, U n) ≤ ∑' n, μ (U n) := measure_iUnion_le _
        _ ≤ ∑' n, (μ (s n) + δ n) := (ENNReal.tsum_le_tsum hU)
        _ = μ (⋃ n, s n) + ∑' n, δ n := by rw [measure_iUnion hsd hsm, ENNReal.tsum_add]
        _ ≤ μ (⋃ n, s n) + ε := add_le_add_left (hδε.le.trans ENNReal.half_le_self) _
#align measure_theory.measure.inner_regular.weakly_regular_of_finite MeasureTheory.Measure.InnerRegularWRT.weaklyRegular_of_finite

/-- In a metric space (or even a pseudo emetric space), an open set can be approximated from inside
by closed sets. -/
theorem of_pseudoEMetricSpace {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) : InnerRegularWRT μ IsClosed IsOpen := by
  intro U hU r hr
  rcases hU.exists_iUnion_isClosed with ⟨F, F_closed, -, rfl, F_mono⟩
  rw [measure_iUnion_eq_iSup F_mono.directed_le] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  exact ⟨F n, subset_iUnion _ _, F_closed n, hn⟩
#align measure_theory.measure.inner_regular.of_pseudo_emetric_space MeasureTheory.Measure.InnerRegularWRT.of_pseudoEMetricSpace

/-- In a `σ`-compact space, any closed set can be approximated by a compact subset. -/
theorem isCompact_isClosed {X : Type*} [TopologicalSpace X] [SigmaCompactSpace X]
    [MeasurableSpace X] (μ : Measure X) : InnerRegularWRT μ IsCompact IsClosed := by
  intro F hF r hr
  set B : ℕ → Set X := compactCovering X
  have hBc : ∀ n, IsCompact (F ∩ B n) := fun n => (isCompact_compactCovering X n).inter_left hF
  have hBU : ⋃ n, F ∩ B n = F := by rw [← inter_iUnion, iUnion_compactCovering, Set.inter_univ]
  have : μ F = ⨆ n, μ (F ∩ B n) := by
    rw [← measure_iUnion_eq_iSup, hBU]
    exact Monotone.directed_le fun m n h => inter_subset_inter_right _ (compactCovering_subset _ h)
  rw [this] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  exact ⟨_, inter_subset_left _ _, hBc n, hn⟩
#align measure_theory.measure.inner_regular.is_compact_is_closed MeasureTheory.Measure.InnerRegularWRT.isCompact_isClosed

end InnerRegularWRT

namespace InnerRegularCompactLTTop

/-- If `μ` is inner regular for finite measure sets with respect to compact sets,
then any measurable set of finite measure can be approximated by a
compact subset. See also `MeasurableSet.exists_lt_isCompact_of_ne_top`. -/
theorem _root_.MeasurableSet.exists_isCompact_lt_add [InnerRegularCompactLTTop μ]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ μ A < μ K + ε :=
  InnerRegularCompactLTTop.innerRegular.exists_subset_lt_add isCompact_empty ⟨hA, h'A⟩ h'A hε
#align measurable_set.exists_is_compact_lt_add MeasurableSet.exists_isCompact_lt_add

/-- If `μ` is inner regular for finite measure sets with respect to compact sets,
then any measurable set of finite measure can be approximated by a
compact subset. See also `MeasurableSet.exists_isCompact_lt_add` and
`MeasurableSet.exists_lt_isCompact_of_ne_top`. -/
theorem _root_.MeasurableSet.exists_isCompact_diff_lt [OpensMeasurableSpace α] [T2Space α]
    [InnerRegularCompactLTTop μ]  ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ μ (A \ K) < ε := by
  rcases hA.exists_isCompact_lt_add h'A hε with ⟨K, hKA, hKc, hK⟩
  exact
    ⟨K, hKA, hKc,
      measure_diff_lt_of_lt_add hKc.measurableSet hKA (ne_top_of_le_ne_top h'A <| measure_mono hKA)
        hK⟩
#align measurable_set.exists_is_compact_diff_lt MeasurableSet.exists_isCompact_diff_lt

/-- If `μ` is inner regular for finite measure sets with respect to compact sets,
then any measurable set of finite measure can be approximated by a
compact subset. See also `MeasurableSet.exists_isCompact_lt_add`. -/
theorem _root_.MeasurableSet.exists_lt_isCompact_of_ne_top [InnerRegularCompactLTTop μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {r : ℝ≥0∞} (hr : r < μ A) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ r < μ K :=
  InnerRegularCompactLTTop.innerRegular ⟨hA, h'A⟩ _ hr
#align measurable_set.exists_lt_is_compact_of_ne_top MeasurableSet.exists_lt_isCompact_of_ne_top

/-- If `μ` is inner regular for finite measure sets with respect to compact sets,
any measurable set of finite mass can be approximated from
inside by compact sets. -/
theorem _root_.MeasurableSet.measure_eq_iSup_isCompact_of_ne_top [InnerRegularCompactLTTop μ]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞) :
    μ A = ⨆ (K) (_ : K ⊆ A) (_ : IsCompact K), μ K :=
  InnerRegularCompactLTTop.innerRegular.measure_eq_iSup ⟨hA, h'A⟩
#align measurable_set.measure_eq_supr_is_compact_of_ne_top MeasurableSet.measure_eq_iSup_isCompact_of_ne_top

/-- If `μ` is inner regular for finite measure sets with respect to compact sets, then its
restriction to finite measure measurable sets also is. Superseded by `restrict_of_measure_lt_top`,
which removes the measurability assumption. -/
lemma restrict_of_measure_lt_top_aux
    [InnerRegularCompactLTTop μ] {A : Set α} (hA : MeasurableSet A) (h'A : μ A ≠ ∞) :
    InnerRegularCompactLTTop (μ.restrict A) := by
  constructor
  rintro U ⟨hU, -⟩ r hr
  rw [Measure.restrict_apply hU] at hr
  obtain ⟨K, KU, K_comp, hK⟩ : ∃ K, K ⊆ U ∩ A ∧ IsCompact K ∧ r < μ K := by
    apply MeasurableSet.exists_lt_isCompact_of_ne_top (hU.inter hA) _ hr
    exact ((measure_mono (inter_subset_right _ _)).trans_lt h'A.lt_top).ne
  refine ⟨K, KU.trans (inter_subset_left _ _), K_comp, ?_⟩
  have : K ∩ A = K := inter_eq_left_iff_subset.2 (subset_inter_iff.1 KU).2
  rwa [Measure.restrict_apply' hA, this]

/-- If `μ` is inner regular for finite measure sets with respect to compact sets, then its
restriction to finite measure sets also is -/
lemma restrict_of_measure_lt_top
    [InnerRegularCompactLTTop μ] {A : Set α} (h'A : μ A ≠ ∞) :
    InnerRegularCompactLTTop (μ.restrict A) := by
  rw [← restrict_toMeasurable h'A]
  exact InnerRegularCompactLTTop.restrict_of_measure_lt_top_aux (measurableSet_toMeasurable μ A)
    (by simpa using h'A)

end InnerRegularCompactLTTop


namespace WeaklyRegular

/-- If `μ` is a weakly regular measure, then any open set can be approximated by a closed subset. -/
theorem _root_.IsOpen.exists_lt_isClosed [WeaklyRegular μ] ⦃U : Set α⦄ (hU : IsOpen U) {r : ℝ≥0∞}
    (hr : r < μ U) : ∃ F, F ⊆ U ∧ IsClosed F ∧ r < μ F :=
  WeaklyRegular.innerRegular hU r hr
#align is_open.exists_lt_is_closed IsOpen.exists_lt_isClosed

/-- If `μ` is a weakly regular measure, then any open set can be approximated by a closed subset. -/
theorem _root_.IsOpen.measure_eq_iSup_isClosed ⦃U : Set α⦄ (hU : IsOpen U) (μ : Measure α)
    [WeaklyRegular μ] : μ U = ⨆ (F) (_ : F ⊆ U) (_ : IsClosed F), μ F :=
  WeaklyRegular.innerRegular.measure_eq_iSup hU
#align is_open.measure_eq_supr_is_closed IsOpen.measure_eq_iSup_isClosed

theorem innerRegular_measurable [WeaklyRegular μ] :
    InnerRegularWRT μ IsClosed fun s => MeasurableSet s ∧ μ s ≠ ∞ :=
  WeaklyRegular.innerRegular.measurableSet_of_open isClosed_empty fun _ _ h₁ h₂ =>
    h₁.inter h₂.isClosed_compl
#align measure_theory.measure.weakly_regular.inner_regular_measurable MeasureTheory.Measure.WeaklyRegular.innerRegular_measurable

/-- If `s` is a measurable set, a weakly regular measure `μ` is finite on `s`, and `ε` is a positive
number, then there exist a closed set `K ⊆ s` such that `μ s < μ K + ε`. -/
theorem _root_.MeasurableSet.exists_isClosed_lt_add [WeaklyRegular μ] {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K, K ⊆ s ∧ IsClosed K ∧ μ s < μ K + ε :=
  innerRegular_measurable.exists_subset_lt_add isClosed_empty ⟨hs, hμs⟩ hμs hε
#align measurable_set.exists_is_closed_lt_add MeasurableSet.exists_isClosed_lt_add

theorem _root_.MeasurableSet.exists_isClosed_diff_lt [OpensMeasurableSpace α] [WeaklyRegular μ]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ F, F ⊆ A ∧ IsClosed F ∧ μ (A \ F) < ε := by
  rcases hA.exists_isClosed_lt_add h'A hε with ⟨F, hFA, hFc, hF⟩
  exact
    ⟨F, hFA, hFc,
      measure_diff_lt_of_lt_add hFc.measurableSet hFA (ne_top_of_le_ne_top h'A <| measure_mono hFA)
        hF⟩
#align measurable_set.exists_is_closed_diff_lt MeasurableSet.exists_isClosed_diff_lt

/-- Given a weakly regular measure, any measurable set of finite mass can be approximated from
inside by closed sets. -/
theorem _root_.MeasurableSet.exists_lt_isClosed_of_ne_top [WeaklyRegular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {r : ℝ≥0∞} (hr : r < μ A) :
    ∃ K, K ⊆ A ∧ IsClosed K ∧ r < μ K :=
  innerRegular_measurable ⟨hA, h'A⟩ _ hr
#align measurable_set.exists_lt_is_closed_of_ne_top MeasurableSet.exists_lt_isClosed_of_ne_top

/-- Given a weakly regular measure, any measurable set of finite mass can be approximated from
inside by closed sets. -/
theorem _root_.MeasurableSet.measure_eq_iSup_isClosed_of_ne_top [WeaklyRegular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) : μ A = ⨆ (K) (_ : K ⊆ A) (_ : IsClosed K), μ K :=
  innerRegular_measurable.measure_eq_iSup ⟨hA, h'A⟩
#align measurable_set.measure_eq_supr_is_closed_of_ne_top MeasurableSet.measure_eq_iSup_isClosed_of_ne_top

/-- The restriction of a weakly regular measure to a measurable set of finite measure is
weakly regular. Superseded by `restrict_of_measure_ne_top` that removes the measurability
assumption. -/
theorem restrict_of_measure_ne_top_aux [BorelSpace α] [WeaklyRegular μ] {A : Set α}
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) : WeaklyRegular (μ.restrict A) := by
  haveI : Fact (μ A < ∞) := ⟨h'A.lt_top⟩
  refine' InnerRegularWRT.weaklyRegular_of_finite (μ.restrict A) fun V V_open => _
  simp only [restrict_apply' hA]
  intro r hr
  have : μ (V ∩ A) ≠ ∞ := ne_top_of_le_ne_top h'A (measure_mono <| inter_subset_right _ _)
  rcases(V_open.measurableSet.inter hA).exists_lt_isClosed_of_ne_top this hr with
    ⟨F, hFVA, hFc, hF⟩
  refine' ⟨F, hFVA.trans (inter_subset_left _ _), hFc, _⟩
  rwa [inter_eq_self_of_subset_left (hFVA.trans <| inter_subset_right _ _)]
#align measure_theory.measure.weakly_regular.restrict_of_measurable_set MeasureTheory.Measure.WeaklyRegular.restrict_of_measure_ne_top_aux

/-- The restriction of a weakly regular measure to a set of finite measure is
weakly regular. -/
theorem restrict_of_measure_ne_top [BorelSpace α] [WeaklyRegular μ] {A : Set α} (h'A : μ A ≠ ∞) :
    WeaklyRegular (μ.restrict A) := by
  rw [← restrict_toMeasurable h'A]
  exact restrict_of_measure_ne_top_aux (measurableSet_toMeasurable μ A) (by simpa using h'A)

-- see Note [lower instance priority]
/-- Any finite measure on a metric space (or even a pseudo emetric space) is weakly regular. -/
instance (priority := 100) of_pseudoEMetricSpace_of_isFiniteMeasure {X : Type*}
    [PseudoEMetricSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] :
    WeaklyRegular μ :=
  (InnerRegularWRT.of_pseudoEMetricSpace μ).weaklyRegular_of_finite μ
#align measure_theory.measure.weakly_regular.of_pseudo_emetric_space_of_is_finite_measure MeasureTheory.Measure.WeaklyRegular.of_pseudoEMetricSpace_of_isFiniteMeasure

-- see Note [lower instance priority]
/-- Any locally finite measure on a second countable metric space (or even a pseudo emetric space)
is weakly regular. -/
instance (priority := 100) of_pseudoEMetric_secondCountable_of_locallyFinite {X : Type*}
    [PseudoEMetricSpace X] [TopologicalSpace.SecondCountableTopology X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ] : WeaklyRegular μ :=
  haveI : OuterRegular μ := by
    refine' (μ.finiteSpanningSetsInOpen'.mono' fun U hU => _).outerRegular
    have : Fact (μ U < ∞) := ⟨hU.2⟩
    exact ⟨hU.1, inferInstance⟩
  ⟨InnerRegularWRT.of_pseudoEMetricSpace μ⟩
#align measure_theory.measure.weakly_regular.of_pseudo_emetric_second_countable_of_locally_finite MeasureTheory.Measure.WeaklyRegular.of_pseudoEMetric_secondCountable_of_locallyFinite

end WeaklyRegular

namespace Regular

instance zero : Regular (0 : Measure α) :=
  ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isCompact_empty, hr⟩⟩
#align measure_theory.measure.regular.zero MeasureTheory.Measure.Regular.zero

/-- If `μ` is a regular measure, then any open set can be approximated by a compact subset. -/
theorem _root_.IsOpen.exists_lt_isCompact [Regular μ] ⦃U : Set α⦄ (hU : IsOpen U) {r : ℝ≥0∞}
    (hr : r < μ U) : ∃ K, K ⊆ U ∧ IsCompact K ∧ r < μ K :=
  Regular.innerRegular hU r hr
#align is_open.exists_lt_is_compact IsOpen.exists_lt_isCompact

/-- The measure of an open set is the supremum of the measures of compact sets it contains. -/
theorem _root_.IsOpen.measure_eq_iSup_isCompact ⦃U : Set α⦄ (hU : IsOpen U) (μ : Measure α)
    [Regular μ] : μ U = ⨆ (K : Set α) (_ : K ⊆ U) (_ : IsCompact K), μ K :=
  Regular.innerRegular.measure_eq_iSup hU
#align is_open.measure_eq_supr_is_compact IsOpen.measure_eq_iSup_isCompact

theorem exists_compact_not_null [Regular μ] : (∃ K, IsCompact K ∧ μ K ≠ 0) ↔ μ ≠ 0 := by
  simp_rw [Ne.def, ← measure_univ_eq_zero, isOpen_univ.measure_eq_iSup_isCompact,
    ENNReal.iSup_eq_zero, not_forall, exists_prop, subset_univ, true_and_iff]
#align measure_theory.measure.regular.exists_compact_not_null MeasureTheory.Measure.Regular.exists_compact_not_null

/-- If `μ` is a regular measure, then any measurable set of finite measure can be approximated by a
compact subset. See also `MeasurableSet.exists_isCompact_lt_add` and
`MeasurableSet.exists_lt_isCompact_of_ne_top`. -/
instance [Regular μ] : InnerRegularCompactLTTop μ :=
  ⟨Regular.innerRegular.measurableSet_of_open isCompact_empty fun _ _ => IsCompact.diff⟩
#noalign measure_theory.measure.regular.inner_regular_measurable

protected theorem map [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β] [T2Space β]
    [BorelSpace β] [Regular μ] (f : α ≃ₜ β) : (Measure.map f μ).Regular := by
  haveI := OuterRegular.map f μ
  haveI := IsFiniteMeasureOnCompacts.map μ f
  exact
    ⟨Regular.innerRegular.map f.toEquiv f.measurable.aemeasurable
        (fun U hU => hU.preimage f.continuous) (fun K hK => hK.image f.continuous)
        (fun K hK => hK.measurableSet) fun U hU => hU.measurableSet⟩
#align measure_theory.measure.regular.map MeasureTheory.Measure.Regular.map

protected theorem smul [Regular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) : (x • μ).Regular := by
  haveI := OuterRegular.smul μ hx
  haveI := IsFiniteMeasureOnCompacts.smul μ hx
  exact ⟨Regular.innerRegular.smul x⟩
#align measure_theory.measure.regular.smul MeasureTheory.Measure.Regular.smul

-- see Note [lower instance priority]
/-- A regular measure in a σ-compact space is σ-finite. -/
instance (priority := 100) sigmaFinite [SigmaCompactSpace α] [Regular μ] : SigmaFinite μ :=
  ⟨⟨{   set := compactCovering α
        set_mem := fun _ => trivial
        finite := fun n => (isCompact_compactCovering α n).measure_lt_top
        spanning := iUnion_compactCovering α }⟩⟩
#align measure_theory.measure.regular.sigma_finite MeasureTheory.Measure.Regular.sigmaFinite

/-- The restriction of a regular measure to a set of finite measure is regular. -/
theorem restrict_of_measure_ne_top_aux [T2Space α] [BorelSpace α] [Regular μ] (A : Set α)
    (h'A : μ A ≠ ∞) : Regular (μ.restrict A) := by
  have : Fact (μ A < ∞) := ⟨h'A.lt_top⟩
  have : WeaklyRegular (μ.restrict A) := WeaklyRegular.restrict_of_measure_ne_top h'A
  have : InnerRegularCompactLTTop (μ.restrict A) :=
    InnerRegularCompactLTTop.restrict_of_measure_lt_top h'A
  constructor
  intro V hV r hr
  apply MeasurableSet.exists_lt_isCompact_of_ne_top hV.measurableSet _ hr
  rw [restrict_apply hV.measurableSet]
  exact ((measure_mono (inter_subset_right _ _)).trans_lt h'A.lt_top).ne

end Regular

attribute [local instance] EMetric.secondCountable_of_sigmaCompact

-- see Note [lower instance priority]
/-- Any locally finite measure on a `σ`-compact (e)metric space is regular. -/
instance (priority := 100) Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure {X : Type*}
    [EMetricSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsLocallyFiniteMeasure μ] : Regular μ where
  lt_top_of_isCompact _K hK := hK.measure_lt_top
  innerRegular := (InnerRegularWRT.isCompact_isClosed μ).trans
    (InnerRegularWRT.of_pseudoEMetricSpace μ)
#align measure_theory.measure.regular.of_sigma_compact_space_of_is_locally_finite_measure MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure

end Measure

end MeasureTheory
