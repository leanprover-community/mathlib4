/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Covering.VitaliFamily

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Vitali covering theorems

The topological Vitali covering theorem, in its most classical version, states the following.
Consider a family of balls `(B (x_i, r_i))_{i ∈ I}` in a metric space, with uniformly bounded
radii. Then one can extract a disjoint subfamily indexed by `J ⊆ I`, such that any `B (x_i, r_i)`
is included in a ball `B (x_j, 5 r_j)`.

We prove this theorem in `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall`.
It is deduced from a more general version, called
`Vitali.exists_disjoint_subfamily_covering_enlargement`, which applies to any family of sets
together with a size function `δ` (think "radius" or "diameter").

We deduce the measurable Vitali covering theorem. Assume one is given a family `t` of closed sets
with nonempty interior, such that each `a ∈ t` is included in a ball `B (x, r)` and covers a
definite proportion of the ball `B (x, 6 r)` for a given measure `μ` (think of the situation
where `μ` is a doubling measure and `t` is a family of balls). Consider a set `s` at which the
family is fine, i.e., every point of `s` belongs to arbitrarily small elements of `t`. Then one
can extract from `t` a disjoint subfamily that covers almost all `s`. It is proved in
`Vitali.exists_disjoint_covering_ae`. The proportion is allowed to depend on the center `x` of the
ball, i.e., we only need `μ (B (x, 3 r)) ≤ C x * μ a` for some function `C`.

A way to restate this theorem is to say that the set of closed sets `a` with nonempty interior
covering a fixed proportion `1/C` of the ball `closedBall x (3 * diam a)` forms a Vitali family.
This version is given in `Vitali.vitaliFamily`.
-/

@[expose] public section


variable {α ι : Type*}

open Set Metric MeasureTheory TopologicalSpace Filter
open scoped NNReal ENNReal Topology

namespace Vitali

/-- **Vitali covering theorem**: given a set `t` of subsets of a type, one may extract a disjoint
subfamily `u` such that the `τ`-enlargement of this family covers all elements of `t`, where `τ > 1`
is any fixed number.

When `t` is a family of balls, the `τ`-enlargement of `ball x r` is `ball x ((1+2τ) r)`. In general,
it is expressed in terms of a function `δ` (think "radius" or "diameter"), positive and bounded on
all elements of `t`. The condition is that every element `a` of `t` should intersect an
element `b` of `u` of size larger than that of `a` up to `τ`, i.e., `δ b ≥ δ a / τ`.

We state the lemma slightly more generally, with an indexed family of sets `B a` for `a ∈ t`, for
wider applicability.
-/
theorem exists_disjoint_subfamily_covering_enlargement (B : ι → Set α) (t : Set ι) (δ : ι → ℝ)
    (τ : ℝ) (hτ : 1 < τ) (δnonneg : ∀ a ∈ t, 0 ≤ δ a) (R : ℝ) (δle : ∀ a ∈ t, δ a ≤ R)
    (hne : ∀ a ∈ t, (B a).Nonempty) :
    ∃ u ⊆ t,
      u.PairwiseDisjoint B ∧ ∀ a ∈ t, ∃ b ∈ u, (B a ∩ B b).Nonempty ∧ δ a ≤ τ * δ b := by
  /- The proof could be formulated as a transfinite induction. First pick an element of `t` with `δ`
  as large as possible (up to a factor of `τ`). Then among the remaining elements not intersecting
  the already chosen one, pick another element with large `δ`. Go on forever (transfinitely) until
  there is nothing left.

  Instead, we give a direct Zorn-based argument. Consider a maximal family `u` of disjoint sets
  with the following property: if an element `a` of `t` intersects some element `b` of `u`, then it
  intersects some `b' ∈ u` with `δ b' ≥ δ a / τ`. Such a maximal family exists by Zorn. If this
  family did not intersect some element `a ∈ t`, then take an element `a' ∈ t` which does not
  intersect any element of `u`, with `δ a'` almost as large as possible. One checks easily
  that `u ∪ {a'}` still has this property, contradicting the maximality. Therefore, `u`
  intersects all elements of `t`, and by definition it satisfies all the desired properties.
  -/
  let T : Set (Set ι) := { u | u ⊆ t ∧ u.PairwiseDisjoint B ∧
    ∀ a ∈ t, ∀ b ∈ u, (B a ∩ B b).Nonempty → ∃ c ∈ u, (B a ∩ B c).Nonempty ∧ δ a ≤ τ * δ c }
  -- By Zorn, choose a maximal family in the good set `T` of disjoint families.
  obtain ⟨u, hu⟩ : ∃ m, Maximal (fun x ↦ x ∈ T) m := by
    refine zorn_subset _ fun U UT hU => ?_
    refine ⟨⋃₀ U, ?_, fun s hs => subset_sUnion_of_mem hs⟩
    simp only [T, Set.sUnion_subset_iff, and_imp, forall_exists_index, mem_sUnion,
      Set.mem_ofPred_eq]
    refine
      ⟨fun u hu => (UT hu).1, (pairwiseDisjoint_sUnion hU.directedOn).2 fun u hu => (UT hu).2.1,
        fun a hat b u uU hbu hab => ?_⟩
    obtain ⟨c, cu, ac, hc⟩ : ∃ c, c ∈ u ∧ (B a ∩ B c).Nonempty ∧ δ a ≤ τ * δ c :=
      (UT uU).2.2 a hat b hbu hab
    exact ⟨c, ⟨u, uU, cu⟩, ac, hc⟩
  -- The only nontrivial bit is to check that every `a ∈ t` intersects an element `b ∈ u` with
  -- comparatively large `δ b`. Assume this is not the case, then we will contradict the maximality.
  refine ⟨u, hu.prop.1, hu.prop.2.1, fun a hat => ?_⟩
  by_contra! hcon
  have a_disj : ∀ c ∈ u, Disjoint (B a) (B c) := by
    intro c hc
    by_contra h
    rw [not_disjoint_iff_nonempty_inter] at h
    obtain ⟨d, du, ad, hd⟩ : ∃ d, d ∈ u ∧ (B a ∩ B d).Nonempty ∧ δ a ≤ τ * δ d :=
      hu.prop.2.2 a hat c hc h
    exact lt_irrefl _ ((hcon d du ad).trans_le hd)
  -- Let `A` be all the elements of `t` which do not intersect the family `u`. It is nonempty as it
  -- contains `a`. We will pick an element `a'` of `A` with `δ a'` almost as large as possible.
  let A := { a' | a' ∈ t ∧ ∀ c ∈ u, Disjoint (B a') (B c) }
  have Anonempty : A.Nonempty := ⟨a, hat, a_disj⟩
  let m := sSup (δ '' A)
  have bddA : BddAbove (δ '' A) := by
    refine ⟨R, fun x xA => ?_⟩
    rcases (mem_image _ _ _).1 xA with ⟨a', ha', rfl⟩
    exact δle a' ha'.1
  obtain ⟨a', a'A, ha'⟩ : ∃ a' ∈ A, m / τ ≤ δ a' := by
    have : 0 ≤ m := (δnonneg a hat).trans (le_csSup bddA (mem_image_of_mem _ ⟨hat, a_disj⟩))
    rcases eq_or_lt_of_le this with (mzero | mpos)
    · refine ⟨a, ⟨hat, a_disj⟩, ?_⟩
      simpa only [← mzero, zero_div] using δnonneg a hat
    · have I : m / τ < m := by
        rw [div_lt_iff₀ (zero_lt_one.trans hτ)]
        conv_lhs => rw [← mul_one m]
        gcongr
      rcases exists_lt_of_lt_csSup (Anonempty.image _) I with ⟨x, xA, hx⟩
      rcases (mem_image _ _ _).1 xA with ⟨a', ha', rfl⟩
      exact ⟨a', ha', hx.le⟩
  clear hat hcon a_disj a
  have a'_ne_u : a' ∉ u := fun H => (hne _ a'A.1).ne_empty (disjoint_self.1 (a'A.2 _ H))
  -- we claim that `u ∪ {a'}` still belongs to `T`, contradicting the maximality of `u`.
  refine a'_ne_u (hu.mem_of_prop_insert ⟨?_, ?_, ?_⟩)
  · -- check that `u ∪ {a'}` is made of elements of `t`.
    rw [insert_subset_iff]
    exact ⟨a'A.1, hu.prop.1⟩
  · -- Check that `u ∪ {a'}` is a disjoint family. This follows from the fact that `a'` does not
    -- intersect `u`.
    exact hu.prop.2.1.insert fun b bu _ => a'A.2 b bu
  · -- check that every element `c` of `t` intersecting `u ∪ {a'}` intersects an element of this
    -- family with large `δ`.
    intro c ct b ba'u hcb
    -- if `c` already intersects an element of `u`, then it intersects an element of `u` with
    -- large `δ` by the assumption on `u`, and there is nothing left to do.
    by_cases! H : ∃ d ∈ u, (B c ∩ B d).Nonempty
    · rcases H with ⟨d, du, hd⟩
      rcases hu.prop.2.2 c ct d du hd with ⟨d', d'u, hd'⟩
      exact ⟨d', mem_insert_of_mem _ d'u, hd'⟩
    · -- Otherwise, `c` belongs to `A`. The element of `u ∪ {a'}` that it intersects has to be `a'`.
      -- Moreover, `δ c` is smaller than the maximum `m` of `δ` over `A`, which is `≤ δ a' / τ`
      -- thanks to the good choice of `a'`. This is the desired inequality.
      simp only [← disjoint_iff_inter_eq_empty] at H
      rcases mem_insert_iff.1 ba'u with (rfl | H')
      · refine ⟨b, mem_insert _ _, hcb, ?_⟩
        calc
          δ c ≤ m := le_csSup bddA (mem_image_of_mem _ ⟨ct, H⟩)
          _ = τ * (m / τ) := by field
          _ ≤ τ * δ b := by gcongr
      · rw [← not_disjoint_iff_nonempty_inter] at hcb
        exact (hcb (H _ H')).elim

/-- Vitali covering theorem, closed balls version: given a family `t` of closed balls, one can
extract a disjoint subfamily `u ⊆ t` so that all balls in `t` are covered by the τ-times
dilations of balls in `u`, for some `τ > 3`. -/
theorem exists_disjoint_subfamily_covering_enlargement_closedBall
    [PseudoMetricSpace α] (t : Set ι)
    (x : ι → α) (r : ι → ℝ) (R : ℝ) (hr : ∀ a ∈ t, r a ≤ R) (τ : ℝ) (hτ : 3 < τ) :
    ∃ u ⊆ t,
      (u.PairwiseDisjoint fun a => closedBall (x a) (r a)) ∧
        ∀ a ∈ t, ∃ b ∈ u, closedBall (x a) (r a) ⊆ closedBall (x b) (τ * r b) := by
  rcases eq_empty_or_nonempty t with (rfl | _)
  · exact ⟨∅, Subset.refl _, pairwiseDisjoint_empty, by simp⟩
  by_cases! ht : ∀ a ∈ t, r a < 0
  · exact ⟨t, Subset.rfl, fun a ha b _ _ => by
      simp only [closedBall_eq_empty.2 (ht a ha), empty_disjoint, Function.onFun],
      fun a ha => ⟨a, ha, by simp only [closedBall_eq_empty.2 (ht a ha), empty_subset]⟩⟩
  let t' := { a ∈ t | 0 ≤ r a }
  rcases exists_disjoint_subfamily_covering_enlargement (fun a => closedBall (x a) (r a)) t' r
      ((τ - 1) / 2) (by linarith) (fun a ha => ha.2) R (fun a ha => hr a ha.1) fun a ha =>
      ⟨x a, mem_closedBall_self ha.2⟩ with
    ⟨u, ut', u_disj, hu⟩
  have A : ∀ a ∈ t', ∃ b ∈ u, closedBall (x a) (r a) ⊆ closedBall (x b) (τ * r b) := by
    intro a ha
    rcases hu a ha with ⟨b, bu, hb, rb⟩
    refine ⟨b, bu, ?_⟩
    have : dist (x a) (x b) ≤ r a + r b := dist_le_add_of_nonempty_closedBall_inter_closedBall hb
    apply closedBall_subset_closedBall'
    linarith
  refine ⟨u, ut'.trans fun a ha => ha.1, u_disj, fun a ha => ?_⟩
  rcases le_or_gt 0 (r a) with (h'a | h'a)
  · exact A a ⟨ha, h'a⟩
  · rcases ht with ⟨b, rb⟩
    rcases A b ⟨rb.1, rb.2⟩ with ⟨c, cu, _⟩
    exact ⟨c, cu, by simp only [closedBall_eq_empty.2 h'a, empty_subset]⟩

/- Note: it seems easier to do the analogous proof again than to apply the previous one, because the
interior of a closed ball may not equal the open ball. -/

/-- Vitali covering theorem, open balls version: given a family `t` of balls, one can
extract a disjoint subfamily `u ⊆ t` so that all balls in `t` are covered by the τ-times
dilations of balls in `u`, for some `τ > 3`. -/
theorem exists_disjoint_subfamily_covering_enlargement_ball
    [PseudoMetricSpace α] (t : Set ι)
    (x : ι → α) (r : ι → ℝ) (R : ℝ) (hr : ∀ a ∈ t, r a ≤ R) (τ : ℝ) (hτ : 3 < τ) :
    ∃ u ⊆ t,
      (u.PairwiseDisjoint fun a => ball (x a) (r a)) ∧
        ∀ a ∈ t, ∃ b ∈ u, ball (x a) (r a) ⊆ ball (x b) (τ * r b) := by
  rcases eq_empty_or_nonempty t with (rfl | _)
  · exact ⟨∅, Subset.refl _, pairwiseDisjoint_empty, by simp⟩
  by_cases! ht : ∀ a ∈ t, r a ≤ 0
  · exact ⟨t, Subset.rfl, fun a ha b _ _ => by
      simp only [ball_eq_empty.2 (ht a ha), empty_disjoint, Function.onFun],
      fun a ha => ⟨a, ha, by simp only [ball_eq_empty.2 (ht a ha), empty_subset]⟩⟩
  let t' := { a ∈ t | 0 < r a }
  rcases exists_disjoint_subfamily_covering_enlargement (fun a => ball (x a) (r a)) t' r
      ((τ - 1) / 2) (by linarith) (fun a ha => ha.2.le) R (fun a ha => hr a ha.1) fun a ha =>
      ⟨x a, mem_ball_self ha.2⟩ with
    ⟨u, ut', u_disj, hu⟩
  have A : ∀ a ∈ t', ∃ b ∈ u, ball (x a) (r a) ⊆ ball (x b) (τ * r b) := by
    intro a ha
    rcases hu a ha with ⟨b, bu, hb, rb⟩
    refine ⟨b, bu, ?_⟩
    have : dist (x a) (x b) < r a + r b := dist_lt_add_of_nonempty_ball_inter_ball hb
    apply ball_subset_ball'
    linarith
  refine ⟨u, ut'.trans fun a ha => ha.1, u_disj, fun a ha => ?_⟩
  rcases lt_or_ge 0 (r a) with (h'a | h'a)
  · exact A a ⟨ha, h'a⟩
  · rcases ht with ⟨b, rb⟩
    rcases A b ⟨rb.1, rb.2⟩ with ⟨c, cu, _⟩
    exact ⟨c, cu, by simp only [ball_eq_empty.2 h'a, empty_subset]⟩

/-- The measurable **Vitali covering theorem**.

Assume one is given a family `t` of closed sets with nonempty interior, such that each `a ∈ t` is
included in a ball `B (x, r)` and covers a definite proportion `1 / C x` of the ball `B (x, 3 r)`
for a given measure `μ` (think of the situation where `μ` is a doubling measure and `t` is a family
of balls). The proportion may depend on the center `x`.
Consider a (possibly non-measurable) set `s` at which the family is fine, i.e., every point of `s`
belongs to arbitrarily small elements of `t`. Then one can extract from `t` a disjoint subfamily
that covers almost all `s`.

For more flexibility, we give a statement with a parameterized family of sets.
-/
theorem exists_disjoint_covering_ae
    [PseudoMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α] (μ : Measure α) [IsLocallyFiniteMeasure μ] (s : Set α) (t : Set ι)
    (C : α → ℝ≥0) (r : ι → ℝ) (c : ι → α) (B : ι → Set α)
    (hB : ∀ a ∈ t, B a ⊆ closedBall (c a) (r a))
    (μB : ∀ a ∈ t, μ (closedBall (c a) (3 * r a)) ≤ C (c a) * μ (B a))
    (ht : ∀ a ∈ t, (interior (B a)).Nonempty) (h't : ∀ a ∈ t, IsClosed (B a))
    (hf : ∀ x ∈ s, ∀ ε > (0 : ℝ), ∃ a ∈ t, r a ≤ ε ∧ c a = x) :
    ∃ u ⊆ t, u.Countable ∧ u.PairwiseDisjoint B ∧ μ (s \ ⋃ a ∈ u, B a) = 0 := by
  /- The idea of the proof is the following. Fix a monotone sequence of open sets `U n` of finite
  measure covering the space, and let `s n` be the set of points `x ∈ s ∩ U n` such that `C x ≤ n`.
  We construct inductively an increasing sequence of finite disjoint subfamilies `F n` of `t` such
  that the measure of `s n \ ⋃ F (n + 1)` is at most `1 / n`.

  To construct `F (n + 1)` from `F n`, consider the closed set `K = ⋃ F n` and the elements
  `a ∈ t` that are disjoint from `K`, contained in `U n`, with `r a ≤ 1` and `C (c a) ≤ n`.
  Applying the abstract Vitali covering theorem to this family, one obtains a disjoint subfamily
  `u` such that any element of the family intersects an element of `u` with comparable radius.
  Since the elements of `u` are contained in `U n`, they have summable measures, so one can keep
  finitely many of them, forming a family `w`, so that the measure of the remaining ones is small.
  Consider now a point `z ∈ s n` not in `K` and not in the elements of `w`. There is a small ball
  around `z` not intersecting `K` and the elements of `w` (as they are closed), an element `a ∈ t`
  centered at `z` contained in this small ball (as the family `t` is fine at `z`) and an element
  `b ∈ u` intersecting `a`, with comparable radius. Then `b ∉ w` and `z` belongs to the
  enlargement of `b`. This shows that `s n \ (K ∪ ⋃ w)` is contained in the union of the
  enlargements of the elements of `u \ w`, whose measure is at most `n * ∑ b ∈ u \ w, μ b`, which
  is small. We let `F (n + 1) = F n ∪ w`.

  The union of the `F n` is the desired family. -/
  set U := μ.finiteSpanningSetsInOpen
  /- A finite disjoint subfamily of `t`, encoded as an element of a subtype to make the inductive
  construction easier. -/
  let S := {F : Set ι // F.Finite ∧ F ⊆ t ∧ F.PairwiseDisjoint B}
  -- The main step: one can enlarge a finite disjoint subfamily to cover most of `s n`.
  have step : ∀ (F : S) (n : ℕ), ∃ G : S, F.val ⊆ G.val ∧
      μ ({x ∈ s ∩ U.set n | C x ≤ n} \ ⋃ a ∈ G.val, B a) ≤ (n : ℝ≥0∞)⁻¹ := by
    rintro ⟨F, hFfin, hFt, hFdisj⟩ n
    set K := ⋃ a ∈ F, B a
    let t' := {a ∈ t | C (c a) ≤ n ∧ Disjoint (B a) K ∧ B a ⊆ U.set n ∧ r a ≤ 1}
    -- extract a disjoint subfamily `u` of `t'` thanks to the abstract Vitali covering theorem.
    obtain ⟨u, ut', u_disj, hu⟩ : ∃ u ⊆ t',
        u.PairwiseDisjoint B ∧ ∀ a ∈ t', ∃ b ∈ u, (B a ∩ B b).Nonempty ∧ r a ≤ 2 * r b := by
      have A : ∀ a ∈ t', (B a).Nonempty := fun a ha ↦ (ht a ha.1).mono interior_subset
      refine exists_disjoint_subfamily_covering_enlargement B t' r 2 one_lt_two (fun a ha ↦ ?_) 1
        (fun a ha ↦ ha.2.2.2.2) A
      exact nonempty_closedBall.1 ((A a ha).mono (hB a ha.1))
    choose hut hCu hud huBU hur using ut'
    change u ⊆ t at hut
    -- As the space is second countable, the family is countable since all its sets have nonempty
    -- interior.
    have u_count : u.Countable := u_disj.countable_of_nonempty_interior fun a ha ↦ ht a (hut ha)
    have : Countable u := u_count.to_subtype
    -- the elements of `u` are disjoint and contained in `U n`, so they have summable measures and
    -- one can keep finitely many of them so that the remaining ones have a small total measure.
    have I : ∑' a : u, μ (B a) ≠ ∞ := by
      rw [← measure_biUnion u_count u_disj fun a ha ↦ (h't a (hut ha)).measurableSet]
      grw [iUnion₂_subset huBU]
      exact (U.finite n).ne
    obtain ⟨w, hw⟩ : ∃ w : Finset u, ∑' a : {a // a ∉ w}, μ (B a) < (n : ℝ≥0∞)⁻¹ / n :=
      (ENNReal.tendsto_tsum_compl_atTop_zero I).eventually_lt_const (by simp [ENNReal.div_pos_iff])
        |>.exists
    set G := F ∪ (↑) '' (w : Set u)
    have hGfin : G.Finite := hFfin.union ((w.finite_toSet).image _)
    have hGt : G ⊆ t := union_subset hFt (by rintro - ⟨a, -, rfl⟩; exact hut a.property)
    refine ⟨⟨G, hGfin, hGt, ?_⟩, subset_union_left, ?_⟩
    · refine hFdisj.union (u_disj.subset (by rintro - ⟨a, -, rfl⟩; exact a.property)) ?_
      rintro a ha - ⟨b, -, rfl⟩ -
      exact ((hud b.property).mono_right (subset_biUnion_of_mem ha)).symm
    -- main property: the points of `s n` which are not covered by `G` are contained in the
    -- enlargements of the elements of `u` not in `w`.
    have M : {x ∈ s ∩ U.set n | C x ≤ n} \ ⋃ a ∈ G, B a ⊆
        ⋃ a : {a : u // a ∉ w}, closedBall (c a) (3 * r a) := by
      rintro z ⟨⟨⟨hzs, hzU⟩, hzC⟩, hzG⟩
      -- since the elements of `G` are closed and finitely many, one can find a small ball
      -- around `z` not intersecting them
      have hG : IsClosed (⋃ a ∈ G, B a) := hGfin.isClosed_biUnion fun a ha ↦ h't a (hGt ha)
      obtain ⟨d, dpos, hd⟩ : ∃ d > 0, closedBall z d ⊆ U.set n \ ⋃ a ∈ G, B a :=
        nhds_basis_closedBall.mem_iff.1 (((U.set_mem n).sdiff hG).mem_nhds ⟨hzU, hzG⟩)
      -- choose an element `a` of the family `t` contained in this small ball
      obtain ⟨a, hat, ha, rfl⟩ := hf z hzs (min d 1) (lt_min dpos one_pos)
      have haG : B a ⊆ U.set n \ ⋃ a ∈ G, B a :=
        (hB a hat).trans ((closedBall_subset_closedBall (ha.trans (min_le_left _ _))).trans hd)
      have hat' : a ∈ t' :=
        ⟨hat, hzC, (subset_compl_iff_disjoint_right.1 fun x hx ↦ (haG hx).2).mono_right
          (biUnion_subset_biUnion_left subset_union_left), fun x hx ↦ (haG hx).1,
          ha.trans (min_le_right _ _)⟩
      -- it intersects an element `b` of `u` with comparable radius, by definition of `u`
      obtain ⟨b, bu, ⟨e, ea, eb⟩, hab⟩ := hu a hat'
      -- `b` cannot belong to `w`, as the elements of `w` do not intersect `B a`.
      have bw : (⟨b, bu⟩ : u) ∉ w := fun hbw ↦
        (haG ea).2 (mem_biUnion (subset_union_right (mem_image_of_mem _ hbw)) eb)
      refine mem_iUnion.2 ⟨⟨⟨b, bu⟩, bw⟩, ?_⟩
      -- since `a` and `b` have comparable radii, `z` belongs to the enlargement of `b`
      have hea : dist (c a) e ≤ r a := mem_closedBall'.1 (hB a hat ea)
      have heb : dist e (c b) ≤ r b := mem_closedBall.1 (hB b (hut bu) eb)
      simp only [mem_closedBall]
      linarith only [dist_triangle (c a) e (c b), hea, heb, hab]
    calc
      μ ({x ∈ s ∩ U.set n | C x ≤ n} \ ⋃ a ∈ G, B a)
        ≤ ∑' a : {a : u // a ∉ w}, μ (closedBall (c a) (3 * r a)) :=
          (measure_mono M).trans (measure_iUnion_le _)
      _ ≤ ∑' a : {a : u // a ∉ w}, n * μ (B a) := by
        grw [μB, hCu]
        exacts [le_rfl, a.val.prop, hut a.val.prop]
      _ = n * ∑' a : {a : u // a ∉ w}, μ (B a) := ENNReal.tsum_mul_left
      _ ≤ n * ((n : ℝ≥0∞)⁻¹ / n) := by gcongr
      _ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.mul_div_le
  choose G hFG hG using step
  -- the inductive construction of the sequence of finite subfamilies
  let F : ℕ → S := fun n ↦ Nat.rec ⟨∅, finite_empty, empty_subset _, pairwiseDisjoint_empty⟩
    (fun n Fn ↦ G Fn n) n
  have F_succ (n : ℕ) : F (n + 1) = G (F n) n := rfl
  have F_mono : Monotone fun n ↦ (F n).val :=
    monotone_nat_of_le_succ fun n ↦ by rw [F_succ]; exact hFG _ _
  refine ⟨⋃ n, (F n).val, iUnion_subset fun n ↦ (F n).property.2.1,
    countable_iUnion fun n ↦ (F n).property.1.countable,
    (pairwiseDisjoint_iUnion F_mono.directed_le).2 fun n ↦ (F n).property.2.2, ?_⟩
  -- it suffices to show that each `s n` is almost everywhere covered
  have : s \ ⋃ a ∈ ⋃ n, (F n).val, B a ⊆
      ⋃ n : ℕ, {x ∈ s ∩ U.set n | C x ≤ n} \ ⋃ a ∈ ⋃ n, (F n).val, B a := by
    intro x ⟨hxs, hx⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (C x)
    obtain ⟨k, hk⟩ : ∃ k, x ∈ U.set k := by simpa [← U.spanning] using mem_univ x
    refine mem_iUnion.2 ⟨max n k, ⟨⟨hxs, μ.monotone_finiteSpanningSetsInOpen
      (le_max_right _ _) hk⟩, hn.trans (Nat.cast_le.2 (le_max_left _ _))⟩, hx⟩
  refine measure_mono_null this (measure_iUnion_null fun n ↦ ?_)
  -- the measure of the uncovered part of `s n` is at most `1 / m` for any `m ≥ n`.
  refine le_antisymm (ge_of_tendsto ENNReal.tendsto_inv_nat_nhds_zero ?_) bot_le
  filter_upwards [eventually_ge_atTop n] with m hm
  refine le_trans (measure_mono ?_) (hG (F m) m)
  refine sdiff_subset_sdiff (fun x hx ↦ ⟨⟨hx.1.1, μ.monotone_finiteSpanningSetsInOpen hm hx.1.2⟩,
    hx.2.trans (by exact_mod_cast hm)⟩) ?_
  rw [← F_succ]
  exact biUnion_subset_biUnion_left (subset_iUnion (fun n ↦ (F n).val) (m + 1))

/-- The measurable **Vitali covering theorem**, filter version.

Assume one is given a family `t` of closed sets with nonempty interior, such that each `a ∈ t` is
included in a ball `B (x, r)` and covers a definite proportion of the ball `B (x, 3 r)` for a given
measure `μ` (think of the situation where `μ` is a doubling measure and `t` is a family of balls).
Consider a (possibly non-measurable) set `s` at which the family is fine, i.e., every point of `s`
belongs to arbitrarily small elements of `t`. Then one can extract from `t` a disjoint subfamily
that covers almost all `s`.

For more flexibility, we give a statement with a parameterized family of sets.
-/
theorem exists_disjoint_covering_ae'
    [PseudoMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α] (μ : Measure α) [IsLocallyFiniteMeasure μ] (s : Set α) (t : Set ι)
    (C : α → ℝ≥0) (r : ι → ℝ) (c : ι → α) (B : ι → Set α)
    (hB : ∀ a ∈ t, B a ⊆ closedBall (c a) (r a))
    (μB : ∀ a ∈ t, μ (closedBall (c a) (3 * r a)) ≤ C (c a) * μ (B a))
    (ht : ∀ a ∈ t, (interior (B a)).Nonempty) (h't : ∀ a ∈ t, IsClosed (B a))
    (hf : ∀ x ∈ s, ∃ᶠ ε in 𝓝[>] 0, ∃ a ∈ t, r a = ε ∧ c a = x) :
    ∃ u ⊆ t, u.Countable ∧ u.PairwiseDisjoint B ∧ μ (s \ ⋃ a ∈ u, B a) = 0 := by
  suffices ∀ x ∈ s, ∀ ε > (0 : ℝ), ∃ a ∈ t, r a ≤ ε ∧ c a = x from
    exists_disjoint_covering_ae μ s t C r c B hB μB ht h't this
  intro x hx ε hε
  specialize hf x hx
  rw [frequently_nhdsWithin_iff, frequently_nhds_iff] at hf
  obtain ⟨_, _, ⟨a, ha₁, ha₂, ha₃⟩, _⟩ := hf (Ioo (-ε) ε) (by grind) isOpen_Ioo
  exact ⟨a, ha₁, by grind, ha₃⟩

/-- Assume that around every point `x` there are arbitrarily small scales at which the measure is
doubling, with a doubling constant `C x` that may depend on `x`. Then the set of closed sets `a`
with nonempty interior contained in `closedBall x r` and covering a proportion `1 / C x` of the ball
`closedBall x (3 * r)` forms a Vitali family.
This is essentially a restatement of the measurable Vitali theorem. -/
protected def vitaliFamily [PseudoMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α] (μ : Measure α) [IsLocallyFiniteMeasure μ] (C : α → ℝ≥0)
    (h : ∀ x, ∃ᶠ r in 𝓝[>] 0, μ (closedBall x (3 * r)) ≤ C x * μ (closedBall x r)) :
    VitaliFamily μ where
  setsAt x := { a | IsClosed a ∧ (interior a).Nonempty ∧
    ∃ r, a ⊆ closedBall x r ∧ μ (closedBall x (3 * r)) ≤ C x * μ a }
  measurableSet _ _ ha := ha.1.measurableSet
  nonempty_interior _ _ ha := ha.2.1
  nontrivial x ε εpos := by
    obtain ⟨r, μr, rpos, rε⟩ :
        ∃ r, μ (closedBall x (3 * r)) ≤ C x * μ (closedBall x r) ∧ r ∈ Ioc (0 : ℝ) ε :=
      ((h x).and_eventually (Ioc_mem_nhdsGT εpos)).exists
    refine ⟨closedBall x r, ⟨isClosed_closedBall, ?_, ⟨r, Subset.rfl, μr⟩⟩, by gcongr⟩
    exact (nonempty_ball.2 rpos).mono ball_subset_interior_closedBall
  covering := by
    intro s f fsubset ffine
    let t : Set (ℝ × α × Set α) :=
      { p | p.2.2 ⊆ closedBall p.2.1 p.1 ∧ μ (closedBall p.2.1 (3 * p.1)) ≤ C p.2.1 * μ p.2.2 ∧
            (interior p.2.2).Nonempty ∧ IsClosed p.2.2 ∧ p.2.2 ∈ f p.2.1 ∧ p.2.1 ∈ s }
    have A : ∀ x ∈ s, ∀ ε : ℝ, ε > 0 → ∃ p, p ∈ t ∧ p.1 ≤ ε ∧ p.2.1 = x := by
      intro x xs ε εpos
      rcases ffine x xs ε εpos with ⟨a, ha, h'a⟩
      rcases fsubset x xs ha with ⟨a_closed, a_int, ⟨r, ar, μr⟩⟩
      refine ⟨⟨min r ε, x, a⟩, ⟨?_, ?_, a_int, a_closed, ha, xs⟩, min_le_right _ _, rfl⟩
      · rcases min_cases r ε with (h' | h') <;> rwa [h'.1]
      · apply le_trans ?_ μr
        gcongr
        apply min_le_left
    rcases exists_disjoint_covering_ae μ s t C (fun p => p.1) (fun p => p.2.1) (fun p => p.2.2)
        (fun p hp => hp.1) (fun p hp => hp.2.1) (fun p hp => hp.2.2.1) (fun p hp => hp.2.2.2.1) A
      with ⟨t', t't, _, t'_disj, μt'⟩
    refine ⟨(fun p : ℝ × α × Set α => p.2) '' t', ?_, ?_, ?_, ?_⟩
    · rintro - ⟨q, hq, rfl⟩
      exact (t't hq).2.2.2.2.2
    · rintro p ⟨q, hq, rfl⟩ p' ⟨q', hq', rfl⟩ hqq'
      exact t'_disj hq hq' (ne_of_apply_ne _ hqq')
    · rintro - ⟨q, hq, rfl⟩
      exact (t't hq).2.2.2.2.1
    · convert μt' using 3
      rw [biUnion_image]

end Vitali
