/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

#align_import analysis.convex.krein_milman from "leanprover-community/mathlib"@"279297937dede7b1b3451b7b0f1786352ad011fa"

/-!
# The Krein-Milman theorem

This file proves the Krein-Milman lemma and the Krein-Milman theorem.

## The lemma

The lemma states that a nonempty compact set `s` has an extreme point. The proof goes:
1. Using Zorn's lemma, find a minimal nonempty closed `t` that is an extreme subset of `s`. We will
  show that `t` is a singleton, thus corresponding to an extreme point.
2. By contradiction, `t` contains two distinct points `x` and `y`.
3. With the (geometric) Hahn-Banach theorem, find a hyperplane that separates `x` and `y`.
4. Look at the extreme (actually exposed) subset of `t` obtained by going the furthest away from
  the separating hyperplane in the direction of `x`. It is nonempty, closed and an extreme subset
  of `s`.
5. It is a strict subset of `t` (`y` isn't in it), so `t` isn't minimal. Absurd.

## The theorem

The theorem states that a compact convex set `s` is the closure of the convex hull of its extreme
points. It is an almost immediate strengthening of the lemma. The proof goes:
1. By contradiction, `s \ closure (convexHull ℝ (extremePoints ℝ s))` is nonempty, say with `x`.
2. With the (geometric) Hahn-Banach theorem, find a hyperplane that separates `x` from
  `closure (convexHull ℝ (extremePoints ℝ s))`.
3. Look at the extreme (actually exposed) subset of
  `s \ closure (convexHull ℝ (extremePoints ℝ s))` obtained by going the furthest away from the
  separating hyperplane. It is nonempty by assumption of nonemptiness and compactness, so by the
  lemma it has an extreme point.
4. This point is also an extreme point of `s`. Absurd.

## Related theorems

When the space is finite dimensional, the `closure` can be dropped to strengthen the result of the
Krein-Milman theorem. This leads to the Minkowski-Carathéodory theorem (currently not in mathlib).
Birkhoff's theorem is the Minkowski-Carathéodory theorem applied to the set of bistochastic
matrices, permutation matrices being the extreme points.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

-/


open Set

open Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [TopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {s : Set E}

/-- **Krein-Milman lemma**: In a LCTVS, any nonempty compact set has an extreme point. -/
theorem IsCompact.has_extreme_point (hscomp : IsCompact s) (hsnemp : s.Nonempty) :
    (s.extremePoints ℝ).Nonempty := by
  let S : Set (Set E) := { t | t.Nonempty ∧ IsClosed t ∧ IsExtreme ℝ s t }
  -- ⊢ Set.Nonempty (extremePoints ℝ s)
  rsuffices ⟨t, ⟨⟨x, hxt⟩, htclos, hst⟩, hBmin⟩ : ∃ t ∈ S, ∀ u ∈ S, u ⊆ t → u = t
  -- ⊢ Set.Nonempty (extremePoints ℝ s)
  · refine' ⟨x, mem_extremePoints_iff_extreme_singleton.2 _⟩
    -- ⊢ IsExtreme ℝ s {x}
    rwa [← eq_singleton_iff_unique_mem.2 ⟨hxt, fun y hyB => ?_⟩]
    -- ⊢ y = x
    by_contra hyx
    -- ⊢ False
    obtain ⟨l, hl⟩ := geometric_hahn_banach_point_point hyx
    -- ⊢ False
    obtain ⟨z, hzt, hz⟩ :=
      (isCompact_of_isClosed_subset hscomp htclos hst.1).exists_forall_ge ⟨x, hxt⟩
        l.continuous.continuousOn
    have h : IsExposed ℝ t ({ z ∈ t | ∀ w ∈ t, l w ≤ l z }) := fun _ => ⟨l, rfl⟩
    -- ⊢ False
    rw [← hBmin ({ z ∈ t | ∀ w ∈ t, l w ≤ l z })
      ⟨⟨z, hzt, hz⟩, h.isClosed htclos, hst.trans h.isExtreme⟩ (t.sep_subset _)] at hyB
    exact hl.not_le (hyB.2 x hxt)
    -- 🎉 no goals
  refine' zorn_superset _ fun F hFS hF => _
  -- ⊢ ∃ lb, lb ∈ S ∧ ∀ (s : Set E), s ∈ F → lb ⊆ s
  obtain rfl | hFnemp := F.eq_empty_or_nonempty
  -- ⊢ ∃ lb, lb ∈ S ∧ ∀ (s : Set E), s ∈ ∅ → lb ⊆ s
  · exact ⟨s, ⟨hsnemp, hscomp.isClosed, IsExtreme.rfl⟩, fun _ => False.elim⟩
    -- 🎉 no goals
  refine' ⟨⋂₀ F, ⟨_, isClosed_sInter fun t ht => (hFS ht).2.1,
    isExtreme_sInter hFnemp fun t ht => (hFS ht).2.2⟩, fun t ht => sInter_subset_of_mem ht⟩
  haveI : Nonempty (↥F) := hFnemp.to_subtype
  -- ⊢ Set.Nonempty (⋂₀ F)
  rw [sInter_eq_iInter]
  -- ⊢ Set.Nonempty (⋂ (i : ↑F), ↑i)
  refine' IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed _ (fun t u => _)
    (fun t => (hFS t.mem).1)
    (fun t => isCompact_of_isClosed_subset hscomp (hFS t.mem).2.1 (hFS t.mem).2.2.1) fun t =>
      (hFS t.mem).2.1
  obtain htu | hut := hF.total t.mem u.mem
  -- ⊢ ∃ z, (fun x x_1 => x ⊇ x_1) ↑t ↑z ∧ (fun x x_1 => x ⊇ x_1) ↑u ↑z
  exacts [⟨t, Subset.rfl, htu⟩, ⟨u, hut, Subset.rfl⟩]
  -- 🎉 no goals
#align is_compact.has_extreme_point IsCompact.has_extreme_point

/-- **Krein-Milman theorem**: In a LCTVS, any compact convex set is the closure of the convex hull
    of its extreme points. -/
theorem closure_convexHull_extremePoints (hscomp : IsCompact s) (hAconv : Convex ℝ s) :
    closure (convexHull ℝ <| s.extremePoints ℝ) = s := by
  apply (closure_minimal (convexHull_min extremePoints_subset hAconv) hscomp.isClosed).antisymm
  -- ⊢ s ⊆ closure (↑(convexHull ℝ) (extremePoints ℝ s))
  by_contra hs
  -- ⊢ False
  obtain ⟨x, hxA, hxt⟩ := not_subset.1 hs
  -- ⊢ False
  obtain ⟨l, r, hlr, hrx⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull _ _).closure isClosed_closure hxt
  have h : IsExposed ℝ s ({ y ∈ s | ∀ z ∈ s, l z ≤ l y }) := fun _ => ⟨l, rfl⟩
  -- ⊢ False
  obtain ⟨z, hzA, hz⟩ := hscomp.exists_forall_ge ⟨x, hxA⟩ l.continuous.continuousOn
  -- ⊢ False
  obtain ⟨y, hy⟩ := (h.isCompact hscomp).has_extreme_point ⟨z, hzA, hz⟩
  -- ⊢ False
  linarith [hlr _ (subset_closure <| subset_convexHull _ _ <|
    h.isExtreme.extremePoints_subset_extremePoints hy), hy.1.2 x hxA]
#align closure_convex_hull_extreme_points closure_convexHull_extremePoints
