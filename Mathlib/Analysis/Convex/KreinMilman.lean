/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Topology.Algebra.ContinuousAffineMap

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

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {s : Set E}
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [T1Space F]

/-- **Krein-Milman lemma**: In a LCTVS, any nonempty compact set has an extreme point. -/
theorem IsCompact.extremePoints_nonempty (hscomp : IsCompact s) (hsnemp : s.Nonempty) :
    (s.extremePoints ℝ).Nonempty := by
  let S : Set (Set E) := { t | t.Nonempty ∧ IsClosed t ∧ IsExtreme ℝ s t }
  rsuffices ⟨t, ht⟩ : ∃ t, Minimal (· ∈ S) t
  · obtain ⟨⟨x,hxt⟩, htclos, hst⟩ := ht.prop
    refine ⟨x, IsExtreme.mem_extremePoints ?_⟩
    rwa [← eq_singleton_iff_unique_mem.2 ⟨hxt, fun y hyB => ?_⟩]
    by_contra hyx
    obtain ⟨l, hl⟩ := geometric_hahn_banach_point_point hyx
    obtain ⟨z, hzt, hz⟩ :=
      (hscomp.of_isClosed_subset htclos hst.1).exists_isMaxOn ⟨x, hxt⟩
        l.continuous.continuousOn
    have h : IsExposed ℝ t ({ z ∈ t | ∀ w ∈ t, l w ≤ l z }) := fun _ => ⟨l, rfl⟩
    rw [ht.eq_of_ge (y := ({ z ∈ t | ∀ w ∈ t, l w ≤ l z }))
      ⟨⟨z, hzt, hz⟩, h.isClosed htclos, hst.trans h.isExtreme⟩ (t.sep_subset _)] at hyB
    exact hl.not_ge (hyB.2 x hxt)
  refine zorn_superset _ fun F hFS hF => ?_
  obtain rfl | hFnemp := F.eq_empty_or_nonempty
  · exact ⟨s, ⟨hsnemp, hscomp.isClosed, IsExtreme.rfl⟩, fun _ => False.elim⟩
  refine ⟨⋂₀ F, ⟨?_, isClosed_sInter fun t ht => (hFS ht).2.1,
    isExtreme_sInter hFnemp fun t ht => (hFS ht).2.2⟩, fun t ht => sInter_subset_of_mem ht⟩
  haveI : Nonempty (↥F) := hFnemp.to_subtype
  rw [sInter_eq_iInter]
  refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ (fun t u => ?_)
    (fun t => (hFS t.mem).1)
    (fun t => hscomp.of_isClosed_subset (hFS t.mem).2.1 (hFS t.mem).2.2.1) fun t =>
      (hFS t.mem).2.1
  obtain htu | hut := hF.total t.mem u.mem
  exacts [⟨t, Subset.rfl, htu⟩, ⟨u, hut, Subset.rfl⟩]

/-- **Krein-Milman theorem**: In a LCTVS, any compact convex set is the closure of the convex hull
of its extreme points. -/
theorem closure_convexHull_extremePoints (hscomp : IsCompact s) (hAconv : Convex ℝ s) :
    closure (convexHull ℝ <| s.extremePoints ℝ) = s := by
  apply (closure_minimal (convexHull_min extremePoints_subset hAconv) hscomp.isClosed).antisymm
  by_contra hs
  obtain ⟨x, hxA, hxt⟩ := not_subset.1 hs
  obtain ⟨l, r, hlr, hrx⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull _ _).closure isClosed_closure hxt
  have h : IsExposed ℝ s ({ y ∈ s | ∀ z ∈ s, l z ≤ l y }) := fun _ => ⟨l, rfl⟩
  obtain ⟨z, hzA, hz⟩ := hscomp.exists_isMaxOn ⟨x, hxA⟩ l.continuous.continuousOn
  obtain ⟨y, hy⟩ := (h.isCompact hscomp).extremePoints_nonempty ⟨z, hzA, hz⟩
  linarith [hlr _ (subset_closure <| subset_convexHull _ _ <|
    h.isExtreme.extremePoints_subset_extremePoints hy), hy.1.2 x hxA]

/-- A continuous affine map is surjective from the extreme points of a compact set to the extreme
points of the image of that set. This inclusion is in general strict. -/
lemma surjOn_extremePoints_image (f : E →ᴬ[ℝ] F) (hs : IsCompact s) :
    SurjOn f (extremePoints ℝ s) (extremePoints ℝ (f '' s)) := by
  rintro w hw
  -- The fiber of `w` is nonempty and compact
  have ht : IsCompact {x ∈ s | f x = w} :=
    hs.inter_right <| isClosed_singleton.preimage f.continuous
  have ht₀ : {x ∈ s | f x = w}.Nonempty := by simpa using extremePoints_subset hw
  -- Hence by the Krein-Milman lemma it has an extreme point `x`
  obtain ⟨x, ⟨hx, rfl⟩, hyt⟩ := ht.extremePoints_nonempty ht₀
  -- `f x = w` and `x` is an extreme point of `s`, so we're done
  refine mem_image_of_mem _ ⟨hx, fun y hy z hz hxyz ↦ ?_⟩
  have := by simpa using image_openSegment _ f.toAffineMap y z
  rw [mem_extremePoints] at hw
  have := hw.2 _ (mem_image_of_mem _ hy) _ (mem_image_of_mem _ hz) <| by
    rw [← this]; exact mem_image_of_mem _ hxyz
  exact hyt ⟨hy, this.1⟩ ⟨hz, this.2⟩ hxyz
