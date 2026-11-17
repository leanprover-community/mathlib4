/-
Copyright (c) 2026 David Iach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Iach
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Independent

/-!
# Betweenness in convex independent sets

Three distinct members of a convex independent set are not collinear. A base midpoint is excluded
from the set, and if collinear with two other members it lies strictly between them.
-/

@[expose] public section

open Set

namespace ConvexIndependent

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] {s : Set E}

/-- Three distinct members of a convex independent set cannot be collinear. -/
theorem not_collinear (hs : ConvexIndependent 𝕜 ((↑) : s → E))
    {a b c : E} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ Collinear 𝕜 ({a, b, c} : Set E) := by
  intro h
  rcases h.wbtw_or_wbtw_or_wbtw with h | h | h
  · rcases eq_or_eq_of_mem_segment hs ha hc hb h.mem_segment with h | h
    · exact hab h.symm
    · exact hbc h
  · rcases eq_or_eq_of_mem_segment hs hb ha hc h.mem_segment with h | h
    · exact hbc h.symm
    · exact hac h.symm
  · rcases eq_or_eq_of_mem_segment hs hc hb ha h.mem_segment with h | h
    · exact hac h
    · exact hab h

/-- The midpoint of two distinct members does not belong to a convex independent set. -/
theorem midpoint_notMem (hs : ConvexIndependent 𝕜 ((↑) : s → E))
    {a b : E} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    midpoint 𝕜 a b ∉ s := by
  intro hm
  have ht := sbtw_midpoint_of_ne 𝕜 hab
  rcases eq_or_eq_of_mem_segment hs ha hb hm ht.wbtw.mem_segment with h | h
  · exact ht.ne_left h
  · exact ht.ne_right h

/-- If the midpoint of a base is collinear with two other members of a convex independent
set, it lies strictly between them. -/
theorem sbtw_midpoint_of_collinear (hs : ConvexIndependent 𝕜 ((↑) : s → E))
    {a b p q : E} (ha : a ∈ s) (hb : b ∈ s) (hp : p ∈ s) (hq : q ∈ s)
    (hab : a ≠ b) (hpq : p ≠ q) (hpa : p ≠ a) (hpb : p ≠ b)
    (hqa : q ≠ a) (hqb : q ≠ b)
    (hcol : Collinear 𝕜 ({p, midpoint 𝕜 a b, q} : Set E)) :
    Sbtw 𝕜 p (midpoint 𝕜 a b) q := by
  have hm := midpoint_notMem hs ha hb hab
  have hw : Wbtw 𝕜 p (midpoint 𝕜 a b) q := by
    rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
    · exact h
    · exfalso
      apply (convexIndependent_set_iff_notMem_convexHull_sdiff.mp hs) q hq
      apply (convex_convexHull 𝕜 (s \ {q})).mem_of_wbtw h
      · exact (convex_convexHull 𝕜 (s \ {q})).midpoint_mem
          (subset_convexHull 𝕜 _ ⟨ha, hqa.symm⟩)
          (subset_convexHull 𝕜 _ ⟨hb, hqb.symm⟩)
      · exact subset_convexHull 𝕜 _ ⟨hp, hpq⟩
    · exfalso
      apply (convexIndependent_set_iff_notMem_convexHull_sdiff.mp hs) p hp
      apply (convex_convexHull 𝕜 (s \ {p})).mem_of_wbtw h
      · exact subset_convexHull 𝕜 _ ⟨hq, hpq.symm⟩
      · exact (convex_convexHull 𝕜 (s \ {p})).midpoint_mem
          (subset_convexHull 𝕜 _ ⟨ha, hpa.symm⟩)
          (subset_convexHull 𝕜 _ ⟨hb, hpb.symm⟩)
  exact ⟨hw, fun h => hm (h.symm ▸ hp), fun h => hm (h.symm ▸ hq)⟩

end ConvexIndependent
