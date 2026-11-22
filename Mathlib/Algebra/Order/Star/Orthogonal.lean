/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Star.Orthogonal

import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Star-orthogonality in star-ordered rings

This file develops the API for `IsStarOrtho` in a `StarOrderedRing` with `IsProperStar`
(e.g., a C⋆-algebra).

## Main declarations

+ `isStarOrtho_iff_of_nonneg`: if `0 ≤ a`, then `a ⋆⟂ b` if and only if
  `star b * a * b = 0` and `b * a * star b = 0`.
+ `IsStarOrtho.anti_left`: if `0 ≤ a ≤ b` and `b ⋆⟂ c`, then `a ⋆⟂ c`.
+ `IsStarOrtho.sum_left_iff`: a finite sum of nonnegative elements is star-orthogonal to `c` if
  and only if each summand is.
+ `isStarProjection_sum_iff`: a finite sum of star projections is a star projection if and only if
  they are pairwise star-orthogonal.
+ `IsStarProjection.isStarOrtho_of_add`: If the sum of a star projection and a nonnegative element
  is a star projection, then they are star-orthogonal.
+ `isStarProjection_add_iff_of_nonneg`: if `p` is a star projection and `0 ≤ q`, then `p + q` is a
  star projection if and only if `q` is a star projection and `p ⋆⟂ q`.
-/

public section

open scoped Function StarRing

variable {A : Type*}

section StarOrderedRing

variable [NonUnitalSemiring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]

lemma isStarOrtho_iff_of_nonneg {a b : A} (ha : 0 ≤ a) :
    a ⋆⟂ b ↔ star b * a * b = 0 ∧ b * a * star b = 0 := by
  rw [star_left_conjugate_eq_zero_iff ha, star_right_conjugate_eq_zero_iff ha,
    ← star_eq_zero (x := b * a), star_mul, isStarOrtho_iff', (IsSelfAdjoint.of_nonneg ha).star_eq,
    and_comm]

lemma isStarOrtho_iff_of_nonneg_of_isSelfAdjoint {a b : A} (ha : 0 ≤ a) (hb : IsSelfAdjoint b) :
    a ⋆⟂ b ↔ b * a * b = 0 := by
  simp [isStarOrtho_iff_of_nonneg ha, hb.star_eq]

namespace IsStarOrtho

lemma of_nonneg {a b : A} (ha : 0 ≤ a) (h₁ : star b * a * b ≤ 0) (h₂ : b * a * star b ≤ 0) :
    a ⋆⟂ b :=
  isStarOrtho_iff_of_nonneg ha |>.mpr
    ⟨le_antisymm h₁ (star_left_conjugate_nonneg ha b),
      le_antisymm h₂ (star_right_conjugate_nonneg ha b)⟩

lemma anti_left {a b c : A} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ⋆⟂ c) : a ⋆⟂ c := by
  obtain ⟨h₁, h₂⟩ := isStarOrtho_iff_of_nonneg (ha.trans hab) |>.mp hbc
  exact .of_nonneg ha (h₁ ▸ star_left_conjugate_le_conjugate hab c)
    (h₂ ▸ star_right_conjugate_le_conjugate hab c)

lemma anti_right {a b c : A} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : c ⋆⟂ b) : c ⋆⟂ a :=
  hbc.symm.anti_left ha hab |>.symm

lemma anti {a b c d : A} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d)
    (hbd : b ⋆⟂ d) : a ⋆⟂ c :=
  hbd.anti_left ha hab |>.anti_right hc hcd

/-- If `0 ≤ a` and `0 ≤ b` and `(a + b) ⋆⟂ c`, then `a ⋆⟂ c`. -/
lemma left_of_add_left {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : (a + b) ⋆⟂ c) : a ⋆⟂ c :=
  h.anti_left ha (le_add_of_nonneg_right hb)

/-- If `0 ≤ a` and `0 ≤ b` and `(a + b) ⋆⟂ c`, then `b ⋆⟂ c`. -/
lemma right_of_add_left {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : (a + b) ⋆⟂ c) : b ⋆⟂ c :=
  h.anti_left hb (le_add_of_nonneg_left ha)

/-- If `0 ≤ a` and `0 ≤ b` and `c ⋆⟂ (a + b)`, then `c ⋆⟂ a`. -/
lemma left_of_add_right {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : c ⋆⟂ (a + b)) : c ⋆⟂ a :=
  h.symm.left_of_add_left ha hb |>.symm

/-- If `0 ≤ a` and `0 ≤ b` and `c ⋆⟂ (a + b)`, then `c ⋆⟂ b`. -/
lemma right_of_add_right {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : c ⋆⟂ (a + b)) : c ⋆⟂ b :=
  h.symm.right_of_add_left ha hb |>.symm

lemma add_left_iff {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ⋆⟂ c ↔ a ⋆⟂ c ∧ b ⋆⟂ c :=
  ⟨fun h ↦ ⟨h.left_of_add_left ha hb, h.right_of_add_left ha hb⟩, fun h ↦ h.1.add_left h.2⟩

lemma add_right_iff {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    c ⋆⟂ (a + b) ↔ c ⋆⟂ a ∧ c ⋆⟂ b := by
  simpa [isStarOrtho_comm] using add_left_iff ha hb

/-- If each `f i` is nonnegative then `(∑ i ∈ s, f i) ⋆⟂ c` if and only if `f j ⋆⟂ c`
for every `j ∈ s`. -/
lemma sum_left_iff {ι : Type*} {s : Finset ι} {f : ι → A} {c : A} (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i) ⋆⟂ c ↔ ∀ j ∈ s, f j ⋆⟂ c :=
  ⟨fun h _j hj ↦ h.anti_left (hf _ hj) (Finset.single_le_sum hf hj), sum_left⟩

/-- If each `f i` is nonnegative then `c ⋆⟂ (∑ i ∈ s, f i)` if and only if `c ⋆⟂ f j`
for every `j ∈ s`. -/
lemma sum_right_iff {ι : Type*} {s : Finset ι} {f : ι → A} {c : A} (hf : ∀ i ∈ s, 0 ≤ f i) :
    c ⋆⟂ (∑ i ∈ s, f i) ↔ ∀ j ∈ s, c ⋆⟂ f j := by
  simpa [isStarOrtho_comm] using sum_left_iff hf

alias ⟨of_sum_left, _⟩ := sum_left_iff
alias ⟨of_sum_right, _⟩ := sum_right_iff

end IsStarOrtho

end StarOrderedRing

section NonUnitalRing

variable [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]

/-- If `p` and `p + q` are star projections and `0 ≤ q`, then `p ⋆⟂ q`. -/
lemma IsStarProjection.isStarOrtho_of_add {p q : A} (hp : IsStarProjection p)
    (hq : 0 ≤ q) (hr : IsStarProjection (p + q)) : p ⋆⟂ q := by
  have := hr.mul_right_and_mul_left_of_nonneg_of_le hp.nonneg (le_add_of_nonneg_right hq) |>.1
  rw [mul_add, hp.isIdempotentElem.eq, add_eq_left] at this
  exact hp.isSelfAdjoint.isStarOrtho_iff_mul_eq_zero (.of_nonneg hq) |>.mpr this

/-- If `p` and `q` are star projections, their sum is a star projection if and only if they are
star-orthogonal. -/
lemma isStarProjection_add_iff {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (p + q) ↔ p ⋆⟂ q :=
  ⟨hp.isStarOrtho_of_add hq.nonneg, fun h ↦ hp.add hq (h.mul_eq_zero' hq.isSelfAdjoint)⟩

/-- If `p` is a star projection and `0 ≤ q`, then `p + q` is a star projection if and only if
`q` is a star projection and `p ⋆⟂ q`. -/
lemma isStarProjection_add_iff_of_nonneg {p q : A} (hp : IsStarProjection p) (hq : 0 ≤ q) :
    IsStarProjection (p + q) ↔ IsStarProjection q ∧ p ⋆⟂ q := by
  refine ⟨fun hr ↦ ?_, fun h ↦ isStarProjection_add_iff hp h.1 |>.mpr h.2⟩
  have hpq := hp.isStarOrtho_of_add hq hr
  refine ⟨?_, hpq⟩
  simpa using hp.sub_of_mul_eq_left hr <| by
    rw [mul_add, hp.isIdempotentElem.eq, hpq.mul_eq_zero' (.of_nonneg hq), add_zero]

/-- In a star-ordered ring with proper star (e.g., a C⋆-algebra), a finite sum of star
projections is a star projection if and only if they are pairwise star-orthogonal. -/
lemma isStarProjection_sum_iff {ι : Type*} {s : Finset ι} {f : ι → A}
    (hf : ∀ i ∈ s, IsStarProjection (f i)) :
    IsStarProjection (∑ i ∈ s, f i) ↔ (s : Set ι).Pairwise ((· ⋆⟂ ·) on f) := by
  classical
  refine ⟨fun hP i hi j hj hij ↦ ?_, .sum hf⟩
  rw [← Finset.add_sum_erase s f hi] at hP
  have hf' (k : ι) (hk : k ∈ s.erase i) : 0 ≤ f k := (hf k (by grind)).nonneg
  exact (hf i hi).isStarOrtho_of_add (Finset.sum_nonneg hf') hP
    |>.symm.of_sum_left hf' j (Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩) |>.symm

end NonUnitalRing
