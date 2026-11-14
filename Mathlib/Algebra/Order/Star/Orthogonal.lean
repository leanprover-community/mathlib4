/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Star.Orthogonal

/-!
# Star-orthogonality in star-ordered rings

This file develops the API for `IsStarOrtho` in a `StarOrderedRing` with `IsProperStar`
(e.g., a C⋆-algebra).

## Main declarations

+ `isStarOrtho_iff_of_nonneg`: if `0 ≤ a`, then `a ⋆⟂ b` if and only if
  `star b * a * b = 0` and `b * a * star b = 0`.
+ `IsStarOrtho.mono`: if `0 ≤ a ≤ b` and `b ⋆⟂ c`, then `a ⋆⟂ c`.
+ `IsStarOrtho.sum_iff`: a finite sum of nonnegative elements is star-orthogonal to `c` if and only
  if each summand is.
+ `isStarProjection_sum_iff`: a finite sum of star projections is a star projection if and only if
  they are pairwise star-orthogonal.
+ `IsStarProjection.isStarOrtho_of_add`: If the sum of a star projection and a nonnegative element
  is a star projection, then they are star-orthogonal.
-/

public section

open scoped Function StarRing

variable {A : Type*}

section StarOrderedRing

variable [NonUnitalSemiring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]

lemma isStarOrtho_iff_of_nonneg {a b : A} (ha : 0 ≤ a) :
    a ⋆⟂ b ↔ star b * a * b = 0 ∧ b * a * star b = 0 := by
  rw [isStarOrtho_iff', (IsSelfAdjoint.of_nonneg ha).star_eq]
  refine ⟨fun h ↦ ⟨by simp [mul_assoc, h.2], by simp [mul_assoc, h.1]⟩, fun h ↦ ⟨?_, ?_⟩⟩
  all_goals apply mul_eq_zero_of_star_left_conjugate_eq_zero ha
  exacts [by simpa using h.2, h.1]

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

/-- If `0 ≤ a` and `0 ≤ b` and `c ⋆⟂ (a + b)`, then `c ⋆⟂ a`. -/
lemma right_of_add_right {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : c ⋆⟂ (a + b)) : c ⋆⟂ b :=
  h.symm.right_of_add_left ha hb |>.symm

lemma add_left_iff {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ⋆⟂ c ↔ a ⋆⟂ c ∧ b ⋆⟂ c :=
  ⟨fun h ↦ ⟨h.left_of_add_left ha hb, h.right_of_add_left ha hb⟩, fun h ↦ h.1.add_left h.2⟩

lemma add_right_iff {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    c ⋆⟂ (a + b) ↔ c ⋆⟂ a ∧ c ⋆⟂ b := by
  simpa [isStarOrtho_comm] using add_left_iff ha hb

lemma sum_left_iff {ι : Type*} {s : Finset ι} {f : ι → A} {c : A} (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i) ⋆⟂ c ↔ ∀ j ∈ s, f j ⋆⟂ c :=
  ⟨fun h _j hj ↦ h.anti_left (hf _ hj) (Finset.single_le_sum hf hj), sum_left⟩

lemma sum_right_iff {ι : Type*} {s : Finset ι} {f : ι → A} {c : A} (hf : ∀ i ∈ s, 0 ≤ f i) :
    c ⋆⟂ (∑ i ∈ s, f i) ↔ ∀ j ∈ s, c ⋆⟂ f j := by
  simpa [isStarOrtho_comm] using sum_left_iff hf

/-- If each `f i` is nonnegative then `(∑ i ∈ s, f i) ⋆⟂ c`, if and only if `f j ⋆⟂ c`
for every `j ∈ s`. -/
alias ⟨of_sum_left, _⟩ := sum_left_iff
/-- If each `f i` is nonnegative then `c ⋆⟂ (∑ i ∈ s, f i)`, if and only if `c ⋆⟂ f j`
for every `j ∈ s`. -/
alias ⟨of_sum_right, _⟩ := sum_right_iff

end IsStarOrtho

end StarOrderedRing

section NonUnitalRing

variable [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]

/-- If `p` and `p + q` are star projections and `0 ≤ q`, then `q ⋆⟂ p`. -/
lemma IsStarProjection.isStarOrtho_of_add {p q : A} (hp : IsStarProjection p)
    (hq : 0 ≤ q) (hr : IsStarProjection (p + q)) : p ⋆⟂ q := by
  set r := p + q
  have hpp : p * p = p := hp.isIdempotentElem.eq
  /- `p * q * p = p * r * p - p`, and `p - p * r * p = (p - p * r) * star (p - p * r) ≥ 0`. -/
  have h₁ : p * q * p = p * r * p - p := by
    simp [r, mul_add, add_mul, hpp]
  have h₂ : p - p * r * p = (p - p * r) * star (p - p * r) := by
    have hrr : p * r * r * p = p * r * p := by rw [mul_assoc p r r, hr.isIdempotentElem.eq]
    rw [star_sub, star_mul, hp.isSelfAdjoint.star_eq, hr.isSelfAdjoint.star_eq]
    simp only [mul_sub, sub_mul, ← mul_assoc, hpp, hrr]
    rw [sub_self, sub_zero]
  have h : p * q * p ≤ 0 := by
    rw [h₁, sub_nonpos, ← sub_nonneg, h₂]
    exact mul_star_self_nonneg _
  exact .symm <| .of_nonneg hq
    (by rwa [hp.isSelfAdjoint.star_eq]) (by rwa [hp.isSelfAdjoint.star_eq])

/-- If `p` and `q` are star projections, their sum is a star projection if and only if they are
star-orthogonal. -/
lemma isStarProjection_add_iff {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (p + q) ↔ p ⋆⟂ q :=
  ⟨hp.isStarOrtho_of_add hq.nonneg, fun h ↦ hp.add hq (h.mul_eq_zero' hq.isSelfAdjoint)⟩

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
