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

+ `isStarOrtho_of_nonneg_iff`: if `0 ≤ a`, then `a ⋆⟂ b` if and only if
  `star b * a * b = 0` and `b * a * star b = 0`.
+ `IsStarOrtho.of_le`: if `0 ≤ a ≤ b` and `b ⋆⟂ c`, then `a ⋆⟂ c`.
+ `IsStarOrtho.sum_iff`: a finite sum of nonnegative elements is star-orthogonal to `c` if and only
  if each summand is.
+ `isStarProjection_sum_iff`: a finite sum of star projections is a star projection if and only if
  they are pairwise star-orthogonal.
-/

public section

open scoped Function StarRing

variable {A : Type*}

section StarOrderedRing

variable [NonUnitalSemiring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]

/-- If `0 ≤ a` and `c * a * star c = 0`, then `a * star c = 0`. -/
lemma mul_star_eq_zero_of_mul_mul_star_eq_zero {a c : A} (ha : 0 ≤ a)
    (h : c * a * star c = 0) : a * star c = 0 := by
  rw [StarOrderedRing.nonneg_iff] at ha
  induction ha using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨x, rfl⟩ := hx
    have : star (x * star c) * (x * star c) = 0 := by simpa [mul_assoc] using h
    rw [mul_assoc, star_mul_self_eq_zero.mp this, mul_zero]
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [← StarOrderedRing.nonneg_iff] at hx hy
    rw [mul_add, add_mul, add_eq_zero_iff_of_nonneg (star_right_conjugate_nonneg hx c)
      (star_right_conjugate_nonneg hy c)] at h
    rw [add_mul, ihx h.1, ihy h.2, add_zero]

lemma isStarOrtho_of_nonneg_iff {a b : A} (ha : 0 ≤ a) :
    a ⋆⟂ b ↔ star b * a * b = 0 ∧ b * a * star b = 0 := by
  rw [isStarOrtho_iff', (IsSelfAdjoint.of_nonneg ha).star_eq]
  refine ⟨fun h ↦ ⟨by simp [mul_assoc, h.2], by simp [mul_assoc, h.1]⟩, fun h ↦ ⟨?_, ?_⟩⟩
  · exact mul_star_eq_zero_of_mul_mul_star_eq_zero ha h.2
  · simpa using mul_star_eq_zero_of_mul_mul_star_eq_zero ha (c := star b) (by simpa using h.1)

lemma isStarOrtho_of_nonneg_of_isSelfAdjoint_iff {a b : A} (ha : 0 ≤ a) (hb : IsSelfAdjoint b) :
    a ⋆⟂ b ↔ b * a * b = 0 := by
  simp [isStarOrtho_of_nonneg_iff ha, hb.star_eq]

namespace IsStarOrtho

lemma of_nonneg {a b : A} (ha : 0 ≤ a) (h₁ : star b * a * b ≤ 0) (h₂ : b * a * star b ≤ 0) :
    a ⋆⟂ b :=
  isStarOrtho_of_nonneg_iff ha |>.mpr
    ⟨le_antisymm h₁ (star_left_conjugate_nonneg ha b),
      le_antisymm h₂ (star_right_conjugate_nonneg ha b)⟩

lemma of_le {a b c : A} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ⋆⟂ c) : a ⋆⟂ c := by
  obtain ⟨h₁, h₂⟩ := isStarOrtho_of_nonneg_iff (ha.trans hab) |>.mp hbc
  exact .of_nonneg ha (h₁ ▸ star_left_conjugate_le_conjugate hab c)
    (h₂ ▸ star_right_conjugate_le_conjugate hab c)

/-- If `0 ≤ a` and `0 ≤ b` and `(a + b) ⋆⟂ c`, then `a ⋆⟂ c`. -/
lemma of_add_left {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : (a + b) ⋆⟂ c) : a ⋆⟂ c :=
  h.of_le ha (le_add_of_nonneg_right hb)

/-- If `0 ≤ a` and `0 ≤ b` and `(a + b) ⋆⟂ c`, then `b ⋆⟂ c`. -/
lemma of_add_right {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : (a + b) ⋆⟂ c) : b ⋆⟂ c :=
  h.of_le hb (le_add_of_nonneg_left ha)

lemma add_iff {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ⋆⟂ c ↔ a ⋆⟂ c ∧ b ⋆⟂ c :=
  ⟨fun h ↦ ⟨h.of_add_left ha hb, h.of_add_right ha hb⟩, fun h ↦ h.1.add_left h.2⟩

lemma sum_iff {ι : Type*} {s : Finset ι} {f : ι → A} {c : A} (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i) ⋆⟂ c ↔ ∀ j ∈ s, f j ⋆⟂ c :=
  ⟨fun h _j hj ↦ h.of_le (hf _ hj) (Finset.single_le_sum hf hj), sum_left⟩

/-- If each `f i` is nonnegative and `(∑ i ∈ s, f i) ⋆⟂ c`, then `f j ⋆⟂ c` for every `j ∈ s`. -/
alias ⟨of_sum, _⟩ := sum_iff

end IsStarOrtho

end StarOrderedRing

section NonUnitalRing

variable [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]

/-- If `p` and `p + q` are star projections and `0 ≤ q`, then `q ⋆⟂ p`. -/
private lemma IsStarProjection.isStarOrtho_of_add {p q : A} (hp : IsStarProjection p)
    (hq : 0 ≤ q) (hr : IsStarProjection (p + q)) : q ⋆⟂ p := by
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
  exact .of_nonneg hq (by rwa [hp.isSelfAdjoint.star_eq]) (by rwa [hp.isSelfAdjoint.star_eq])

/-- In a star-ordered ring with proper star (e.g., a C⋆-algebra), a finite sum of star
projections is a star projection if and only if they are pairwise star-orthogonal. -/
lemma isStarProjection_sum_iff {ι : Type*} {s : Finset ι} {f : ι → A}
    (hf : ∀ i ∈ s, IsStarProjection (f i)) :
    IsStarProjection (∑ i ∈ s, f i) ↔ (s : Set ι).Pairwise ((· ⋆⟂ ·) on f) := by
  classical
  refine ⟨fun hP i hi j hj hij ↦ ?_, isStarProjection_sum hf⟩
  rw [← Finset.add_sum_erase s f hi] at hP
  have hf' (k : ι) (hk : k ∈ s.erase i) : 0 ≤ f k := (hf k (by grind)).nonneg
  exact (hf i hi).isStarOrtho_of_add (Finset.sum_nonneg hf') hP |>.of_sum hf' j
    (Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩) |>.symm

end NonUnitalRing
