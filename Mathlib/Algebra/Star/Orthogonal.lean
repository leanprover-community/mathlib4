/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.Star.StarProjection

/-!
# Star-orthogonality

This file develops the basic API for `IsStarOrtho`, the predicate that two elements `p` and `q`
of a ⋆-ring are *star-orthogonal*, i.e., `p * star q = 0` and `star q * p = 0`. This is denoted
`p ⋆⟂ q` with the notation available in the `StarRing` namespace. The definition is in
`Mathlib/Algebra/Star/Basic.lean`.

## Main declarations

+ `isStarOrtho_iff_mul_eq_zero`: selfadjoint elements are star-orthogonal if and only if their
  product is zero.
+ `IsStarOrtho.star_add_mul_add`: if `p ⋆⟂ q`, then
  `star (p + q) * (p + q) = star p * p + star q * q`.
+ `IsStarProjection.add_iff_isStarOrtho`: the sum of star projections is a star projection if and
  only if they are star-orthogonal.
+ `isStarProjection_sum`: a finite sum of pairwise star-orthogonal star projections is a star
  projection.
-/

public section

open scoped Function StarRing
open Finset

section NonUnitalSemiring

variable {R : Type*} [NonUnitalSemiring R] [StarRing R] {p q : R}

lemma IsStarOrtho.commute_star (h : p ⋆⟂ q) : Commute p (star q) :=
  h.mul_star_eq_zero.trans h.star_mul_eq_zero.symm

lemma IsStarOrtho.star_commute (h : p ⋆⟂ q) : Commute (star p) q :=
  h.symm.commute_star.symm

namespace IsStarOrtho

@[simp]
lemma zero_left (q : R) : (0 : R) ⋆⟂ q := by simp [isStarOrtho_iff]

@[simp]
lemma zero_right (p : R) : p ⋆⟂ 0 := by simp [isStarOrtho_iff]

protected lemma star (h : p ⋆⟂ q) : star p ⋆⟂ star q :=
  ⟨by rw [star_star, h.symm.star_mul_eq_zero], by rw [star_star, h.symm.mul_star_eq_zero]⟩

@[simp]
lemma star_iff : star p ⋆⟂ star q ↔ p ⋆⟂ q :=
  ⟨fun h ↦ by simpa using h.star, .star⟩

lemma add_left {p₁ p₂ : R} (h₁ : p₁ ⋆⟂ q) (h₂ : p₂ ⋆⟂ q) : (p₁ + p₂) ⋆⟂ q :=
  ⟨by rw [add_mul, h₁.mul_star_eq_zero, h₂.mul_star_eq_zero, add_zero],
    by rw [mul_add, h₁.star_mul_eq_zero, h₂.star_mul_eq_zero, add_zero]⟩

lemma add_right {q₁ q₂ : R} (h₁ : p ⋆⟂ q₁) (h₂ : p ⋆⟂ q₂) : p ⋆⟂ (q₁ + q₂) :=
  (h₁.symm.add_left h₂.symm).symm

lemma smul_left {S : Type*} [SMulZeroClass S R] [IsScalarTower S R R] [SMulCommClass S R R]
    (h : p ⋆⟂ q) (c : S) : (c • p) ⋆⟂ q :=
  ⟨by rw [smul_mul_assoc, h.mul_star_eq_zero, smul_zero],
    by rw [mul_smul_comm, h.star_mul_eq_zero, smul_zero]⟩

lemma smul_right {S : Type*} [SMulZeroClass S R] [IsScalarTower S R R] [SMulCommClass S R R]
    (h : p ⋆⟂ q) (c : S) : p ⋆⟂ (c • q) :=
  (h.symm.smul_left c).symm

lemma list_sum_left {l : List R} (h : ∀ x ∈ l, x ⋆⟂ q) : l.sum ⋆⟂ q := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.sum_cons]
    exact (h x List.mem_cons_self).add_left <| ih fun y hy ↦ h y <| List.mem_cons_of_mem x hy

lemma list_sum_right {l : List R} (h : ∀ x ∈ l, p ⋆⟂ x) : p ⋆⟂ l.sum :=
  (list_sum_left fun x hx ↦ (h x hx).symm).symm

lemma multiset_sum_left {s : Multiset R} (h : ∀ x ∈ s, x ⋆⟂ q) : s.sum ⋆⟂ q := by
  induction s using Quotient.inductionOn
  exact list_sum_left h

lemma multiset_sum_right {s : Multiset R} (h : ∀ x ∈ s, p ⋆⟂ x) : p ⋆⟂ s.sum :=
  (multiset_sum_left fun x hx ↦ (h x hx).symm).symm

lemma sum_left {ι : Type*} {s : Finset ι} {f : ι → R} (h : ∀ i ∈ s, f i ⋆⟂ q) :
    (∑ i ∈ s, f i) ⋆⟂ q :=
  multiset_sum_left <| Multiset.forall_mem_map_iff.mpr h

lemma sum_right {ι : Type*} {s : Finset ι} {f : ι → R} (h : ∀ i ∈ s, p ⋆⟂ f i) :
    p ⋆⟂ (∑ i ∈ s, f i) :=
  (sum_left fun i hi ↦ (h i hi).symm).symm

/-- If `p` and `q` are star-orthogonal, then so are `p * a * star p` and `q * b * star q`. -/
protected lemma star_right_conjugate (h : p ⋆⟂ q) (a b : R) :
    (p * a * star p) ⋆⟂ (q * b * star q) where
  mul_star_eq_zero := by
    simp only [star_mul, star_star, mul_assoc]
    rw [← mul_assoc (star p) q, h.symm.star_mul_eq_zero]
    simp
  star_mul_eq_zero := by
    simp only [star_mul, star_star, mul_assoc]
    rw [← mul_assoc (star q) p, h.star_mul_eq_zero]
    simp

/-- If `p` and `q` are star-orthogonal, then so are `star p * a * p` and `star q * b * q`. -/
protected lemma star_left_conjugate (h : p ⋆⟂ q) (a b : R) :
    (star p * a * p) ⋆⟂ (star q * b * q) := by
  simpa using h.star.star_right_conjugate a b

/-- A version of `IsStarOrtho.mul_mul` with slightly weaker hypotheses. -/
lemma mul_mul' {p₁ p₂ q₁ q₂ : R} (h₁ : star q₁ * p₁ = 0) (h₂ : p₂ * star q₂ = 0) (a b : R) :
    (p₁ * a * p₂) ⋆⟂ (q₁ * b * q₂) where
  mul_star_eq_zero := by
    have : p₁ * a * p₂ * (star q₂ * (star b * star q₁)) =
        p₁ * a * (p₂ * star q₂) * star b * star q₁ := by simp [mul_assoc]
    simp [this, h₂]
  star_mul_eq_zero := by
    have : (star q₂ * (star b * star q₁)) * (p₁ * a * p₂) =
        star q₂ * star b * (star q₁ * p₁) * a * p₂ := by simp [mul_assoc]
    simp [this, h₁]

lemma mul_mul {p₁ p₂ q₁ q₂ : R} (h₁ : p₁ ⋆⟂ q₁) (h₂ : p₂ ⋆⟂ q₂) (a b : R) :
    (p₁ * a * p₂) ⋆⟂ (q₁ * b * q₂) :=
  mul_mul' h₁.star_mul_eq_zero h₂.mul_star_eq_zero a b

lemma mul_star_self (h : p ⋆⟂ q) : (p * star p) ⋆⟂ (q * star q) where
  mul_star_eq_zero := by simp [mul_assoc, ← mul_assoc (star p) q, h.symm.star_mul_eq_zero]
  star_mul_eq_zero := by simp [mul_assoc, ← mul_assoc (star q) p, h.star_mul_eq_zero]

lemma star_mul_self (h : p ⋆⟂ q) : (star p * p) ⋆⟂ (star q * q) := by
  simpa using h.star.mul_star_self

lemma map {S F : Type*} [NonUnitalSemiring S] [StarRing S] [FunLike F R S]
    [NonUnitalRingHomClass F R S] [StarHomClass F R S] (f : F) (h : p ⋆⟂ q) : f p ⋆⟂ f q where
  mul_star_eq_zero := by rw [← map_star, ← map_mul, h.mul_star_eq_zero, map_zero]
  star_mul_eq_zero := by rw [← map_star, ← map_mul, h.star_mul_eq_zero, map_zero]

lemma map_iff {S F : Type*} [NonUnitalSemiring S] [StarRing S] [FunLike F R S]
    [NonUnitalRingHomClass F R S] [StarHomClass F R S] {f : F} (hf : Function.Injective f) :
    f p ⋆⟂ f q ↔ p ⋆⟂ q where
  mp h := by constructor <;> apply hf <;> simp [map_star, h.mul_star_eq_zero, h.star_mul_eq_zero]
  mpr := map f

lemma star_add_mul_add (h : p ⋆⟂ q) :
    star (p + q) * (p + q) = star p * p + star q * q := by
  simp [mul_add, add_mul, h.symm.star_mul_eq_zero, h.star_mul_eq_zero]

lemma add_mul_star_add (h : p ⋆⟂ q) :
    (p + q) * star (p + q) = p * star p + q * star q := by
  simpa using h.star.star_add_mul_add

end IsStarOrtho

lemma Set.Pairwise.star_sum_mul_sum_of_isStarOrtho {ι : Type*} {s : Finset ι} {f : ι → R}
    (h : (s : Set ι).Pairwise ((· ⋆⟂ ·) on f)) :
    star (∑ i ∈ s, f i) * (∑ i ∈ s, f i) = ∑ i ∈ s, star (f i) * f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ha' : f a ⋆⟂ ∑ i ∈ s, f i :=
      .sum_right fun j hj ↦ h (by simp) (by simp [hj]) (fun h' ↦ ha (h' ▸ hj))
    rw [sum_insert ha, sum_insert ha, ha'.star_add_mul_add, ih (h.mono (by simp))]

lemma Set.Pairwise.sum_mul_star_sum_of_isStarOrtho {ι : Type*} {s : Finset ι} {f : ι → R}
    (h : (s : Set ι).Pairwise ((· ⋆⟂ ·) on f)) :
    (∑ i ∈ s, f i) * star (∑ i ∈ s, f i) = ∑ i ∈ s, f i * star (f i) := by
  simpa using h.imp (fun _ _ ↦ IsStarOrtho.star) |>.star_sum_mul_sum_of_isStarOrtho

protected lemma IsSelfAdjoint.isStarOrtho_iff (hq : IsSelfAdjoint q) :
    p ⋆⟂ q ↔ p * q = 0 ∧ q * p = 0 := by
  rw [isStarOrtho_iff, hq.star_eq]

protected lemma IsSelfAdjoint.isStarOrtho_iff' (hp : IsSelfAdjoint p) :
    p ⋆⟂ q ↔ p * q = 0 ∧ q * p = 0 := by
  rw [isStarOrtho_comm, hp.isStarOrtho_iff, and_comm]

/-- Selfadjoint elements are star-orthogonal if and only if their product is zero. -/
@[grind =]
lemma isStarOrtho_iff_mul_eq_zero (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q) :
    p ⋆⟂ q ↔ p * q = 0 := by
  rw [hq.isStarOrtho_iff, and_iff_left_iff_imp]
  intro h
  simpa [hp.star_eq, hq.star_eq] using congr(star $h)

lemma IsStarOrtho.mul_eq_zero (h : p ⋆⟂ q) (hq : IsSelfAdjoint q) : p * q = 0 :=
  hq.isStarOrtho_iff.mp h |>.left

lemma IsStarOrtho.mul_eq_zero' (h : p ⋆⟂ q) (hq : IsSelfAdjoint q) : q * p = 0 :=
  hq.isStarOrtho_iff.mp h |>.right

/-- The sum of star-orthogonal star projections is a star projection. -/
lemma IsStarOrtho.isStarProjection_add (h : p ⋆⟂ q) (hp : IsStarProjection p)
    (hq : IsStarProjection q) : IsStarProjection (p + q) :=
  hp.add hq <| h.mul_eq_zero hq.isSelfAdjoint

/-- The sum of star projections is a star projection if and only if they are star-orthogonal. -/
lemma IsStarProjection.add_iff_isStarOrtho [IsCancelAdd R] [HasUniqueDiv R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (p + q) ↔ p ⋆⟂ q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.isStarProjection_add hp hq⟩
  have := hp.isIdempotentElem.add_iff hq.isIdempotentElem |>.mp h.isIdempotentElem
  grind [IsIdempotentElem.mul_eq_zero_of_anticommute]

/-- A finite sum of pairwise star-orthogonal star projections is a star projection.
The converse holds in a star-ordered ring with proper star. See `isStarProjection_sum_iff`.
The converse is not an immediate corollary of `IsStarProjection.add_iff_isStarOrtho` because we are
not assuming the intermediate sums (i.e., over a subset of `s`) are star projections. -/
lemma isStarProjection_sum {ι : Type*} {s : Finset ι} {f : ι → R}
    (hf : ∀ i ∈ s, IsStarProjection (f i)) (h : (s : Set ι).Pairwise ((· ⋆⟂ ·) on f)) :
    IsStarProjection (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine IsStarOrtho.isStarProjection_add ?_ (hf a (by simp)) ?_
    · exact .sum_right fun j hj ↦ h (by simp) (by simp [hj]) (fun h' ↦ ha (h' ▸ hj))
    · exact ih (fun i hi ↦ hf i (by simp [hi])) <| h.mono <| by simp

end NonUnitalSemiring

section NonUnitalRing

variable {R : Type*} [NonUnitalRing R] [StarRing R] {p q : R}

namespace IsStarOrtho

@[simp]
lemma neg_left_iff : (-p) ⋆⟂ q ↔ p ⋆⟂ q := by
  simp [isStarOrtho_iff]

@[simp]
lemma neg_right_iff : p ⋆⟂ (-q) ↔ p ⋆⟂ q := by
  simp [isStarOrtho_iff]

alias ⟨of_neg_left, neg_left⟩ := neg_left_iff
alias ⟨of_neg_right, neg_right⟩ := neg_right_iff

lemma sub_left {p₁ p₂ : R} (h₁ : p₁ ⋆⟂ q) (h₂ : p₂ ⋆⟂ q) : (p₁ - p₂) ⋆⟂ q := by
  simpa [sub_eq_add_neg] using h₁.add_left h₂.neg_left

lemma sub_right {q₁ q₂ : R} (h₁ : p ⋆⟂ q₁) (h₂ : p ⋆⟂ q₂) : p ⋆⟂ (q₁ - q₂) :=
  (h₁.symm.sub_left h₂.symm).symm

end IsStarOrtho

end NonUnitalRing

section Semiring

variable {R : Type*} [Semiring R] [StarRing R] {p q : R}

@[simp]
lemma isStarOrtho_one_left : 1 ⋆⟂ q ↔ q = 0 := by
  simp [isStarOrtho_iff]

@[simp]
lemma isStarOrtho_one_right : p ⋆⟂ 1 ↔ p = 0 := by
  simp [isStarOrtho_iff]

namespace IsStarOrtho

-- TODO: add `PNat` version
lemma pow_left (h : p ⋆⟂ q) {n : ℕ} (hn : n ≠ 0) : p ^ n ⋆⟂ q := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact ⟨by rw [pow_succ, mul_assoc, h.mul_star_eq_zero, mul_zero],
    by rw [pow_succ', ← mul_assoc, h.star_mul_eq_zero, zero_mul]⟩

-- TODO: add `PNat` version
lemma pow_right (h : p ⋆⟂ q) {n : ℕ} (hn : n ≠ 0) : p ⋆⟂ q ^ n :=
  (h.symm.pow_left hn).symm

lemma pow_pow (h : p ⋆⟂ q) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : p ^ m ⋆⟂ q ^ n :=
  (h.pow_left hm).pow_right hn

end IsStarOrtho

end Semiring

section Ring

variable {R : Type*} [Ring R] [StarRing R] {p : R}

lemma IsStarProjection.isStarOrtho_one_sub (hp : IsStarProjection p) : p ⋆⟂ (1 - p) :=
  (isStarOrtho_iff_mul_eq_zero hp.isSelfAdjoint hp.one_sub.isSelfAdjoint).mpr
    hp.mul_one_sub_self

lemma IsStarProjection.one_sub_isStarOrtho (hp : IsStarProjection p) : (1 - p) ⋆⟂ p :=
  hp.isStarOrtho_one_sub.symm

end Ring

section IsProperStar

variable {R : Type*} [NonUnitalSemiring R] [StarRing R] [IsProperStar R]

@[simp]
lemma isStarOrtho_self_iff (p : R) : p ⋆⟂ p ↔ p = 0 := by
  simp [isStarOrtho_iff]

/-- If `a` is normal and `a ⋆⟂ b`, then `star a ⋆⟂ b`. -/
lemma IsStarOrtho.star_left_of_isStarNormal {a b : R} (h : a ⋆⟂ b) (ha : IsStarNormal a) :
    star a ⋆⟂ b where
  mul_star_eq_zero := by
    rw [← star_mul_self_eq_zero]
    simp only [star_mul, star_star, mul_assoc]
    rw [← mul_assoc a, ← ha.star_comm_self.eq, mul_assoc, h.mul_star_eq_zero, mul_zero, mul_zero]
  star_mul_eq_zero := by
    rw [← mul_star_self_eq_zero]
    simp only [star_mul, star_star, ← mul_assoc]
    rw [mul_assoc _ (star a), ha.star_comm_self.eq, ← mul_assoc, h.star_mul_eq_zero, zero_mul,
      zero_mul]

section IsStarNormal

variable {a b : R}

/-- If `a` is normal, then `star a ⋆⟂ b ↔ a ⋆⟂ b`. -/
lemma IsStarNormal.isStarOrtho_star_left_iff (ha : IsStarNormal a) :
    star a ⋆⟂ b ↔ a ⋆⟂ b where
  mp h := star_star a ▸ h.star_left_of_isStarNormal ha.star
  mpr h := h.star_left_of_isStarNormal ha

/-- If `a` is normal, then `a ⋆⟂ star b ↔ a ⋆⟂ b`. -/
lemma IsStarNormal.isStarOrtho_star_right_iff (ha : IsStarNormal a) :
    a ⋆⟂ star b ↔ a ⋆⟂ b := by
  rw [← IsStarOrtho.star_iff, star_star, ha.isStarOrtho_star_left_iff]

/-- If `a` is normal and commutes with `b`, then `a ⋆⟂ b` if and only if `a * b = 0`. -/
lemma IsStarNormal.isStarOrtho_iff_mul_eq_zero (ha : IsStarNormal a) (hab : Commute a b) :
    a ⋆⟂ b ↔ a * b = 0 := by
  refine ⟨fun h ↦ by simpa using (ha.isStarOrtho_star_right_iff.mpr h).mul_star_eq_zero,
    fun h ↦ ⟨?_, ?_⟩⟩
  · rw [← star_mul_self_eq_zero]
    simp only [star_mul, star_star, mul_assoc]
    rw [← mul_assoc (star a) a, ha.star_comm_self.eq, ← mul_assoc, ← mul_assoc, ← hab.eq, h]
    simp
  · rw [← mul_star_self_eq_zero]
    simp only [star_mul, star_star, mul_assoc]
    rw [← mul_assoc a (star a), ← ha.star_comm_self.eq, mul_assoc (star a), h]
    simp

end IsStarNormal

end IsProperStar

section Comm

variable {R : Type*} [NonUnitalCommSemiring R] [StarRing R] [IsProperStar R] {a b : R}

/-- When the ring is commutative, `star a ⋆⟂ b ↔ a ⋆⟂ b`. -/
lemma isStarOrtho_star_left_iff : star a ⋆⟂ b ↔ a ⋆⟂ b :=
  (IsStarNormal.all a).isStarOrtho_star_left_iff

alias ⟨_, IsStarOrtho.star_left⟩ := isStarOrtho_star_left_iff

/-- When the ring is commutative, `a ⋆⟂ star b ↔ a ⋆⟂ b`. -/
lemma isStarOrtho_star_right_iff : a ⋆⟂ star b ↔ a ⋆⟂ b :=
  (IsStarNormal.all a).isStarOrtho_star_right_iff

alias ⟨_, IsStarOrtho.star_right⟩ := isStarOrtho_star_right_iff

/-- When the ring is commutative, `a ⋆⟂ b` if and only if `a * b = 0`. -/
lemma isStarOrtho_iff_mul_eq_zero_of_comm : a ⋆⟂ b ↔ a * b = 0 :=
  (IsStarNormal.all a).isStarOrtho_iff_mul_eq_zero (.all a b)

end Comm
