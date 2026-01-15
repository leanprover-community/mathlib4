/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Ring.SumsOfSquares

/-!
# Formally real rings

A ring `R` is *formally real* if, whenever `∑ i, x i ^ 2 = 0`,
we in fact have `x i = 0` for all `i`.

## Main declaration

- `IsFormallyReal`: typeclass stating that a ring is formally real.

-/

@[expose] public section

variable (R : Type*)

/--
A ring is formally real if, whenever `∑ i, x i ^ 2 = 0`, we in fact have `x i = 0` for all `i`.
-/
class IsFormallyReal [AddCommMonoid R] [Mul R] : Prop where
  eq_zero_of_sum_eq_zero : ∀ {s : Multiset R}, (s.map (fun a ↦ a * a)).sum = 0 → ∀ a ∈ s, a = 0

namespace IsFormallyReal

theorem of_eq_zero_of_mul_self_of_eq_zero_of_add [AddCommMonoid R] [Mul R]
    (hz : ∀ {a : R}, a * a = 0 → a = 0)
    (ha : ∀ {s₁ s₂ : R}, IsSumSq s₁ → IsSumSq s₂ → s₁ + s₂ = 0 → s₁ = 0) : IsFormallyReal R where
  eq_zero_of_sum_eq_zero {s} := by
    induction s using Multiset.induction with
    | empty => simp
    | cons a m hm =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.mem_cons, forall_eq_or_imp]
        intro h
        have := ha (by simp) (by rw [isSumSq_iff_exists_sum_mul_self_eq]; simp) h
        exact ⟨hz this, hm (by simpa [this] using h)⟩

theorem of_eq_zero_of_eq_zero_of_mul_self_add [NonUnitalNonAssocSemiring R]
    (h : ∀ {s a : R}, IsSumSq s → a * a + s = 0 → a = 0) : IsFormallyReal R where
  eq_zero_of_sum_eq_zero {s} := by
    induction s using Multiset.induction with
    | empty => simp
    | cons a m hm =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.mem_cons, forall_eq_or_imp]
        intro has
        have := h (by rw [isSumSq_iff_exists_sum_mul_self_eq]; simp) has
        exact ⟨this, hm (by simpa [this] using has)⟩

/-- A linearly ordered ring is formally real. -/
instance [Ring R] [LinearOrder R] [IsStrictOrderedRing R] : IsFormallyReal R :=
  of_eq_zero_of_mul_self_of_eq_zero_of_add R mul_self_eq_zero.mp <|
    fun hs₁ hs₂ h ↦ ((add_eq_zero_iff_of_nonneg (IsSumSq.nonneg hs₁) (IsSumSq.nonneg hs₂)).mp h).1

variable {R}

theorem eq_zero_of_mul_self [AddCommMonoid R] [Mul R] [IsFormallyReal R] {a : R} :
  a * a = 0 → a = 0 := by simpa using IsFormallyReal.eq_zero_of_sum_eq_zero (s := {a})

theorem eq_zero_of_add_right [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
    {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₁ = 0 := by
  simp_rw [isSumSq_iff_exists_sum_mul_self_eq] at *
  rcases hs₁ with ⟨m₁, rfl⟩
  rcases hs₂ with ⟨m₂, rfl⟩
  rw [← Multiset.sum_add, ← Multiset.map_add] at h
  exact Multiset.sum_eq_zero <|by
    simpa using fun _ _ ↦ by simp [eq_zero_of_sum_eq_zero h _ (by aesop)]

theorem eq_zero_of_add_left [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
    {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₂ = 0 := by
  simp_all [eq_zero_of_add_right hs₁ hs₂ h]

theorem eq_zero_of_isSumSq_of_neg_isSumSq [NonUnitalNonAssocRing R] [IsFormallyReal R]
    {s : R} (h₁ : IsSumSq s) (h₂ : IsSumSq (-s)) : s = 0 :=
  IsFormallyReal.eq_zero_of_add_right h₁ h₂ (by simp)

end IsFormallyReal
