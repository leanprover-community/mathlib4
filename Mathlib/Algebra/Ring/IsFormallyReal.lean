/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Ring.SumsOfSquares

/-!
# Formally real rings

A ring `R` is *formally real* if, whenever `∑ i, x i ^ 2 = 0`, in fact `x i = 0` for all `i`.

We define formally real rings in an index-free manner using the inductive predicate
`IsSumNonzeroSq`, which asserts that an element is a finite sum of squares of nonzero elements.
A ring is then formally real if `¬ IsSumNonzeroSq 0`.

## Main declaration

- `IsFormallyReal`: typeclass stating that a ring is formally real.

-/

@[expose] public section

variable {R : Type*}

section IsSumNonzeroSq

/--
The property of being a sum of positive squares is defined inductively by:
`a * a : R` is a sum of nonzero squares for all nonzero `a`, and
if `s : R` is a sum of positive squares, and `a ≠ 0`, then `a * a + s` is a sum of positive squares.
-/
@[mk_iff]
inductive IsSumNonzeroSq [Mul R] [Add R] [Zero R] : R → Prop
  | sq {a : R} (ha : a ≠ 0) : IsSumNonzeroSq (a * a)
  | sq_add {a s : R} (ha : a ≠ 0) (hs : IsSumNonzeroSq s) : IsSumNonzeroSq (a * a + s)

theorem IsSumNonzeroSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R}
    (h₁ : IsSumNonzeroSq s₁) (h₂ : IsSumNonzeroSq s₂) : IsSumNonzeroSq (s₁ + s₂) := by
  induction h₁ <;> simp_all [sq_add, add_assoc]

theorem IsSumSq.isSumNonzeroSq [AddMonoid R] [Mul R] {s : R} (h : IsSumNonzeroSq s) : IsSumSq s := by
  induction h <;> aesop

theorem isSumNonzeroSq_iff_isSumSq [NonUnitalNonAssocSemiring R] {s : R} (hs : s ≠ 0) :
    IsSumNonzeroSq s ↔ IsSumSq s where
  mp := IsSumSq.isSumNonzeroSq
  mpr h := by
    induction h with
    | zero => grind
    | @sq_add a s hs ih =>
    rcases eq_or_ne a 0 with (rfl | ne_a)
    · simp_all
    · rcases eq_or_ne s 0 with (rfl | ne_s)
      · simpa using IsSumNonzeroSq.sq ne_a
      · exact IsSumNonzeroSq.sq_add ne_a (ih ne_s)

alias ⟨_, IsSumSq.isSumNonzeroSq_of_ne_zero⟩ := isSumNonzeroSq_iff_isSumSq

end IsSumNonzeroSq

variable (R)

/--
A ring is formally real if, whenever `∑ i, x i ^ 2 = 0`, we in fact have `x i = 0` for all `i`.
-/
class IsFormallyReal [AddCommMonoid R] [Mul R] : Prop where
  not_isSumNonzeroSq_zero : ¬ IsSumNonzeroSq (0 : R)

namespace IsFormallyReal

theorem of_eq_zero_of_mul_self_of_eq_zero_of_add [AddCommMonoid R] [Mul R]
    (hz : ∀ {a : R}, a * a = 0 → a = 0)
    (ha : ∀ {s₁ s₂ : R}, IsSumSq s₁ → IsSumSq s₂ → s₁ + s₂ = 0 → s₁ = 0) : IsFormallyReal R where
  not_isSumNonzeroSq_zero := by
    suffices ∀ (x : R), IsSumNonzeroSq x → x ≠ 0 by grind
    intro x hx
    induction hx with
    | sq ha => grind
    | @sq_add b s hb hs ih => grind [ha (IsSumSq.mul_self b) (IsSumSq.isSumNonzeroSq hs)]

theorem of_eq_zero_of_eq_zero_of_mul_self_add [NonUnitalNonAssocSemiring R]
    (h : ∀ {s a : R}, IsSumSq s → a * a + s = 0 → a = 0) : IsFormallyReal R where
  not_isSumNonzeroSq_zero := by
    suffices ∀ (x : R), IsSumNonzeroSq x → x ≠ 0 by grind
    intro x hx
    induction hx with
    | sq ha => exact fun hc ↦ ha (h IsSumSq.zero (by simpa using hc))
    | sq_add ha hs ih => grind [IsSumSq.isSumNonzeroSq hs]

instance [Ring R] [LinearOrder R] [IsStrictOrderedRing R] : IsFormallyReal R :=
  of_eq_zero_of_mul_self_of_eq_zero_of_add R mul_self_eq_zero.mp <|
    fun hs₁ hs₂ h ↦ ((add_eq_zero_iff_of_nonneg (IsSumSq.nonneg hs₁) (IsSumSq.nonneg hs₂)).mp h).1

variable {R}

theorem mul_self_eq_zero_iff [AddCommMonoid R] [Mul R] [IsFormallyReal R] {a : R} :
    a * a = 0 ↔ a = 0 where
  mp := by simp
  by_contra! hc
  exact IsFormallyReal.not_isSumNonzeroSq_zero (ha.symm ▸ IsSumNonzeroSq.sq hc)

theorem eq_zero_of_mul_self [AddCommMonoid R] [Mul R] [IsFormallyReal R] {a : R} (ha : a * a = 0) :
    a = 0 := by
  by_contra! hc
  exact IsFormallyReal.not_isSumNonzeroSq_zero (ha.symm ▸ IsSumNonzeroSq.sq hc)

theorem eq_zero_of_add_right [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
    {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₁ = 0 := by
  by_contra! h₁
  have h₂ : s₂ ≠ 0 := fun hc ↦ by simp_all
  rw [← isSumNonzeroSq_iff_isSumSq h₁] at hs₁
  rw [← isSumNonzeroSq_iff_isSumSq h₂] at hs₂
  exact IsFormallyReal.not_isSumNonzeroSq_zero (h ▸ IsSumNonzeroSq.add hs₁ hs₂)

theorem eq_zero_of_add_left [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
    {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₂ = 0 := by
  simp_all [eq_zero_of_add_right hs₁ hs₂ h]

theorem eq_zero_of_isSumSq_of_neg_isSumSq [NonUnitalNonAssocRing R] [IsFormallyReal R]
    {s : R} (h₁ : IsSumSq s) (h₂ : IsSumSq (-s)) : s = 0 :=
  IsFormallyReal.eq_zero_of_add_right h₁ h₂ (by simp)

end IsFormallyReal
