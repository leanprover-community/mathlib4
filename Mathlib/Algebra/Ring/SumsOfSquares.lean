/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Ring.Parity -- Algebra.Group.Even doesn't see `IsSumSq 0` as a simp rule
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Tactic.ApplyFun

/-!
# Sums of squares

We introduce a predicate for sums of squares in a ring.

## Main declarations

- `IsSumSq : R → Prop`: for a type `R` with addition, multiplication and a zero,
  an inductive predicate defining the property of being a sum of squares in `R`.
  `0 : R` is a sum of squares and if `S` is a sum of squares, then, for all `a : R`,
  `a * a + s` is a sum of squares.
- `AddMonoid.sumSq R` and `Subsemiring.sumSq R`: respectively
  the submonoid or subsemiring of sums of squares in an additive monoid or semiring `R`

-/

variable {R : Type*}

/--
The property of being a sum of squares is defined inductively by:
`0 : R` is a sum of squares and if `s : R` is a sum of squares,
then for all `a : R`, `a * a + s` is a sum of squares in `R`.
-/
@[mk_iff]
inductive IsSumSq [Mul R] [Add R] [Zero R] : R → Prop
  | zero                                    : IsSumSq 0
  | sq_add (a : R) {s : R} (hs : IsSumSq s) : IsSumSq (a * a + s)

@[deprecated (since := "2024-08-09")] alias isSumSq := IsSumSq

/-- Alternative induction scheme for `IsSumSq` which uses `IsSquare`. -/
theorem IsSumSq.rec' [Mul R] [Add R] [Zero R]
    {motive : (s : R) → (h : IsSumSq s) → Prop}
    (zero : motive 0 zero)
    (sq_add : ∀ {x s}, (hx : IsSquare x) → (hs : IsSumSq s) → motive s hs →
      motive (x + s) (by rcases hx with ⟨_, rfl⟩; exact sq_add _ hs))
    {s : R} (h : IsSumSq s) : motive s h :=
  match h with
  | .zero        => zero
  | .sq_add _ hs => sq_add (.mul_self _) hs (rec' zero sq_add _)

/--
In an additive monoid with multiplication,
if `s₁` and `s₂` are sums of squares, then `s₁ + s₂` is a sum of squares.
-/
@[aesop unsafe 90% apply]
theorem IsSumSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R}
    (h₁ : IsSumSq s₁) (h₂ : IsSumSq s₂) : IsSumSq (s₁ + s₂) := by
  induction h₁ <;> simp_all [add_assoc, sq_add]

@[deprecated (since := "2024-08-09")] alias isSumSq.add := IsSumSq.add

namespace AddSubmonoid
variable {T : Type*} [AddMonoid T] [Mul T] {s : T}

variable (T) in
/--
In an additive monoid with multiplication `R`, `AddSubmonoid.sumSq R` is the submonoid of sums of
squares in `R`.
-/
@[simps]
def sumSq [AddMonoid T] : AddSubmonoid T where
  carrier   := {s : T | IsSumSq s}
  zero_mem' := .zero
  add_mem'  := .add

attribute [norm_cast] coe_sumSq

@[simp] theorem mem_sumSq : s ∈ sumSq T ↔ IsSumSq s := Iff.rfl

end AddSubmonoid

@[deprecated (since := "2024-08-09")] alias SumSqIn := AddSubmonoid.sumSq
@[deprecated (since := "2025-01-06")] alias sumSq := AddSubmonoid.sumSq

/-- In an additive unital magma with multiplication, `x * x` is a sum of squares for all `x`. -/
@[simp] theorem IsSumSq.mul_self [AddZeroClass R] [Mul R] (a : R) : IsSumSq (a * a) := by
  simpa using sq_add a zero

/--
In an additive unital magma with multiplication, squares are sums of squares
(see Mathlib.Algebra.Group.Even).
-/
@[aesop unsafe 80% apply]
theorem IsSquare.isSumSq [AddZeroClass R] [Mul R] {x : R} (hx : IsSquare x) : IsSumSq x := by aesop

/--
In an additive monoid with multiplication `R`, the submonoid generated by the squares is the set of
sums of squares in `R`.
-/
@[simp]
theorem AddSubmonoid.closure_isSquare [AddMonoid R] [Mul R] :
    closure {x : R | IsSquare x} = sumSq R := by
  refine closure_eq_of_le (fun x hx ↦ IsSquare.isSumSq hx) (fun x hx ↦ ?_)
  induction hx <;> aesop

@[deprecated (since := "2024-08-09")] alias SquaresAddClosure := AddSubmonoid.closure_isSquare

/--
In an additive commutative monoid with multiplication, a finite sum of sums of squares
is a sum of squares.
-/
@[aesop unsafe 90% apply]
theorem IsSumSq.sum [AddCommMonoid R] [Mul R] {ι : Type*} {I : Finset ι} {s : ι → R}
    (hs : ∀ i ∈ I, IsSumSq <| s i) : IsSumSq (∑ i ∈ I, s i) := by
  simpa using sum_mem (S := AddSubmonoid.sumSq _) hs

/--
In an additive commutative monoid with multiplication,
`∑ i ∈ I, x i`, where each `x i` is a square, is a sum of squares.
-/
theorem IsSumSq.sum_isSquare [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) {x : ι → R}
    (hx : ∀ i ∈ I, IsSquare <| x i) : IsSumSq (∑ i ∈ I, x i) := by aesop

/--
In an additive commutative monoid with multiplication,
`∑ i ∈ I, a i * a i` is a sum of squares.
-/
@[simp]
theorem IsSumSq.sum_mul_self [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) (a : ι → R) :
    IsSumSq (∑ i ∈ I, a i * a i) := by aesop

@[deprecated (since := "2024-12-27")] alias isSumSq_sum_mul_self := IsSumSq.sum_mul_self

namespace NonUnitalSubsemiring
variable {T : Type*} [NonUnitalCommSemiring T]

variable (T) in
/--
In a commutative (possibly non-unital) semiring `R`, `NonUnitalSubsemiring.sumSq R` is
the (possibly non-unital) subsemiring of sums of squares in `R`.
-/
def sumSq : NonUnitalSubsemiring T := (Subsemigroup.square T).nonUnitalSubsemiringClosure

@[simp] theorem sumSq_toAddSubmonoid : (sumSq T).toAddSubmonoid = .sumSq T := by
  simp [sumSq, ← AddSubmonoid.closure_isSquare,
    Subsemigroup.nonUnitalSubsemiringClosure_toAddSubmonoid]

@[simp]
theorem mem_sumSq {s : T} : s ∈ sumSq T ↔ IsSumSq s := by
  simp [← NonUnitalSubsemiring.mem_toAddSubmonoid]

@[simp, norm_cast] theorem coe_sumSq : sumSq T = {s : T | IsSumSq s} := by ext; simp

@[simp] theorem closure_isSquare : closure {x : T | IsSquare x} = sumSq T := by
  simp [sumSq, Subsemigroup.nonUnitalSubsemiringClosure_eq_closure]

end NonUnitalSubsemiring

/--
In a commutative (possibly non-unital) semiring,
if `s₁` and `s₂` are sums of squares, then `s₁ * s₂` is a sum of squares.
-/
@[aesop unsafe 90% apply]
theorem IsSumSq.mul [NonUnitalCommSemiring R] {s₁ s₂ : R}
    (h₁ : IsSumSq s₁) (h₂ : IsSumSq s₂) : IsSumSq (s₁ * s₂) := by
  simpa using mul_mem (by simpa : _ ∈ NonUnitalSubsemiring.sumSq R) (by simpa)

private theorem Submonoid.square_subsemiringClosure {T : Type*} [CommSemiring T] :
    (Submonoid.square T).subsemiringClosure = .closure {x : T | IsSquare x} := by
  simp [Submonoid.subsemiringClosure_eq_closure]

namespace Subsemiring
variable {T : Type*} [CommSemiring T]

variable (T) in
/--
In a commutative semiring `R`, `Subsemiring.sumSq R` is the subsemiring of sums of squares in `R`.
-/
def sumSq : Subsemiring T where
  __ := NonUnitalSubsemiring.sumSq T
  one_mem' := by aesop

@[simp] theorem sumSq_toNonUnitalSubsemiring :
    (sumSq T).toNonUnitalSubsemiring = .sumSq T := rfl

@[simp]
theorem mem_sumSq {s : T} : s ∈ sumSq T ↔ IsSumSq s := by
  simp [← Subsemiring.mem_toNonUnitalSubsemiring]

@[simp, norm_cast] theorem coe_sumSq : sumSq T = {s : T | IsSumSq s} := by ext; simp

@[simp] theorem closure_isSquare : closure {x : T | IsSquare x} = sumSq T := by
  apply_fun toNonUnitalSubsemiring using toNonUnitalSubsemiring_injective
  simp [← Submonoid.square_subsemiringClosure]

end Subsemiring

/-- In a commutative semiring, a finite product of sums of squares is a sum of squares. -/
@[aesop unsafe 50% apply]
theorem IsSumSq.prod [CommSemiring R] {ι : Type*} {I : Finset ι} {x : ι → R}
    (hx : ∀ i ∈ I, IsSumSq <| x i) : IsSumSq (∏ i ∈ I, x i) := by
  simpa using prod_mem (S := Subsemiring.sumSq R) (by simpa)

/--
In a linearly ordered semiring with the property `a ≤ b → ∃ c, a + c = b` (e.g. `ℕ`),
sums of squares are non-negative.
-/
theorem IsSumSq.nonneg {R : Type*} [LinearOrderedSemiring R] [ExistsAddOfLE R] {s : R}
    (hs : IsSumSq s) : 0 ≤ s := by
  induction hs using IsSumSq.rec' with
  | zero          => simp
  | sq_add hx _ h => exact add_nonneg (IsSquare.nonneg hx) h

@[deprecated (since := "2024-08-09")] alias isSumSq.nonneg := IsSumSq.nonneg
