/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Basic

/-!
# Sums of squares

We introduce sums of squares in a type `R` endowed with an `[Add R]`, `[Zero R]` and `[Mul R]`
instances. Sums of squares in `R` are defined by an inductive predicate `IsSumSq : R → Prop`:
`0 : R` is a sum of squares and if `S` is a sum of squares, then for all `a : R`, `a * a + S` is a
sum of squares in `R`.

## Declarations

- The predicate `IsSumSq : R → Prop`, defining the property of being a sum of squares in `R`.
- The terms `AddMonoid.sumSqIn R` and `Subsemiring.sumSqIn R` :
in an additive monoid with multiplication `R` and a semiring `R`, we introduce the terms
`AddMonoid.sumSqIn R` and `Subsemiring.sumSqIn R` as the submonoid and subsemiring, respectively,
of `R` whose carrier is the subset `{S : R | IsSumSq S}`.

-/

/- TODO : move to right place -/
namespace Subsemigroup
variable {S : Type*} [CommSemigroup S] {a : S}

variable (S) in
/--
In a commutative semigroup `S`, the type `Subsemigroup.sqIn S`
is the subsemigroup of squares in `S`.
-/
@[to_additive evenIn
"In a commutative additive semigroup `S`, the type `AddSubsemigroup.evenIn S`
is the subsemigroup of even elements of `S`."]
def squareIn : Subsemigroup S where
  carrier := {s : S | IsSquare s}
  mul_mem' := IsSquare.mul

@[to_additive (attr := simp)]
theorem mem_squareIn : a ∈ squareIn S ↔ IsSquare a := Iff.rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_squareIn : squareIn S = {s : S | IsSquare s} := rfl

end Subsemigroup

/- TODO : move to right place -/
namespace Submonoid
variable {M : Type*} [CommMonoid M] {a : M}

variable (M) in
/--
In a commutative monoid `M`, the type `Submonoid.sqIn M`
is the submonoid of squares in `M`.
-/
@[to_additive evenIn
"In a commutative additive monoid `M`, the type `AddSubmonoid.evenIn M`
is the submonoid of even elements of `M`."]
def squareIn : Submonoid M where
  carrier := {s : M | IsSquare s}
  one_mem' := IsSquare.one
  mul_mem' := IsSquare.mul

@[to_additive (attr := simp)]
theorem mem_squareIn : a ∈ squareIn M ↔ IsSquare a := Iff.rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_squareIn : squareIn M = {s : M | IsSquare s} := rfl

end Submonoid

/- TODO : move to right place -/
theorem IsSquare.nonneg {R : Type*} [Semiring R] [LinearOrder R] [IsRightCancelAdd R]
    [ZeroLEOneClass R] [ExistsAddOfLE R] [PosMulMono R] [AddLeftStrictMono R]
    {x : R} (h : IsSquare x) : 0 ≤ x := by
  rcases h with ⟨y, rfl⟩
  exact mul_self_nonneg y

universe u
variable {R : Type*}

/--
In a type `R` with an addition, a zero element and a multiplication, the property of being a sum of
squares is defined by an inductive predicate: `0 : R` is a sum of squares and if `S` is a sum of
squares, then for all `a : R`, `a * a + S` is a sum of squares in `R`.
-/
@[mk_iff]
inductive IsSumSq [Mul R] [Add R] [Zero R] : R → Prop
  | zero                              : IsSumSq 0
  | sq_add {a S : R} (hS : IsSumSq S) : IsSumSq (a * a + S)

@[deprecated (since := "2024-08-09")] alias isSumSq := IsSumSq

/-- Alternative induction scheme for `IsSumSq` using `IsSquare`. -/
theorem IsSumSq.rec' [Mul R] [Add R] [Zero R]
    {motive : (S : R) → (h : IsSumSq S) → Prop}
    (zero : motive 0 zero)
    (sq_add : ∀ {a S}, (ha : IsSquare a) → (hS : IsSumSq S) → motive S hS →
      motive (a + S) (by rcases ha with ⟨_, rfl⟩; exact sq_add hS))
    {S : R} (h : IsSumSq S) : motive S h :=
  match h with
  | .zero         => zero
  | .sq_add ih => sq_add (.mul_self _) ih (rec' zero sq_add _)

/-- In an additive monoid with multiplication,
if `S₁` and `S₂` are sums of squares, then `S₁ + S₂` is a sum of squares. -/
@[aesop unsafe 90% apply]
theorem IsSumSq.add [AddMonoid R] [Mul R] {S₁ S₂ : R}
    (h₁ : IsSumSq S₁) (h₂ : IsSumSq S₂) : IsSumSq (S₁ + S₂) := by
  induction h₁ with
  | zero        => simp_all
  | sq_add _ ih => simp_all [add_assoc, sq_add]

@[deprecated (since := "2024-08-09")] alias isSumSq.add := IsSumSq.add

namespace AddSubmonoid
variable {T : Type*} [AddMonoid T] [Mul T] {a : T}

variable (T) in
/--
In an additive monoid with multiplication `R`, the type `AddSubmonoid.sumSqIn R`
is the submonoid of sums of squares in `R`.
-/
def sumSqIn : AddSubmonoid T where
  carrier := {S : T | IsSumSq S}
  zero_mem' := IsSumSq.zero
  add_mem' := IsSumSq.add

@[simp] theorem mem_sumSqIn : a ∈ sumSqIn T ↔ IsSumSq a := Iff.rfl
@[simp, norm_cast] theorem coe_sumSqIn : sumSqIn T = {x : T | IsSumSq x} := rfl

end AddSubmonoid

/-- In an additive, commutative monoid with multiplication, a finite sum of sums of squares
is a sum of squares. -/
@[aesop unsafe 90% apply]
theorem IsSumSq.sum [AddCommMonoid R] [Mul R] {ι : Type*} {I : Finset ι} {S : ι → R}
    (hS : ∀ i ∈ I, IsSumSq <| S i) : IsSumSq (∑ i ∈ I, S i) := by
  simpa using sum_mem (S := AddSubmonoid.sumSqIn R) hS

/-- In an additive unital magma with multiplication, `x * x` is a sum of squares for all `x`. -/
theorem IsSumSq.mul_self [AddZeroClass R] [Mul R] (a : R) : IsSumSq (a * a) := by
  rw [← add_zero (a * a)]; exact sq_add zero

/-- In an additive unital magma with multiplication `R`, squares in `R` are sums of squares.
By definition, a square in `R` is a term `x : R` such that `x = y * y` for some `y : R`
and in Mathlib this is known as `IsSquare R` (see Mathlib.Algebra.Group.Even). -/
@[aesop unsafe 50% apply]
theorem IsSquare.isSumSq [AddZeroClass R] [Mul R] {x : R} (hx : IsSquare x) :
    IsSumSq x := by rcases hx with ⟨_, rfl⟩; apply IsSumSq.mul_self

/-- A term of the form `∑ i ∈ I, x i`, where each `x i` is a square, satisfies `IsSumSq`. -/
@[aesop safe apply]
theorem IsSumSq.sum_mul_self [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) (x : ι → R) :
    IsSumSq (∑ i ∈ I, x i * x i) := sum (by aesop)

@[deprecated (since := "2024-12-23")] alias isSumSq_sum_mul_self := IsSumSq.sum_mul_self

/--
In an additive monoid with multiplication `R`, the submonoid generated by the squares is the set of
sums of squares in `R`.
-/
@[simp]
theorem AddSubmonoid.closure_isSquare [AddMonoid R] [Mul R] :
    closure {x : R | IsSquare x} = sumSqIn R := by
  refine closure_eq_of_le (fun x hx ↦ IsSquare.isSumSq hx) (fun x hx ↦ ?_)
  induction hx with
  | zero         => exact zero_mem _
  | sq_add _ ih  => exact add_mem (subset_closure (.mul_self _)) ih

@[deprecated (since := "2024-08-09")] alias SquaresAddClosure := AddSubmonoid.closure_isSquare

/- TODO : remove? -/
theorem AddSubmonoid.closure_squareIn [AddMonoid R] [CommSemiring R] :
    (closure <| Submonoid.squareIn R) = sumSqIn R := by simp

private theorem IsSumSq.isSquare_mul [NonUnitalCommSemiring R] {x S : R}
    (hx : IsSquare x) (hS : IsSumSq S) : IsSumSq (x * S) := by
  induction hS using rec'
  case zero   => aesop
  case sq_add a S ha hS ih => rw [left_distrib]; aesop (add unsafe apply IsSquare.mul)

/- TODO : Do non unital version? -/
namespace Subsemiring
variable {T : Type*} [CommSemiring T] {a : T}

variable (T) in
/--
In a commutative semiring `R`, the type `Subsemiring.sumSqIn R`
is the subsemiring of sums of squares in `R`.
-/
def sumSqIn : Subsemiring T := (Submonoid.squareIn T).subsemiringClosure

@[simp] theorem sumSqIn_toAddSubmonoid : (sumSqIn T).toAddSubmonoid = .sumSqIn T := by
  rw [sumSqIn, ← AddSubmonoid.closure_isSquare, Submonoid.subsemiringClosure_toAddSubmonoid]
  simp

@[simp]
theorem mem_sumSqIn : a ∈ sumSqIn T ↔ IsSumSq a := by rw [← Subsemiring.mem_toAddSubmonoid]; simp

@[simp, norm_cast] theorem coe_sumSqIn : sumSqIn T = {x : T | IsSumSq x} := by ext; simp

@[simp] theorem closure_isSquare : closure {x : T | IsSquare x} = sumSqIn T := by
  rw [sumSqIn, Submonoid.subsemiringClosure_eq_closure]
  simp

end Subsemiring

/- TODO : Do non unital version? -/
/-- In a commutative semiring,
if `S₁` and `S₂` are sums of squares, then `S₁ * S₂` is a sum of squares. -/
@[aesop unsafe 50% apply]
theorem IsSumSq.mul [CommSemiring R] {s₁ s₂ : R}
    (h₁ : IsSumSq s₁) (h₂ : IsSumSq s₂) : IsSumSq (s₁ * s₂) := by
  simpa using mul_mem (by simpa : _ ∈ Subsemiring.sumSqIn R) (by simpa)

/-- In a commutative semiring, a finite product of sums of squares
is a sum of squares. -/
@[aesop unsafe 50% apply]
theorem IsSumSq.prod [CommSemiring R] {ι : Type*} {I : Finset ι} {f : ι → R}
    (hf : ∀ i ∈ I, IsSumSq <| f i) : IsSumSq (∏ i ∈ I, f i) := by
  simpa using prod_mem (S := Subsemiring.sumSqIn R) (by simpa)

/--
Let `R` be a linearly ordered semiring in which the property `a ≤ b → ∃ c, a + c = b` holds
(e.g. `R = ℕ`). If `S : R` is a sum of squares in `R`, then `0 ≤ S`. This is used in
`Mathlib.Algebra.Ring.Semireal.Defs` to show that such semirings are semireal.
-/
theorem IsSumSq.nonneg {R : Type*} [LinearOrderedSemiring R] [ExistsAddOfLE R] {S : R}
    (pS : IsSumSq S) : 0 ≤ S := by
  induction pS using IsSumSq.rec'
  case zero => aesop
  case sq_add a S ha hS h_sum => exact add_nonneg (IsSquare.nonneg ha) h_sum

@[deprecated (since := "2024-08-09")] alias isSumSq.nonneg := IsSumSq.nonneg
