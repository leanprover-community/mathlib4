/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Data.SetLike.Basic

#align_import algebra.star.basic from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-!
# Star monoids, rings, and modules

We introduce the basic algebraic notions of star monoids, star rings, and star modules.
A star algebra is simply a star ring that is also a star module.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type*) [Ring R] [StarRing R]`.
This avoids difficulties with diamond inheritance.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star non-unital, non-associative, semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.

## Main declarations

* `Star`: an algebraic structure with a star operation.
* `StarMemClass`: a type of subsets closed under star.
* `InvolutiveStar`: an involutive star operation.
* `TrivialStar`: a trivial star operation.
* `StarMul`: `star` skew-distributes over multiplication.
* `StarHomClass` a type of `star`-preserving maps.
-/

assert_not_exists Finset
assert_not_exists Subgroup
assert_not_exists Rat.instField

universe u v w

/-- Notation typeclass (with no default notation!) for an algebraic structure with a star operation.
-/
class Star (R : Type u) where
  star : R → R
#align has_star Star

-- https://github.com/leanprover/lean4/issues/2096
compile_def% Star.star

variable {R : Type u}

export Star (star)

/-- A star operation (e.g. complex conjugate).
-/
add_decl_doc star

/-- `StarMemClass S G` states `S` is a type of subsets `s ⊆ G` closed under star. -/
class StarMemClass (S R : Type*) [Star R] [SetLike S R] : Prop where
  /-- Closure under star. -/
  star_mem : ∀ {s : S} {r : R}, r ∈ s → star r ∈ s
#align star_mem_class StarMemClass

export StarMemClass (star_mem)

attribute [aesop safe apply (rule_sets := [SetLike])] star_mem

namespace StarMemClass

variable {S : Type w} [Star R] [SetLike S R] [hS : StarMemClass S R] (s : S)

instance instStar : Star s where
  star r := ⟨star (r : R), star_mem r.prop⟩

@[simp] lemma coe_star (x : s) : star x = star (x : R) := rfl

end StarMemClass

/-- Typeclass for a star operation which is involutive.
-/
class InvolutiveStar (R : Type u) extends Star R where
  /-- Involutive condition. -/
  star_involutive : Function.Involutive star
#align has_involutive_star InvolutiveStar

export InvolutiveStar (star_involutive)

@[simp]
theorem star_star [InvolutiveStar R] (r : R) : star (star r) = r :=
  star_involutive _
#align star_star star_star

theorem star_injective [InvolutiveStar R] : Function.Injective (star : R → R) :=
  Function.Involutive.injective star_involutive
#align star_injective star_injective

@[simp]
theorem star_inj [InvolutiveStar R] {x y : R} : star x = star y ↔ x = y :=
  star_injective.eq_iff
#align star_inj star_inj

/-- `star` as an equivalence when it is involutive. -/
protected def Equiv.star [InvolutiveStar R] : Equiv.Perm R :=
  star_involutive.toPerm _
#align equiv.star Equiv.star

theorem eq_star_of_eq_star [InvolutiveStar R] {r s : R} (h : r = star s) : s = star r := by
  simp [h]
#align eq_star_of_eq_star eq_star_of_eq_star

theorem eq_star_iff_eq_star [InvolutiveStar R] {r s : R} : r = star s ↔ s = star r :=
  ⟨eq_star_of_eq_star, eq_star_of_eq_star⟩
#align eq_star_iff_eq_star eq_star_iff_eq_star

theorem star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : star r = s ↔ star s = r :=
  eq_comm.trans <| eq_star_iff_eq_star.trans eq_comm
#align star_eq_iff_star_eq star_eq_iff_star_eq

/-- Typeclass for a trivial star operation. This is mostly meant for `ℝ`.
-/
class TrivialStar (R : Type u) [Star R] : Prop where
  /-- Condition that star is trivial-/
  star_trivial : ∀ r : R, star r = r
#align has_trivial_star TrivialStar

export TrivialStar (star_trivial)

attribute [simp] star_trivial

/-- A `*`-magma is a magma `R` with an involutive operation `star`
such that `star (r * s) = star s * star r`.
-/
class StarMul (R : Type u) [Mul R] extends InvolutiveStar R where
  /-- `star` skew-distributes over multiplication. -/
  star_mul : ∀ r s : R, star (r * s) = star s * star r
#align star_semigroup StarMul

export StarMul (star_mul)

attribute [simp 900] star_mul

section StarMul

/-- Any commutative magma admits the trivial `*`-structure. -/
abbrev starMulOfMulComm {R : Type*} [Mul R] (mul_comm : ∀ r s : R, r * s = s * r) : StarMul R where
  star := id
  star_involutive _ := rfl
  star_mul := mul_comm

instance Nat.instStarMul : StarMul ℕ := starMulOfMulComm Nat.mul_comm
instance Nat.instTrivialStar : TrivialStar ℕ := ⟨fun _ ↦ rfl⟩

instance Int.instStarMul : StarMul ℤ := starMulOfMulComm Int.mul_comm
instance Int.instTrivialStar : TrivialStar ℤ := ⟨fun _ ↦ rfl⟩

variable [Mul R] [StarMul R]

theorem star_star_mul (x y : R) : star (star x * y) = star y * x := by rw [star_mul, star_star]
#align star_star_mul star_star_mul

theorem star_mul_star (x y : R) : star (x * star y) = y * star x := by rw [star_mul, star_star]
#align star_mul_star star_mul_star

end StarMul

section

/-- `StarHomClass F R S` states that `F` is a type of `star`-preserving maps from `R` to `S`. -/
class StarHomClass (F : Type*) (R S : outParam Type*) [Star R] [Star S] [FunLike F R S] : Prop where
  /-- the maps preserve star -/
  map_star : ∀ (f : F) (r : R), f (star r) = star (f r)
#align star_hom_class StarHomClass

export StarHomClass (map_star)

end
