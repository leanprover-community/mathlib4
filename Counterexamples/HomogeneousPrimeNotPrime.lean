/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser, Jujian Zhang

! This file was ported from Lean 3 source module homogeneous_prime_not_prime
! leanprover-community/mathlib commit 328375597f2c0dd00522d9c2e5a33b6a6128feeb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# A homogeneous prime that is homogeneously prime but not prime

In `src/ring_theory/graded_algebra/radical.lean`,  we assumed that the underline grading is indexed
by a `linear_ordered_cancel_add_comm_monoid` to prove that a homogeneous ideal is prime if and only
if it is homogeneously prime. This file is aimed to show that even if this assumption isn't strictly
necessary, the assumption of "being cancellative" is. We construct a counterexample where the
underlying indexing set is a `linear_ordered_add_comm_monoid` but is not cancellative and the
statement is false.

We achieve this by considering the ring `R=ℤ/4ℤ`. We first give the two element set `ι = {0, 1}` a
structure of linear ordered additive commutative monoid by setting `0 + 0 = 0` and `_ + _ = 1` and
`0 < 1`. Then we use `ι` to grade `R²` by setting `{(a, a) | a ∈ R}` to have grade `0`; and
`{(0, b) | b ∈ R}` to have grade 1. Then the ideal `I = span {(0, 2)} ⊆ ℤ/4ℤ` is homogeneous and not
prime. But it is homogeneously prime, i.e. if `(a, b), (c, d)` are two homogeneous elements then
`(a, b) * (c, d) ∈ I` implies either `(a, b) ∈ I` or `(c, d) ∈ I`.


## Tags

homogeneous, prime
-/


namespace Counterexample

namespace CounterexampleNotPrimeButHomogeneousPrime

open DirectSum

attribute [local reducible] WithZero

abbrev Two :=
  WithZero Unit
#align counterexample.counterexample_not_prime_but_homogeneous_prime.two Counterexample.CounterexampleNotPrimeButHomogeneousPrime.Two

instance : LinearOrderedAddCommMonoid Two :=
  { (_ : LinearOrder Two), (_ : AddCommMonoid Two) with
    add_le_add_left := by delta two WithZero <;> decide }

section

variable (R : Type _) [CommRing R]

/-- The grade 0 part of `R²` is `{(a, a) | a ∈ R}`. -/
def submoduleZ : Submodule R (R × R) where
  carrier := {zz | zz.1 = zz.2}
  zero_mem' := rfl
  add_mem' a b ha hb := congr_arg₂ (· + ·) ha hb
  smul_mem' a b hb := congr_arg ((· * ·) a) hb
#align counterexample.counterexample_not_prime_but_homogeneous_prime.submodule_z Counterexample.CounterexampleNotPrimeButHomogeneousPrime.submoduleZ

/-- The grade 1 part of `R²` is `{(0, b) | b ∈ R}`. -/
def submoduleO : Submodule R (R × R) :=
  (LinearMap.fst R R R).ker
#align counterexample.counterexample_not_prime_but_homogeneous_prime.submodule_o Counterexample.CounterexampleNotPrimeButHomogeneousPrime.submoduleO

/-- Given the above grading (see `submodule_z` and `submodule_o`),
  we turn `R²` into a graded ring. -/
def grading : Two → Submodule R (R × R)
  | 0 => submoduleZ R
  | 1 => submoduleO R
#align counterexample.counterexample_not_prime_but_homogeneous_prime.grading Counterexample.CounterexampleNotPrimeButHomogeneousPrime.grading

theorem grading.one_mem : (1 : R × R) ∈ grading R 0 :=
  Eq.refl (1, 1).fst
#align counterexample.counterexample_not_prime_but_homogeneous_prime.grading.one_mem Counterexample.CounterexampleNotPrimeButHomogeneousPrime.grading.one_mem

theorem grading.mul_mem :
    ∀ ⦃i j : Two⦄ {a b : R × R} (ha : a ∈ grading R i) (hb : b ∈ grading R j),
      a * b ∈ grading R (i + j)
  | 0, 0, a, b, (ha : a.1 = a.2), (hb : b.1 = b.2) => show a.1 * b.1 = a.2 * b.2 by rw [ha, hb]
  | 0, 1, a, b, (ha : a.1 = a.2), (hb : b.1 = 0) =>
    show a.1 * b.1 = 0 by rw [hb, MulZeroClass.mul_zero]
  | 1, 0, a, b, (ha : a.1 = 0), hb => show a.1 * b.1 = 0 by rw [ha, MulZeroClass.zero_mul]
  | 1, 1, a, b, (ha : a.1 = 0), hb => show a.1 * b.1 = 0 by rw [ha, MulZeroClass.zero_mul]
#align counterexample.counterexample_not_prime_but_homogeneous_prime.grading.mul_mem Counterexample.CounterexampleNotPrimeButHomogeneousPrime.grading.mul_mem

end

local notation "R" => ZMod 4

/-- `R² ≅ {(a, a) | a ∈ R} ⨁ {(0, b) | b ∈ R}` by `(x, y) ↦ (x, x) + (0, y - x)`. -/
def grading.decompose : R × R →+ DirectSum Two fun i => grading R i where
  toFun zz :=
    of (fun i => grading R i) 0 ⟨(zz.1, zz.1), rfl⟩ +
      of (fun i => grading R i) 1 ⟨(0, zz.2 - zz.1), rfl⟩
  map_zero' := by ext1 (_ | ⟨⟨⟩⟩) <;> rfl
  map_add' := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩
    rw [add_add_add_comm, ← map_add, ← map_add]
    dsimp only [Prod.mk_add_mk]
    simp_rw [add_sub_add_comm]
    congr
#align counterexample.counterexample_not_prime_but_homogeneous_prime.grading.decompose Counterexample.CounterexampleNotPrimeButHomogeneousPrime.grading.decompose

theorem grading.right_inv : Function.RightInverse (coeLinearMap (grading R)) grading.decompose :=
  fun zz => by
  induction' zz using DirectSum.induction_on with i zz d1 d2 ih1 ih2
  · simp only [map_zero]
  ·
    rcases i with (_ | ⟨⟨⟩⟩) <;> rcases zz with ⟨⟨a, b⟩, hab : _ = _⟩ <;> dsimp at hab  <;>
        cases hab <;>
      decide!
  · simp only [map_add, ih1, ih2]
#align counterexample.counterexample_not_prime_but_homogeneous_prime.grading.right_inv Counterexample.CounterexampleNotPrimeButHomogeneousPrime.grading.right_inv

theorem grading.left_inv : Function.LeftInverse (coeLinearMap (grading R)) grading.decompose :=
  fun zz => by
  cases' zz with a b
  unfold grading.decompose
  simp only [AddMonoidHom.coe_mk, map_add, coe_linear_map_of, Subtype.coe_mk, Prod.mk_add_mk,
    add_zero, add_sub_cancel'_right]
#align counterexample.counterexample_not_prime_but_homogeneous_prime.grading.left_inv Counterexample.CounterexampleNotPrimeButHomogeneousPrime.grading.left_inv

instance : GradedAlgebra (grading R) where
  one_mem := grading.one_mem R
  mul_mem := grading.mul_mem R
  decompose' := grading.decompose
  left_inv := by convert grading.left_inv
  right_inv := by convert grading.right_inv

/-- The counterexample is the ideal `I = span {(2, 2)}`. -/
def i : Ideal (R × R) :=
  Ideal.span {((2, 2) : R × R)}
#align counterexample.counterexample_not_prime_but_homogeneous_prime.I Counterexample.CounterexampleNotPrimeButHomogeneousPrime.i

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option class.instance_max_depth -/
set_option class.instance_max_depth 34

theorem i_not_prime : ¬i.IsPrime := by
  rintro ⟨rid1, rid2⟩
  apply rid1; clear rid1; revert rid2
  simp only [I, Ideal.mem_span_singleton, Ideal.eq_top_iff_one]
  decide
#align counterexample.counterexample_not_prime_but_homogeneous_prime.I_not_prime Counterexample.CounterexampleNotPrimeButHomogeneousPrime.i_not_prime

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option class.instance_max_depth -/
-- this is what we change the max instance depth for, it's only 2 above the default
set_option class.instance_max_depth 32

theorem i_isHomogeneous : i.Homogeneous (grading R) := by
  rw [Ideal.IsHomogeneous.iff_exists]
  refine' ⟨{⟨(2, 2), ⟨0, rfl⟩⟩}, _⟩
  rw [Set.image_singleton]
  rfl
#align counterexample.counterexample_not_prime_but_homogeneous_prime.I_is_homogeneous Counterexample.CounterexampleNotPrimeButHomogeneousPrime.i_isHomogeneous

theorem homogeneous_mem_or_mem {x y : R × R} (hx : SetLike.Homogeneous (grading R) x)
    (hy : SetLike.Homogeneous (grading R) y) (hxy : x * y ∈ i) : x ∈ i ∨ y ∈ i := by
  simp only [I, Ideal.mem_span_singleton] at hxy ⊢
  cases x; cases y
  obtain ⟨_ | ⟨⟨⟩⟩, hx : _ = _⟩ := hx <;> obtain ⟨_ | ⟨⟨⟩⟩, hy : _ = _⟩ := hy <;>
            dsimp at hx hy  <;>
          cases hx <;>
        cases hy <;>
      clear hx hy <;>
    decide!
#align counterexample.counterexample_not_prime_but_homogeneous_prime.homogeneous_mem_or_mem Counterexample.CounterexampleNotPrimeButHomogeneousPrime.homogeneous_mem_or_mem

end CounterexampleNotPrimeButHomogeneousPrime

end Counterexample

