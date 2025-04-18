/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser, Jujian Zhang
-/
import Mathlib.Algebra.Divisibility.Finite
import Mathlib.Algebra.Divisibility.Prod
import Mathlib.Data.Fintype.Units
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# A homogeneous ideal that is homogeneously prime but not prime

In `Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem`, we assumed that the underlying grading
is indexed by a `LinearOrderedCancelAddCommMonoid` to prove that a homogeneous ideal is prime
if and only if it is homogeneously prime. This file shows that even if this assumption isn't
strictly necessary, the assumption of "being cancellative" is. We construct a counterexample where
the underlying indexing set is a `LinearOrderedAddCommMonoid` but is not cancellative and the
statement is false.

We achieve this by considering the ring `R=ℤ/4ℤ`. We first give the two element set `ι = {0, 1}` a
structure of linear ordered additive commutative monoid by setting `0 + 0 = 0` and `_ + _ = 1` and
`0 < 1`. Then we use `ι` to grade `R²` by setting `{(a, a) | a ∈ R}` to have grade `0`; and
`{(0, b) | b ∈ R}` to have grade 1. Then the ideal `I = span {(2, 2)} ⊆ ℤ/4ℤ × ℤ/4ℤ` is homogeneous
and not prime. But it is homogeneously prime, i.e. if `(a, b), (c, d)` are two homogeneous elements
then `(a, b) * (c, d) ∈ I` implies either `(a, b) ∈ I` or `(c, d) ∈ I`.


## Tags

homogeneous, prime
-/


namespace Counterexample

namespace CounterexampleNotPrimeButHomogeneousPrime

open DirectSum

abbrev Two :=
  WithZero Unit

instance : Fintype Two :=
  inferInstanceAs (Fintype (Option Unit))

instance : IsOrderedAddMonoid Two :=
  { add_le_add_left := by decide }

section

variable (R : Type*) [CommRing R]

/-- The grade 0 part of `R²` is `{(a, a) | a ∈ R}`. -/
def submoduleZ : Submodule R (R × R) where
  carrier := {zz | zz.1 = zz.2}
  zero_mem' := rfl
  add_mem' := @fun _ _ ha hb => congr_arg₂ (· + ·) ha hb
  smul_mem' a _ hb := congr_arg (a * ·) hb

instance [Fintype R] [DecidableEq R] : Fintype (submoduleZ R) :=
  inferInstanceAs (Fintype {zz : R × R // zz.1 = zz.2})

/-- The grade 1 part of `R²` is `{(0, b) | b ∈ R}`. -/
def submoduleO : Submodule R (R × R) :=
  LinearMap.ker (LinearMap.fst R R R)

instance [Fintype R] [DecidableEq R] : Fintype (submoduleO R) :=
  inferInstanceAs (Fintype {zz : R × R // zz.1 = 0})

/-- Given the above grading (see `submoduleZ` and `submoduleO`),
  we turn `R²` into a graded ring. -/
def grading : Two → Submodule R (R × R)
  | 0 => submoduleZ R
  | 1 => submoduleO R

instance [Fintype R] [DecidableEq R] : ∀ (i : Two), Fintype (grading R i)
  | 0 => inferInstanceAs (Fintype (submoduleZ R))
  | 1 => inferInstanceAs (Fintype (submoduleO R))

theorem grading.one_mem : (1 : R × R) ∈ grading R 0 :=
  Eq.refl (1, 1).fst

theorem grading.mul_mem :
    ∀ ⦃i j : Two⦄ {a b : R × R} (_ : a ∈ grading R i) (_ : b ∈ grading R j),
      a * b ∈ grading R (i + j)
  | 0, 0, a, b, (ha : a.1 = a.2), (hb : b.1 = b.2) => show a.1 * b.1 = a.2 * b.2 by rw [ha, hb]
  | 0, 1, a, b, (_ : a.1 = a.2), (hb : b.1 = 0) =>
    show a.1 * b.1 = 0 by rw [hb, mul_zero]
  | 1, 0, a, b, (ha : a.1 = 0), _ => show a.1 * b.1 = 0 by rw [ha, zero_mul]
  | 1, 1, a, b, (ha : a.1 = 0), _ => show a.1 * b.1 = 0 by rw [ha, zero_mul]

end

local notation "R" => ZMod 4

/-- `R² ≅ {(a, a) | a ∈ R} ⨁ {(0, b) | b ∈ R}` by `(x, y) ↦ (x, x) + (0, y - x)`. -/
def grading.decompose : R × R →+ DirectSum Two fun i => grading R i where
  toFun zz :=
    of (grading R ·) 0 ⟨(zz.1, zz.1), rfl⟩ +
    of (grading R ·) 1 ⟨(0, zz.2 - zz.1), rfl⟩
  map_zero' := by decide
  map_add' := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩
    rw [add_add_add_comm, ← map_add, ← map_add]
    dsimp only [Prod.mk_add_mk]
    simp_rw [add_sub_add_comm]
    rfl

theorem grading.right_inv : Function.RightInverse (coeLinearMap (grading R)) grading.decompose := by
  intro zz
  induction zz using DirectSum.induction_on with
  | zero => decide
  | of => decide +revert
  | add d1 d2 ih1 ih2 => simp only [map_add, ih1, ih2]

instance : GradedAlgebra (grading R) where
  one_mem := grading.one_mem R
  mul_mem := grading.mul_mem R
  decompose' := grading.decompose
  left_inv := by decide
  right_inv := grading.right_inv

/-- The counterexample is the ideal `I = span {(2, 2)}`. -/
def I : Ideal (R × R) :=
  Ideal.span {((2, 2) : R × R)}

theorem I_not_prime : ¬I.IsPrime := by
  rintro ⟨-, h⟩
  simp only [I, Ideal.mem_span_singleton] at h
  revert h
  decide +revert +kernel

theorem I_isHomogeneous : Ideal.IsHomogeneous (grading R) I := by
  rw [Ideal.IsHomogeneous.iff_exists]
  refine ⟨{⟨(2, 2), ⟨0, rfl⟩⟩}, ?_⟩
  rw [Set.image_singleton]
  rfl


theorem homogeneous_mem_or_mem : ∀ {x y : R × R},
    SetLike.IsHomogeneousElem (grading R) x → SetLike.IsHomogeneousElem (grading R) y →
    x * y ∈ I → x ∈ I ∨ y ∈ I := by
  have h2 : Prime (2:R) := by
    unfold Prime
    decide +kernel
  simp only [I, Ideal.mem_span_singleton]
  rintro ⟨x1, x2⟩ ⟨y1, y2⟩ ⟨_ | ⟨⟨⟩⟩, rfl : x1 = _⟩ ⟨_ | ⟨⟨⟩⟩, rfl : y1 = _⟩ h <;>
    decide +revert

end CounterexampleNotPrimeButHomogeneousPrime

end Counterexample
