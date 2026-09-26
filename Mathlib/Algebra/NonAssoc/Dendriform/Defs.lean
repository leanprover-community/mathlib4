/-
Copyright (c) 2026 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/

module
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.NonAssoc.PreLie.Basic

/-!
# Dendriform (Semi)Rings and Algebras

## Main definitions

A nonunital dendriform semiring `M` is a `NonUnitalSemiring` where the associative product can be
split into two operations `prec : M → M → M` and `succ : M → M → M` satisfying
* `prec (prec a b) c = prec a (succ b c + prec b c)`
* `succ a (prec b c) = prec (succ a b) c`
* `succ a (succ b c) = succ (succ a b + prec a b) c`

These identities ensure that `* := prec + succ` is indeed associative.
In the literature it is common to denote `prec` and `succ` as ≺ and ≻, respectively.

Their unital version requires the existence of a unit `1` such that `1 ≻ a = a ≺ 1 = a` and
`1 ≺ a = a ≻ 1 = 0` for all `a ≠ 1`. Note that `1 ≺ 1` and `1 ≻ 1` are left undefined.
This is enough to ensure that `1 * a = a * 1 = 1`. The product `1 * 1` is defined to be `1`.

Dendriform algebras are unital dendriform semirings with an extra module structure over a
commutative semiring `R` such that both `≺` and `≻` are bilinear.

## Main results
Any dendriform ring (algebra) becomes a left or right `PreLieRing` (`PreLieAlgebra`) by
antisymmetrization of operations:
- `fun a b ↦ a ≻ b - b ≺ a` yields a `LeftPreLieRing`
- `fun a b ↦ a ≺ b - b ≻ a` yields a `RightPreLieRing`.
These structures are opposite to each other, see for instance `LeftPreLieRing.instRightPreLieRing`.

## References
[J.-L. Loday, B. Vallette, *Algebraic Operads*][LV2012]
-/

@[expose] public section

/-- A nonunital nonassociative dendriform semiring is an `AddCommMonoid` with two operations
satisfying certain axioms, such that `a * b = prec a b + succ a b` is associative. -/
class NonUnitalDendriformSemiring (M) extends AddCommMonoid M, Mul M where
  /-- The "left" operation splitting the associative product -/
  prec : M →+ M →+ M
  /-- The "right" operation splitting the associative product -/
  succ : M →+ M →+ M
  mul_eq a b : a * b = succ a b + prec a b
  succ_succ_eq a b c : succ a (succ b c) = succ (succ a b + prec a b) c
  prec_succ_assoc a b c : prec (succ a b) c = succ a (prec b c)
  prec_prec_eq a b c : prec (prec a b) c = prec a (succ b c + prec b c)

/-- Notation for the right operation. The symbol points right. -/
infixr:75 " ≻ " => NonUnitalDendriformSemiring.succ
/-- Notation for the left operation. The symbol point left. -/
infixr:75 " ≺ " => NonUnitalDendriformSemiring.prec

/-- A dendriform ring has a `Neg` instance compatible with both `≺` and `≻`. -/
class NonUnitalDendriformRing (M) extends NonUnitalDendriformSemiring M,
  AddCommGroup M where

/-- A dendriform algebra is a `DendriformSemiring` with a `Module` structure compatible with `≺` and
`≻`. -/
class NonUnitalDendriformAlgebra (R M) [CommSemiring R] extends NonUnitalSemiring M,
    Module R M where
  succ : M →ₗ[R] M →ₗ[R] M
  prec : M →ₗ[R] M →ₗ[R] M
  mul_eq a b : a * b = succ a b + prec a b
  succ_succ_eq a b c : succ a (succ b c) = succ (succ a b + prec a b) c
  succ_prec_assoc a b c : succ a (prec b c) = prec (succ a b) c
  prec_prec_eq a b c : prec (prec a b) c = prec a (succ a b + prec a b)

namespace NonUnitalDendriformSemiring

@[instance_reducible]
def ofAddHom {M} [AddCommMonoid M] (prec : M →+ M →+ M) (succ : M →+ M →+ M)
  (hss : ∀ a b c, succ a (succ b c) = succ (succ a b + prec a b) c)
  (hpp : ∀ a b c, prec (prec a b) c = prec a (succ b c + prec b c))
  (hps : ∀ a b c, prec (succ a b) c = succ a (prec b c)) :
    NonUnitalDendriformSemiring M where
  prec := prec
  succ := succ
  mul a b := succ a b + prec a b
  mul_eq a b := by simp [HMul.hMul]
  succ_succ_eq := hss
  prec_succ_assoc := hps
  prec_prec_eq := hpp

class IsComm (M) [NonUnitalDendriformSemiring M] : Prop where
  prec_eq_succ (a b : M) : a ≺ b = b ≻ a

variable {M} [NonUnitalDendriformSemiring M]
variable (a b c : M)

lemma succ_prec_assoc : a ≻ (b ≺ c) = (a ≻ b) ≺ c := (prec_succ_assoc a b c).symm

lemma prec_prec_eq_prec_mul : (a ≺ b) ≺ c = a ≺ (b * c) := by simp [mul_eq, prec_prec_eq]

lemma succ_succ_eq_mul_succ : a ≻ (b ≻ c) = (a * b) ≻ c := by simp [mul_eq, succ_succ_eq]

instance : NonUnitalSemiring M where
  left_distrib a b c := by simpa [mul_eq] using by abel_nf
  right_distrib a b c := by simpa [mul_eq] using by abel_nf
  zero_mul a := by simp [mul_eq]
  mul_zero a := by simp [mul_eq]
  mul_assoc a b c := by
    simpa [mul_eq, succ_prec_assoc, prec_prec_eq_prec_mul, succ_succ_eq_mul_succ] using by abel_nf

instance [IsComm M] : NonUnitalCommSemiring M where
  mul_comm a b := by simp [mul_eq, IsComm.prec_eq_succ, add_comm]

end NonUnitalDendriformSemiring

namespace NonUnitalDendriformRing

open NonUnitalDendriformSemiring

variable {M} [NonUnitalDendriformRing M]
variable (a b c : M)

@[simp]
lemma sub_prec : (a - b) ≺ c = a ≺ c - b ≺ c := by simp [sub_eq_add_neg]

@[simp]
lemma prec_sub : a ≺ (b - c) = a ≺ b - a ≺ c := by simp [sub_eq_add_neg]

@[simp]
lemma sub_succ : (a - b) ≻ c = a ≻ c - b ≻ c := by simp [sub_eq_add_neg]

@[simp]
lemma succ_sub : a ≻ (b - c) = a ≻ b - a ≻ c := by simp [sub_eq_add_neg]

instance : NonUnitalRing M where

instance [IsComm M] : NonUnitalCommRing M where

/-- The antisymmetrization of `≻` and `≺` yield a pre-Lie product. -/
def preLieLR := a ≻ b - b ≺ a

/-- The antisymmetrization of `≺` and `≻` yield a pre-Lie product. -/
def preLieRL := a ≺ b - b ≻ a

/-- The antisymmetrization `a ≻ b - b ≺ a` yields a `NonUnitalNonAssocRing`.
See note [reducible non-instances] -/
abbrev toNonUnitalNonAssocRingLR : NonUnitalNonAssocRing M where
  mul := preLieLR
  left_distrib a b c := by
    simpa [HMul.hMul, preLieLR] using by abel_nf
  right_distrib a b c := by
    simpa [HMul.hMul, preLieLR] using by abel_nf
  zero_mul a := by simp [HMul.hMul, preLieLR]
  mul_zero a := by simp [HMul.hMul, preLieLR]

/-- The antisymmetrization `a ≻ b - b ≺ a` yields a `LeftPreLieRing`.
See note [reducible non-instances] -/
abbrev toLeftPreLieRing : LeftPreLieRing M where
  __ := toNonUnitalNonAssocRingLR
  assoc_symm' x y z := by
    simpa [associator, HMul.hMul, Mul.mul, preLieLR, prec_prec_eq, succ_succ_eq, succ_prec_assoc]
      using by abel_nf

/-- The antisymmetrization `a ≺ b - b ≻ a` yields a `NonUnitalNonAssocRing`.
See note [reducible non-instances] -/
abbrev toNonUnitalNonAssocRingRL : NonUnitalNonAssocRing M where
  mul := preLieRL
  left_distrib a b c := by
    simpa [HMul.hMul, preLieRL] using by abel_nf
  right_distrib a b c := by
    simpa [HMul.hMul, preLieRL] using by abel_nf
  zero_mul a := by simp [HMul.hMul, preLieRL]
  mul_zero a := by simp [HMul.hMul, preLieRL]

/-- The antisymmetrization `a ≻ b - b ≺ a` yields a `RightPreLieRing`.
See note [reducible non-instances] -/
abbrev toRightPreLieRing : RightPreLieRing M where
  __ := toNonUnitalNonAssocRingRL
  assoc_symm' x y z := by
    simpa [associator_apply, HMul.hMul, Mul.mul, preLieRL, succ_prec_assoc, succ_succ_eq,
    prec_prec_eq] using by abel_nf

scoped[DendriformLR] attribute [instance] NonUnitalDendriformRing.toLeftPreLieRing
scoped[DendriformRL] attribute [instance] NonUnitalDendriformRing.toRightPreLieRing

end NonUnitalDendriformRing
