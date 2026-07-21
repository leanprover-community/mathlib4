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
antisymmetrization of operations: either `a ≻ b - b ≺ a` or `a ≺ b - b ≻ a` gives such a structure.

## References
[J.-L. Loday, B. Vallette, *Algebraic Operads*][LV2012]
-/

@[expose] public section

/-- A nonunital nonassociative dendriform semiring is an `AddCommMonoid` with two operations
satisfying certain axioms, such that `a * b = prec a b + succ a b` is associative. -/
class NonUnitalDendriformSemiring (M) extends AddCommMonoid M where
  /-- The "left" operation splitting the associative product -/
  prec : M → M → M
  /-- The "right" operation splitting the associative product -/
  succ : M → M → M
  add_prec' a b c : prec (a + b) c = prec a c + prec b c
  prec_add' a b c : prec a (b + c) = prec a b + prec a c
  add_succ' a b c : succ (a + b) c = succ a c + succ b c
  succ_add' a b c : succ a (b + c) = succ a b + succ a c
  prec_zero' a : prec a 0 = 0
  zero_prec' a : prec 0 a = 0
  succ_zero' a : succ a 0 = 0
  zero_succ' a : succ 0 a = 0
  succ_succ_eq_mul_succ' a b c : succ a (succ b c) = succ (succ a b + prec a b) c
  succ_prec_assoc' a b c : prec (succ a b) c = succ a (prec b c) 
  prec_mul_eq_prec_prec' a b c : prec a (succ b c + prec b c) = prec (prec a b) c

/-- Notation for the right operation. The symbol points right. -/
infixr:75 " ≻ " => NonUnitalDendriformSemiring.succ
/-- Notation for the left operation. The symbol point left. -/
infixr:75 " ≺ " => NonUnitalDendriformSemiring.prec

/-- A dendriform ring has a `Neg` instance compatible with both `≺` and `≻`. -/
class NonUnitalDendriformRing (M) extends NonUnitalDendriformSemiring M, AddCommGroup M where
  prec_id_neg a b : prec a (- b) = - prec a b
  prec_neg_id a b : prec (- a) b = - prec a b
  succ_id_neg a b : succ a (- b) = - succ a b
  succ_neg_id a b : succ (- a) b = - succ a b

/-- A dendriform algebra is a `DendriformSemiring` with a `Module` structure compatible with `≺` and
`≻`. -/
class NonUnitalDendriformAlgebra (R M) [CommSemiring R] extends
    NonUnitalDendriformSemiring M, Module R M where
  smul_prec' (r : R) (a b : M) : (r • a) ≺ b = r • (a ≺ b)
  prec_smul' (r : R) (a b : M) : a ≺ (r • b) = r • (a ≺ b)
  smul_succ' (r : R) (a b : M) : (r • a) ≻ b = r • (a ≻ b)
  succ_smul' (r : R) (a b : M) : a ≻ (r • b) = r • (a ≻ b)

namespace NonUnitalDendriformSemiring

variable {M} [NonUnitalDendriformSemiring M]
variable (a b c : M)

instance : Mul M where
  mul a b := a ≻ b + a ≺ b

@[simp]
lemma mul_def : a * b = a ≻ b + a ≺ b := rfl
@[simp]
lemma succ_zero : a ≻ 0 = (0 : M) := succ_zero' a

@[simp]
lemma zero_succ : 0 ≻ a = (0 : M) := zero_succ' a

@[simp]
lemma prec_zero : a ≺ 0 = (0 : M) := prec_zero' a

@[simp]
lemma zero_prec : 0 ≺ a = (0 : M) := zero_prec' a

@[simp]
lemma add_succ : (a + b) ≻ c = a ≻ c + b ≻ c := add_succ' a b c

@[simp]
lemma succ_add : a ≻ (b + c) = a ≻ b + a ≻ c := succ_add' a b c

@[simp]
lemma add_prec : (a + b) ≺ c = a ≺ c + b ≺ c := add_prec' a b c

@[simp]
lemma prec_add : a ≺ (b + c) = a ≺ b + a ≺ c := prec_add' a b c

@[simp]
lemma succ_prec_assoc : (a ≻ b) ≺ c = a ≻ b ≺ c := succ_prec_assoc' a b c

@[simp]
lemma prec_prec_eq_prec_mul : (a ≺ b) ≺ c = a ≺ (b * c) := by simp [← prec_mul_eq_prec_prec']

@[simp]
lemma succ_succ_eq_mul_succ : a ≻ (b ≻ c) = (a * b) ≻ c := by simp [succ_succ_eq_mul_succ']

instance : NonUnitalSemiring M where
  left_distrib a b c := by simpa using by abel_nf
  right_distrib a b c := by simpa using by abel_nf
  zero_mul a := by simp
  mul_zero a := by simp
  mul_assoc a b c := by simpa using by abel_nf

end NonUnitalDendriformSemiring

namespace NonUnitalDendriformRing

variable {M} [NonUnitalDendriformRing M]
variable (a b c : M)

@[simp]
lemma neg_prec : (- a) ≺ b = -(a ≺ b) := prec_neg_id a b

@[simp]
lemma prec_neg : a ≺ (- b) = -(a ≺ b) := prec_id_neg a b

@[simp]
lemma neg_succ : (- a) ≻ b = -(a ≻ b) := succ_neg_id a b

@[simp]
lemma succ_neg : a ≻ (- b) = -(a ≻ b) := succ_id_neg a b

@[simp]
lemma sub_prec : (a - b) ≺ c = a ≺ c - b ≺ c := by simp [sub_eq_add_neg]

@[simp]
lemma prec_sub : a ≺ (b - c) = a ≺ b - a ≺ c := by simp [sub_eq_add_neg]

@[simp]
lemma sub_succ : (a - b) ≻ c = a ≻ c - b ≻ c := by simp [sub_eq_add_neg]

@[simp]
lemma succ_sub : a ≻ (b - c) = a ≻ b - a ≻ c := by simp [sub_eq_add_neg]

instance : NonUnitalRing M where

/-- The antisymmetrization of `≻` and `≺` yield a pre-Lie product. -/
def preLieLR := a ≻ b - b ≺ a

/-- The antisymmetrization of `≺` and `≻` yield a pre-Lie product. -/
def preLieRL := a ≺ b - b ≻ a

/-- The antisymmetrization `a ≻ b - b ≺ a` yields a `NonUnitalNonAssocRing`.
See note [reducible non-instances] -/
abbrev toNonUnitalNonAssocRingLR : NonUnitalNonAssocRing M where
  mul := preLieLR
  left_distrib a b c := by simpa [HMul.hMul, preLieLR] using by abel_nf
  right_distrib a b c := by simpa [HMul.hMul, preLieLR] using by abel_nf
  zero_mul a := by simp [HMul.hMul, preLieLR]
  mul_zero a := by simp [HMul.hMul, preLieLR]

/-- The antisymmetrization `a ≻ b - b ≺ a` yields a `LeftPreLieRing`.
See note [reducible non-instances] -/
abbrev toLeftPreLieRing : LeftPreLieRing M where
  __ := toNonUnitalNonAssocRingLR
  assoc_symm' x y z := by simpa [associator, HMul.hMul, Mul.mul, preLieLR] using by abel_nf

/-- The antisymmetrization `a ≺ b - b ≻ a` yields a `NonUnitalNonAssocRing`.
See note [reducible non-instances] -/
abbrev toNonUnitalNonAssocRingRL : NonUnitalNonAssocRing M where
  mul := preLieRL
  left_distrib a b c := by simpa [HMul.hMul, preLieRL] using by abel_nf
  right_distrib a b c := by simpa [HMul.hMul, preLieRL] using by abel_nf
  zero_mul a := by simp [HMul.hMul, preLieRL]
  mul_zero a := by simp [HMul.hMul, preLieRL]

/-- The antisymmetrization `a ≻ b - b ≺ a` yields a `RightPreLieRing`.
See note [reducible non-instances] -/
abbrev toRightPreLieRing : RightPreLieRing M where
  __ := toNonUnitalNonAssocRingRL
  assoc_symm' x y z := by simpa [associator_apply, HMul.hMul, Mul.mul, preLieRL] using by abel_nf

scoped[DendriformLR] attribute [instance] NonUnitalDendriformRing.toLeftPreLieRing
scoped[DendriformRL] attribute [instance] NonUnitalDendriformRing.toRightPreLieRing

end NonUnitalDendriformRing

namespace NonUnitalDendriformAlgebra

variable {R M} [CommSemiring R] [NonUnitalDendriformAlgebra R M]
variable (r : R) (a b : M)

@[simp]
lemma smul_prec : (r • a) ≺ b = r • (a ≺ b) := smul_prec' r a b

@[simp]
lemma prec_smul : a ≺ (r • b) = r • (a ≺ b) := prec_smul' r a b

@[simp]
lemma smul_succ : (r • a) ≻ b = r • (a ≻ b) := smul_succ' r a b

@[simp]
lemma succ_smul : a ≻ (r • b) = r • (a ≻ b) := succ_smul' r a b

end NonUnitalDendriformAlgebra
