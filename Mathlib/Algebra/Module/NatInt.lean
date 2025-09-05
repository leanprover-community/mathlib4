/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Modules over `ℕ` and `ℤ`

This file concerns modules where the scalars are the natural numbers or the integers.

## Main definitions

* `AddCommMonoid.toNatModule`: any `AddCommMonoid` is (uniquely) a module over the naturals.
* `AddCommGroup.toIntModule`: any `AddCommGroup` is a module over the integers.

## Main results

* `AddCommMonoid.uniqueNatModule`: there is an unique `AddCommMonoid ℕ M` structure for any `M`

## Tags

semimodule, module, vector space
-/

assert_not_exists RelIso Field Invertible Multiset Pi.single_smul₀ Set.indicator

open Function Set

universe u v

variable {R S M M₂ : Type*}

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M)

instance AddCommMonoid.toNatModule : Module ℕ M where
  one_smul := one_nsmul
  mul_smul m n a := mul_nsmul' a m n
  smul_add n a b := nsmul_add a b n
  smul_zero := nsmul_zero
  zero_smul := zero_nsmul
  add_smul r s x := add_nsmul x r s

end AddCommMonoid

section AddCommGroup

variable (R M) [Semiring R] [AddCommGroup M]

instance AddCommGroup.toIntModule : Module ℤ M where
  one_smul := one_zsmul
  mul_smul m n a := mul_zsmul a m n
  smul_add n a b := zsmul_add a b n
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul
  add_smul r s x := add_zsmul x r s

end AddCommGroup

variable (R) in
/-- An `AddCommMonoid` that is a `Module` over a `Ring` carries a natural `AddCommGroup`
structure.
See note [reducible non-instances]. -/
abbrev Module.addCommMonoidToAddCommGroup
    [Ring R] [AddCommMonoid M] [Module R M] : AddCommGroup M :=
  { (inferInstance : AddCommMonoid M) with
    neg := fun a => (-1 : R) • a
    neg_add_cancel := fun a =>
      show (-1 : R) • a + a = 0 by
        nth_rw 2 [← one_smul R a]
        rw [← add_smul, neg_add_cancel, zero_smul]
    zsmul := fun z a => (z : R) • a
    zsmul_zero' := fun a => by simpa only [Int.cast_zero] using zero_smul R a
    zsmul_succ' := fun z a => by simp [add_comm, add_smul]
    zsmul_neg' := fun z a => by simp [← smul_assoc] }

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

section

variable (R)

/-- `nsmul` is equal to any other module structure via a cast. -/
@[norm_cast]
lemma Nat.cast_smul_eq_nsmul (n : ℕ) (b : M) : (n : R) • b = n • b := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, zero_smul]
  | succ n ih => rw [Nat.cast_succ, add_smul, add_smul, one_smul, ih, one_smul]

/-- `nsmul` is equal to any other module structure via a cast. -/
lemma ofNat_smul_eq_nsmul (n : ℕ) [n.AtLeastTwo] (b : M) :
    (ofNat(n) : R) • b = ofNat(n) • b := Nat.cast_smul_eq_nsmul ..

end

/-- Convert back any exotic `ℕ`-smul to the canonical instance. This should not be needed since in
mathlib all `AddCommMonoid`s should normally have exactly one `ℕ`-module structure by design.
-/
theorem nat_smul_eq_nsmul (h : Module ℕ M) (n : ℕ) (x : M) : h.smul n x = n • x :=
  Nat.cast_smul_eq_nsmul ..

/-- All `ℕ`-module structures are equal. Not an instance since in mathlib all `AddCommMonoid`
should normally have exactly one `ℕ`-module structure by design. -/
def AddCommMonoid.uniqueNatModule : Unique (Module ℕ M) where
  default := inferInstance
  uniq P := (Module.ext' P _) fun n => by convert nat_smul_eq_nsmul P n

/-- All `ℕ`-module structures are equal. See also `AddCommMoniod.uniqueNatModule`. -/
instance AddCommMonoid.subsingletonNatModule : Subsingleton (Module ℕ M) :=
  AddCommMonoid.uniqueNatModule.instSubsingleton

instance AddCommMonoid.nat_isScalarTower : IsScalarTower ℕ R M where
  smul_assoc n x y := by
    induction n with
    | zero => simp only [zero_smul]
    | succ n ih => simp only [add_smul, one_smul, ih]

end AddCommMonoid

theorem map_natCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Semiring R] [Semiring S] [Module R M]
    [Module S M₂] (x : ℕ) (a : M) : f ((x : R) • a) = (x : S) • f a := by
  simp only [Nat.cast_smul_eq_nsmul, map_nsmul]

theorem Nat.smul_one_eq_cast {R : Type*} [NonAssocSemiring R] (m : ℕ) : m • (1 : R) = ↑m := by
  rw [nsmul_eq_mul, mul_one]

theorem Int.smul_one_eq_cast {R : Type*} [NonAssocRing R] (m : ℤ) : m • (1 : R) = ↑m := by
  rw [zsmul_eq_mul, mul_one]

section AddCommGroup

variable [Ring R] [AddCommGroup M] [Module R M]

section

variable (R)

/-- `zsmul` is equal to any other module structure via a cast. -/
@[norm_cast]
lemma Int.cast_smul_eq_zsmul (n : ℤ) (b : M) : (n : R) • b = n • b := by
  cases n with
  | ofNat => simp [Nat.cast_smul_eq_nsmul]
  | negSucc => simp [add_smul, Nat.cast_smul_eq_nsmul]

end

/-- Convert back any exotic `ℤ`-smul to the canonical instance. This should not be needed since in
mathlib all `AddCommGroup`s should normally have exactly one `ℤ`-module structure by design. -/
theorem int_smul_eq_zsmul (h : Module ℤ M) (n : ℤ) (x : M) : h.smul n x = n • x :=
  Int.cast_smul_eq_zsmul ..

/-- All `ℤ`-module structures are equal. Not an instance since in mathlib all `AddCommGroup`
should normally have exactly one `ℤ`-module structure by design. -/
def AddCommGroup.uniqueIntModule : Unique (Module ℤ M) where
  default := inferInstance
  uniq P := (Module.ext' P _) fun n => by convert int_smul_eq_zsmul P n

end AddCommGroup

/-- All `ℤ`-module structures are equal. See also `AddCommGroup.uniqueIntModule`. -/
instance AddCommMonoid.subsingletonIntModule [AddCommMonoid M] : Subsingleton (Module ℤ M) where
  allEq a b :=
    let : AddCommGroup M := Module.addCommMonoidToAddCommGroup ℤ
    AddCommGroup.uniqueIntModule.instSubsingleton.allEq a b

theorem map_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Ring R] [Ring S] [Module R M] [Module S M₂]
    (x : ℤ) (a : M) :
    f ((x : R) • a) = (x : S) • f a := by simp only [Int.cast_smul_eq_zsmul, map_zsmul]

instance AddCommGroup.intIsScalarTower {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
    [Module R M] : IsScalarTower ℤ R M where
  smul_assoc n x y := by
    cases n with
    | ofNat => simp [mul_smul, Nat.cast_smul_eq_nsmul]
    | negSucc => simp [mul_smul, add_smul, Nat.cast_smul_eq_nsmul]
