/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Data.Nat.Cast.Basic

#align_import number_theory.legendre_symbol.add_character from "leanprover-community/mathlib"@"0723536a0522d24fc2f159a096fb3304bef77472"

/-!
# Characters from additive to multiplicative monoids

Let `A` be an additive monoid, and `M` a multiplicative one. An *additive character* of `A` with
values in `M` is simply a map `A → M` which intertwines the addition operation on `A` with the
multiplicative operation on `M`.

We define these objects, using the namespace `AddChar`, and show that if `A` is a commutative group
under addition, then the additive characters are also a group (written multiplicatively). Note that
we do not need `M` to be a group here.

We also include some constructions specific to the case when `A = R` is a ring; then we define
`mulShift ψ r`, where `ψ : AddChar R M` and `r : R`, to be the character defined by
`x ↦ ψ (r * x)`.

For more refined results of a number-theoretic nature (primitive characters, Gauss sums, etc)
see `Mathlib.NumberTheory.LegendreSymbol.AddCharacter`.

## Tags

additive character
-/


universe u v

/-!
### Definitions related to and results on additive characters
-/

section AddCharDef

-- The domain of our additive characters
variable (A : Type u) [AddMonoid A]

-- The target
variable (M : Type v) [CommMonoid M]

/-- Define `AddChar A M` as `(Multiplicative A) →* M`.
The definition works for an additive monoid `A` and a monoid `M`,
but we will restrict to the case that both are commutative rings for most applications.
The trivial additive character (sending everything to `1`) is `(1 : AddChar A M).` -/
def AddChar : Type max u v :=
  Multiplicative A →* M
#align add_char AddChar

end AddCharDef

namespace AddChar

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/5020): added
section DerivedInstances

variable (A : Type u) [AddMonoid A] (M : Type v) [CommMonoid M]

instance : CommMonoid (AddChar A M) :=
  inferInstanceAs (CommMonoid (Multiplicative A →* M))

instance : Inhabited (AddChar A M) :=
  inferInstanceAs (Inhabited (Multiplicative A →* M))

end DerivedInstances

section CoeToFun

variable {A : Type u} [AddMonoid A] {M : Type v} [CommMonoid M]

/-- Interpret an additive character as a monoid homomorphism. -/
def toMonoidHom : AddChar A M → Multiplicative A →* M :=
  id
#align add_char.to_monoid_hom AddChar.toMonoidHom

open Multiplicative

/-- Define coercion to a function so that it includes the move from `A` to `Multiplicative A`.
After we have proved the API lemmas below, we don't need to worry about writing `ofAdd a`
when we want to apply an additive character. -/
instance instFunLike : FunLike (AddChar A M) A M :=
  inferInstanceAs (FunLike (Multiplicative A →* M) A M)
#noalign add_char.has_coe_to_fun

theorem coe_to_fun_apply (ψ : AddChar A M) (a : A) : ψ a = ψ.toMonoidHom (ofAdd a) :=
  rfl
#align add_char.coe_to_fun_apply AddChar.coe_to_fun_apply

-- Porting note: added
theorem mul_apply (ψ φ : AddChar A M) (a : A) : (ψ * φ) a = ψ a * φ a :=
  rfl

-- Porting note: added
@[simp]
theorem one_apply (a : A) : (1 : AddChar A M) a = 1 := rfl

-- this instance was a bad idea and conflicted with `instFunLike` above
#noalign add_char.monoid_hom_class

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/5229): added.
@[ext]
theorem ext (f g : AddChar A M) (h : ∀ x : A, f x = g x) : f = g :=
  MonoidHom.ext h

/-- An additive character maps `0` to `1`. -/
@[simp]
theorem map_zero_one (ψ : AddChar A M) : ψ 0 = 1 := by rw [coe_to_fun_apply, ofAdd_zero, map_one]
#align add_char.map_zero_one AddChar.map_zero_one

/-- An additive character maps sums to products. -/
@[simp]
theorem map_add_mul (ψ : AddChar A M) (x y : A) : ψ (x + y) = ψ x * ψ y := by
  rw [coe_to_fun_apply, coe_to_fun_apply _ x, coe_to_fun_apply _ y, ofAdd_add, map_mul]
#align add_char.map_add_mul AddChar.map_add_mul

/-- An additive character maps multiples by natural numbers to powers. -/
@[simp]
theorem map_nsmul_pow (ψ : AddChar A M) (n : ℕ) (x : A) : ψ (n • x) = ψ x ^ n := by
  rw [coe_to_fun_apply, coe_to_fun_apply _ x, ofAdd_nsmul, map_pow]
#align add_char.map_nsmul_pow AddChar.map_nsmul_pow

end CoeToFun

section GroupStructure

open Multiplicative

variable {A : Type u} [AddCommGroup A] {M : Type v} [CommMonoid M]

/-- An additive character on a commutative additive group has an inverse.

Note that this is a different inverse to the one provided by `MonoidHom.inv`,
as it acts on the domain instead of the codomain. -/
instance hasInv : Inv (AddChar A M) :=
  ⟨fun ψ => ψ.comp invMonoidHom⟩
#align add_char.has_inv AddChar.hasInv

theorem inv_apply (ψ : AddChar A M) (x : A) : ψ⁻¹ x = ψ (-x) :=
  rfl
#align add_char.inv_apply AddChar.inv_apply

/-- An additive character maps multiples by integers to powers. -/
@[simp]
theorem map_zsmul_zpow {M : Type v} [CommGroup M] (ψ : AddChar A M) (n : ℤ) (x : A) :
    ψ (n • x) = ψ x ^ n := by rw [coe_to_fun_apply, coe_to_fun_apply _ x, ofAdd_zsmul, map_zpow]
#align add_char.map_zsmul_zpow AddChar.map_zsmul_zpow

/-- The additive characters on a commutative additive group form a commutative group. -/
instance commGroup : CommGroup (AddChar A M) :=
  { MonoidHom.commMonoid with
    inv := Inv.inv
    mul_left_inv := fun ψ => by
      ext x
      rw [AddChar.mul_apply, AddChar.one_apply, inv_apply, ← map_add_mul, add_left_neg,
        map_zero_one] }
#align add_char.comm_group AddChar.commGroup

end GroupStructure

section nontrivial

variable {A : Type u} [AddMonoid A] {M : Type v} [CommMonoid M]

/-- An additive character is *nontrivial* if it takes a value `≠ 1`. -/
def IsNontrivial (ψ : AddChar A M) : Prop :=
  ∃ a : A, ψ a ≠ 1
#align add_char.is_nontrivial AddChar.IsNontrivial

/-- An additive character is nontrivial iff it is not the trivial character. -/
theorem isNontrivial_iff_ne_trivial (ψ : AddChar A M) : IsNontrivial ψ ↔ ψ ≠ 1 := by
  refine' not_forall.symm.trans (Iff.not _)
  rw [DFunLike.ext_iff]
  rfl
#align add_char.is_nontrivial_iff_ne_trivial AddChar.isNontrivial_iff_ne_trivial

end nontrivial

section Ring

-- The domain and target of our additive characters. Now we restrict to a ring in the domain.
variable {R : Type u} [CommRing R] {M : Type v} [CommMonoid M]

/-- Define the multiplicative shift of an additive character.
This satisfies `mulShift ψ a x = ψ (a * x)`. -/
def mulShift (ψ : AddChar R M) (r : R) : AddChar R M :=
  ψ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft r))
#align add_char.mul_shift AddChar.mulShift

@[simp]
theorem mulShift_apply {ψ : AddChar R M} {r : R} {x : R} : mulShift ψ r x = ψ (r * x) :=
  rfl
#align add_char.mul_shift_apply AddChar.mulShift_apply

/-- `ψ⁻¹ = mulShift ψ (-1))`. -/
theorem inv_mulShift (ψ : AddChar R M) : ψ⁻¹ = mulShift ψ (-1) := by
  ext
  rw [inv_apply, mulShift_apply, neg_mul, one_mul]
#align add_char.inv_mul_shift AddChar.inv_mulShift

/-- If `n` is a natural number, then `mulShift ψ n x = (ψ x) ^ n`. -/
theorem mulShift_spec' (ψ : AddChar R M) (n : ℕ) (x : R) : mulShift ψ n x = ψ x ^ n := by
  rw [mulShift_apply, ← nsmul_eq_mul, map_nsmul_pow]
#align add_char.mul_shift_spec' AddChar.mulShift_spec'

/-- If `n` is a natural number, then `ψ ^ n = mulShift ψ n`. -/
theorem pow_mulShift (ψ : AddChar R M) (n : ℕ) : ψ ^ n = mulShift ψ n := by
  ext x
  rw [show (ψ ^ n) x = ψ x ^ n from rfl, ← mulShift_spec']
#align add_char.pow_mul_shift AddChar.pow_mulShift

/-- The product of `mulShift ψ r` and `mulShift ψ s` is `mulShift ψ (r + s)`. -/
theorem mulShift_mul (ψ : AddChar R M) (r s : R) :
    mulShift ψ r * mulShift ψ s = mulShift ψ (r + s) := by
  ext
  rw [mulShift_apply, right_distrib, map_add_mul]; norm_cast
#align add_char.mul_shift_mul AddChar.mulShift_mul

/-- `mulShift ψ 0` is the trivial character. -/
@[simp]
theorem mulShift_zero (ψ : AddChar R M) : mulShift ψ 0 = 1 := by
  ext
  rw [mulShift_apply, zero_mul, map_zero_one]; norm_cast
#align add_char.mul_shift_zero AddChar.mulShift_zero

end Ring

end AddChar
