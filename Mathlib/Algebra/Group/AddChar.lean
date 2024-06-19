/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Logic.Equiv.TransferInstance

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

/-!
### Definitions related to and results on additive characters
-/

open Function Multiplicative

section AddCharDef

-- The domain of our additive characters
variable (A : Type*) [AddMonoid A]

-- The target
variable (M : Type*) [Monoid M]

/-- `AddChar A M` is the type of maps `A → M`, for `A` an additive monoid and `M` a multiplicative
monoid, which intertwine addition in `A` with multiplication in `M`.

We only put the typeclasses needed for the definition, although in practice we are usually
interested in much more specific cases (e.g. when `A` is a group and `M` a commutative ring).
 -/
structure AddChar where
  /-- The underlying function.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : A → M
  /-- The function maps `0` to `1`.

  Do not use this directly. Instead use `AddChar.map_zero_eq_one`. -/
  map_zero_eq_one' : toFun 0 = 1
  /-- The function maps addition in `A` to multiplication in `M`.

  Do not use this directly. Instead use `AddChar.map_add_eq_mul`. -/
  map_add_eq_mul' : ∀ a b : A, toFun (a + b) = toFun a * toFun b

#align add_char AddChar

end AddCharDef

namespace AddChar

section Basic
-- results which don't require commutativity or inverses

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

/-- Define coercion to a function. -/
instance instFunLike : FunLike (AddChar A M) A M where
  coe := AddChar.toFun
  coe_injective' φ ψ h := by cases φ; cases ψ; congr

#noalign add_char.has_coe_to_fun

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/5229): added.
@[ext] lemma ext (f g : AddChar A M) (h : ∀ x : A, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp] lemma coe_mk (f : A → M)
    (map_zero_eq_one' : f 0 = 1) (map_add_eq_mul' : ∀ a b : A, f (a + b) = f a * f b) :
    AddChar.mk f map_zero_eq_one' map_add_eq_mul' = f := by
  rfl

/-- An additive character maps `0` to `1`. -/
@[simp] lemma map_zero_eq_one (ψ : AddChar A M) : ψ 0 = 1 := ψ.map_zero_eq_one'
#align add_char.map_zero_one AddChar.map_zero_eq_one

/-- An additive character maps sums to products. -/
lemma map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (x + y) = ψ x * ψ y := ψ.map_add_eq_mul' x y
#align add_char.map_add_mul AddChar.map_add_eq_mul

@[deprecated (since := "2024-06-06")] alias map_zero_one := map_zero_eq_one
@[deprecated (since := "2024-06-06")] alias map_add_mul := map_add_eq_mul

/-- Interpret an additive character as a monoid homomorphism. -/
def toMonoidHom (φ : AddChar A M) : Multiplicative A →* M where
  toFun := φ.toFun
  map_one' := φ.map_zero_eq_one'
  map_mul' := φ.map_add_eq_mul'
#align add_char.to_monoid_hom AddChar.toMonoidHom

-- this instance was a bad idea and conflicted with `instFunLike` above
#noalign add_char.monoid_hom_class

@[simp] lemma toMonoidHom_apply (ψ : AddChar A M) (a : Multiplicative A) :
  ψ.toMonoidHom a = ψ (Multiplicative.toAdd a) :=
  rfl
#align add_char.coe_to_fun_apply AddChar.toMonoidHom_apply

/-- An additive character maps multiples by natural numbers to powers. -/
lemma map_nsmul_eq_pow (ψ : AddChar A M) (n : ℕ) (x : A) : ψ (n • x) = ψ x ^ n :=
  ψ.toMonoidHom.map_pow x n
#align add_char.map_nsmul_pow AddChar.map_nsmul_eq_pow

@[deprecated (since := "2024-06-06")] alias map_nsmul_pow := map_nsmul_eq_pow

/-- Additive characters `A → M` are the same thing as monoid homomorphisms from `Multiplicative A`
to `M`. -/
def toMonoidHomEquiv : AddChar A M ≃ (Multiplicative A →* M) where
  toFun φ := φ.toMonoidHom
  invFun f :=
  { toFun := f.toFun
    map_zero_eq_one' := f.map_one'
    map_add_eq_mul' := f.map_mul' }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp, norm_cast] lemma coe_toMonoidHomEquiv (ψ : AddChar A M) :
    ⇑(toMonoidHomEquiv ψ) = ψ ∘ Multiplicative.toAdd := rfl

@[simp, norm_cast] lemma coe_toMonoidHomEquiv_symm (ψ : Multiplicative A →* M) :
    ⇑(toMonoidHomEquiv.symm ψ) = ψ ∘ Multiplicative.ofAdd := rfl

@[simp] lemma toMonoidHomEquiv_apply (ψ : AddChar A M) (a : Multiplicative A) :
    toMonoidHomEquiv ψ a = ψ (Multiplicative.toAdd a) := rfl

@[simp] lemma toMonoidHomEquiv_symm_apply (ψ : Multiplicative A →* M) (a : A) :
    toMonoidHomEquiv.symm ψ a = ψ (Multiplicative.ofAdd a) := rfl

/-- Interpret an additive character as a monoid homomorphism. -/
def toAddMonoidHom (φ : AddChar A M) : A →+ Additive M where
  toFun := φ.toFun
  map_zero' := φ.map_zero_eq_one'
  map_add' := φ.map_add_eq_mul'

@[simp] lemma coe_toAddMonoidHom (ψ : AddChar A M) : ⇑ψ.toAddMonoidHom = Additive.ofMul ∘ ψ := rfl

@[simp] lemma toAddMonoidHom_apply (ψ : AddChar A M) (a : A) :
    ψ.toAddMonoidHom a = Additive.ofMul (ψ a) := rfl

/-- Additive characters `A → M` are the same thing as additive homomorphisms from `A` to
`Additive M`. -/
def toAddMonoidHomEquiv : AddChar A M ≃ (A →+ Additive M) where
  toFun φ := φ.toAddMonoidHom
  invFun f :=
  { toFun := f.toFun
    map_zero_eq_one' := f.map_zero'
    map_add_eq_mul' := f.map_add' }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp, norm_cast]
lemma coe_toAddMonoidHomEquiv (ψ : AddChar A M) :
    ⇑(toAddMonoidHomEquiv ψ) = Additive.ofMul ∘ ψ := rfl

@[simp, norm_cast] lemma coe_toAddMonoidHomEquiv_symm (ψ : A →+ Additive M) :
    ⇑(toAddMonoidHomEquiv.symm ψ) = Additive.toMul ∘ ψ := rfl

@[simp] lemma toAddMonoidHomEquiv_apply (ψ : AddChar A M) (a : A) :
    toAddMonoidHomEquiv ψ a = Additive.ofMul (ψ a) := rfl

@[simp] lemma toAddMonoidHomEquiv_symm_apply (ψ : A →+ Additive M) (a : A) :
    toAddMonoidHomEquiv.symm ψ a = Additive.toMul (ψ a) := rfl

/-- The trivial additive character (sending everything to `1`) is `(1 : AddChar A M).` -/
instance instOne : One (AddChar A M) := toMonoidHomEquiv.one

@[simp, norm_cast] lemma coe_one : ⇑(1 : AddChar A M) = 1 := rfl
@[simp] lemma one_apply (a : A) : (1 : AddChar A M) a = 1 := rfl

instance instInhabited : Inhabited (AddChar A M) := ⟨1⟩

/-- Composing a `MonoidHom` with an `AddChar` yields another `AddChar`. -/
def _root_.MonoidHom.compAddChar {N : Type*} [Monoid N] (f : M →* N) (φ : AddChar A M) :
    AddChar A N := toMonoidHomEquiv.symm (f.comp φ.toMonoidHom)

@[simp, norm_cast]
lemma _root_.MonoidHom.coe_compAddChar {N : Type*} [Monoid N] (f : M →* N) (φ : AddChar A M) :
    f.compAddChar φ = f ∘ φ :=
  rfl

@[simp, norm_cast]
lemma _root_.MonoidHom.compAddChar_apply (f : M →* N) (φ : AddChar A M) : f.compAddChar φ = f ∘ φ :=
  rfl

lemma _root_.MonoidHom.compAddChar_injective_left (ψ : AddChar A M) (hψ : Surjective ψ) :
    Injective fun f : M →* N ↦ f.compAddChar ψ := by
  rintro f g h; rw [DFunLike.ext'_iff] at h ⊢; exact hψ.injective_comp_right h

lemma _root_.MonoidHom.compAddChar_injective_right (f : M →* N) (hf : Injective f) :
    Injective fun ψ : AddChar B M ↦ f.compAddChar ψ := by
  rintro ψ χ h; rw [DFunLike.ext'_iff] at h ⊢; exact hf.comp_left h

/-- Composing an `AddChar` with an `AddMonoidHom` yields another `AddChar`. -/
def compAddMonoidHom (φ : AddChar B M) (f : A →+ B) : AddChar A M :=
  toAddMonoidHomEquiv.symm (φ.toAddMonoidHom.comp f)

@[simp, norm_cast]
lemma coe_compAddMonoidHom (φ : AddChar B M) (f : A →+ B) : φ.compAddMonoidHom f = φ ∘ f := rfl

@[simp] lemma compAddMonoidHom_apply (ψ : AddChar B M) (f : A →+ B)
    (a : A) : ψ.compAddMonoidHom f a = ψ (f a) := rfl

lemma compAddMonoidHom_injective_left (f : A →+ B) (hf : Surjective f) :
    Injective fun ψ : AddChar B M ↦ ψ.compAddMonoidHom f := by
  rintro ψ χ h; rw [DFunLike.ext'_iff] at h ⊢; exact hf.injective_comp_right h

lemma compAddMonoidHom_injective_right (ψ : AddChar B M) (hψ : Injective ψ) :
    Injective fun f : A →+ B ↦ ψ.compAddMonoidHom f := by
  rintro f g h
  rw [DFunLike.ext'_iff] at h ⊢; exact hψ.comp_left h

lemma eq_one_iff : ψ = 1 ↔ ∀ x, ψ x = 1 := DFunLike.ext_iff
lemma ne_one_iff : ψ ≠ 1 ↔ ∃ x, ψ x ≠ 1 := DFunLike.ne_iff

/-- An additive character is *nontrivial* if it takes a value `≠ 1`. -/
@[deprecated (since := "2024-06-06")]
def IsNontrivial (ψ : AddChar A M) : Prop := ∃ a : A, ψ a ≠ 1
#align add_char.is_nontrivial AddChar.IsNontrivial

set_option linter.deprecated false in
/-- An additive character is nontrivial iff it is not the trivial character. -/
@[deprecated ne_one_iff (since := "2024-06-06")]
lemma isNontrivial_iff_ne_trivial (ψ : AddChar A M) : IsNontrivial ψ ↔ ψ ≠ 1 :=
  not_forall.symm.trans (DFunLike.ext_iff (f := ψ) (g := 1)).symm.not

#align add_char.is_nontrivial_iff_ne_trivial AddChar.isNontrivial_iff_ne_trivial

end Basic

section toCommMonoid

variable {A M : Type*} [AddMonoid A] [CommMonoid M]

/-- When `M` is commutative, `AddChar A M` is a commutative monoid. -/
instance instCommMonoid : CommMonoid (AddChar A M) := toMonoidHomEquiv.commMonoid

@[simp, norm_cast] lemma coe_mul (ψ χ : AddChar A M) : ⇑(ψ * χ) = ψ * χ := rfl
@[simp, norm_cast] lemma coe_pow (ψ : AddChar A M) (n : ℕ) : ⇑(ψ ^ n) = ψ ^ n := rfl
@[simp, norm_cast] lemma mul_apply (ψ φ : AddChar A M) (a : A) : (ψ * φ) a = ψ a * φ a := rfl
@[simp, norm_cast] lemma pow_apply (ψ : AddChar A M) (n : ℕ) (a : A) : (ψ ^ n) a = (ψ a) ^ n := rfl

/-- The natural equivalence to `(Multiplicative A →* M)` is a monoid isomorphism. -/
def toMonoidHomMulEquiv : AddChar A M ≃* (Multiplicative A →* M) :=
  { toMonoidHomEquiv with map_mul' := fun φ ψ ↦ by rfl }

/-- Additive characters `A → M` are the same thing as additive homomorphisms from `A` to
`Additive M`. -/
def toAddMonoidAddEquiv : Additive (AddChar A M) ≃+ (A →+ Additive M) :=
  { toAddMonoidHomEquiv with map_add' := fun φ ψ ↦ by rfl }

end toCommMonoid

/-!
## Additive characters of additive abelian groups
-/
section fromAddCommGroup

variable {A M : Type*} [AddCommGroup A] [CommMonoid M]

/-- The additive characters on a commutative additive group form a commutative group.

Note that the inverse is defined using negation on the domain; we do not assume `M` has an
inversion operation for the definition (but see `AddChar.map_neg_eq_inv` below). -/
instance instCommGroup : CommGroup (AddChar A M) :=
  { instCommMonoid with
    inv := fun ψ ↦ ψ.compAddMonoidHom negAddMonoidHom
    mul_left_inv := fun ψ ↦ by ext1 x; simp [negAddMonoidHom, ← map_add_eq_mul]}
#align add_char.comm_group AddChar.instCommGroup
#align add_char.has_inv AddChar.instCommGroup

@[simp] lemma inv_apply (ψ : AddChar A M) (x : A) : ψ⁻¹ x = ψ (-x) := rfl
#align add_char.inv_apply AddChar.inv_apply

end fromAddCommGroup

section fromAddGrouptoCommMonoid

/-- The values of an additive character on an additive group are units. -/
lemma val_isUnit {A M} [AddGroup A] [Monoid M] (φ : AddChar A M) (a : A) : IsUnit (φ a) :=
  IsUnit.map φ.toMonoidHom <| Group.isUnit (Multiplicative.ofAdd a)

end fromAddGrouptoCommMonoid

section fromAddGrouptoDivisionMonoid

variable {A M : Type*} [AddGroup A] [DivisionMonoid M]

/-- An additive character maps negatives to inverses (when defined) -/
lemma map_neg_eq_inv (ψ : AddChar A M) (a : A) : ψ (-a) = (ψ a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simp only [← map_add_eq_mul, add_left_neg, map_zero_eq_one]

/-- An additive character maps integer scalar multiples to integer powers. -/
lemma map_zsmul_eq_zpow (ψ : AddChar A M) (n : ℤ) (a : A) : ψ (n • a) = (ψ a) ^ n :=
  ψ.toMonoidHom.map_zpow a n
#align add_char.map_zsmul_zpow AddChar.map_zsmul_eq_zpow

@[deprecated (since := "2024-06-06")] alias map_neg_inv := map_neg_eq_inv
@[deprecated (since := "2024-06-06")] alias map_zsmul_zpow := map_zsmul_eq_zpow

end fromAddGrouptoDivisionMonoid

section fromAddGrouptoDivisionCommMonoid

variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

lemma inv_apply' (ψ : AddChar A M) (x : A) : ψ⁻¹ x = (ψ x)⁻¹ := by rw [inv_apply, map_neg_eq_inv]

lemma map_sub_eq_div (ψ : AddChar A M) (a b : A) : ψ (a - b) = ψ a / ψ b :=
  ψ.toMonoidHom.map_div _ _

lemma injective_iff {ψ : AddChar A M} : Injective ψ ↔ ∀ ⦃x⦄, ψ x = 1 → x = 0 :=
  ψ.toMonoidHom.ker_eq_bot_iff.symm.trans eq_bot_iff

end fromAddGrouptoDivisionCommMonoid

/-!
## Additive characters of rings
-/
section Ring

-- The domain and target of our additive characters. Now we restrict to a ring in the domain.
variable {R M : Type*} [Ring R] [CommMonoid M]

/-- Define the multiplicative shift of an additive character.
This satisfies `mulShift ψ a x = ψ (a * x)`. -/
def mulShift (ψ : AddChar R M) (r : R) : AddChar R M :=
  ψ.compAddMonoidHom (AddMonoidHom.mulLeft r)
#align add_char.mul_shift AddChar.mulShift

@[simp] lemma mulShift_apply {ψ : AddChar R M} {r : R} {x : R} : mulShift ψ r x = ψ (r * x) :=
  rfl
#align add_char.mul_shift_apply AddChar.mulShift_apply

/-- `ψ⁻¹ = mulShift ψ (-1))`. -/
theorem inv_mulShift (ψ : AddChar R M) : ψ⁻¹ = mulShift ψ (-1) := by
  ext
  rw [inv_apply, mulShift_apply, neg_mul, one_mul]
#align add_char.inv_mul_shift AddChar.inv_mulShift

/-- If `n` is a natural number, then `mulShift ψ n x = (ψ x) ^ n`. -/
theorem mulShift_spec' (ψ : AddChar R M) (n : ℕ) (x : R) : mulShift ψ n x = ψ x ^ n := by
  rw [mulShift_apply, ← nsmul_eq_mul, map_nsmul_eq_pow]
#align add_char.mul_shift_spec' AddChar.mulShift_spec'

/-- If `n` is a natural number, then `ψ ^ n = mulShift ψ n`. -/
theorem pow_mulShift (ψ : AddChar R M) (n : ℕ) : ψ ^ n = mulShift ψ n := by
  ext x
  rw [pow_apply, ← mulShift_spec']
#align add_char.pow_mul_shift AddChar.pow_mulShift

/-- The product of `mulShift ψ r` and `mulShift ψ s` is `mulShift ψ (r + s)`. -/
theorem mulShift_mul (ψ : AddChar R M) (r s : R) :
    mulShift ψ r * mulShift ψ s = mulShift ψ (r + s) := by
  ext
  rw [mulShift_apply, right_distrib, map_add_eq_mul]; norm_cast
#align add_char.mul_shift_mul AddChar.mulShift_mul

lemma mulShift_mulShift (ψ : AddChar R M) (r s : R) :
    mulShift (mulShift ψ r) s = mulShift ψ (r * s) := by
  ext
  simp only [mulShift_apply, mul_assoc]

/-- `mulShift ψ 0` is the trivial character. -/
@[simp]
theorem mulShift_zero (ψ : AddChar R M) : mulShift ψ 0 = 1 := by
  ext; rw [mulShift_apply, zero_mul, map_zero_eq_one, one_apply]
#align add_char.mul_shift_zero AddChar.mulShift_zero

@[simp]
lemma mulShift_one (ψ : AddChar R M) : mulShift ψ 1 = ψ := by
  ext; rw [mulShift_apply, one_mul]

lemma mulShift_unit_eq_one_iff (ψ : AddChar R M) {u : R} (hu : IsUnit u) :
    ψ.mulShift u = 1 ↔ ψ = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · ext1 y
    rw [show y = u * (hu.unit⁻¹ * y) by rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]]
    simpa only [mulShift_apply] using DFunLike.ext_iff.mp h (hu.unit⁻¹ * y)
  · rintro rfl
    ext1 y
    rw [mulShift_apply, one_apply, one_apply]

end Ring

end AddChar
