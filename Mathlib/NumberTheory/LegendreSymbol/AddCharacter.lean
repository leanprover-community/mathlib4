/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.FieldTheory.Finite.Trace

#align_import number_theory.legendre_symbol.add_character from "leanprover-community/mathlib"@"0723536a0522d24fc2f159a096fb3304bef77472"

/-!
# Additive characters of finite rings and fields

Let `R` be a finite commutative ring. An *additive character* of `R` with values
in another commutative ring `R'` is simply a morphism from the additive group
of `R` into the multiplicative monoid of `R'`.

The additive characters on `R` with values in `R'` form a commutative group.

We use the namespace `AddChar`.

## Main definitions and results

We define `mulShift ψ a`, where `ψ : AddChar R R'` and `a : R`, to be the
character defined by `x ↦ ψ (a * x)`. An additive character `ψ` is *primitive*
if `mulShift ψ a` is trivial only when `a = 0`.

We show that when `ψ` is primitive, then the map `a ↦ mulShift ψ a` is injective
(`AddChar.to_mulShift_inj_of_isPrimitive`) and that `ψ` is primitive when `R` is a field
and `ψ` is nontrivial (`AddChar.IsNontrivial.isPrimitive`).

We also show that there are primitive additive characters on `R` (with suitable
target `R'`) when `R` is a field or `R = ZMod n` (`AddChar.primitiveCharFiniteField`
and `AddChar.primitiveZModChar`).

Finally, we show that the sum of all character values is zero when the character
is nontrivial (and the target is a domain); see `AddChar.sum_eq_zero_of_isNontrivial`.

## Tags

additive character
-/


universe u v

/-!
### Definitions related to and results on additive characters
-/


section AddCharDef

-- The domain of our additive characters
variable (R : Type u) [AddMonoid R]

-- The target
variable (R' : Type v) [CommMonoid R']

/-- Define `AddChar R R'` as `(Multiplicative R) →* R'`.
The definition works for an additive monoid `R` and a monoid `R'`,
but we will restrict to the case that both are commutative rings below.
We assume right away that `R'` is commutative, so that `AddChar R R'` carries
a structure of commutative monoid.
The trivial additive character (sending everything to `1`) is `(1 : AddChar R R').` -/
def AddChar : Type max u v :=
  Multiplicative R →* R'
#align add_char AddChar

end AddCharDef

namespace AddChar

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/5020): added
section DerivedInstances

variable (R : Type u) [AddMonoid R] (R' : Type v) [CommMonoid R']

instance : CommMonoid (AddChar R R') :=
  inferInstanceAs (CommMonoid (Multiplicative R →* R'))

instance : Inhabited (AddChar R R') :=
  inferInstanceAs (Inhabited (Multiplicative R →* R'))

end DerivedInstances

section CoeToFun

variable {R : Type u} [AddMonoid R] {R' : Type v} [CommMonoid R']

/-- Interpret an additive character as a monoid homomorphism. -/
def toMonoidHom : AddChar R R' → Multiplicative R →* R' :=
  id
#align add_char.to_monoid_hom AddChar.toMonoidHom

open Multiplicative

-- Porting note: added.
@[coe]
def toFun (ψ : AddChar R R') (x : R) : R' := ψ.toMonoidHom (ofAdd x)

/-- Define coercion to a function so that it includes the move from `R` to `Multiplicative R`.
After we have proved the API lemmas below, we don't need to worry about writing `ofAdd a`
when we want to apply an additive character. -/
instance hasCoeToFun : CoeFun (AddChar R R') fun _ => R → R' where
  coe := toFun
#align add_char.has_coe_to_fun AddChar.hasCoeToFun

theorem coe_to_fun_apply (ψ : AddChar R R') (a : R) : ψ a = ψ.toMonoidHom (ofAdd a) :=
  rfl
#align add_char.coe_to_fun_apply AddChar.coe_to_fun_apply

-- porting note: added
theorem mul_apply (ψ φ : AddChar R R') (a : R) : (ψ * φ) a = ψ a * φ a :=
  rfl

-- porting note: added
@[simp]
theorem one_apply (a : R) : (1 : AddChar R R') a = 1 := rfl

instance monoidHomClass : MonoidHomClass (AddChar R R') (Multiplicative R) R' :=
  MonoidHom.monoidHomClass
#align add_char.monoid_hom_class AddChar.monoidHomClass

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/5229): added.
@[ext]
theorem ext (f g : AddChar R R') (h : ∀ x : R, f x = g x) : f = g :=
  MonoidHom.ext h

/-- An additive character maps `0` to `1`. -/
@[simp]
theorem map_zero_one (ψ : AddChar R R') : ψ 0 = 1 := by rw [coe_to_fun_apply, ofAdd_zero, map_one]
                                                        -- 🎉 no goals
#align add_char.map_zero_one AddChar.map_zero_one

/-- An additive character maps sums to products. -/
@[simp]
theorem map_add_mul (ψ : AddChar R R') (x y : R) : ψ (x + y) = ψ x * ψ y := by
  rw [coe_to_fun_apply, coe_to_fun_apply _ x, coe_to_fun_apply _ y, ofAdd_add, map_mul]
  -- 🎉 no goals
#align add_char.map_add_mul AddChar.map_add_mul

/-- An additive character maps multiples by natural numbers to powers. -/
@[simp]
theorem map_nsmul_pow (ψ : AddChar R R') (n : ℕ) (x : R) : ψ (n • x) = ψ x ^ n := by
  rw [coe_to_fun_apply, coe_to_fun_apply _ x, ofAdd_nsmul, map_pow]
  -- 🎉 no goals
#align add_char.map_nsmul_pow AddChar.map_nsmul_pow

end CoeToFun

section GroupStructure

open Multiplicative

variable {R : Type u} [AddCommGroup R] {R' : Type v} [CommMonoid R']

/-- An additive character on a commutative additive group has an inverse.

Note that this is a different inverse to the one provided by `MonoidHom.inv`,
as it acts on the domain instead of the codomain. -/
instance hasInv : Inv (AddChar R R') :=
  ⟨fun ψ => ψ.comp invMonoidHom⟩
#align add_char.has_inv AddChar.hasInv

theorem inv_apply (ψ : AddChar R R') (x : R) : ψ⁻¹ x = ψ (-x) :=
  rfl
#align add_char.inv_apply AddChar.inv_apply

/-- An additive character maps multiples by integers to powers. -/
@[simp]
theorem map_zsmul_zpow {R' : Type v} [CommGroup R'] (ψ : AddChar R R') (n : ℤ) (x : R) :
    ψ (n • x) = ψ x ^ n := by rw [coe_to_fun_apply, coe_to_fun_apply _ x, ofAdd_zsmul, map_zpow]
                              -- 🎉 no goals
#align add_char.map_zsmul_zpow AddChar.map_zsmul_zpow

/-- The additive characters on a commutative additive group form a commutative group. -/
instance commGroup : CommGroup (AddChar R R') :=
  { MonoidHom.commMonoid with
    inv := Inv.inv
    mul_left_inv := fun ψ => by
      ext x
      -- ⊢ ↑(ψ⁻¹ * ψ) x = ↑1 x
      rw [AddChar.mul_apply, AddChar.one_apply, inv_apply, ← map_add_mul, add_left_neg,
        map_zero_one] }
#align add_char.comm_group AddChar.commGroup

end GroupStructure

section Additive

-- The domain and target of our additive characters. Now we restrict to rings on both sides.
variable {R : Type u} [CommRing R] {R' : Type v} [CommRing R']

/-- An additive character is *nontrivial* if it takes a value `≠ 1`. -/
def IsNontrivial (ψ : AddChar R R') : Prop :=
  ∃ a : R, ψ a ≠ 1
#align add_char.is_nontrivial AddChar.IsNontrivial

/-- An additive character is nontrivial iff it is not the trivial character. -/
theorem isNontrivial_iff_ne_trivial (ψ : AddChar R R') : IsNontrivial ψ ↔ ψ ≠ 1 := by
  refine' not_forall.symm.trans (Iff.not _)
  -- ⊢ (∀ (x : R), ↑ψ x = 1) ↔ ψ = 1
  rw [FunLike.ext_iff]
  -- ⊢ (∀ (x : R), ↑ψ x = 1) ↔ ∀ (x : Multiplicative R), ↑ψ x = ↑1 x
  rfl
  -- 🎉 no goals
#align add_char.is_nontrivial_iff_ne_trivial AddChar.isNontrivial_iff_ne_trivial

/-- Define the multiplicative shift of an additive character.
This satisfies `mulShift ψ a x = ψ (a * x)`. -/
def mulShift (ψ : AddChar R R') (a : R) : AddChar R R' :=
  ψ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft a))
#align add_char.mul_shift AddChar.mulShift

@[simp]
theorem mulShift_apply {ψ : AddChar R R'} {a : R} {x : R} : mulShift ψ a x = ψ (a * x) :=
  rfl
#align add_char.mul_shift_apply AddChar.mulShift_apply

/-- `ψ⁻¹ = mulShift ψ (-1))`. -/
theorem inv_mulShift (ψ : AddChar R R') : ψ⁻¹ = mulShift ψ (-1) := by
  ext
  -- ⊢ ↑ψ⁻¹ x✝ = ↑(mulShift ψ (-1)) x✝
  rw [inv_apply, mulShift_apply, neg_mul, one_mul]
  -- 🎉 no goals
#align add_char.inv_mul_shift AddChar.inv_mulShift

/-- If `n` is a natural number, then `mulShift ψ n x = (ψ x) ^ n`. -/
theorem mulShift_spec' (ψ : AddChar R R') (n : ℕ) (x : R) : mulShift ψ n x = ψ x ^ n := by
  rw [mulShift_apply, ← nsmul_eq_mul, map_nsmul_pow]
  -- 🎉 no goals
#align add_char.mul_shift_spec' AddChar.mulShift_spec'

/-- If `n` is a natural number, then `ψ ^ n = mulShift ψ n`. -/
theorem pow_mulShift (ψ : AddChar R R') (n : ℕ) : ψ ^ n = mulShift ψ n := by
  ext x
  -- ⊢ ↑(ψ ^ n) x = ↑(mulShift ψ ↑n) x
  rw [show (ψ ^ n) x = ψ x ^ n from rfl, ← mulShift_spec']
  -- 🎉 no goals
#align add_char.pow_mul_shift AddChar.pow_mulShift

/-- The product of `mulShift ψ a` and `mulShift ψ b` is `mulShift ψ (a + b)`. -/
theorem mulShift_mul (ψ : AddChar R R') (a b : R) :
    mulShift ψ a * mulShift ψ b = mulShift ψ (a + b) := by
  ext
  -- ⊢ ↑(mulShift ψ a * mulShift ψ b) x✝ = ↑(mulShift ψ (a + b)) x✝
  rw [mulShift_apply, right_distrib, map_add_mul]; norm_cast
  -- ⊢ ↑(mulShift ψ a * mulShift ψ b) x✝ = ↑ψ (a * x✝) * ↑ψ (b * x✝)
                                                   -- 🎉 no goals
#align add_char.mul_shift_mul AddChar.mulShift_mul

/-- `mulShift ψ 0` is the trivial character. -/
@[simp]
theorem mulShift_zero (ψ : AddChar R R') : mulShift ψ 0 = 1 := by
  ext
  -- ⊢ ↑(mulShift ψ 0) x✝ = ↑1 x✝
  rw [mulShift_apply, zero_mul, map_zero_one]; norm_cast
  -- ⊢ 1 = ↑1 x✝
                                               -- 🎉 no goals
#align add_char.mul_shift_zero AddChar.mulShift_zero

/-- An additive character is *primitive* iff all its multiplicative shifts by nonzero
elements are nontrivial. -/
def IsPrimitive (ψ : AddChar R R') : Prop :=
  ∀ a : R, a ≠ 0 → IsNontrivial (mulShift ψ a)
#align add_char.is_primitive AddChar.IsPrimitive

/-- The map associating to `a : R` the multiplicative shift of `ψ` by `a`
is injective when `ψ` is primitive. -/
theorem to_mulShift_inj_of_isPrimitive {ψ : AddChar R R'} (hψ : IsPrimitive ψ) :
    Function.Injective ψ.mulShift := by
  intro a b h
  -- ⊢ a = b
  apply_fun fun x => x * mulShift ψ (-b) at h
  -- ⊢ a = b
  simp only [mulShift_mul, mulShift_zero, add_right_neg] at h
  -- ⊢ a = b
  have h₂ := hψ (a + -b)
  -- ⊢ a = b
  rw [h, isNontrivial_iff_ne_trivial, ← sub_eq_add_neg, sub_ne_zero] at h₂
  -- ⊢ a = b
  exact not_not.mp fun h => h₂ h rfl
  -- 🎉 no goals
#align add_char.to_mul_shift_inj_of_is_primitive AddChar.to_mulShift_inj_of_isPrimitive

-- `AddCommGroup.equiv_direct_sum_zmod_of_fintype`
-- gives the structure theorem for finite abelian groups.
-- This could be used to show that the map above is a bijection.
-- We leave this for a later occasion.
/-- When `R` is a field `F`, then a nontrivial additive character is primitive -/
theorem IsNontrivial.isPrimitive {F : Type u} [Field F] {ψ : AddChar F R'} (hψ : IsNontrivial ψ) :
    IsPrimitive ψ := by
  intro a ha
  -- ⊢ IsNontrivial (mulShift ψ a)
  cases' hψ with x h
  -- ⊢ IsNontrivial (mulShift ψ a)
  use a⁻¹ * x
  -- ⊢ ↑(mulShift ψ a) (a⁻¹ * x) ≠ 1
  rwa [mulShift_apply, mul_inv_cancel_left₀ ha]
  -- 🎉 no goals
#align add_char.is_nontrivial.is_primitive AddChar.IsNontrivial.isPrimitive

-- Porting note: Using `structure` gives a timeout, see
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/mysterious.20finsupp.20related.20timeout/near/365719262 and
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/mysterious.20finsupp.20related.20timeout
-- In Lean4, `set_option genInjectivity false in` may solve this issue.
-- can't prove that they always exist
/-- Definition for a primitive additive character on a finite ring `R` into a cyclotomic extension
of a field `R'`. It records which cyclotomic extension it is, the character, and the
fact that the character is primitive. -/
-- @[nolint has_nonempty_instance] -- Porting note: removed
def PrimitiveAddChar (R : Type u) [CommRing R] (R' : Type v) [Field R'] :=
  Σ n : ℕ+, Σ' char : AddChar R (CyclotomicField n R'), IsPrimitive char
#align add_char.primitive_add_char AddChar.PrimitiveAddChar

/-- The first projection from `PrimitiveAddChar`, giving the cyclotomic field. -/
noncomputable def PrimitiveAddChar.n {R : Type u} [CommRing R] {R' : Type v} [Field R'] :
    PrimitiveAddChar R R' → ℕ+ := fun χ => χ.1
#align add_char.primitive_add_char.n AddChar.PrimitiveAddChar.n

/-- The second projection from `PrimitiveAddChar`, giving the character. -/
noncomputable def PrimitiveAddChar.char {R : Type u} [CommRing R] {R' : Type v} [Field R'] :
    ∀ χ : PrimitiveAddChar R R', AddChar R (CyclotomicField χ.n R') := fun χ => χ.2.1
#align add_char.primitive_add_char.char AddChar.PrimitiveAddChar.char

/-- The third projection from `PrimitiveAddChar`, showing that `χ.2` is primitive. -/
theorem PrimitiveAddChar.prim {R : Type u} [CommRing R] {R' : Type v} [Field R'] :
    ∀ χ : PrimitiveAddChar R R', IsPrimitive χ.char := fun χ => χ.2.2
#align add_char.primitive_add_char.prim AddChar.PrimitiveAddChar.prim

/-!
### Additive characters on `ZMod n`
-/


variable {C : Type v} [CommRing C]

section ZModCharDef

open Multiplicative

-- so we can write simply `toAdd`, which we need here again
/-- We can define an additive character on `ZMod n` when we have an `n`th root of unity `ζ : C`. -/
def zmodChar (n : ℕ+) {ζ : C} (hζ : ζ ^ (n : ℕ) = 1) : AddChar (ZMod n) C where
  toFun := fun a : Multiplicative (ZMod n) => ζ ^ a.toAdd.val
  map_one' := by simp only [toAdd_one, ZMod.val_zero, pow_zero]
                 -- 🎉 no goals
  map_mul' x y := by
    dsimp only
    -- ⊢ ζ ^ ZMod.val (↑toAdd (x * y)) = ζ ^ ZMod.val (↑toAdd x) * ζ ^ ZMod.val (↑toA …
    rw [toAdd_mul, ← pow_add, ZMod.val_add (toAdd x) (toAdd y), ← pow_eq_pow_mod _ hζ]
    -- 🎉 no goals
#align add_char.zmod_char AddChar.zmodChar

/-- The additive character on `ZMod n` defined using `ζ` sends `a` to `ζ^a`. -/
theorem zmodChar_apply {n : ℕ+} {ζ : C} (hζ : ζ ^ (n : ℕ) = 1) (a : ZMod n) :
    zmodChar n hζ a = ζ ^ a.val :=
  rfl
#align add_char.zmod_char_apply AddChar.zmodChar_apply

theorem zmodChar_apply' {n : ℕ+} {ζ : C} (hζ : ζ ^ (n : ℕ) = 1) (a : ℕ) :
    zmodChar n hζ a = ζ ^ a := by
  rw [pow_eq_pow_mod a hζ, zmodChar_apply, ZMod.val_nat_cast a]
  -- 🎉 no goals
#align add_char.zmod_char_apply' AddChar.zmodChar_apply'

end ZModCharDef

/-- An additive character on `ZMod n` is nontrivial iff it takes a value `≠ 1` on `1`. -/
theorem zmod_char_isNontrivial_iff (n : ℕ+) (ψ : AddChar (ZMod n) C) :
    IsNontrivial ψ ↔ ψ 1 ≠ 1 := by
  refine' ⟨_, fun h => ⟨1, h⟩⟩
  -- ⊢ IsNontrivial ψ → ↑ψ 1 ≠ 1
  contrapose!
  -- ⊢ ↑ψ 1 = 1 → ¬IsNontrivial ψ
  rintro h₁ ⟨a, ha⟩
  -- ⊢ False
  have ha₁ : a = a.val • (1 : ZMod ↑n) := by
    rw [nsmul_eq_mul, mul_one]; exact (ZMod.nat_cast_zmod_val a).symm
  rw [ha₁, map_nsmul_pow, h₁, one_pow] at ha
  -- ⊢ False
  exact ha rfl
  -- 🎉 no goals
#align add_char.zmod_char_is_nontrivial_iff AddChar.zmod_char_isNontrivial_iff

/-- A primitive additive character on `ZMod n` takes the value `1` only at `0`. -/
theorem IsPrimitive.zmod_char_eq_one_iff (n : ℕ+) {ψ : AddChar (ZMod n) C} (hψ : IsPrimitive ψ)
    (a : ZMod n) : ψ a = 1 ↔ a = 0 := by
  refine' ⟨fun h => not_imp_comm.mp (hψ a) _, fun ha => by rw [ha, map_zero_one]⟩
  -- ⊢ ¬IsNontrivial (mulShift ψ a)
  rw [zmod_char_isNontrivial_iff n (mulShift ψ a), mulShift_apply, mul_one, h, Classical.not_not]
  -- 🎉 no goals
#align add_char.is_primitive.zmod_char_eq_one_iff AddChar.IsPrimitive.zmod_char_eq_one_iff

/-- The converse: if the additive character takes the value `1` only at `0`,
then it is primitive. -/
theorem zmod_char_primitive_of_eq_one_only_at_zero (n : ℕ) (ψ : AddChar (ZMod n) C)
    (hψ : ∀ a, ψ a = 1 → a = 0) : IsPrimitive ψ := by
  refine' fun a ha => (isNontrivial_iff_ne_trivial _).mpr fun hf => _
  -- ⊢ False
  have h : mulShift ψ a 1 = (1 : AddChar (ZMod n) C) (1 : ZMod n) :=
    congr_fun (congr_arg (↑) hf) 1
  rw [mulShift_apply, mul_one] at h; norm_cast at h
  -- ⊢ False
                                     -- ⊢ False
  exact ha (hψ a h)
  -- 🎉 no goals
#align add_char.zmod_char_primitive_of_eq_one_only_at_zero AddChar.zmod_char_primitive_of_eq_one_only_at_zero

/-- The additive character on `ZMod n` associated to a primitive `n`th root of unity
is primitive -/
theorem zmodChar_primitive_of_primitive_root (n : ℕ+) {ζ : C} (h : IsPrimitiveRoot ζ n) :
    IsPrimitive (zmodChar n ((IsPrimitiveRoot.iff_def ζ n).mp h).left) := by
  apply zmod_char_primitive_of_eq_one_only_at_zero
  -- ⊢ ∀ (a : ZMod ↑n), ↑(zmodChar n (_ : ζ ^ ↑n = 1)) a = 1 → a = 0
  intro a ha
  -- ⊢ a = 0
  rw [zmodChar_apply, ← pow_zero ζ] at ha
  -- ⊢ a = 0
  exact (ZMod.val_eq_zero a).mp (IsPrimitiveRoot.pow_inj h (ZMod.val_lt a) n.pos ha)
  -- 🎉 no goals
#align add_char.zmod_char_primitive_of_primitive_root AddChar.zmodChar_primitive_of_primitive_root

/-- There is a primitive additive character on `ZMod n` if the characteristic of the target
does not divide `n` -/
noncomputable def primitiveZModChar (n : ℕ+) (F' : Type v) [Field F'] (h : (n : F') ≠ 0) :
    PrimitiveAddChar (ZMod n) F' :=
  haveI : NeZero ((n : ℕ) : F') := ⟨h⟩
  ⟨n, zmodChar n (IsCyclotomicExtension.zeta_pow n F' _),
    zmodChar_primitive_of_primitive_root n (IsCyclotomicExtension.zeta_spec n F' _)⟩
#align add_char.primitive_zmod_char AddChar.primitiveZModChar

/-!
### Existence of a primitive additive character on a finite field
-/


/-- There is a primitive additive character on the finite field `F` if the characteristic
of the target is different from that of `F`.
We obtain it as the composition of the trace from `F` to `ZMod p` with a primitive
additive character on `ZMod p`, where `p` is the characteristic of `F`. -/
noncomputable def primitiveCharFiniteField (F F' : Type*) [Field F] [Fintype F] [Field F']
    (h : ringChar F' ≠ ringChar F) : PrimitiveAddChar F F' := by
  let p := ringChar F
  -- ⊢ PrimitiveAddChar F F'
  haveI hp : Fact p.Prime := ⟨CharP.char_is_prime F _⟩
  -- ⊢ PrimitiveAddChar F F'
  let pp := p.toPNat hp.1.pos
  -- ⊢ PrimitiveAddChar F F'
  have hp₂ : ¬ringChar F' ∣ p := by
    cases' CharP.char_is_prime_or_zero F' (ringChar F') with hq hq
    · exact mt (Nat.Prime.dvd_iff_eq hp.1 (Nat.Prime.ne_one hq)).mp h.symm
    · rw [hq]
      exact fun hf => Nat.Prime.ne_zero hp.1 (zero_dvd_iff.mp hf)
  let ψ := primitiveZModChar pp F' (neZero_iff.mp (NeZero.of_not_dvd F' hp₂))
  -- ⊢ PrimitiveAddChar F F'
  letI : Algebra (ZMod p) F := ZMod.algebra _ _
  -- ⊢ PrimitiveAddChar F F'
  let ψ' := ψ.char.comp (AddMonoidHom.toMultiplicative (Algebra.trace (ZMod p) F).toAddMonoidHom)
  -- ⊢ PrimitiveAddChar F F'
  have hψ' : IsNontrivial ψ' := by
    obtain ⟨a, ha⟩ := FiniteField.trace_to_zmod_nondegenerate F one_ne_zero
    rw [one_mul] at ha
    exact ⟨a, fun hf => ha <| (ψ.prim.zmod_char_eq_one_iff pp <| Algebra.trace (ZMod p) F a).mp hf⟩
  exact ⟨ψ.n, ψ', hψ'.isPrimitive⟩
  -- 🎉 no goals
#align add_char.primitive_char_finite_field AddChar.primitiveCharFiniteField

/-!
### The sum of all character values
-/


open scoped BigOperators

variable [Fintype R]

/-- The sum over the values of a nontrivial additive character vanishes if the target ring
is a domain. -/
theorem sum_eq_zero_of_isNontrivial [IsDomain R'] {ψ : AddChar R R'} (hψ : IsNontrivial ψ) :
    ∑ a, ψ a = 0 := by
  rcases hψ with ⟨b, hb⟩
  -- ⊢ ∑ a : R, ↑ψ a = 0
  have h₁ : ∑ a : R, ψ (b + a) = ∑ a : R, ψ a :=
    Fintype.sum_bijective _ (AddGroup.addLeft_bijective b) _ _ fun x => rfl
  simp_rw [map_add_mul] at h₁
  -- ⊢ ∑ a : R, ↑ψ a = 0
  have h₂ : ∑ a : R, ψ a = Finset.univ.sum ↑ψ := rfl
  -- ⊢ ∑ a : R, ↑ψ a = 0
  rw [← Finset.mul_sum, h₂] at h₁
  -- ⊢ ∑ a : R, ↑ψ a = 0
  exact eq_zero_of_mul_eq_self_left hb h₁
  -- 🎉 no goals
#align add_char.sum_eq_zero_of_is_nontrivial AddChar.sum_eq_zero_of_isNontrivial

/-- The sum over the values of the trivial additive character is the cardinality of the source. -/
theorem sum_eq_card_of_is_trivial {ψ : AddChar R R'} (hψ : ¬IsNontrivial ψ) :
    ∑ a, ψ a = Fintype.card R := by
  simp only [IsNontrivial] at hψ
  -- ⊢ ∑ a : R, ↑ψ a = ↑(Fintype.card R)
  push_neg at hψ
  -- ⊢ ∑ a : R, ↑ψ a = ↑(Fintype.card R)
  simp only [hψ, Finset.sum_const, Nat.smul_one_eq_coe]
  -- ⊢ ↑(Finset.card Finset.univ) = ↑(Fintype.card R)
  rfl
  -- 🎉 no goals
#align add_char.sum_eq_card_of_is_trivial AddChar.sum_eq_card_of_is_trivial

/-- The sum over the values of `mulShift ψ b` for `ψ` primitive is zero when `b ≠ 0`
and `#R` otherwise. -/
theorem sum_mulShift [DecidableEq R] [IsDomain R'] {ψ : AddChar R R'} (b : R)
    (hψ : IsPrimitive ψ) : ∑ x : R, ψ (x * b) = if b = 0 then Fintype.card R else 0 := by
  split_ifs with h
  -- ⊢ ∑ x : R, ↑ψ (x * b) = ↑(Fintype.card R)
  · -- case `b = 0`
    simp only [h, mul_zero, map_zero_one, Finset.sum_const, Nat.smul_one_eq_coe]
    -- ⊢ ↑(Finset.card Finset.univ) = ↑(Fintype.card R)
    rfl
    -- 🎉 no goals
  · -- case `b ≠ 0`
    simp_rw [mul_comm]
    -- ⊢ ∑ x : R, ↑ψ (b * x) = ↑0
    exact_mod_cast sum_eq_zero_of_isNontrivial (hψ b h)
    -- 🎉 no goals
#align add_char.sum_mul_shift AddChar.sum_mulShift

end Additive

end AddChar
