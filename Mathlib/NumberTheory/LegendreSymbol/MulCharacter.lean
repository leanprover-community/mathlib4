/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Fintype.Units

#align_import number_theory.legendre_symbol.mul_character from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Multiplicative characters of finite rings and fields

Let `R` and `R'` be a commutative rings.
A *multiplicative character* of `R` with values in `R'` is a morphism of
monoids from the multiplicative monoid of `R` into that of `R'`
that sends non-units to zero.

We use the namespace `MulChar` for the definitions and results.

## Main results

We show that the multiplicative characters form a group (if `R'` is commutative);
see `MulChar.commGroup`. We also provide an equivalence with the
homomorphisms `Rˣ →* R'ˣ`; see `MulChar.equivToUnitHom`.

We define a multiplicative character to be *quadratic* if its values
are among `0`, `1` and `-1`, and we prove some properties of quadratic characters.

Finally, we show that the sum of all values of a nontrivial multiplicative
character vanishes; see `MulChar.IsNontrivial.sum_eq_zero`.

## Tags

multiplicative character
-/


/-!
### Definitions related to multiplicative characters

Even though the intended use is when domain and target of the characters
are commutative rings, we define them in the more general setting when
the domain is a commutative monoid and the target is a commutative monoid
with zero. (We need a zero in the target, since non-units are supposed
to map to zero.)

In this setting, there is an equivalence between multiplicative characters
`R → R'` and group homomorphisms `Rˣ → R'ˣ`, and the multiplicative characters
have a natural structure as a commutative group.
-/


section Defi

-- The domain of our multiplicative characters
variable (R : Type*) [CommMonoid R]

-- The target
variable (R' : Type*) [CommMonoidWithZero R']

/-- Define a structure for multiplicative characters.
A multiplicative character from a commutative monoid `R` to a commutative monoid with zero `R'`
is a homomorphism of (multiplicative) monoids that sends non-units to zero. -/
structure MulChar extends MonoidHom R R' where
  map_nonunit' : ∀ a : R, ¬IsUnit a → toFun a = 0
#align mul_char MulChar

instance MulChar.instFunLike : FunLike (MulChar R R') R R' :=
  ⟨fun χ => χ.toFun,
    fun χ₀ χ₁ h => by cases χ₀; cases χ₁; congr; apply MonoidHom.ext (fun _ => congr_fun h _)⟩

/-- This is the corresponding extension of `MonoidHomClass`. -/
class MulCharClass (F : Type*) (R R' : outParam Type*) [CommMonoid R]
  [CommMonoidWithZero R'] [FunLike F R R'] extends MonoidHomClass F R R' : Prop where
  map_nonunit : ∀ (χ : F) {a : R} (_ : ¬IsUnit a), χ a = 0
#align mul_char_class MulCharClass

initialize_simps_projections MulChar (toFun → apply, -toMonoidHom)

attribute [simp] MulCharClass.map_nonunit

end Defi

namespace MulChar

section Group

-- The domain of our multiplicative characters
variable {R : Type*} [CommMonoid R]

-- The target
variable {R' : Type*} [CommMonoidWithZero R']

variable (R R') in
/-- The trivial multiplicative character. It takes the value `0` on non-units and
the value `1` on units. -/
@[simps]
noncomputable def trivial : MulChar R R' where
  toFun := by classical exact fun x => if IsUnit x then 1 else 0
  map_nonunit' := by
    intro a ha
    simp only [ha, if_false]
  map_one' := by simp only [isUnit_one, if_true]
  map_mul' := by
    intro x y
    classical
      simp only [IsUnit.mul_iff, boole_mul]
      split_ifs <;> tauto
#align mul_char.trivial MulChar.trivial

@[simp]
theorem coe_mk (f : R →* R') (hf) : (MulChar.mk f hf : R → R') = f :=
  rfl
#align mul_char.coe_mk MulChar.coe_mk

/-- Extensionality. See `ext` below for the version that will actually be used. -/
theorem ext' {χ χ' : MulChar R R'} (h : ∀ a, χ a = χ' a) : χ = χ' := by
  cases χ
  cases χ'
  congr
  exact MonoidHom.ext h
#align mul_char.ext' MulChar.ext'

instance : MulCharClass (MulChar R R') R R' where
  map_mul χ := χ.map_mul'
  map_one χ := χ.map_one'
  map_nonunit χ := χ.map_nonunit' _

theorem map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUnit a) : χ a = 0 :=
  χ.map_nonunit' a ha
#align mul_char.map_nonunit MulChar.map_nonunit

/-- Extensionality. Since `MulChar`s always take the value zero on non-units, it is sufficient
to compare the values on units. -/
@[ext]
theorem ext {χ χ' : MulChar R R'} (h : ∀ a : Rˣ, χ a = χ' a) : χ = χ' := by
  apply ext'
  intro a
  by_cases ha : IsUnit a
  · exact h ha.unit
  · rw [map_nonunit χ ha, map_nonunit χ' ha]
#align mul_char.ext MulChar.ext

theorem ext_iff {χ χ' : MulChar R R'} : χ = χ' ↔ ∀ a : Rˣ, χ a = χ' a :=
  ⟨by
    rintro rfl a
    rfl, ext⟩
#align mul_char.ext_iff MulChar.ext_iff

/-!
### Equivalence of multiplicative characters with homomorphisms on units

We show that restriction / extension by zero gives an equivalence
between `MulChar R R'` and `Rˣ →* R'ˣ`.
-/


/-- Turn a `MulChar` into a homomorphism between the unit groups. -/
def toUnitHom (χ : MulChar R R') : Rˣ →* R'ˣ :=
  Units.map χ
#align mul_char.to_unit_hom MulChar.toUnitHom

theorem coe_toUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(χ.toUnitHom a) = χ a :=
  rfl
#align mul_char.coe_to_unit_hom MulChar.coe_toUnitHom

/-- Turn a homomorphism between unit groups into a `MulChar`. -/
noncomputable def ofUnitHom (f : Rˣ →* R'ˣ) : MulChar R R' where
  toFun := by classical exact fun x => if hx : IsUnit x then f hx.unit else 0
  map_one' := by
    have h1 : (isUnit_one.unit : Rˣ) = 1 := Units.eq_iff.mp rfl
    simp only [h1, dif_pos, Units.val_eq_one, map_one, isUnit_one]
  map_mul' := by
    classical
      intro x y
      by_cases hx : IsUnit x
      · simp only [hx, IsUnit.mul_iff, true_and_iff, dif_pos]
        by_cases hy : IsUnit y
        · simp only [hy, dif_pos]
          have hm : (IsUnit.mul_iff.mpr ⟨hx, hy⟩).unit = hx.unit * hy.unit := Units.eq_iff.mp rfl
          rw [hm, map_mul]
          norm_cast
        · simp only [hy, not_false_iff, dif_neg, mul_zero]
      · simp only [hx, IsUnit.mul_iff, false_and_iff, not_false_iff, dif_neg, zero_mul]
  map_nonunit' := by
    intro a ha
    simp only [ha, not_false_iff, dif_neg]
#align mul_char.of_unit_hom MulChar.ofUnitHom

theorem ofUnitHom_coe (f : Rˣ →* R'ˣ) (a : Rˣ) : ofUnitHom f ↑a = f a := by simp [ofUnitHom]
#align mul_char.of_unit_hom_coe MulChar.ofUnitHom_coe

/-- The equivalence between multiplicative characters and homomorphisms of unit groups. -/
noncomputable def equivToUnitHom : MulChar R R' ≃ (Rˣ →* R'ˣ) where
  toFun := toUnitHom
  invFun := ofUnitHom
  left_inv := by
    intro χ
    ext x
    rw [ofUnitHom_coe, coe_toUnitHom]
  right_inv := by
    intro f
    ext x
    simp only [coe_toUnitHom, ofUnitHom_coe]
#align mul_char.equiv_to_unit_hom MulChar.equivToUnitHom

@[simp]
theorem toUnitHom_eq (χ : MulChar R R') : toUnitHom χ = equivToUnitHom χ :=
  rfl
#align mul_char.to_unit_hom_eq MulChar.toUnitHom_eq

@[simp]
theorem ofUnitHom_eq (χ : Rˣ →* R'ˣ) : ofUnitHom χ = equivToUnitHom.symm χ :=
  rfl
#align mul_char.of_unit_hom_eq MulChar.ofUnitHom_eq

@[simp]
theorem coe_equivToUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(equivToUnitHom χ a) = χ a :=
  coe_toUnitHom χ a
#align mul_char.coe_equiv_to_unit_hom MulChar.coe_equivToUnitHom

@[simp]
theorem equivToUnitHom_symm_coe (f : Rˣ →* R'ˣ) (a : Rˣ) : equivToUnitHom.symm f ↑a = f a :=
  ofUnitHom_coe f a
#align mul_char.equiv_unit_hom_symm_coe MulChar.equivToUnitHom_symm_coe

@[simp]
lemma coe_toMonoidHom [CommMonoid R] (χ : MulChar R R')
    (x : R) : χ.toMonoidHom x = χ x := rfl

/-!
### Commutative group structure on multiplicative characters

The multiplicative characters `R → R'` form a commutative group.
-/


protected theorem map_one (χ : MulChar R R') : χ (1 : R) = 1 :=
  χ.map_one'
#align mul_char.map_one MulChar.map_one

/-- If the domain has a zero (and is nontrivial), then `χ 0 = 0`. -/
protected theorem map_zero {R : Type*} [CommMonoidWithZero R] [Nontrivial R] (χ : MulChar R R') :
    χ (0 : R) = 0 := by rw [map_nonunit χ not_isUnit_zero]
#align mul_char.map_zero MulChar.map_zero

/-- We can convert a multiplicative character into a homomorphism of monoids with zero when
the source has a zero and another element. -/
@[coe, simps]
def toMonoidWithZeroHom {R : Type*} [CommMonoidWithZero R] [Nontrivial R] (χ : MulChar R R') :
    R →*₀ R' where
  toFun := χ.toFun
  map_zero' := χ.map_zero
  map_one' := χ.map_one'
  map_mul' := χ.map_mul'

/-- If the domain is a ring `R`, then `χ (ringChar R) = 0`. -/
theorem map_ringChar {R : Type*} [CommRing R] [Nontrivial R] (χ : MulChar R R') :
    χ (ringChar R) = 0 := by rw [ringChar.Nat.cast_ringChar, χ.map_zero]
#align mul_char.map_ring_char MulChar.map_ringChar

noncomputable instance hasOne : One (MulChar R R') :=
  ⟨trivial R R'⟩
#align mul_char.has_one MulChar.hasOne

noncomputable instance inhabited : Inhabited (MulChar R R') :=
  ⟨1⟩
#align mul_char.inhabited MulChar.inhabited

/-- Evaluation of the trivial character -/
@[simp]
theorem one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1 := by classical exact dif_pos a.isUnit
#align mul_char.one_apply_coe MulChar.one_apply_coe

/-- Evaluation of the trivial character -/
lemma one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R') x = 1 := one_apply_coe hx.unit

/-- Multiplication of multiplicative characters. (This needs the target to be commutative.) -/
def mul (χ χ' : MulChar R R') : MulChar R R' :=
  { χ.toMonoidHom * χ'.toMonoidHom with
    toFun := χ * χ'
    map_nonunit' := fun a ha => by simp only [map_nonunit χ ha, zero_mul, Pi.mul_apply] }
#align mul_char.mul MulChar.mul

instance hasMul : Mul (MulChar R R') :=
  ⟨mul⟩
#align mul_char.has_mul MulChar.hasMul

theorem mul_apply (χ χ' : MulChar R R') (a : R) : (χ * χ') a = χ a * χ' a :=
  rfl
#align mul_char.mul_apply MulChar.mul_apply

@[simp]
theorem coeToFun_mul (χ χ' : MulChar R R') : ⇑(χ * χ') = χ * χ' :=
  rfl
#align mul_char.coe_to_fun_mul MulChar.coeToFun_mul

protected theorem one_mul (χ : MulChar R R') : (1 : MulChar R R') * χ = χ := by
  ext
  simp only [one_mul, Pi.mul_apply, MulChar.coeToFun_mul, MulChar.one_apply_coe]
#align mul_char.one_mul MulChar.one_mul

protected theorem mul_one (χ : MulChar R R') : χ * 1 = χ := by
  ext
  simp only [mul_one, Pi.mul_apply, MulChar.coeToFun_mul, MulChar.one_apply_coe]
#align mul_char.mul_one MulChar.mul_one

/-- The inverse of a multiplicative character. We define it as `inverse ∘ χ`. -/
noncomputable def inv (χ : MulChar R R') : MulChar R R' :=
  { MonoidWithZero.inverse.toMonoidHom.comp χ.toMonoidHom with
    toFun := fun a => MonoidWithZero.inverse (χ a)
    map_nonunit' := fun a ha => by simp [map_nonunit _ ha] }
#align mul_char.inv MulChar.inv

noncomputable instance hasInv : Inv (MulChar R R') :=
  ⟨inv⟩
#align mul_char.has_inv MulChar.hasInv

/-- The inverse of a multiplicative character `χ`, applied to `a`, is the inverse of `χ a`. -/
theorem inv_apply_eq_inv (χ : MulChar R R') (a : R) : χ⁻¹ a = Ring.inverse (χ a) :=
  Eq.refl <| inv χ a
#align mul_char.inv_apply_eq_inv MulChar.inv_apply_eq_inv

/-- The inverse of a multiplicative character `χ`, applied to `a`, is the inverse of `χ a`.
Variant when the target is a field -/
theorem inv_apply_eq_inv' {R' : Type*} [Field R'] (χ : MulChar R R') (a : R) : χ⁻¹ a = (χ a)⁻¹ :=
  (inv_apply_eq_inv χ a).trans <| Ring.inverse_eq_inv (χ a)
#align mul_char.inv_apply_eq_inv' MulChar.inv_apply_eq_inv'

/-- When the domain has a zero, then the inverse of a multiplicative character `χ`,
applied to `a`, is `χ` applied to the inverse of `a`. -/
theorem inv_apply {R : Type*} [CommMonoidWithZero R] (χ : MulChar R R') (a : R) :
    χ⁻¹ a = χ (Ring.inverse a) := by
  by_cases ha : IsUnit a
  · rw [inv_apply_eq_inv]
    have h := IsUnit.map χ ha
    apply_fun (χ a * ·) using IsUnit.mul_right_injective h
    dsimp only
    rw [Ring.mul_inverse_cancel _ h, ← map_mul, Ring.mul_inverse_cancel _ ha, map_one]
  · revert ha
    nontriviality R
    intro ha
    -- `nontriviality R` by itself doesn't do it
    rw [map_nonunit _ ha, Ring.inverse_non_unit a ha, MulChar.map_zero χ]
#align mul_char.inv_apply MulChar.inv_apply

/-- When the domain has a zero, then the inverse of a multiplicative character `χ`,
applied to `a`, is `χ` applied to the inverse of `a`. -/
theorem inv_apply' {R : Type*} [Field R] (χ : MulChar R R') (a : R) : χ⁻¹ a = χ a⁻¹ :=
  (inv_apply χ a).trans <| congr_arg _ (Ring.inverse_eq_inv a)
#align mul_char.inv_apply' MulChar.inv_apply'

/-- The product of a character with its inverse is the trivial character. -/
-- Porting note (#10618): @[simp] can prove this (later)
theorem inv_mul (χ : MulChar R R') : χ⁻¹ * χ = 1 := by
  ext x
  rw [coeToFun_mul, Pi.mul_apply, inv_apply_eq_inv]
  simp only [Ring.inverse_mul_cancel _ (IsUnit.map χ x.isUnit)]
  rw [one_apply_coe]
#align mul_char.inv_mul MulChar.inv_mul

/-- The commutative group structure on `MulChar R R'`. -/
noncomputable instance commGroup : CommGroup (MulChar R R') :=
  { one := 1
    mul := (· * ·)
    inv := Inv.inv
    mul_left_inv := inv_mul
    mul_assoc := by
      intro χ₁ χ₂ χ₃
      ext a
      simp only [mul_assoc, Pi.mul_apply, MulChar.coeToFun_mul]
    mul_comm := by
      intro χ₁ χ₂
      ext a
      simp only [mul_comm, Pi.mul_apply, MulChar.coeToFun_mul]
    one_mul := MulChar.one_mul
    mul_one := MulChar.mul_one }
#align mul_char.comm_group MulChar.commGroup

/-- If `a` is a unit and `n : ℕ`, then `(χ ^ n) a = (χ a) ^ n`. -/
theorem pow_apply_coe (χ : MulChar R R') (n : ℕ) (a : Rˣ) : (χ ^ n) a = χ a ^ n := by
  induction' n with n ih
  · rw [pow_zero, pow_zero, one_apply_coe]
  · rw [pow_succ, pow_succ, mul_apply, ih]
#align mul_char.pow_apply_coe MulChar.pow_apply_coe

/-- If `n` is positive, then `(χ ^ n) a = (χ a) ^ n`. -/
theorem pow_apply' (χ : MulChar R R') {n : ℕ} (hn : n ≠ 0) (a : R) : (χ ^ n) a = χ a ^ n := by
  by_cases ha : IsUnit a
  · exact pow_apply_coe χ n ha.unit
  · rw [map_nonunit (χ ^ n) ha, map_nonunit χ ha, zero_pow hn]
#align mul_char.pow_apply' MulChar.pow_apply'

lemma equivToUnitHom_mul_apply (χ₁ χ₂ : MulChar R R') (a : Rˣ) :
    equivToUnitHom (χ₁ * χ₂) a = equivToUnitHom χ₁ a * equivToUnitHom χ₂ a := by
  apply_fun ((↑) : R'ˣ → R') using Units.ext
  push_cast
  simp_rw [coe_equivToUnitHom]
  rfl

/-- The equivalence between multiplicative characters and homomorphisms of unit groups
as a multiplicative equivalence. -/
noncomputable
def mulEquivToUnitHom : MulChar R R' ≃* (Rˣ →* R'ˣ) :=
  { equivToUnitHom with
    map_mul' := by
      intro χ ψ
      ext
      simp only [Equiv.toFun_as_coe, coe_equivToUnitHom, coeToFun_mul, Pi.mul_apply,
        MonoidHom.mul_apply, Units.val_mul]
  }

end Group


/-!
### Properties of multiplicative characters

We introduce the properties of being nontrivial or quadratic and prove
some basic facts about them.

We now (mostly) assume that the target is a commutative ring.
-/


section Properties

section nontrivial

variable {R : Type*} [CommMonoid R] {R' : Type*} [CommMonoidWithZero R']

/-- A multiplicative character is *nontrivial* if it takes a value `≠ 1` on a unit. -/
def IsNontrivial (χ : MulChar R R') : Prop :=
  ∃ a : Rˣ, χ a ≠ 1
#align mul_char.is_nontrivial MulChar.IsNontrivial

/-- A multiplicative character is nontrivial iff it is not the trivial character. -/
theorem isNontrivial_iff (χ : MulChar R R') : χ.IsNontrivial ↔ χ ≠ 1 := by
  simp only [IsNontrivial, Ne, ext_iff, not_forall, one_apply_coe]
#align mul_char.is_nontrivial_iff MulChar.isNontrivial_iff

end nontrivial

section quadratic_and_comp

variable {R : Type*} [CommMonoid R] {R' : Type*} [CommRing R'] {R'' : Type*} [CommRing R'']

/-- A multiplicative character is *quadratic* if it takes only the values `0`, `1`, `-1`. -/
def IsQuadratic (χ : MulChar R R') : Prop :=
  ∀ a, χ a = 0 ∨ χ a = 1 ∨ χ a = -1
#align mul_char.is_quadratic MulChar.IsQuadratic

/-- If two values of quadratic characters with target `ℤ` agree after coercion into a ring
of characteristic not `2`, then they agree in `ℤ`. -/
theorem IsQuadratic.eq_of_eq_coe {χ : MulChar R ℤ} (hχ : IsQuadratic χ) {χ' : MulChar R' ℤ}
    (hχ' : IsQuadratic χ') [Nontrivial R''] (hR'' : ringChar R'' ≠ 2) {a : R} {a' : R'}
    (h : (χ a : R'') = χ' a') : χ a = χ' a' :=
  Int.cast_injOn_of_ringChar_ne_two hR'' (hχ a) (hχ' a') h
#align mul_char.is_quadratic.eq_of_eq_coe MulChar.IsQuadratic.eq_of_eq_coe

/-- We can post-compose a multiplicative character with a ring homomorphism. -/
@[simps]
def ringHomComp (χ : MulChar R R') (f : R' →+* R'') : MulChar R R'' :=
  { f.toMonoidHom.comp χ.toMonoidHom with
    toFun := fun a => f (χ a)
    map_nonunit' := fun a ha => by simp only [map_nonunit χ ha, map_zero] }
#align mul_char.ring_hom_comp MulChar.ringHomComp

/-- Composition with an injective ring homomorphism preserves nontriviality. -/
theorem IsNontrivial.comp {χ : MulChar R R'} (hχ : χ.IsNontrivial) {f : R' →+* R''}
    (hf : Function.Injective f) : (χ.ringHomComp f).IsNontrivial := by
  obtain ⟨a, ha⟩ := hχ
  use a
  simp_rw [ringHomComp_apply, ← RingHom.map_one f]
  exact fun h => ha (hf h)
#align mul_char.is_nontrivial.comp MulChar.IsNontrivial.comp

/-- Composition with a ring homomorphism preserves the property of being a quadratic character. -/
theorem IsQuadratic.comp {χ : MulChar R R'} (hχ : χ.IsQuadratic) (f : R' →+* R'') :
    (χ.ringHomComp f).IsQuadratic := by
  intro a
  rcases hχ a with (ha | ha | ha) <;> simp [ha]
#align mul_char.is_quadratic.comp MulChar.IsQuadratic.comp

/-- The inverse of a quadratic character is itself. →  -/
theorem IsQuadratic.inv {χ : MulChar R R'} (hχ : χ.IsQuadratic) : χ⁻¹ = χ := by
  ext x
  rw [inv_apply_eq_inv]
  rcases hχ x with (h₀ | h₁ | h₂)
  · rw [h₀, Ring.inverse_zero]
  · rw [h₁, Ring.inverse_one]
  · -- Porting note: was `by norm_cast`
    have : (-1 : R') = (-1 : R'ˣ) := by rw [Units.val_neg, Units.val_one]
    rw [h₂, this, Ring.inverse_unit (-1 : R'ˣ)]
    rfl
#align mul_char.is_quadratic.inv MulChar.IsQuadratic.inv

/-- The square of a quadratic character is the trivial character. -/
theorem IsQuadratic.sq_eq_one {χ : MulChar R R'} (hχ : χ.IsQuadratic) : χ ^ 2 = 1 := by
  rw [← mul_left_inv χ, pow_two, hχ.inv]
#align mul_char.is_quadratic.sq_eq_one MulChar.IsQuadratic.sq_eq_one

/-- The `p`th power of a quadratic character is itself, when `p` is the (prime) characteristic
of the target ring. -/
theorem IsQuadratic.pow_char {χ : MulChar R R'} (hχ : χ.IsQuadratic) (p : ℕ) [hp : Fact p.Prime]
    [CharP R' p] : χ ^ p = χ := by
  ext x
  rw [pow_apply_coe]
  rcases hχ x with (hx | hx | hx) <;> rw [hx]
  · rw [zero_pow (@Fact.out p.Prime).ne_zero]
  · rw [one_pow]
  · exact CharP.neg_one_pow_char R' p
#align mul_char.is_quadratic.pow_char MulChar.IsQuadratic.pow_char

/-- The `n`th power of a quadratic character is the trivial character, when `n` is even. -/
theorem IsQuadratic.pow_even {χ : MulChar R R'} (hχ : χ.IsQuadratic) {n : ℕ} (hn : Even n) :
    χ ^ n = 1 := by
  obtain ⟨n, rfl⟩ := even_iff_two_dvd.mp hn
  rw [pow_mul, hχ.sq_eq_one, one_pow]
#align mul_char.is_quadratic.pow_even MulChar.IsQuadratic.pow_even

/-- The `n`th power of a quadratic character is itself, when `n` is odd. -/
theorem IsQuadratic.pow_odd {χ : MulChar R R'} (hχ : χ.IsQuadratic) {n : ℕ} (hn : Odd n) :
    χ ^ n = χ := by
  obtain ⟨n, rfl⟩ := hn
  rw [pow_add, pow_one, hχ.pow_even (even_two_mul _), one_mul]
#align mul_char.is_quadratic.pow_odd MulChar.IsQuadratic.pow_odd

end quadratic_and_comp

end Properties

/-!
### Multiplicative characters with finite domain
-/

section Finite

variable {M : Type*} [CommMonoid M] [Fintype M] [DecidableEq M]
variable {R : Type*} [CommMonoidWithZero R]

/-- A multiplicative character on a finite commutative monoid has finite (= positive) order. -/
lemma orderOf_pos (χ : MulChar M R) : 0 < orderOf χ := by
  let e := MulChar.mulEquivToUnitHom (R := M) (R' := R)
  rw [← MulEquiv.orderOf_eq e χ]
  have : orderOf (e χ) ∣ Fintype.card Mˣ := by
    refine orderOf_dvd_of_pow_eq_one ?_
    ext1 x
    simp only [MonoidHom.pow_apply, ← map_pow (e χ), pow_card_eq_one, map_one, MonoidHom.one_apply]
  exact Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero Fintype.card_ne_zero this

/-- If `χ` is a multiplicative character on a finite commutative monoid `M`, then `χ ^ #Mˣ = 1`. -/
protected
lemma pow_card_eq_one (χ : MulChar M R) : χ ^ (Fintype.card Mˣ) = 1 := by
  ext1
  rw [pow_apply_coe, ← map_pow, one_apply_coe, ← Units.val_pow_eq_pow_val, pow_card_eq_one,
    Units.val_eq_one.mpr rfl, map_one]

end Finite

section sum

variable {R : Type*} [CommMonoid R] [Fintype R] {R' : Type*} [CommRing R']

/-- The sum over all values of a nontrivial multiplicative character on a finite ring is zero
(when the target is a domain). -/
theorem IsNontrivial.sum_eq_zero [IsDomain R'] {χ : MulChar R R'}
    (hχ : χ.IsNontrivial) : ∑ a, χ a = 0 := by
  rcases hχ with ⟨b, hb⟩
  refine eq_zero_of_mul_eq_self_left hb ?_
  simp only [Finset.mul_sum, ← map_mul]
  exact Fintype.sum_bijective _ (Units.mulLeft_bijective b) _ _ fun x => rfl
#align mul_char.is_nontrivial.sum_eq_zero MulChar.IsNontrivial.sum_eq_zero

/-- The sum over all values of the trivial multiplicative character on a finite ring is
the cardinality of its unit group. -/
theorem sum_one_eq_card_units [DecidableEq R] :
    (∑ a, (1 : MulChar R R') a) = Fintype.card Rˣ := by
  calc
    (∑ a, (1 : MulChar R R') a) = ∑ a : R, if IsUnit a then 1 else 0 :=
      Finset.sum_congr rfl fun a _ => ?_
    _ = ((Finset.univ : Finset R).filter IsUnit).card := Finset.sum_boole _ _
    _ = (Finset.univ.map ⟨((↑) : Rˣ → R), Units.ext⟩).card := ?_
    _ = Fintype.card Rˣ := congr_arg _ (Finset.card_map _)
  · split_ifs with h
    · exact one_apply_coe h.unit
    · exact map_nonunit _ h
  · congr
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and_iff, Finset.mem_map,
      Function.Embedding.coeFn_mk, exists_true_left, IsUnit]
#align mul_char.sum_one_eq_card_units MulChar.sum_one_eq_card_units

end sum

/-!
### Multiplicative characters on rings
-/

section Ring

variable {R R' : Type*} [CommRing R] [CommMonoidWithZero R']

/-- If `χ` is of odd order, then `χ(-1) = 1` -/
lemma val_neg_one_eq_one_of_odd_order {χ : MulChar R R'} {n : ℕ} (hn : Odd n) (hχ : χ ^ n = 1) :
    χ (-1) = 1 := by
  rw [← hn.neg_one_pow, map_pow, ← χ.pow_apply' (Nat.ne_of_odd_add hn), hχ]
  exact MulChar.one_apply_coe (-1)

end Ring
