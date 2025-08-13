/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes Hölzl, Chris Hughes, Jens Wagemaker, Jon Eugster
-/
import Mathlib.Algebra.Group.Commute.Defs

/-!
# Units (i.e., invertible elements) of a monoid

An element of a `Monoid` is a unit if it has a two-sided inverse.

## Main declarations

* `Units M`: the group of units (i.e., invertible elements) of a monoid.
* `IsUnit x`: a predicate asserting that `x` is a unit (i.e., invertible element) of a monoid.

For both declarations, there is an additive counterpart: `AddUnits` and `IsAddUnit`.
See also `Prime`, `Associated`, and `Irreducible` in `Mathlib/Algebra/Associated.lean`.

## Notation

We provide `Mˣ` as notation for `Units M`,
resembling the notation $R^{\times}$ for the units of a ring, which is common in mathematics.

## TODO

The results here should be used to golf the basic `Group` lemmas.
-/

assert_not_exists Multiplicative MonoidWithZero DenselyOrdered

open Function

universe u

variable {α : Type u}

/-- Units of a `Monoid`, bundled version. Notation: `αˣ`.

An element of a `Monoid` is a unit if it has a two-sided inverse.
This version bundles the inverse element so that it can be computed.
For a predicate see `IsUnit`. -/
structure Units (α : Type u) [Monoid α] where
  /-- The underlying value in the base `Monoid`. -/
  val : α
  /-- The inverse value of `val` in the base `Monoid`. -/
  inv : α
  /-- `inv` is the right inverse of `val` in the base `Monoid`. -/
  val_inv : val * inv = 1
  /-- `inv` is the left inverse of `val` in the base `Monoid`. -/
  inv_val : inv * val = 1

attribute [coe] Units.val

@[inherit_doc]
postfix:1024 "ˣ" => Units

-- We don't provide notation for the additive version, because its use is somewhat rare.
/-- Units of an `AddMonoid`, bundled version.

An element of an `AddMonoid` is a unit if it has a two-sided additive inverse.
This version bundles the inverse element so that it can be computed.
For a predicate see `isAddUnit`. -/
structure AddUnits (α : Type u) [AddMonoid α] where
  /-- The underlying value in the base `AddMonoid`. -/
  val : α
  /-- The additive inverse value of `val` in the base `AddMonoid`. -/
  neg : α
  /-- `neg` is the right additive inverse of `val` in the base `AddMonoid`. -/
  val_neg : val + neg = 0
  /-- `neg` is the left additive inverse of `val` in the base `AddMonoid`. -/
  neg_val : neg + val = 0

attribute [to_additive] Units
attribute [coe] AddUnits.val

namespace Units
section Monoid
variable [Monoid α]

-- Porting note: unclear whether this should be a `CoeHead` or `CoeTail`
/-- A unit can be interpreted as a term in the base `Monoid`. -/
@[to_additive /-- An additive unit can be interpreted as a term in the base `AddMonoid`. -/]
instance : CoeHead αˣ α :=
  ⟨val⟩

/-- The inverse of a unit in a `Monoid`. -/
@[to_additive /-- The additive inverse of an additive unit in an `AddMonoid`. -/]
instance instInv : Inv αˣ :=
  ⟨fun u => ⟨u.2, u.1, u.4, u.3⟩⟩
attribute [instance] AddUnits.instNeg

/-- See Note [custom simps projection] -/
@[to_additive
/-- See Note [custom simps projection] -/]
def Simps.val_inv (u : αˣ) : α := ↑(u⁻¹)

initialize_simps_projections Units (as_prefix val, val_inv → null, inv → val_inv, as_prefix val_inv)

initialize_simps_projections AddUnits
  (as_prefix val, val_neg → null, neg → val_neg, as_prefix val_neg)

@[to_additive]
theorem val_mk (a : α) (b h₁ h₂) : ↑(Units.mk a b h₁ h₂) = a :=
  rfl

@[to_additive]
theorem val_injective : Function.Injective (val : αˣ → α)
  | ⟨v, i₁, vi₁, iv₁⟩, ⟨v', i₂, vi₂, iv₂⟩, e => by
    simp only at e; subst v'; congr
    simpa only [iv₂, vi₁, one_mul, mul_one] using mul_assoc i₂ v i₁

@[to_additive (attr := ext)]
theorem ext {u v : αˣ} (huv : u.val = v.val) : u = v := val_injective huv

@[to_additive (attr := norm_cast)]
theorem val_inj {a b : αˣ} : (a : α) = b ↔ a = b :=
  val_injective.eq_iff

@[to_additive (attr := deprecated val_inj (since := "2025-06-21"))] alias eq_iff := val_inj

/-- Units have decidable equality if the base `Monoid` has decidable equality. -/
@[to_additive /-- Additive units have decidable equality
if the base `AddMonoid` has decidable equality. -/]
instance [DecidableEq α] : DecidableEq αˣ := fun _ _ => decidable_of_iff' _ Units.ext_iff

@[to_additive (attr := simp)]
theorem mk_val (u : αˣ) (y h₁ h₂) : mk (u : α) y h₁ h₂ = u :=
  ext rfl

/-- Copy a unit, adjusting definition equalities. -/
@[to_additive (attr := simps) /-- Copy an `AddUnit`, adjusting definitional equalities. -/]
def copy (u : αˣ) (val : α) (hv : val = u) (inv : α) (hi : inv = ↑u⁻¹) : αˣ :=
  { val, inv, inv_val := hv.symm ▸ hi.symm ▸ u.inv_val, val_inv := hv.symm ▸ hi.symm ▸ u.val_inv }

@[to_additive]
theorem copy_eq (u : αˣ) (val hv inv hi) : u.copy val hv inv hi = u :=
  ext hv

/-- Units of a monoid have an induced multiplication. -/
@[to_additive /-- Additive units of an additive monoid have an induced addition. -/]
instance : Mul αˣ where
  mul u₁ u₂ :=
    ⟨u₁.val * u₂.val, u₂.inv * u₁.inv,
      by rw [mul_assoc, ← mul_assoc u₂.val, val_inv, one_mul, val_inv],
      by rw [mul_assoc, ← mul_assoc u₁.inv, inv_val, one_mul, inv_val]⟩

/-- Units of a monoid have a unit -/
@[to_additive /-- Additive units of an additive monoid have a zero. -/]
instance : One αˣ where
  one := ⟨1, 1, one_mul 1, one_mul 1⟩

/-- Units of a monoid have a multiplication and multiplicative identity. -/
@[to_additive
/-- Additive units of an additive monoid have an addition and an additive identity. -/]
instance instMulOneClass : MulOneClass αˣ where
  one_mul u := ext <| one_mul (u : α)
  mul_one u := ext <| mul_one (u : α)

/-- Units of a monoid are inhabited because `1` is a unit. -/
@[to_additive
/-- Additive units of an additive monoid are inhabited because `0` is an additive unit. -/]
instance : Inhabited αˣ :=
  ⟨1⟩

/-- Units of a monoid have a representation of the base value in the `Monoid`. -/
@[to_additive /-- Additive units of an additive monoid have a representation of the base value in
the `AddMonoid`. -/]
instance [Repr α] : Repr αˣ :=
  ⟨reprPrec ∘ val⟩

variable (a b : αˣ) {u : αˣ}

@[to_additive (attr := simp, norm_cast)]
theorem val_mul : (↑(a * b) : α) = a * b :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem val_one : ((1 : αˣ) : α) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1 := by rw [← Units.val_one, val_inj]

@[to_additive (attr := simp)]
theorem inv_mk (x y : α) (h₁ h₂) : (mk x y h₁ h₂)⁻¹ = mk y x h₂ h₁ :=
  rfl

@[to_additive (attr := simp)]
theorem inv_eq_val_inv : a.inv = ((a⁻¹ : αˣ) : α) :=
  rfl

@[to_additive (attr := simp)]
theorem inv_mul : (↑a⁻¹ * a : α) = 1 :=
  inv_val _

@[to_additive (attr := simp)]
theorem mul_inv : (a * ↑a⁻¹ : α) = 1 :=
  val_inv _

@[to_additive] lemma commute_coe_inv : Commute (a : α) ↑a⁻¹ := by
  rw [Commute, SemiconjBy, inv_mul, mul_inv]

@[to_additive] lemma commute_inv_coe : Commute ↑a⁻¹ (a : α) := a.commute_coe_inv.symm

@[to_additive]
theorem inv_mul_of_eq {a : α} (h : ↑u = a) : ↑u⁻¹ * a = 1 := by rw [← h, u.inv_mul]

@[to_additive]
theorem mul_inv_of_eq {a : α} (h : ↑u = a) : a * ↑u⁻¹ = 1 := by rw [← h, u.mul_inv]

@[to_additive (attr := simp)]
theorem mul_inv_cancel_left (a : αˣ) (b : α) : (a : α) * (↑a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv, one_mul]

@[to_additive (attr := simp)]
theorem inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ : α) * (a * b) = b := by
  rw [← mul_assoc, inv_mul, one_mul]

@[to_additive]
theorem inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩

@[to_additive]
instance instMonoid : Monoid αˣ :=
  { (inferInstance : MulOneClass αˣ) with
    mul_assoc := fun _ _ _ => ext <| mul_assoc _ _ _,
    npow := fun n a ↦
      { val := a ^ n
        inv := a⁻¹ ^ n
        val_inv := by rw [← a.commute_coe_inv.mul_pow]; simp
        inv_val := by rw [← a.commute_inv_coe.mul_pow]; simp }
    npow_zero := fun a ↦ by ext; simp
    npow_succ := fun n a ↦ by ext; simp [pow_succ] }

/-- Units of a monoid have division -/
@[to_additive /-- Additive units of an additive monoid have subtraction. -/]
instance : Div αˣ where
  div := fun a b ↦
    { val := a * b⁻¹
      inv := b * a⁻¹
      val_inv := by rw [mul_assoc, inv_mul_cancel_left, mul_inv]
      inv_val := by rw [mul_assoc, inv_mul_cancel_left, mul_inv] }

/-- Units of a monoid form a `DivInvMonoid`. -/
@[to_additive /-- Additive units of an additive monoid form a `SubNegMonoid`. -/]
instance instDivInvMonoid : DivInvMonoid αˣ where
  zpow := fun n a ↦ match n, a with
    | Int.ofNat n, a => a ^ n
    | Int.negSucc n, a => (a ^ n.succ)⁻¹
  zpow_zero' := fun a ↦ by simp
  zpow_succ' := fun n a ↦ by simp [pow_succ]
  zpow_neg' := fun n a ↦ by simp

/-- Units of a monoid form a group. -/
@[to_additive /-- Additive units of an additive monoid form an additive group. -/]
instance instGroup : Group αˣ where
  inv_mul_cancel := fun u => ext u.inv_val

/-- Units of a commutative monoid form a commutative group. -/
@[to_additive /-- Additive units of an additive commutative monoid form
an additive commutative group. -/]
instance instCommGroupUnits {α} [CommMonoid α] : CommGroup αˣ where
  mul_comm := fun _ _ => ext <| mul_comm _ _

@[to_additive (attr := simp, norm_cast)]
lemma val_pow_eq_pow_val (n : ℕ) : ↑(a ^ n) = (a ^ n : α) := rfl

@[to_additive (attr := simp, norm_cast)]
lemma inv_pow_eq_pow_inv (n : ℕ) : ↑(a ^ n)⁻¹ = (a⁻¹ ^ n : α) := rfl

end Monoid

section DivisionMonoid
variable [DivisionMonoid α]

@[to_additive (attr := simp, norm_cast)] lemma val_inv_eq_inv_val (u : αˣ) : ↑u⁻¹ = (u⁻¹ : α) :=
  Eq.symm <| inv_eq_of_mul_eq_one_right u.mul_inv

@[to_additive (attr := simp, norm_cast)]
lemma val_div_eq_div_val : ∀ u₁ u₂ : αˣ, ↑(u₁ / u₂) = (u₁ / u₂ : α) := by simp [div_eq_mul_inv]

end DivisionMonoid
end Units

/-- For `a, b` in a `CommMonoid` such that `a * b = 1`, makes a unit out of `a`. -/
@[to_additive
  /-- For `a, b` in an `AddCommMonoid` such that `a + b = 0`, makes an addUnit out of `a`. -/]
def Units.mkOfMulEqOne [CommMonoid α] (a b : α) (hab : a * b = 1) : αˣ :=
  ⟨a, b, hab, (mul_comm b a).trans hab⟩

@[to_additive (attr := simp)]
theorem Units.val_mkOfMulEqOne [CommMonoid α] {a b : α} (h : a * b = 1) :
    (Units.mkOfMulEqOne a b h : α) = a :=
  rfl

section Monoid

variable [Monoid α] {a : α}

/-- Partial division, denoted `a /ₚ u`. It is defined when the
  second argument is invertible, and unlike the division operator
  in `DivisionRing` it is not totalized at zero. -/
def divp (a : α) (u : Units α) : α :=
  a * (u⁻¹ : αˣ)

@[inherit_doc]
infixl:70 " /ₚ " => divp

@[simp]
theorem divp_self (u : αˣ) : (u : α) /ₚ u = 1 :=
  Units.mul_inv _

@[simp]
theorem divp_one (a : α) : a /ₚ 1 = a :=
  mul_one _

theorem divp_assoc (a b : α) (u : αˣ) : a * b /ₚ u = a * (b /ₚ u) :=
  mul_assoc _ _ _

/-- `field_simp` needs the reverse direction of `divp_assoc` to move all `/ₚ` to the right. -/
@[field_simps]
theorem divp_assoc' (x y : α) (u : αˣ) : x * (y /ₚ u) = x * y /ₚ u :=
  (divp_assoc _ _ _).symm

@[simp]
theorem divp_inv (u : αˣ) : a /ₚ u⁻¹ = a * u :=
  rfl

@[simp]
theorem divp_mul_cancel (a : α) (u : αˣ) : a /ₚ u * u = a :=
  (mul_assoc _ _ _).trans <| by rw [Units.inv_mul, mul_one]

@[simp]
theorem mul_divp_cancel (a : α) (u : αˣ) : a * u /ₚ u = a :=
  (mul_assoc _ _ _).trans <| by rw [Units.mul_inv, mul_one]

@[field_simps]
theorem divp_divp_eq_divp_mul (x : α) (u₁ u₂ : αˣ) : x /ₚ u₁ /ₚ u₂ = x /ₚ (u₂ * u₁) := by
  simp only [divp, mul_inv_rev, Units.val_mul, mul_assoc]

@[simp]
theorem one_divp (u : αˣ) : 1 /ₚ u = ↑u⁻¹ :=
  one_mul _

/-- Used for `field_simp` to deal with inverses of units. -/
@[field_simps]
theorem inv_eq_one_divp (u : αˣ) : ↑u⁻¹ = 1 /ₚ u := by rw [one_divp]

/-- `field_simp` moves division inside `αˣ` to the right, and this lemma
lifts the calculation to `α`.
-/
@[field_simps]
theorem val_div_eq_divp (u₁ u₂ : αˣ) : ↑(u₁ / u₂) = ↑u₁ /ₚ u₂ := by
  rw [divp, division_def, Units.val_mul]

end Monoid

/-!
# `IsUnit` predicate
-/

section IsUnit

variable {M : Type*} {N : Type*}

/-- An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse.
The actual definition says that `a` is equal to some `u : Mˣ`, where
`Mˣ` is a bundled version of `IsUnit`. -/
@[to_additive /-- An element `a : M` of an `AddMonoid` is an `AddUnit` if it has a two-sided
additive inverse. The actual definition says that `a` is equal to some `u : AddUnits M`,
where `AddUnits M` is a bundled version of `IsAddUnit`. -/]
def IsUnit [Monoid M] (a : M) : Prop :=
  ∃ u : Mˣ, (u : M) = a

/-- See `isUnit_iff_exists_and_exists` for a similar lemma with two existentials. -/
@[to_additive
/-- See `isAddUnit_iff_exists_and_exists` for a similar lemma with two existentials. -/]
lemma isUnit_iff_exists [Monoid M] {x : M} : IsUnit x ↔ ∃ b, x * b = 1 ∧ b * x = 1 := by
  refine ⟨fun ⟨u, hu⟩ => ?_, fun ⟨b, h1b, h2b⟩ => ⟨⟨x, b, h1b, h2b⟩, rfl⟩⟩
  subst x
  exact ⟨u.inv, u.val_inv, u.inv_val⟩

/-- See `isUnit_iff_exists` for a similar lemma with one existential. -/
@[to_additive /-- See `isAddUnit_iff_exists` for a similar lemma with one existential. -/]
theorem isUnit_iff_exists_and_exists [Monoid M] {a : M} :
    IsUnit a ↔ (∃ b, a * b = 1) ∧ (∃ c, c * a = 1) :=
  isUnit_iff_exists.trans
    ⟨fun ⟨b, hba, hab⟩ => ⟨⟨b, hba⟩, ⟨b, hab⟩⟩,
      fun ⟨⟨b, hb⟩, ⟨_, hc⟩⟩ => ⟨b, hb, left_inv_eq_right_inv hc hb ▸ hc⟩⟩

@[to_additive (attr := simp)]
protected theorem Units.isUnit [Monoid M] (u : Mˣ) : IsUnit (u : M) :=
  ⟨u, rfl⟩

@[to_additive (attr := simp, grind)]
theorem isUnit_one [Monoid M] : IsUnit (1 : M) :=
  ⟨1, rfl⟩

@[to_additive]
theorem isUnit_of_mul_eq_one [CommMonoid M] (a b : M) (h : a * b = 1) : IsUnit a :=
  ⟨Units.mkOfMulEqOne a b h, rfl⟩

@[to_additive]
theorem isUnit_of_mul_eq_one_right [CommMonoid M] (a b : M) (h : a * b = 1) : IsUnit b := by
  rw [mul_comm] at h
  exact isUnit_of_mul_eq_one b a h

section Monoid
variable [Monoid M] {a b : M}

@[to_additive IsAddUnit.exists_neg]
lemma IsUnit.exists_right_inv (h : IsUnit a) : ∃ b, a * b = 1 := by
  rcases h with ⟨⟨a, b, hab, _⟩, rfl⟩
  exact ⟨b, hab⟩

@[to_additive IsAddUnit.exists_neg']
lemma IsUnit.exists_left_inv {a : M} (h : IsUnit a) : ∃ b, b * a = 1 := by
  rcases h with ⟨⟨a, b, _, hba⟩, rfl⟩
  exact ⟨b, hba⟩

@[to_additive] lemma IsUnit.mul : IsUnit a → IsUnit b → IsUnit (a * b) := by
  rintro ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, rfl⟩

@[to_additive] lemma IsUnit.pow (n : ℕ) : IsUnit a → IsUnit (a ^ n) := by
  rintro ⟨u, rfl⟩; exact ⟨u ^ n, rfl⟩

@[to_additive (attr := simp)]
lemma isUnit_iff_eq_one [Subsingleton Mˣ] {x : M} : IsUnit x ↔ x = 1 :=
  ⟨fun ⟨u, hu⟩ ↦ by rw [← hu, Subsingleton.elim u 1, Units.val_one], fun h ↦ h ▸ isUnit_one⟩

end Monoid

@[to_additive]
theorem isUnit_iff_exists_inv [CommMonoid M] {a : M} : IsUnit a ↔ ∃ b, a * b = 1 :=
  ⟨fun h => h.exists_right_inv, fun ⟨b, hab⟩ => isUnit_of_mul_eq_one _ b hab⟩

@[to_additive]
theorem isUnit_iff_exists_inv' [CommMonoid M] {a : M} : IsUnit a ↔ ∃ b, b * a = 1 := by
  simp [isUnit_iff_exists_inv, mul_comm]

/-- Multiplication by a `u : Mˣ` on the right doesn't affect `IsUnit`. -/
@[to_additive (attr := simp)
/-- Addition of a `u : AddUnits M` on the right doesn't affect `IsAddUnit`. -/]
theorem Units.isUnit_mul_units [Monoid M] (a : M) (u : Mˣ) : IsUnit (a * u) ↔ IsUnit a :=
  Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (a * ↑u * ↑u⁻¹) := by exists v * u⁻¹; rw [← hv, Units.val_mul]
      rwa [mul_assoc, Units.mul_inv, mul_one] at this)
    fun v => v.mul u.isUnit

/-- Multiplication by a `u : Mˣ` on the left doesn't affect `IsUnit`. -/
@[to_additive (attr := simp)
/-- Addition of a `u : AddUnits M` on the left doesn't affect `IsAddUnit`. -/]
theorem Units.isUnit_units_mul {M : Type*} [Monoid M] (u : Mˣ) (a : M) :
    IsUnit (↑u * a) ↔ IsUnit a :=
  Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (↑u⁻¹ * (↑u * a)) := by exists u⁻¹ * v; rw [← hv, Units.val_mul]
      rwa [← mul_assoc, Units.inv_mul, one_mul] at this)
    u.isUnit.mul

@[to_additive]
theorem isUnit_of_mul_isUnit_left [CommMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit x :=
  let ⟨z, hz⟩ := isUnit_iff_exists_inv.1 hu
  isUnit_iff_exists_inv.2 ⟨y * z, by rwa [← mul_assoc]⟩

@[to_additive]
theorem isUnit_of_mul_isUnit_right [CommMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit y :=
  @isUnit_of_mul_isUnit_left _ _ y x <| by rwa [mul_comm]

namespace IsUnit

@[to_additive (attr := simp, grind =)]
theorem mul_iff [CommMonoid M] {x y : M} : IsUnit (x * y) ↔ IsUnit x ∧ IsUnit y :=
  ⟨fun h => ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩,
   fun h => IsUnit.mul h.1 h.2⟩

section Monoid

variable [Monoid M] {a b : M}

/-- The element of the group of units, corresponding to an element of a monoid which is a unit. When
`α` is a `DivisionMonoid`, use `IsUnit.unit'` instead. -/
@[to_additive /-- The element of the additive group of additive units, corresponding to an element
of an additive monoid which is an additive unit. When `α` is a `SubtractionMonoid`, use
`IsAddUnit.addUnit'` instead. -/]
protected noncomputable def unit (h : IsUnit a) : Mˣ :=
  (Classical.choose h).copy a (Classical.choose_spec h).symm _ rfl

@[to_additive (attr := simp)]
theorem unit_of_val_units {a : Mˣ} (h : IsUnit (a : M)) : h.unit = a :=
  Units.ext rfl

@[to_additive (attr := simp)]
theorem unit_spec (h : IsUnit a) : ↑h.unit = a :=
  rfl

@[to_additive (attr := simp)]
theorem unit_one (h : IsUnit (1 : M)) : h.unit = 1 :=
  Units.ext rfl

@[to_additive]
theorem unit_mul (ha : IsUnit a) (hb : IsUnit b) : (ha.mul hb).unit = ha.unit * hb.unit :=
  Units.ext rfl

@[to_additive]
theorem unit_pow (h : IsUnit a) (n : ℕ) : (h.pow n).unit = h.unit ^ n :=
  Units.ext rfl

@[to_additive (attr := simp)]
theorem val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1 :=
  Units.mul_inv _

@[to_additive (attr := simp)]
theorem mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1 := by
  rw [← h.unit.mul_inv]; congr

/-- `IsUnit x` is decidable if we can decide if `x` comes from `Mˣ`. -/
@[to_additive /-- `IsAddUnit x` is decidable if we can decide if `x` comes from `AddUnits M`. -/]
instance (x : M) [h : Decidable (∃ u : Mˣ, ↑u = x)] : Decidable (IsUnit x) :=
  h

end Monoid

section DivisionMonoid
variable [DivisionMonoid α] {a b c : α}

@[to_additive (attr := simp)]
protected theorem inv_mul_cancel : IsUnit a → a⁻¹ * a = 1 := by
  rintro ⟨u, rfl⟩
  rw [← Units.val_inv_eq_inv_val, Units.inv_mul]

@[to_additive (attr := simp)]
protected theorem mul_inv_cancel : IsUnit a → a * a⁻¹ = 1 := by
  rintro ⟨u, rfl⟩
  rw [← Units.val_inv_eq_inv_val, Units.mul_inv]

/-- The element of the group of units, corresponding to an element of a monoid which is a unit. As
opposed to `IsUnit.unit`, the inverse is computable and comes from the inversion on `α`. This is
useful to transfer properties of inversion in `Units α` to `α`. See also `toUnits`. -/
@[to_additive (attr := simps val)
/-- The element of the additive group of additive units, corresponding to an element of
an additive monoid which is an additive unit. As opposed to `IsAddUnit.addUnit`, the negation is
computable and comes from the negation on `α`. This is useful to transfer properties of negation
in `AddUnits α` to `α`. See also `toAddUnits`. -/]
def unit' (h : IsUnit a) : αˣ := ⟨a, a⁻¹, h.mul_inv_cancel, h.inv_mul_cancel⟩

@[to_additive] lemma val_inv_unit' (h : IsUnit a) : ↑(h.unit'⁻¹) = a⁻¹ := rfl

@[to_additive (attr := simp)]
protected lemma mul_inv_cancel_left (h : IsUnit a) : ∀ b, a * (a⁻¹ * b) = b :=
  h.unit'.mul_inv_cancel_left

@[to_additive (attr := simp)]
protected lemma inv_mul_cancel_left (h : IsUnit a) : ∀ b, a⁻¹ * (a * b) = b :=
  h.unit'.inv_mul_cancel_left

@[to_additive]
protected lemma div_self (h : IsUnit a) : a / a = 1 := by rw [div_eq_mul_inv, h.mul_inv_cancel]

@[to_additive]
lemma inv (h : IsUnit a) : IsUnit a⁻¹ := by
  obtain ⟨u, hu⟩ := h
  rw [← hu, ← Units.val_inv_eq_inv_val]
  exact Units.isUnit _

@[to_additive]
lemma unit_inv (h : IsUnit a) : h.inv.unit = h.unit⁻¹ :=
  Units.ext h.unit.val_inv_eq_inv_val.symm

@[to_additive]
lemma div (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a / b) := by
  rw [div_eq_mul_inv]; exact ha.mul hb.inv

@[to_additive]
lemma unit_div (ha : IsUnit a) (hb : IsUnit b) : (ha.div hb).unit = ha.unit / hb.unit :=
  Units.ext (ha.unit.val_div_eq_div_val hb.unit).symm

@[to_additive]
protected lemma div_mul_cancel_right (h : IsUnit b) (a : α) : b / (a * b) = a⁻¹ := by
  rw [div_eq_mul_inv, mul_inv_rev, h.mul_inv_cancel_left]

@[to_additive]
protected lemma mul_div_mul_right (h : IsUnit c) (a b : α) : a * c / (b * c) = a / b := by
  simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, h.mul_inv_cancel_left]

end DivisionMonoid

section DivisionCommMonoid
variable [DivisionCommMonoid α] {a c : α}

@[to_additive]
protected lemma div_mul_cancel_left (h : IsUnit a) (b : α) : a / (a * b) = b⁻¹ := by
  rw [mul_comm, h.div_mul_cancel_right]

@[to_additive]
protected lemma mul_div_mul_left (h : IsUnit c) (a b : α) : c * a / (c * b) = a / b := by
  rw [mul_comm c, mul_comm c, h.mul_div_mul_right]

end DivisionCommMonoid
end IsUnit

@[field_simps]
lemma divp_eq_div [DivisionMonoid α] (a : α) (u : αˣ) : a /ₚ u = a / u := by
  rw [div_eq_mul_inv, divp, u.val_inv_eq_inv_val]

@[to_additive]
lemma Group.isUnit [Group α] (a : α) : IsUnit a :=
  ⟨⟨a, a⁻¹, mul_inv_cancel _, inv_mul_cancel _⟩, rfl⟩

-- namespace
end IsUnit

-- section
section NoncomputableDefs

variable {M : Type*}

/-- Constructs an inv operation for a `Monoid` consisting only of units. -/
noncomputable def invOfIsUnit [Monoid M] (h : ∀ a : M, IsUnit a) : Inv M where
  inv := fun a => ↑(h a).unit⁻¹

/-- Constructs a `Group` structure on a `Monoid` consisting only of units. -/
noncomputable def groupOfIsUnit [hM : Monoid M] (h : ∀ a : M, IsUnit a) : Group M :=
  { hM with
    toInv := invOfIsUnit h,
    inv_mul_cancel := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }

/-- Constructs a `CommGroup` structure on a `CommMonoid` consisting only of units. -/
noncomputable def commGroupOfIsUnit [hM : CommMonoid M] (h : ∀ a : M, IsUnit a) : CommGroup M :=
  { hM with
    toInv := invOfIsUnit h,
    inv_mul_cancel := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }

end NoncomputableDefs
