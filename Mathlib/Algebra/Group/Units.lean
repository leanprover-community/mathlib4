/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes Hölzl, Chris Hughes, Jens Wagemaker, Jon Eugster
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Logic.Nontrivial
import Mathlib.Logic.Unique
import Mathlib.Tactic.Nontriviality

#align_import algebra.group.units from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Units (i.e., invertible elements) of a monoid

An element of a `Monoid` is a unit if it has a two-sided inverse.

## Main declarations

* `Units M`: the group of units (i.e., invertible elements) of a monoid.
* `IsUnit x`: a predicate asserting that `x` is a unit (i.e., invertible element) of a monoid.

For both declarations, there is an additive counterpart: `AddUnits` and `IsAddUnit`.
See also `Prime`, `Associated`, and `Irreducible` in `Mathlib.Algebra.Associated`.

## Notation

We provide `Mˣ` as notation for `Units M`,
resembling the notation $R^{\times}$ for the units of a ring, which is common in mathematics.

-/


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
#align units Units
#align units.val Units.val
#align units.inv Units.inv
#align units.val_inv Units.val_inv
#align units.inv_val Units.inv_val

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
#align add_units AddUnits
#align add_units.val AddUnits.val
#align add_units.neg AddUnits.neg
#align add_units.val_neg AddUnits.val_neg
#align add_units.neg_val AddUnits.neg_val

attribute [to_additive] Units
attribute [coe] AddUnits.val

section HasElem

@[to_additive]
theorem unique_one {α : Type*} [Unique α] [One α] : default = (1 : α) :=
  Unique.default_eq 1
#align unique_has_one unique_one
#align unique_has_zero unique_zero

end HasElem

namespace Units

variable [Monoid α]

-- Porting note: unclear whether this should be a `CoeHead` or `CoeTail`
/-- A unit can be interpreted as a term in the base `Monoid`. -/
@[to_additive "An additive unit can be interpreted as a term in the base `AddMonoid`."]
instance : CoeHead αˣ α :=
  ⟨val⟩

/-- The inverse of a unit in a `Monoid`. -/
@[to_additive "The additive inverse of an additive unit in an `AddMonoid`."]
instance instInv : Inv αˣ :=
  ⟨fun u => ⟨u.2, u.1, u.4, u.3⟩⟩
attribute [instance] AddUnits.instNeg

/- porting note: the result of these definitions is syntactically equal to `Units.val` because of
the way coercions work in Lean 4, so there is no need for these custom `simp` projections. -/
#noalign units.simps.coe
#noalign add_units.simps.coe

/-- See Note [custom simps projection] -/
@[to_additive "See Note [custom simps projection]"]
def Simps.val_inv (u : αˣ) : α := ↑(u⁻¹)
#align units.simps.coe_inv Units.Simps.val_inv
#align add_units.simps.coe_neg AddUnits.Simps.val_neg

initialize_simps_projections Units (as_prefix val, val_inv → null, inv → val_inv, as_prefix val_inv)

initialize_simps_projections AddUnits
  (as_prefix val, val_neg → null, neg → val_neg, as_prefix val_neg)

-- Porting note: removed `simp` tag because of the tautology
@[to_additive]
theorem val_mk (a : α) (b h₁ h₂) : ↑(Units.mk a b h₁ h₂) = a :=
  rfl
#align units.coe_mk Units.val_mk
#align add_units.coe_mk AddUnits.val_mk

@[to_additive (attr := ext)]
theorem ext : Function.Injective (val : αˣ → α)
  | ⟨v, i₁, vi₁, iv₁⟩, ⟨v', i₂, vi₂, iv₂⟩, e => by
    simp only at e; subst v'; congr;
    -- ⊢ { val := v, inv := i₁, val_inv := vi₁, inv_val := iv₁ } = { val := v', inv : …
                    -- ⊢ { val := v, inv := i₁, val_inv := vi₁, inv_val := iv₁ } = { val := v, inv := …
                              -- ⊢ i₁ = i₂
    simpa only [iv₂, vi₁, one_mul, mul_one] using mul_assoc i₂ v i₁
    -- 🎉 no goals
#align units.ext Units.ext
#align add_units.ext AddUnits.ext

@[to_additive (attr := norm_cast)]
theorem eq_iff {a b : αˣ} : (a : α) = b ↔ a = b :=
  ext.eq_iff
#align units.eq_iff Units.eq_iff
#align add_units.eq_iff AddUnits.eq_iff

@[to_additive]
theorem ext_iff {a b : αˣ} : a = b ↔ (a : α) = b :=
  eq_iff.symm
#align units.ext_iff Units.ext_iff
#align add_units.ext_iff AddUnits.ext_iff

/-- Units have decidable equality if the base `Monoid` has decidable equality. -/
@[to_additive "Additive units have decidable equality
if the base `AddMonoid` has deciable equality."]
instance [DecidableEq α] : DecidableEq αˣ := fun _ _ => decidable_of_iff' _ ext_iff

@[to_additive (attr := simp)]
theorem mk_val (u : αˣ) (y h₁ h₂) : mk (u : α) y h₁ h₂ = u :=
  ext rfl
#align units.mk_coe Units.mk_val
#align add_units.mk_coe AddUnits.mk_val

/-- Copy a unit, adjusting definition equalities. -/
@[to_additive (attr := simps) "Copy an `AddUnit`, adjusting definitional equalities."]
def copy (u : αˣ) (val : α) (hv : val = u) (inv : α) (hi : inv = ↑u⁻¹) : αˣ :=
  { val, inv, inv_val := hv.symm ▸ hi.symm ▸ u.inv_val, val_inv := hv.symm ▸ hi.symm ▸ u.val_inv }
#align units.copy Units.copy
#align add_units.copy AddUnits.copy
#align units.coe_copy Units.val_copy
#align add_units.coe_copy AddUnits.val_copy
#align units.coe_inv_copy Units.val_inv_copy
#align add_units.coe_neg_copy AddUnits.val_neg_copy

@[to_additive]
theorem copy_eq (u : αˣ) (val hv inv hi) : u.copy val hv inv hi = u :=
  ext hv
#align units.copy_eq Units.copy_eq
#align add_units.copy_eq AddUnits.copy_eq

/-- Units of a monoid form have a multiplication and multiplicative identity. -/
@[to_additive "Additive units of an additive monoid have an addition and an additive identity."]
instance : MulOneClass αˣ where
  mul u₁ u₂ :=
    ⟨u₁.val * u₂.val, u₂.inv * u₁.inv,
      by rw [mul_assoc, ← mul_assoc u₂.val, val_inv, one_mul, val_inv],
         -- 🎉 no goals
      by rw [mul_assoc, ← mul_assoc u₁.inv, inv_val, one_mul, inv_val]⟩
         -- 🎉 no goals
  one := ⟨1, 1, one_mul 1, one_mul 1⟩
  one_mul u := ext <| one_mul (u : α)
  mul_one u := ext <| mul_one (u : α)

/-- Units of a monoid form a group. -/
@[to_additive "Additive units of an additive monoid form an additive group."]
instance : Group αˣ :=
  { (inferInstance : MulOneClass αˣ) with
    one := 1,
    mul_assoc := fun _ _ _ => ext <| mul_assoc _ _ _,
    inv := Inv.inv, mul_left_inv := fun u => ext u.inv_val }

/-- Units of a commutative monoid form a commutative group. -/
@[to_additive "Additive units of an additive commutative monoid form
an additive commutative group."]
instance instCommGroupUnits {α} [CommMonoid α] : CommGroup αˣ :=
  -- note: the original ported file had `{ (inferInstance : Group αˣ) with ... }`
  -- and this was removed because it was causing slowdowns: see lean4#2387
  { mul_comm := fun _ _ => ext <| mul_comm _ _ }
#align units.comm_group Units.instCommGroupUnits
#align add_units.add_comm_group AddUnits.instAddCommGroupAddUnits

/-- Units of a monoid are inhabited because `1` is a unit. -/
@[to_additive "Additive units of an additive monoid are inhabited because `0` is an additive unit."]
instance : Inhabited αˣ :=
  ⟨1⟩


/-- Units of a monoid have a representation of the base value in the `Monoid`. -/
@[to_additive "Additive units of an additive monoid have a representation of the base value in
the `AddMonoid`."]
instance [Repr α] : Repr αˣ :=
  ⟨reprPrec ∘ val⟩

variable (a b c : αˣ) {u : αˣ}

@[to_additive (attr := simp, norm_cast)]
theorem val_mul : (↑(a * b) : α) = a * b :=
  rfl
#align units.coe_mul Units.val_mul
#align add_units.coe_add AddUnits.val_add

@[to_additive (attr := simp, norm_cast)]
theorem val_one : ((1 : αˣ) : α) = 1 :=
  rfl
#align units.coe_one Units.val_one
#align add_units.coe_zero AddUnits.val_zero

@[to_additive (attr := simp, norm_cast)]
theorem val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1 := by rw [← Units.val_one, eq_iff]
                                                        -- 🎉 no goals
#align units.coe_eq_one Units.val_eq_one
#align add_units.coe_eq_zero AddUnits.val_eq_zero

@[to_additive (attr := simp)]
theorem inv_mk (x y : α) (h₁ h₂) : (mk x y h₁ h₂)⁻¹ = mk y x h₂ h₁ :=
  rfl
#align units.inv_mk Units.inv_mk
#align add_units.neg_mk AddUnits.neg_mk

-- Porting note: coercions are now eagerly elaborated, so no need for `val_eq_coe`
#noalign units.val_eq_coe
#noalign add_units.val_eq_coe

@[to_additive (attr := simp)]
theorem inv_eq_val_inv : a.inv = ((a⁻¹ : αˣ) : α) :=
  rfl
#align units.inv_eq_coe_inv Units.inv_eq_val_inv
#align add_units.neg_eq_coe_neg AddUnits.neg_eq_val_neg

@[to_additive (attr := simp)]
theorem inv_mul : (↑a⁻¹ * a : α) = 1 :=
  inv_val _
#align units.inv_mul Units.inv_mul
#align add_units.neg_add AddUnits.neg_add

@[to_additive (attr := simp)]
theorem mul_inv : (a * ↑a⁻¹ : α) = 1 :=
  val_inv _
#align units.mul_inv Units.mul_inv
#align add_units.add_neg AddUnits.add_neg

@[to_additive]
theorem inv_mul_of_eq {a : α} (h : ↑u = a) : ↑u⁻¹ * a = 1 := by rw [← h, u.inv_mul]
                                                                -- 🎉 no goals
#align units.inv_mul_of_eq Units.inv_mul_of_eq
#align add_units.neg_add_of_eq AddUnits.neg_add_of_eq

@[to_additive]
theorem mul_inv_of_eq {a : α} (h : ↑u = a) : a * ↑u⁻¹ = 1 := by rw [← h, u.mul_inv]
                                                                -- 🎉 no goals
#align units.mul_inv_of_eq Units.mul_inv_of_eq
#align add_units.add_neg_of_eq AddUnits.add_neg_of_eq

@[to_additive (attr := simp)]
theorem mul_inv_cancel_left (a : αˣ) (b : α) : (a : α) * (↑a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv, one_mul]
  -- 🎉 no goals
#align units.mul_inv_cancel_left Units.mul_inv_cancel_left
#align add_units.add_neg_cancel_left AddUnits.add_neg_cancel_left

@[to_additive (attr := simp)]
theorem inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ : α) * (a * b) = b := by
  rw [← mul_assoc, inv_mul, one_mul]
  -- 🎉 no goals
#align units.inv_mul_cancel_left Units.inv_mul_cancel_left
#align add_units.neg_add_cancel_left AddUnits.neg_add_cancel_left

@[to_additive (attr := simp)]
theorem mul_inv_cancel_right (a : α) (b : αˣ) : a * b * ↑b⁻¹ = a := by
  rw [mul_assoc, mul_inv, mul_one]
  -- 🎉 no goals
#align units.mul_inv_cancel_right Units.mul_inv_cancel_right
#align add_units.add_neg_cancel_right AddUnits.add_neg_cancel_right

@[to_additive (attr := simp)]
theorem inv_mul_cancel_right (a : α) (b : αˣ) : a * ↑b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul, mul_one]
  -- 🎉 no goals
#align units.inv_mul_cancel_right Units.inv_mul_cancel_right
#align add_units.neg_add_cancel_right AddUnits.neg_add_cancel_right

@[to_additive (attr := simp)]
theorem mul_right_inj (a : αˣ) {b c : α} : (a : α) * b = a * c ↔ b = c :=
  ⟨fun h => by simpa only [inv_mul_cancel_left] using congr_arg (fun x : α => ↑(a⁻¹ : αˣ) * x) h,
               -- 🎉 no goals
    congr_arg _⟩
#align units.mul_right_inj Units.mul_right_inj
#align add_units.add_right_inj AddUnits.add_right_inj

@[to_additive (attr := simp)]
theorem mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b = c :=
  ⟨fun h => by simpa only [mul_inv_cancel_right] using congr_arg (fun x : α => x * ↑(a⁻¹ : αˣ)) h,
               -- 🎉 no goals
    congr_arg (· * a.val)⟩
#align units.mul_left_inj Units.mul_left_inj
#align add_units.add_left_inj AddUnits.add_left_inj

@[to_additive]
theorem eq_mul_inv_iff_mul_eq {a b : α} : a = b * ↑c⁻¹ ↔ a * c = b :=
  ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩
               -- 🎉 no goals
                                                         -- 🎉 no goals
#align units.eq_mul_inv_iff_mul_eq Units.eq_mul_inv_iff_mul_eq
#align add_units.eq_add_neg_iff_add_eq AddUnits.eq_add_neg_iff_add_eq

@[to_additive]
theorem eq_inv_mul_iff_mul_eq {a c : α} : a = ↑b⁻¹ * c ↔ ↑b * a = c :=
  ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩
               -- 🎉 no goals
                                                        -- 🎉 no goals
#align units.eq_inv_mul_iff_mul_eq Units.eq_inv_mul_iff_mul_eq
#align add_units.eq_neg_add_iff_add_eq AddUnits.eq_neg_add_iff_add_eq

@[to_additive]
theorem inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩
               -- 🎉 no goals
                                                          -- 🎉 no goals
#align units.inv_mul_eq_iff_eq_mul Units.inv_mul_eq_iff_eq_mul
#align add_units.neg_add_eq_iff_eq_add AddUnits.neg_add_eq_iff_eq_add

@[to_additive]
theorem mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ = c ↔ a = c * b :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩
               -- 🎉 no goals
                                                           -- 🎉 no goals
#align units.mul_inv_eq_iff_eq_mul Units.mul_inv_eq_iff_eq_mul
#align add_units.add_neg_eq_iff_eq_add AddUnits.add_neg_eq_iff_eq_add

-- Porting note: have to explicitly type annotate the 1
@[to_additive]
protected theorem inv_eq_of_mul_eq_one_left {a : α} (h : a * u = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = (1 : α) * ↑u⁻¹ := by rw [one_mul]
                                -- 🎉 no goals
    _ = a := by rw [← h, mul_inv_cancel_right]
                -- 🎉 no goals
#align units.inv_eq_of_mul_eq_one_left Units.inv_eq_of_mul_eq_one_left
#align add_units.neg_eq_of_add_eq_zero_left AddUnits.neg_eq_of_add_eq_zero_left


-- Porting note: have to explicitly type annotate the 1
@[to_additive]
protected theorem inv_eq_of_mul_eq_one_right {a : α} (h : ↑u * a = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = ↑u⁻¹ * (1 : α) := by rw [mul_one]
                                -- 🎉 no goals
    _ = a := by rw [← h, inv_mul_cancel_left]
                -- 🎉 no goals
#align units.inv_eq_of_mul_eq_one_right Units.inv_eq_of_mul_eq_one_right
#align add_units.neg_eq_of_add_eq_zero_right AddUnits.neg_eq_of_add_eq_zero_right


@[to_additive]
protected theorem eq_inv_of_mul_eq_one_left {a : α} (h : ↑u * a = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_right h).symm
#align units.eq_inv_of_mul_eq_one_left Units.eq_inv_of_mul_eq_one_left
#align add_units.eq_neg_of_add_eq_zero_left AddUnits.eq_neg_of_add_eq_zero_left

@[to_additive]
protected theorem eq_inv_of_mul_eq_one_right {a : α} (h : a * u = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_left h).symm
#align units.eq_inv_of_mul_eq_one_right Units.eq_inv_of_mul_eq_one_right
#align add_units.eq_neg_of_add_eq_zero_right AddUnits.eq_neg_of_add_eq_zero_right

@[to_additive (attr := simp)]
theorem mul_inv_eq_one {a : α} : a * ↑u⁻¹ = 1 ↔ a = u :=
  ⟨inv_inv u ▸ Units.eq_inv_of_mul_eq_one_right, fun h => mul_inv_of_eq h.symm⟩
#align units.mul_inv_eq_one Units.mul_inv_eq_one
#align add_units.add_neg_eq_zero AddUnits.add_neg_eq_zero

@[to_additive (attr := simp)]
theorem inv_mul_eq_one {a : α} : ↑u⁻¹ * a = 1 ↔ ↑u = a :=
  ⟨inv_inv u ▸ Units.inv_eq_of_mul_eq_one_right, inv_mul_of_eq⟩
#align units.inv_mul_eq_one Units.inv_mul_eq_one
#align add_units.neg_add_eq_zero AddUnits.neg_add_eq_zero

@[to_additive]
theorem mul_eq_one_iff_eq_inv {a : α} : a * u = 1 ↔ a = ↑u⁻¹ := by rw [← mul_inv_eq_one, inv_inv]
                                                                   -- 🎉 no goals
#align units.mul_eq_one_iff_eq_inv Units.mul_eq_one_iff_eq_inv
#align add_units.add_eq_zero_iff_eq_neg AddUnits.add_eq_zero_iff_eq_neg

@[to_additive]
theorem mul_eq_one_iff_inv_eq {a : α} : ↑u * a = 1 ↔ ↑u⁻¹ = a := by rw [← inv_mul_eq_one, inv_inv]
                                                                    -- 🎉 no goals
#align units.mul_eq_one_iff_inv_eq Units.mul_eq_one_iff_inv_eq
#align add_units.add_eq_zero_iff_neg_eq AddUnits.add_eq_zero_iff_neg_eq

@[to_additive]
theorem inv_unique {u₁ u₂ : αˣ} (h : (↑u₁ : α) = ↑u₂) : (↑u₁⁻¹ : α) = ↑u₂⁻¹ :=
  Units.inv_eq_of_mul_eq_one_right <| by rw [h, u₂.mul_inv]
                                         -- 🎉 no goals
#align units.inv_unique Units.inv_unique
#align add_units.neg_unique AddUnits.neg_unique

@[to_additive (attr := simp)]
theorem val_inv_eq_inv_val {M : Type*} [DivisionMonoid M] (u : Units M) : ↑u⁻¹ = (u⁻¹ : M) :=
  Eq.symm <| inv_eq_of_mul_eq_one_right u.mul_inv
#align units.coe_inv Units.val_inv_eq_inv_val

end Units

/-- For `a, b` in a `CommMonoid` such that `a * b = 1`, makes a unit out of `a`. -/
@[to_additive
  "For `a, b` in an `AddCommMonoid` such that `a + b = 0`, makes an addUnit out of `a`."]
def Units.mkOfMulEqOne [CommMonoid α] (a b : α) (hab : a * b = 1) : αˣ :=
  ⟨a, b, hab, (mul_comm b a).trans hab⟩
#align units.mk_of_mul_eq_one Units.mkOfMulEqOne
#align add_units.mk_of_add_eq_zero AddUnits.mkOfAddEqZero

@[to_additive (attr := simp)]
theorem Units.val_mkOfMulEqOne [CommMonoid α] {a b : α} (h : a * b = 1) :
    (Units.mkOfMulEqOne a b h : α) = a :=
  rfl
#align units.coe_mk_of_mul_eq_one Units.val_mkOfMulEqOne
#align add_units.coe_mk_of_add_eq_zero AddUnits.val_mkOfAddEqZero

section Monoid

variable [Monoid α] {a b c : α}

/-- Partial division. It is defined when the
  second argument is invertible, and unlike the division operator
  in `DivisionRing` it is not totalized at zero. -/
def divp (a : α) (u : Units α) : α :=
  a * (u⁻¹ : αˣ)
#align divp divp

@[inherit_doc]
infixl:70 " /ₚ " => divp

@[simp]
theorem divp_self (u : αˣ) : (u : α) /ₚ u = 1 :=
  Units.mul_inv _
#align divp_self divp_self

@[simp]
theorem divp_one (a : α) : a /ₚ 1 = a :=
  mul_one _
#align divp_one divp_one

theorem divp_assoc (a b : α) (u : αˣ) : a * b /ₚ u = a * (b /ₚ u) :=
  mul_assoc _ _ _
#align divp_assoc divp_assoc

/-- `field_simp` needs the reverse direction of `divp_assoc` to move all `/ₚ` to the right. -/
@[field_simps]
theorem divp_assoc' (x y : α) (u : αˣ) : x * (y /ₚ u) = x * y /ₚ u :=
  (divp_assoc _ _ _).symm
#align divp_assoc' divp_assoc'

@[simp]
theorem divp_inv (u : αˣ) : a /ₚ u⁻¹ = a * u :=
  rfl
#align divp_inv divp_inv

@[simp]
theorem divp_mul_cancel (a : α) (u : αˣ) : a /ₚ u * u = a :=
  (mul_assoc _ _ _).trans <| by rw [Units.inv_mul, mul_one]
                                -- 🎉 no goals
#align divp_mul_cancel divp_mul_cancel

@[simp]
theorem mul_divp_cancel (a : α) (u : αˣ) : a * u /ₚ u = a :=
  (mul_assoc _ _ _).trans <| by rw [Units.mul_inv, mul_one]
                                -- 🎉 no goals
#align mul_divp_cancel mul_divp_cancel

@[simp]
theorem divp_left_inj (u : αˣ) {a b : α} : a /ₚ u = b /ₚ u ↔ a = b :=
  Units.mul_left_inj _
#align divp_left_inj divp_left_inj

@[field_simps]
theorem divp_divp_eq_divp_mul (x : α) (u₁ u₂ : αˣ) : x /ₚ u₁ /ₚ u₂ = x /ₚ (u₂ * u₁) := by
  simp only [divp, mul_inv_rev, Units.val_mul, mul_assoc]
  -- 🎉 no goals
#align divp_divp_eq_divp_mul divp_divp_eq_divp_mul

/- Port note: to match the mathlib3 behavior, this needs to have higher simp
priority than eq_divp_iff_mul_eq. -/
@[field_simps 1010]
theorem divp_eq_iff_mul_eq {x : α} {u : αˣ} {y : α} : x /ₚ u = y ↔ y * u = x :=
  u.mul_left_inj.symm.trans <| by rw [divp_mul_cancel]; exact ⟨Eq.symm, Eq.symm⟩
                                  -- ⊢ x = y * ↑u ↔ y * ↑u = x
                                                        -- 🎉 no goals
#align divp_eq_iff_mul_eq divp_eq_iff_mul_eq

@[field_simps]
theorem eq_divp_iff_mul_eq {x : α} {u : αˣ} {y : α} : x = y /ₚ u ↔ x * u = y := by
  rw [eq_comm, divp_eq_iff_mul_eq]
  -- 🎉 no goals
#align eq_divp_iff_mul_eq eq_divp_iff_mul_eq

theorem divp_eq_one_iff_eq {a : α} {u : αˣ} : a /ₚ u = 1 ↔ a = u :=
  (Units.mul_left_inj u).symm.trans <| by rw [divp_mul_cancel, one_mul]
                                          -- 🎉 no goals
#align divp_eq_one_iff_eq divp_eq_one_iff_eq

@[simp]
theorem one_divp (u : αˣ) : 1 /ₚ u = ↑u⁻¹ :=
  one_mul _
#align one_divp one_divp

/-- Used for `field_simp` to deal with inverses of units. -/
@[field_simps]
theorem inv_eq_one_divp (u : αˣ) : ↑u⁻¹ = 1 /ₚ u := by rw [one_divp]
                                                       -- 🎉 no goals
#align inv_eq_one_divp inv_eq_one_divp

/-- Used for `field_simp` to deal with inverses of units. This form of the lemma
is essential since `field_simp` likes to use `inv_eq_one_div` to rewrite
`↑u⁻¹ = ↑(1 / u)`.
-/
@[field_simps]
theorem inv_eq_one_divp' (u : αˣ) : ((1 / u : αˣ) : α) = 1 /ₚ u := by
  rw [one_div, one_divp]
  -- 🎉 no goals
#align inv_eq_one_divp' inv_eq_one_divp'

/-- `field_simp` moves division inside `αˣ` to the right, and this lemma
lifts the calculation to `α`.
-/
@[field_simps]
theorem val_div_eq_divp (u₁ u₂ : αˣ) : ↑(u₁ / u₂) = ↑u₁ /ₚ u₂ := by
  rw [divp, division_def, Units.val_mul]
  -- 🎉 no goals
#align coe_div_eq_divp val_div_eq_divp

end Monoid

section CommMonoid

variable [CommMonoid α]

@[field_simps]
theorem divp_mul_eq_mul_divp (x y : α) (u : αˣ) : x /ₚ u * y = x * y /ₚ u := by
  rw [divp, divp, mul_right_comm]
  -- 🎉 no goals
#align divp_mul_eq_mul_divp divp_mul_eq_mul_divp

-- Theoretically redundant as `field_simp` lemma.
@[field_simps]
theorem divp_eq_divp_iff {x y : α} {ux uy : αˣ} : x /ₚ ux = y /ₚ uy ↔ x * uy = y * ux := by
  rw [divp_eq_iff_mul_eq, divp_mul_eq_mul_divp, divp_eq_iff_mul_eq]
  -- 🎉 no goals
#align divp_eq_divp_iff divp_eq_divp_iff

-- Theoretically redundant as `field_simp` lemma.
@[field_simps]
theorem divp_mul_divp (x y : α) (ux uy : αˣ) : x /ₚ ux * (y /ₚ uy) = x * y /ₚ (ux * uy) := by
  rw [divp_mul_eq_mul_divp, divp_assoc', divp_divp_eq_divp_mul]
  -- 🎉 no goals
#align divp_mul_divp divp_mul_divp

variable [Subsingleton αˣ] {a b : α}

@[to_additive]
theorem eq_one_of_mul_right (h : a * b = 1) : a = 1 :=
  congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ (by rwa [mul_comm]) h) 1
                                                             -- 🎉 no goals
#align eq_one_of_mul_right eq_one_of_mul_right
#align eq_zero_of_add_right eq_zero_of_add_right

@[to_additive]
theorem eq_one_of_mul_left (h : a * b = 1) : b = 1 :=
  congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ h <| by rwa [mul_comm]) 1
                                                                 -- 🎉 no goals
#align eq_one_of_mul_left eq_one_of_mul_left
#align eq_zero_of_add_left eq_zero_of_add_left

@[to_additive (attr := simp)]
theorem mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨eq_one_of_mul_right h, eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    -- ⊢ 1 * 1 = 1
    exact mul_one _⟩
    -- 🎉 no goals
#align mul_eq_one mul_eq_one
#align add_eq_zero add_eq_zero

end CommMonoid

/-!
# `IsUnit` predicate
-/


section IsUnit

variable {M : Type*} {N : Type*}

/-- An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse.
The actual definition says that `a` is equal to some `u : Mˣ`, where
`Mˣ` is a bundled version of `IsUnit`. -/
@[to_additive
      "An element `a : M` of an `AddMonoid` is an `AddUnit` if it has a two-sided additive inverse.
      The actual definition says that `a` is equal to some `u : AddUnits M`,
      where `AddUnits M` is a bundled version of `IsAddUnit`."]
def IsUnit [Monoid M] (a : M) : Prop :=
  ∃ u : Mˣ, (u : M) = a
#align is_unit IsUnit
#align is_add_unit IsAddUnit

@[to_additive (attr := nontriviality)]
theorem isUnit_of_subsingleton [Monoid M] [Subsingleton M] (a : M) : IsUnit a :=
  ⟨⟨a, a, Subsingleton.elim _ _, Subsingleton.elim _ _⟩, rfl⟩
#align is_unit_of_subsingleton isUnit_of_subsingleton
#align is_add_unit_of_subsingleton isAddUnit_of_subsingleton

@[to_additive]
instance [Monoid M] : CanLift M Mˣ Units.val IsUnit :=
  { prf := fun _ ↦ id }

/-- A subsingleton `Monoid` has a unique unit. -/
@[to_additive "A subsingleton `AddMonoid` has a unique additive unit."]
instance [Monoid M] [Subsingleton M] : Unique Mˣ where
  default := 1
  uniq a := Units.val_eq_one.mp <| Subsingleton.elim (a : M) 1


@[to_additive (attr := simp)]
protected theorem Units.isUnit [Monoid M] (u : Mˣ) : IsUnit (u : M) :=
  ⟨u, rfl⟩
#align units.is_unit Units.isUnit
#align add_units.is_add_unit_add_unit AddUnits.isAddUnit

@[to_additive (attr := simp)]
theorem isUnit_one [Monoid M] : IsUnit (1 : M) :=
  ⟨1, rfl⟩
#align is_unit_one isUnit_one
#align is_add_unit_zero isAddUnit_zero

@[to_additive]
theorem isUnit_of_mul_eq_one [CommMonoid M] (a b : M) (h : a * b = 1) : IsUnit a :=
  ⟨Units.mkOfMulEqOne a b h, rfl⟩
#align is_unit_of_mul_eq_one isUnit_of_mul_eq_one
#align is_add_unit_of_add_eq_zero isAddUnit_of_add_eq_zero

@[to_additive IsAddUnit.exists_neg]
theorem IsUnit.exists_right_inv [Monoid M] {a : M} (h : IsUnit a) : ∃ b, a * b = 1 := by
  rcases h with ⟨⟨a, b, hab, _⟩, rfl⟩
  -- ⊢ ∃ b_1, ↑{ val := a, inv := b, val_inv := hab, inv_val := inv_val✝ } * b_1 = 1
  exact ⟨b, hab⟩
  -- 🎉 no goals
#align is_unit.exists_right_inv IsUnit.exists_right_inv
#align is_add_unit.exists_neg IsAddUnit.exists_neg

@[to_additive IsAddUnit.exists_neg']
theorem IsUnit.exists_left_inv [Monoid M] {a : M} (h : IsUnit a) : ∃ b, b * a = 1 := by
  rcases h with ⟨⟨a, b, _, hba⟩, rfl⟩
  -- ⊢ ∃ b_1, b_1 * ↑{ val := a, inv := b, val_inv := val_inv✝, inv_val := hba } = 1
  exact ⟨b, hba⟩
  -- 🎉 no goals
#align is_unit.exists_left_inv IsUnit.exists_left_inv
#align is_add_unit.exists_neg' IsAddUnit.exists_neg'

@[to_additive]
theorem isUnit_iff_exists_inv [CommMonoid M] {a : M} : IsUnit a ↔ ∃ b, a * b = 1 :=
  ⟨fun h => h.exists_right_inv, fun ⟨b, hab⟩ => isUnit_of_mul_eq_one _ b hab⟩
#align is_unit_iff_exists_inv isUnit_iff_exists_inv
#align is_add_unit_iff_exists_neg isAddUnit_iff_exists_neg

@[to_additive]
theorem isUnit_iff_exists_inv' [CommMonoid M] {a : M} : IsUnit a ↔ ∃ b, b * a = 1 := by
  simp [isUnit_iff_exists_inv, mul_comm]
  -- 🎉 no goals
#align is_unit_iff_exists_inv' isUnit_iff_exists_inv'
#align is_add_unit_iff_exists_neg' isAddUnit_iff_exists_neg'

@[to_additive]
theorem IsUnit.mul [Monoid M] {x y : M} : IsUnit x → IsUnit y → IsUnit (x * y) := by
  rintro ⟨x, rfl⟩ ⟨y, rfl⟩
  -- ⊢ IsUnit (↑x * ↑y)
  exact ⟨x * y, Units.val_mul _ _⟩
  -- 🎉 no goals
#align is_unit.mul IsUnit.mul
#align is_add_unit.add IsAddUnit.add

/-- Multiplication by a `u : Mˣ` on the right doesn't affect `IsUnit`. -/
@[to_additive (attr := simp)
"Addition of a `u : AddUnits M` on the right doesn't affect `IsAddUnit`."]
theorem Units.isUnit_mul_units [Monoid M] (a : M) (u : Mˣ) : IsUnit (a * u) ↔ IsUnit a :=
  Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (a * ↑u * ↑u⁻¹) := by exists v * u⁻¹; rw [← hv, Units.val_mul]
      -- ⊢ IsUnit a
      rwa [mul_assoc, Units.mul_inv, mul_one] at this)
      -- 🎉 no goals
    fun v => v.mul u.isUnit
#align units.is_unit_mul_units Units.isUnit_mul_units
#align add_units.is_add_unit_add_add_units AddUnits.isAddUnit_add_addUnits

/-- Multiplication by a `u : Mˣ` on the left doesn't affect `IsUnit`. -/
@[to_additive (attr := simp)
"Addition of a `u : AddUnits M` on the left doesn't affect `IsAddUnit`."]
theorem Units.isUnit_units_mul {M : Type*} [Monoid M] (u : Mˣ) (a : M) :
    IsUnit (↑u * a) ↔ IsUnit a :=
  Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (↑u⁻¹ * (↑u * a)) := by exists u⁻¹ * v; rw [← hv, Units.val_mul]
      -- ⊢ IsUnit a
      rwa [← mul_assoc, Units.inv_mul, one_mul] at this)
      -- 🎉 no goals
    u.isUnit.mul
#align units.is_unit_units_mul Units.isUnit_units_mul
#align add_units.is_add_unit_add_units_add AddUnits.isAddUnit_addUnits_add

@[to_additive]
theorem isUnit_of_mul_isUnit_left [CommMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit x :=
  let ⟨z, hz⟩ := isUnit_iff_exists_inv.1 hu
  isUnit_iff_exists_inv.2 ⟨y * z, by rwa [← mul_assoc]⟩
                                     -- 🎉 no goals
#align is_unit_of_mul_is_unit_left isUnit_of_mul_isUnit_left
#align is_add_unit_of_add_is_add_unit_left isAddUnit_of_add_isAddUnit_left

@[to_additive]
theorem isUnit_of_mul_isUnit_right [CommMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit y :=
  @isUnit_of_mul_isUnit_left _ _ y x <| by rwa [mul_comm]
                                           -- 🎉 no goals
#align is_unit_of_mul_is_unit_right isUnit_of_mul_isUnit_right
#align is_add_unit_of_add_is_add_unit_right isAddUnit_of_add_isAddUnit_right

namespace IsUnit

@[to_additive (attr := simp)]
theorem mul_iff [CommMonoid M] {x y : M} : IsUnit (x * y) ↔ IsUnit x ∧ IsUnit y :=
  ⟨fun h => ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩,
   fun h => IsUnit.mul h.1 h.2⟩
#align is_unit.mul_iff IsUnit.mul_iff
#align is_add_unit.add_iff IsAddUnit.add_iff

section Monoid

variable [Monoid M] {a b c : M}

/-- The element of the group of units, corresponding to an element of a monoid which is a unit. When
`α` is a `DivisionMonoid`, use `IsUnit.unit'` instead. -/
protected noncomputable def unit (h : IsUnit a) : Mˣ :=
  (Classical.choose h).copy a (Classical.choose_spec h).symm _ rfl
#align is_unit.unit IsUnit.unit

-- Porting note: `to_additive` doesn't carry over `noncomputable` so we make an explicit defn
/-- "The element of the additive group of additive units, corresponding to an element of
an additive monoid which is an additive unit. When `α` is a `SubtractionMonoid`, use
`IsAddUnit.addUnit'` instead. -/
protected noncomputable def _root_.IsAddUnit.addUnit [AddMonoid N] {a : N} (h : IsAddUnit a) :
    AddUnits N :=
  (Classical.choose h).copy a (Classical.choose_spec h).symm _ rfl
#align is_add_unit.add_unit IsAddUnit.addUnit
attribute [to_additive existing] IsUnit.unit

@[to_additive (attr := simp)]
theorem unit_of_val_units {a : Mˣ} (h : IsUnit (a : M)) : h.unit = a :=
  Units.ext <| rfl
#align is_unit.unit_of_coe_units IsUnit.unit_of_val_units
#align is_add_unit.add_unit_of_coe_add_units IsAddUnit.addUnit_of_val_addUnits

@[to_additive (attr := simp)]
theorem unit_spec (h : IsUnit a) : ↑h.unit = a :=
  rfl
#align is_unit.unit_spec IsUnit.unit_spec
#align is_add_unit.add_unit_spec IsAddUnit.addUnit_spec

@[to_additive (attr := simp)]
theorem val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1 :=
  Units.mul_inv _
#align is_unit.coe_inv_mul IsUnit.val_inv_mul
#align is_add_unit.coe_neg_add IsAddUnit.val_neg_add

@[to_additive (attr := simp)]
theorem mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1 := by
  rw [←h.unit.mul_inv]; congr
  -- ⊢ a * ↑(IsUnit.unit h)⁻¹ = ↑(IsUnit.unit h) * ↑(IsUnit.unit h)⁻¹
                        -- 🎉 no goals
#align is_unit.mul_coe_inv IsUnit.mul_val_inv
#align is_add_unit.add_coe_neg IsAddUnit.add_val_neg

/-- `IsUnit x` is decidable if we can decide if `x` comes from `Mˣ`. -/
@[to_additive "`IsAddUnit x` is decidable if we can decide if `x` comes from `AddUnits M`."]
instance (x : M) [h : Decidable (∃ u : Mˣ, ↑u = x)] : Decidable (IsUnit x) :=
  h

@[to_additive]
theorem mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_left_inj
#align is_unit.mul_left_inj IsUnit.mul_left_inj
#align is_add_unit.add_left_inj IsAddUnit.add_left_inj

@[to_additive]
theorem mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_right_inj
#align is_unit.mul_right_inj IsUnit.mul_right_inj
#align is_add_unit.add_right_inj IsAddUnit.add_right_inj

@[to_additive]
protected theorem mul_left_cancel (h : IsUnit a) : a * b = a * c → b = c :=
  h.mul_right_inj.1
#align is_unit.mul_left_cancel IsUnit.mul_left_cancel
#align is_add_unit.add_left_cancel IsAddUnit.add_left_cancel

@[to_additive]
protected theorem mul_right_cancel (h : IsUnit b) : a * b = c * b → a = c :=
  h.mul_left_inj.1
#align is_unit.mul_right_cancel IsUnit.mul_right_cancel
#align is_add_unit.add_right_cancel IsAddUnit.add_right_cancel

@[to_additive]
protected theorem mul_right_injective (h : IsUnit a) : Injective ((· * ·) a) :=
  fun _ _ => h.mul_left_cancel
#align is_unit.mul_right_injective IsUnit.mul_right_injective
#align is_add_unit.add_right_injective IsAddUnit.add_right_injective

@[to_additive]
protected theorem mul_left_injective (h : IsUnit b) : Injective (· * b) :=
  fun _ _ => h.mul_right_cancel
#align is_unit.mul_left_injective IsUnit.mul_left_injective
#align is_add_unit.add_left_injective IsAddUnit.add_left_injective

end Monoid

variable [DivisionMonoid M] {a : M}

@[to_additive (attr := simp)]
protected theorem inv_mul_cancel : IsUnit a → a⁻¹ * a = 1 := by
  rintro ⟨u, rfl⟩
  -- ⊢ (↑u)⁻¹ * ↑u = 1
  rw [← Units.val_inv_eq_inv_val, Units.inv_mul]
  -- 🎉 no goals
#align is_unit.inv_mul_cancel IsUnit.inv_mul_cancel
#align is_add_unit.neg_add_cancel IsAddUnit.neg_add_cancel

@[to_additive (attr := simp)]
protected theorem mul_inv_cancel : IsUnit a → a * a⁻¹ = 1 := by
  rintro ⟨u, rfl⟩
  -- ⊢ ↑u * (↑u)⁻¹ = 1
  rw [← Units.val_inv_eq_inv_val, Units.mul_inv]
  -- 🎉 no goals
#align is_unit.mul_inv_cancel IsUnit.mul_inv_cancel
#align is_add_unit.add_neg_cancel IsAddUnit.add_neg_cancel

end IsUnit

-- namespace
end IsUnit

-- section
section NoncomputableDefs

variable {M : Type*}

/-- Constructs a `Group` structure on a `Monoid` consisting only of units. -/
noncomputable def groupOfIsUnit [hM : Monoid M] (h : ∀ a : M, IsUnit a) : Group M :=
  { hM with
    inv := fun a => ↑(h a).unit⁻¹,
    mul_left_inv := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      -- ⊢ ↑(IsUnit.unit (_ : IsUnit a))⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }
      -- 🎉 no goals
#align group_of_is_unit groupOfIsUnit

/-- Constructs a `CommGroup` structure on a `CommMonoid` consisting only of units. -/
noncomputable def commGroupOfIsUnit [hM : CommMonoid M] (h : ∀ a : M, IsUnit a) : CommGroup M :=
  { hM with
    inv := fun a => ↑(h a).unit⁻¹,
    mul_left_inv := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      -- ⊢ ↑(IsUnit.unit (_ : IsUnit a))⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }
      -- 🎉 no goals
#align comm_group_of_is_unit commGroupOfIsUnit

end NoncomputableDefs
