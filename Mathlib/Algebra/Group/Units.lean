/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes Hölzl, Chris Hughes, Jens Wagemaker, Jon Eugster
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Logic.Unique
import Mathlib.Tactic.Nontriviality
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Subsingleton

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

## TODO

The results here should be used to golf the basic `Group` lemmas.
-/

assert_not_exists Multiplicative
assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered

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

section HasElem

@[to_additive]
theorem unique_one {α : Type*} [Unique α] [One α] : default = (1 : α) :=
  Unique.default_eq 1

end HasElem

namespace Units
section Monoid
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

/-- See Note [custom simps projection] -/
@[to_additive "See Note [custom simps projection]"]
def Simps.val_inv (u : αˣ) : α := ↑(u⁻¹)

initialize_simps_projections Units (as_prefix val, val_inv → null, inv → val_inv, as_prefix val_inv)

initialize_simps_projections AddUnits
  (as_prefix val, val_neg → null, neg → val_neg, as_prefix val_neg)

-- Porting note: removed `simp` tag because of the tautology
@[to_additive]
theorem val_mk (a : α) (b h₁ h₂) : ↑(Units.mk a b h₁ h₂) = a :=
  rfl

@[to_additive (attr := ext)]
theorem ext : Function.Injective (val : αˣ → α)
  | ⟨v, i₁, vi₁, iv₁⟩, ⟨v', i₂, vi₂, iv₂⟩, e => by
    simp only at e; subst v'; congr
    simpa only [iv₂, vi₁, one_mul, mul_one] using mul_assoc i₂ v i₁

@[to_additive (attr := norm_cast)]
theorem eq_iff {a b : αˣ} : (a : α) = b ↔ a = b :=
  ext.eq_iff

@[to_additive]
protected theorem ext_iff {a b : αˣ} : a = b ↔ (a : α) = b :=
  eq_iff.symm

/-- Units have decidable equality if the base `Monoid` has decidable equality. -/
@[to_additive "Additive units have decidable equality
if the base `AddMonoid` has deciable equality."]
instance [DecidableEq α] : DecidableEq αˣ := fun _ _ => decidable_of_iff' _ Units.ext_iff

@[to_additive (attr := simp)]
theorem mk_val (u : αˣ) (y h₁ h₂) : mk (u : α) y h₁ h₂ = u :=
  ext rfl

/-- Copy a unit, adjusting definition equalities. -/
@[to_additive (attr := simps) "Copy an `AddUnit`, adjusting definitional equalities."]
def copy (u : αˣ) (val : α) (hv : val = u) (inv : α) (hi : inv = ↑u⁻¹) : αˣ :=
  { val, inv, inv_val := hv.symm ▸ hi.symm ▸ u.inv_val, val_inv := hv.symm ▸ hi.symm ▸ u.val_inv }

@[to_additive]
theorem copy_eq (u : αˣ) (val hv inv hi) : u.copy val hv inv hi = u :=
  ext hv

/-- Units of a monoid have an induced multiplication. -/
@[to_additive "Additive units of an additive monoid have an induced addition."]
instance : Mul αˣ where
  mul u₁ u₂ :=
    ⟨u₁.val * u₂.val, u₂.inv * u₁.inv,
      by rw [mul_assoc, ← mul_assoc u₂.val, val_inv, one_mul, val_inv],
      by rw [mul_assoc, ← mul_assoc u₁.inv, inv_val, one_mul, inv_val]⟩

/-- Units of a monoid have a unit -/
@[to_additive "Additive units of an additive monoid have a zero."]
instance : One αˣ where
  one := ⟨1, 1, one_mul 1, one_mul 1⟩

/-- Units of a monoid have a multiplication and multiplicative identity. -/
@[to_additive "Additive units of an additive monoid have an addition and an additive identity."]
instance instMulOneClass : MulOneClass αˣ where
  one_mul u := ext <| one_mul (u : α)
  mul_one u := ext <| mul_one (u : α)

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

@[to_additive (attr := simp, norm_cast)]
theorem val_one : ((1 : αˣ) : α) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1 := by rw [← Units.val_one, eq_iff]

@[to_additive (attr := simp)]
theorem inv_mk (x y : α) (h₁ h₂) : (mk x y h₁ h₂)⁻¹ = mk y x h₂ h₁ :=
  rfl

-- Porting note: coercions are now eagerly elaborated, so no need for `val_eq_coe`

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

@[to_additive (attr := simp)]
theorem mul_inv_cancel_right (a : α) (b : αˣ) : a * b * ↑b⁻¹ = a := by
  rw [mul_assoc, mul_inv, mul_one]

@[to_additive (attr := simp)]
theorem inv_mul_cancel_right (a : α) (b : αˣ) : a * ↑b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul, mul_one]

@[to_additive (attr := simp)]
theorem mul_right_inj (a : αˣ) {b c : α} : (a : α) * b = a * c ↔ b = c :=
  ⟨fun h => by simpa only [inv_mul_cancel_left] using congr_arg (fun x : α => ↑(a⁻¹ : αˣ) * x) h,
    congr_arg _⟩

@[to_additive (attr := simp)]
theorem mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b = c :=
  ⟨fun h => by simpa only [mul_inv_cancel_right] using congr_arg (fun x : α => x * ↑(a⁻¹ : αˣ)) h,
    congr_arg (· * a.val)⟩

@[to_additive]
theorem eq_mul_inv_iff_mul_eq {a b : α} : a = b * ↑c⁻¹ ↔ a * c = b :=
  ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]
theorem eq_inv_mul_iff_mul_eq {a c : α} : a = ↑b⁻¹ * c ↔ ↑b * a = c :=
  ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]
theorem inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩

@[to_additive]
theorem mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ = c ↔ a = c * b :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩

-- Porting note: have to explicitly type annotate the 1
@[to_additive]
protected theorem inv_eq_of_mul_eq_one_left {a : α} (h : a * u = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = (1 : α) * ↑u⁻¹ := by rw [one_mul]
    _ = a := by rw [← h, mul_inv_cancel_right]


-- Porting note: have to explicitly type annotate the 1
@[to_additive]
protected theorem inv_eq_of_mul_eq_one_right {a : α} (h : ↑u * a = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = ↑u⁻¹ * (1 : α) := by rw [mul_one]
    _ = a := by rw [← h, inv_mul_cancel_left]


@[to_additive]
protected theorem eq_inv_of_mul_eq_one_left {a : α} (h : ↑u * a = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_right h).symm

@[to_additive]
protected theorem eq_inv_of_mul_eq_one_right {a : α} (h : a * u = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_left h).symm

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
@[to_additive "Additive units of an additive monoid have subtraction."]
instance : Div αˣ where
  div := fun a b ↦
    { val := a * b⁻¹
      inv := b * a⁻¹
      val_inv := by rw [mul_assoc, inv_mul_cancel_left, mul_inv]
      inv_val := by rw [mul_assoc, inv_mul_cancel_left, mul_inv] }

/-- Units of a monoid form a `DivInvMonoid`. -/
@[to_additive "Additive units of an additive monoid form a `SubNegMonoid`."]
instance instDivInvMonoid : DivInvMonoid αˣ where
  zpow := fun n a ↦ match n, a with
    | Int.ofNat n, a => a ^ n
    | Int.negSucc n, a => (a ^ n.succ)⁻¹
  zpow_zero' := fun a ↦ by simp
  zpow_succ' := fun n a ↦ by simp [pow_succ]
  zpow_neg' := fun n a ↦ by simp

/-- Units of a monoid form a group. -/
@[to_additive "Additive units of an additive monoid form an additive group."]
instance instGroup : Group αˣ where
  mul_left_inv := fun u => ext u.inv_val

/-- Units of a commutative monoid form a commutative group. -/
@[to_additive "Additive units of an additive commutative monoid form
an additive commutative group."]
instance instCommGroupUnits {α} [CommMonoid α] : CommGroup αˣ where
  mul_comm := fun _ _ => ext <| mul_comm _ _

@[to_additive (attr := simp, norm_cast)]
lemma val_pow_eq_pow_val (n : ℕ) : ↑(a ^ n) = (a ^ n : α) := rfl

@[to_additive (attr := simp)]
theorem mul_inv_eq_one {a : α} : a * ↑u⁻¹ = 1 ↔ a = u :=
  ⟨inv_inv u ▸ Units.eq_inv_of_mul_eq_one_right, fun h => mul_inv_of_eq h.symm⟩

@[to_additive (attr := simp)]
theorem inv_mul_eq_one {a : α} : ↑u⁻¹ * a = 1 ↔ ↑u = a :=
  ⟨inv_inv u ▸ Units.inv_eq_of_mul_eq_one_right, inv_mul_of_eq⟩

@[to_additive]
theorem mul_eq_one_iff_eq_inv {a : α} : a * u = 1 ↔ a = ↑u⁻¹ := by rw [← mul_inv_eq_one, inv_inv]

@[to_additive]
theorem mul_eq_one_iff_inv_eq {a : α} : ↑u * a = 1 ↔ ↑u⁻¹ = a := by rw [← inv_mul_eq_one, inv_inv]

@[to_additive]
theorem inv_unique {u₁ u₂ : αˣ} (h : (↑u₁ : α) = ↑u₂) : (↑u₁⁻¹ : α) = ↑u₂⁻¹ :=
  Units.inv_eq_of_mul_eq_one_right <| by rw [h, u₂.mul_inv]

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
  "For `a, b` in an `AddCommMonoid` such that `a + b = 0`, makes an addUnit out of `a`."]
def Units.mkOfMulEqOne [CommMonoid α] (a b : α) (hab : a * b = 1) : αˣ :=
  ⟨a, b, hab, (mul_comm b a).trans hab⟩

@[to_additive (attr := simp)]
theorem Units.val_mkOfMulEqOne [CommMonoid α] {a b : α} (h : a * b = 1) :
    (Units.mkOfMulEqOne a b h : α) = a :=
  rfl

section Monoid

variable [Monoid α] {a b c : α}

/-- Partial division. It is defined when the
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

@[simp]
theorem divp_left_inj (u : αˣ) {a b : α} : a /ₚ u = b /ₚ u ↔ a = b :=
  Units.mul_left_inj _

@[field_simps]
theorem divp_divp_eq_divp_mul (x : α) (u₁ u₂ : αˣ) : x /ₚ u₁ /ₚ u₂ = x /ₚ (u₂ * u₁) := by
  simp only [divp, mul_inv_rev, Units.val_mul, mul_assoc]

/- Porting note: to match the mathlib3 behavior, this needs to have higher simp
priority than eq_divp_iff_mul_eq. -/
@[field_simps 1010]
theorem divp_eq_iff_mul_eq {x : α} {u : αˣ} {y : α} : x /ₚ u = y ↔ y * u = x :=
  u.mul_left_inj.symm.trans <| by rw [divp_mul_cancel]; exact ⟨Eq.symm, Eq.symm⟩

@[field_simps]
theorem eq_divp_iff_mul_eq {x : α} {u : αˣ} {y : α} : x = y /ₚ u ↔ x * u = y := by
  rw [eq_comm, divp_eq_iff_mul_eq]

theorem divp_eq_one_iff_eq {a : α} {u : αˣ} : a /ₚ u = 1 ↔ a = u :=
  (Units.mul_left_inj u).symm.trans <| by rw [divp_mul_cancel, one_mul]

@[simp]
theorem one_divp (u : αˣ) : 1 /ₚ u = ↑u⁻¹ :=
  one_mul _

/-- Used for `field_simp` to deal with inverses of units. -/
@[field_simps]
theorem inv_eq_one_divp (u : αˣ) : ↑u⁻¹ = 1 /ₚ u := by rw [one_divp]

/-- Used for `field_simp` to deal with inverses of units. This form of the lemma
is essential since `field_simp` likes to use `inv_eq_one_div` to rewrite
`↑u⁻¹ = ↑(1 / u)`.
-/
@[field_simps]
theorem inv_eq_one_divp' (u : αˣ) : ((1 / u : αˣ) : α) = 1 /ₚ u := by
  rw [one_div, one_divp]

/-- `field_simp` moves division inside `αˣ` to the right, and this lemma
lifts the calculation to `α`.
-/
@[field_simps]
theorem val_div_eq_divp (u₁ u₂ : αˣ) : ↑(u₁ / u₂) = ↑u₁ /ₚ u₂ := by
  rw [divp, division_def, Units.val_mul]

end Monoid

section CommMonoid

variable [CommMonoid α]

@[field_simps]
theorem divp_mul_eq_mul_divp (x y : α) (u : αˣ) : x /ₚ u * y = x * y /ₚ u := by
  rw [divp, divp, mul_right_comm]

-- Theoretically redundant as `field_simp` lemma.
@[field_simps]
theorem divp_eq_divp_iff {x y : α} {ux uy : αˣ} : x /ₚ ux = y /ₚ uy ↔ x * uy = y * ux := by
  rw [divp_eq_iff_mul_eq, divp_mul_eq_mul_divp, divp_eq_iff_mul_eq]

-- Theoretically redundant as `field_simp` lemma.
@[field_simps]
theorem divp_mul_divp (x y : α) (ux uy : αˣ) : x /ₚ ux * (y /ₚ uy) = x * y /ₚ (ux * uy) := by
  rw [divp_mul_eq_mul_divp, divp_assoc', divp_divp_eq_divp_mul]

variable [Subsingleton αˣ] {a b : α}

@[to_additive]
theorem eq_one_of_mul_right (h : a * b = 1) : a = 1 :=
  congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ (by rwa [mul_comm]) h) 1

@[to_additive]
theorem eq_one_of_mul_left (h : a * b = 1) : b = 1 :=
  congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ h <| by rwa [mul_comm]) 1

@[to_additive (attr := simp)]
theorem mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨eq_one_of_mul_right h, eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

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

/-- See `isUnit_iff_exists_and_exists` for a similar lemma with two existentials. -/
@[to_additive "See `isAddUnit_iff_exists_and_exists` for a similar lemma with two existentials."]
lemma isUnit_iff_exists [Monoid M] {x : M} : IsUnit x ↔ ∃ b, x * b = 1 ∧ b * x = 1 := by
  refine ⟨fun ⟨u, hu⟩ => ?_, fun ⟨b, h1b, h2b⟩ => ⟨⟨x, b, h1b, h2b⟩, rfl⟩⟩
  subst x
  exact ⟨u.inv, u.val_inv, u.inv_val⟩

/-- See `isUnit_iff_exists` for a similar lemma with one existential. -/
@[to_additive "See `isAddUnit_iff_exists` for a similar lemma with one existential."]
theorem isUnit_iff_exists_and_exists [Monoid M] {a : M} :
    IsUnit a ↔ (∃ b, a * b = 1) ∧ (∃ c, c * a = 1) :=
  isUnit_iff_exists.trans
    ⟨fun ⟨b, hba, hab⟩ => ⟨⟨b, hba⟩, ⟨b, hab⟩⟩,
      fun ⟨⟨b, hb⟩, ⟨_, hc⟩⟩ => ⟨b, hb, left_inv_eq_right_inv hc hb ▸ hc⟩⟩

@[to_additive (attr := nontriviality)]
theorem isUnit_of_subsingleton [Monoid M] [Subsingleton M] (a : M) : IsUnit a :=
  ⟨⟨a, a, by subsingleton, by subsingleton⟩, rfl⟩

@[to_additive]
instance [Monoid M] : CanLift M Mˣ Units.val IsUnit :=
  { prf := fun _ ↦ id }

/-- A subsingleton `Monoid` has a unique unit. -/
@[to_additive "A subsingleton `AddMonoid` has a unique additive unit."]
instance [Monoid M] [Subsingleton M] : Unique Mˣ where
  uniq _ := Units.val_eq_one.mp (by subsingleton)

@[to_additive (attr := simp)]
protected theorem Units.isUnit [Monoid M] (u : Mˣ) : IsUnit (u : M) :=
  ⟨u, rfl⟩

@[to_additive (attr := simp)]
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

theorem units_eq_one [Unique Mˣ] (u : Mˣ) : u = 1 := by subsingleton

@[to_additive] lemma isUnit_iff_eq_one [Unique Mˣ] {x : M} : IsUnit x ↔ x = 1 :=
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
"Addition of a `u : AddUnits M` on the right doesn't affect `IsAddUnit`."]
theorem Units.isUnit_mul_units [Monoid M] (a : M) (u : Mˣ) : IsUnit (a * u) ↔ IsUnit a :=
  Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (a * ↑u * ↑u⁻¹) := by exists v * u⁻¹; rw [← hv, Units.val_mul]
      rwa [mul_assoc, Units.mul_inv, mul_one] at this)
    fun v => v.mul u.isUnit

/-- Multiplication by a `u : Mˣ` on the left doesn't affect `IsUnit`. -/
@[to_additive (attr := simp)
"Addition of a `u : AddUnits M` on the left doesn't affect `IsAddUnit`."]
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

@[to_additive (attr := simp)]
theorem mul_iff [CommMonoid M] {x y : M} : IsUnit (x * y) ↔ IsUnit x ∧ IsUnit y :=
  ⟨fun h => ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩,
   fun h => IsUnit.mul h.1 h.2⟩

section Monoid

variable [Monoid M] {a b c : M}

/-- The element of the group of units, corresponding to an element of a monoid which is a unit. When
`α` is a `DivisionMonoid`, use `IsUnit.unit'` instead. -/
protected noncomputable def unit (h : IsUnit a) : Mˣ :=
  (Classical.choose h).copy a (Classical.choose_spec h).symm _ rfl

-- Porting note: `to_additive` doesn't carry over `noncomputable` so we make an explicit defn
/-- "The element of the additive group of additive units, corresponding to an element of
an additive monoid which is an additive unit. When `α` is a `SubtractionMonoid`, use
`IsAddUnit.addUnit'` instead. -/
protected noncomputable def _root_.IsAddUnit.addUnit [AddMonoid N] {a : N} (h : IsAddUnit a) :
    AddUnits N :=
  (Classical.choose h).copy a (Classical.choose_spec h).symm _ rfl
attribute [to_additive existing] IsUnit.unit

@[to_additive (attr := simp)]
theorem unit_of_val_units {a : Mˣ} (h : IsUnit (a : M)) : h.unit = a :=
  Units.ext <| rfl

@[to_additive (attr := simp)]
theorem unit_spec (h : IsUnit a) : ↑h.unit = a :=
  rfl

@[to_additive (attr := simp)]
theorem unit_one (h : IsUnit (1 : M)) : h.unit = 1 :=
  Units.eq_iff.1 rfl

@[to_additive (attr := simp)]
theorem val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1 :=
  Units.mul_inv _

@[to_additive (attr := simp)]
theorem mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1 := by
  rw [← h.unit.mul_inv]; congr

/-- `IsUnit x` is decidable if we can decide if `x` comes from `Mˣ`. -/
@[to_additive "`IsAddUnit x` is decidable if we can decide if `x` comes from `AddUnits M`."]
instance (x : M) [h : Decidable (∃ u : Mˣ, ↑u = x)] : Decidable (IsUnit x) :=
  h

@[to_additive]
theorem mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_left_inj

@[to_additive]
theorem mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_right_inj

@[to_additive]
protected theorem mul_left_cancel (h : IsUnit a) : a * b = a * c → b = c :=
  h.mul_right_inj.1

@[to_additive]
protected theorem mul_right_cancel (h : IsUnit b) : a * b = c * b → a = c :=
  h.mul_left_inj.1

@[to_additive]
protected theorem mul_right_injective (h : IsUnit a) : Injective (a * ·) :=
  fun _ _ => h.mul_left_cancel

@[to_additive]
protected theorem mul_left_injective (h : IsUnit b) : Injective (· * b) :=
  fun _ _ => h.mul_right_cancel

@[to_additive]
theorem isUnit_iff_mulLeft_bijective {a : M} :
    IsUnit a ↔ Function.Bijective (a * ·) :=
  ⟨fun h ↦ ⟨h.mul_right_injective, fun y ↦ ⟨h.unit⁻¹ * y, by simp [← mul_assoc]⟩⟩, fun h ↦
    ⟨⟨a, _, (h.2 1).choose_spec, h.1
      (by simpa [mul_assoc] using congr_arg (· * a) (h.2 1).choose_spec)⟩, rfl⟩⟩

@[to_additive]
theorem isUnit_iff_mulRight_bijective {a : M} :
    IsUnit a ↔ Function.Bijective (· * a) :=
  ⟨fun h ↦ ⟨h.mul_left_injective, fun y ↦ ⟨y * h.unit⁻¹, by simp [mul_assoc]⟩⟩,
    fun h ↦ ⟨⟨a, _, h.1 (by simpa [mul_assoc] using congr_arg (a * ·) (h.2 1).choose_spec),
      (h.2 1).choose_spec⟩, rfl⟩⟩

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
@[to_additive (attr := simps val )
"The element of the additive group of additive units, corresponding to an element of
an additive monoid which is an additive unit. As opposed to `IsAddUnit.addUnit`, the negation is
computable and comes from the negation on `α`. This is useful to transfer properties of negation
in `AddUnits α` to `α`. See also `toAddUnits`."]
def unit' (h : IsUnit a) : αˣ := ⟨a, a⁻¹, h.mul_inv_cancel, h.inv_mul_cancel⟩

-- Porting note (#11215): TODO: `simps val_inv` fails
@[to_additive] lemma val_inv_unit' (h : IsUnit a) : ↑(h.unit'⁻¹) = a⁻¹ := rfl

@[to_additive (attr := simp)]
protected lemma mul_inv_cancel_left (h : IsUnit a) : ∀ b, a * (a⁻¹ * b) = b :=
  h.unit'.mul_inv_cancel_left

@[to_additive (attr := simp)]
protected lemma inv_mul_cancel_left (h : IsUnit a) : ∀ b, a⁻¹ * (a * b) = b :=
  h.unit'.inv_mul_cancel_left

@[to_additive (attr := simp)]
protected lemma mul_inv_cancel_right (h : IsUnit b) (a : α) : a * b * b⁻¹ = a :=
  h.unit'.mul_inv_cancel_right _

@[to_additive (attr := simp)]
protected lemma inv_mul_cancel_right (h : IsUnit b) (a : α) : a * b⁻¹ * b = a :=
  h.unit'.inv_mul_cancel_right _

@[to_additive]
protected lemma div_self (h : IsUnit a) : a / a = 1 := by rw [div_eq_mul_inv, h.mul_inv_cancel]

@[to_additive]
protected lemma eq_mul_inv_iff_mul_eq (h : IsUnit c) : a = b * c⁻¹ ↔ a * c = b :=
  h.unit'.eq_mul_inv_iff_mul_eq

@[to_additive]
protected lemma eq_inv_mul_iff_mul_eq (h : IsUnit b) : a = b⁻¹ * c ↔ b * a = c :=
  h.unit'.eq_inv_mul_iff_mul_eq

@[to_additive]
protected lemma inv_mul_eq_iff_eq_mul (h : IsUnit a) : a⁻¹ * b = c ↔ b = a * c :=
  h.unit'.inv_mul_eq_iff_eq_mul

@[to_additive]
protected lemma mul_inv_eq_iff_eq_mul (h : IsUnit b) : a * b⁻¹ = c ↔ a = c * b :=
  h.unit'.mul_inv_eq_iff_eq_mul

@[to_additive]
protected lemma mul_inv_eq_one (h : IsUnit b) : a * b⁻¹ = 1 ↔ a = b :=
  @Units.mul_inv_eq_one _ _ h.unit' _

@[to_additive]
protected lemma inv_mul_eq_one (h : IsUnit a) : a⁻¹ * b = 1 ↔ a = b :=
  @Units.inv_mul_eq_one _ _ h.unit' _

@[to_additive]
protected lemma mul_eq_one_iff_eq_inv (h : IsUnit b) : a * b = 1 ↔ a = b⁻¹ :=
  @Units.mul_eq_one_iff_eq_inv _ _ h.unit' _

@[to_additive]
protected lemma mul_eq_one_iff_inv_eq (h : IsUnit a) : a * b = 1 ↔ a⁻¹ = b :=
  @Units.mul_eq_one_iff_inv_eq _ _ h.unit' _

@[to_additive (attr := simp)]
protected lemma div_mul_cancel (h : IsUnit b) (a : α) : a / b * b = a := by
  rw [div_eq_mul_inv, h.inv_mul_cancel_right]

@[to_additive (attr := simp)]
protected lemma mul_div_cancel_right (h : IsUnit b) (a : α) : a * b / b = a := by
  rw [div_eq_mul_inv, h.mul_inv_cancel_right]

@[to_additive]
protected lemma mul_one_div_cancel (h : IsUnit a) : a * (1 / a) = 1 := by simp [h]

@[to_additive]
protected lemma one_div_mul_cancel (h : IsUnit a) : 1 / a * a = 1 := by simp [h]

@[to_additive]
lemma inv (h : IsUnit a) : IsUnit a⁻¹ := by
  obtain ⟨u, hu⟩ := h
  rw [← hu, ← Units.val_inv_eq_inv_val]
  exact Units.isUnit _

@[to_additive] lemma div (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a / b) := by
  rw [div_eq_mul_inv]; exact ha.mul hb.inv

@[to_additive]
protected lemma div_left_inj (h : IsUnit c) : a / c = b / c ↔ a = b := by
  simp only [div_eq_mul_inv]
  exact Units.mul_left_inj h.inv.unit'

@[to_additive]
protected lemma div_eq_iff (h : IsUnit b) : a / b = c ↔ a = c * b := by
  rw [div_eq_mul_inv, h.mul_inv_eq_iff_eq_mul]

@[to_additive]
protected lemma eq_div_iff (h : IsUnit c) : a = b / c ↔ a * c = b := by
  rw [div_eq_mul_inv, h.eq_mul_inv_iff_mul_eq]

@[to_additive]
protected lemma div_eq_of_eq_mul (h : IsUnit b) : a = c * b → a / b = c :=
  h.div_eq_iff.2

@[to_additive]
protected lemma eq_div_of_mul_eq (h : IsUnit c) : a * c = b → a = b / c :=
  h.eq_div_iff.2

@[to_additive]
protected lemma div_eq_one_iff_eq (h : IsUnit b) : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun hab => hab.symm ▸ h.div_self⟩

@[to_additive]
protected lemma div_mul_cancel_right (h : IsUnit b) (a : α) : b / (a * b) = a⁻¹ := by
  rw [div_eq_mul_inv, mul_inv_rev, h.mul_inv_cancel_left]

@[to_additive]
protected lemma div_mul_left (h : IsUnit b) : b / (a * b) = 1 / a := by
  rw [h.div_mul_cancel_right, one_div]

@[to_additive]
protected lemma mul_div_mul_right (h : IsUnit c) (a b : α) : a * c / (b * c) = a / b := by
  simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, h.mul_inv_cancel_left]

@[to_additive]
protected lemma mul_mul_div (a : α) (h : IsUnit b) : a * b * (1 / b) = a := by simp [h]

end DivisionMonoid

section DivisionCommMonoid
variable [DivisionCommMonoid α] {a b c d : α}

@[to_additive]
protected lemma div_mul_cancel_left (h : IsUnit a) (b : α) : a / (a * b) = b⁻¹ := by
  rw [mul_comm, h.div_mul_cancel_right]

@[to_additive]
protected lemma div_mul_right (h : IsUnit a) (b : α) : a / (a * b) = 1 / b := by
  rw [mul_comm, h.div_mul_left]

@[to_additive]
protected lemma mul_div_cancel_left (h : IsUnit a) (b : α) : a * b / a = b := by
  rw [mul_comm, h.mul_div_cancel_right]

@[to_additive]
protected lemma mul_div_cancel (h : IsUnit a) (b : α) : a * (b / a) = b := by
  rw [mul_comm, h.div_mul_cancel]

@[to_additive]
protected lemma mul_div_mul_left (h : IsUnit c) (a b : α) : c * a / (c * b) = a / b := by
  rw [mul_comm c, mul_comm c, h.mul_div_mul_right]

@[to_additive]
protected lemma mul_eq_mul_of_div_eq_div (hb : IsUnit b) (hd : IsUnit d)
    (a c : α) (h : a / b = c / d) : a * d = c * b := by
  rw [← mul_one a, ← hb.div_self, ← mul_comm_div, h, div_mul_eq_mul_div, hd.div_mul_cancel]

@[to_additive]
protected lemma div_eq_div_iff (hb : IsUnit b) (hd : IsUnit d) :
    a / b = c / d ↔ a * d = c * b := by
  rw [← (hb.mul hd).mul_left_inj, ← mul_assoc, hb.div_mul_cancel, ← mul_assoc, mul_right_comm,
    hd.div_mul_cancel]

@[to_additive]
protected lemma div_div_cancel (h : IsUnit a) : a / (a / b) = b := by
  rw [div_div_eq_mul_div, h.mul_div_cancel_left]

@[to_additive]
protected lemma div_div_cancel_left (h : IsUnit a) : a / b / a = b⁻¹ := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, h.mul_inv_cancel, one_mul]

end DivisionCommMonoid
end IsUnit

@[field_simps]
lemma divp_eq_div [DivisionMonoid α] (a : α) (u : αˣ) : a /ₚ u = a / u := by
  rw [div_eq_mul_inv, divp, u.val_inv_eq_inv_val]

@[to_additive]
lemma Group.isUnit [Group α] (a : α) : IsUnit a := ⟨⟨a, a⁻¹, mul_inv_self _, inv_mul_self _⟩, rfl⟩

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
    mul_left_inv := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }

/-- Constructs a `CommGroup` structure on a `CommMonoid` consisting only of units. -/
noncomputable def commGroupOfIsUnit [hM : CommMonoid M] (h : ∀ a : M, IsUnit a) : CommGroup M :=
  { hM with
    toInv := invOfIsUnit h,
    mul_left_inv := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }

end NoncomputableDefs

attribute [deprecated div_mul_cancel_right (since := "2024-03-20")] IsUnit.div_mul_left
attribute [deprecated sub_add_cancel_right (since := "2024-03-20")] IsAddUnit.sub_add_left
attribute [deprecated div_mul_cancel_left (since := "2024-03-20")] IsUnit.div_mul_right
attribute [deprecated sub_add_cancel_left (since := "2024-03-20")] IsAddUnit.sub_add_right
-- The names `IsUnit.mul_div_cancel` and `IsAddUnit.add_sub_cancel` have been reused
-- @[deprecated (since := "2024-03-20")] alias IsUnit.mul_div_cancel := IsUnit.mul_div_cancel_right
-- @[deprecated (since := "2024-03-20")]
-- alias IsAddUnit.add_sub_cancel := IsAddUnit.add_sub_cancel_right
@[deprecated (since := "2024-03-20")] alias IsUnit.mul_div_cancel' := IsUnit.mul_div_cancel
@[deprecated (since := "2024-03-20")] alias IsAddUnit.add_sub_cancel' := IsAddUnit.add_sub_cancel
