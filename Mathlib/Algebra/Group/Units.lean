/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes Hölzl, Chris Hughes, Jens Wagemaker, Jon Eugster
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Logic.Nontrivial
import Mathlib.Logic.Unique
import Mathlib.Tactic.Nontriviality
import Mathlib.Tactic.Simps.Basic

/-!
# Units (i.e., invertible elements) of a monoid

An element of a `Monoid` is a unit if it has a two-sided inverse.

## Main declarations

* `Units M`: the group of units (i.e., invertible elements) of a monoid.
* `isUnit x`: a predicate asserting that `x` is a unit (i.e., invertible element) of a monoid.

For both declarations, there is an additive counterpart: `AddUnits` and `OsAddUnit`.

## Notation

We provide `Mˣ` as notation for `Units M`,
resembling the notation $R^{\times}$ for the units of a ring, which is common in mathematics.

-/


open Function

universe u

variable {α : Type u}

/-- Units of a `monoid`, bundled version. Notation: `αˣ`.

An element of a `monoid` is a unit if it has a two-sided inverse.
This version bundles the inverse element so that it can be computed.
For a predicate see `isUnit`. -/
structure Units (α : Type u) [Monoid α] where
  /-- The underlying value in the base `Monoid`. -/
  val : α
  /-- The inverse value of `val` in the base `Monoid`. -/
  inv : α
  /-- `inv` is the right inverse of `val` in the base `Monoid`. -/
  val_inv : val * inv = 1
  /-- `inv` is the left inverse of `val` in the base `Monoid`. -/
  inv_val : inv * val = 1

-- mathport name: «expr ˣ»
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

attribute [to_additive AddUnits] Units

section HasElem

@[to_additive]
theorem unique_has_one {α : Type _} [Unique α] [One α] : default = (1 : α) :=
  Unique.default_eq 1

end HasElem

namespace Units

variable [Monoid α]

instance : Coe αˣ α :=
  ⟨val⟩

-- Porting note: `to_additive` didn't generate this
variable {β : Type _} [AddMonoid β] in
instance : Coe (AddUnits β) β :=
  ⟨AddUnits.val⟩

attribute [to_additive instCoeAddUnits] instCoeUnits

-- Porting note: `to_additive` names the instance `instInvUnits` currently
@[to_additive AddUnits.instNegAddUnits]
instance : Inv αˣ :=
  ⟨fun u => ⟨u.2, u.1, u.4, u.3⟩⟩

-- Porting note: before, had `@[to_additive " See Note [custom simps projection] "]`
/-- See Note [custom simps projection] -/
@[to_additive]
def Simps.coe (u : αˣ) : α :=
  u

-- Porting note: before, had `@[to_additive " See Note [custom simps projection] "]`
/-- See Note [custom simps projection] -/
@[to_additive]
def Simps.coeInv (u : αˣ) : α :=
  ((u⁻¹ : αˣ) : α)

initialize_simps_projections Units (val → coe as_prefix, inv → coeInv as_prefix)

initialize_simps_projections AddUnits (val → coe as_prefix, neg → coeNeg as_prefix)

-- Porting note: removed `simp` tag because of the tautology
@[to_additive]
theorem coe_mk (a : α) (b h₁ h₂) : ↑(Units.mk a b h₁ h₂) = a :=
  rfl

@[ext]
theorem ext : Function.Injective (fun (u : αˣ) => (u : α))
  | ⟨v, i₁, vi₁, iv₁⟩, ⟨v', i₂, vi₂, iv₂⟩, e => by
    simp only at e; subst v'; congr;
    simpa only [iv₂, vi₁, one_mul, mul_one] using mul_assoc i₂ v i₁

-- Porting note: `@[ext, to_additive]` didn't work on it's own
attribute [to_additive] Units.ext.match_1
attribute [to_additive] Units.ext

-- Porting note: "norm_cast: badly shaped lemma, lhs must contain at least one coe"
-- so `@[norm_cast]` removed
@[to_additive]
theorem eq_iff {a b : αˣ} : (a : α) = b ↔ a = b :=
  ext.eq_iff

@[to_additive]
theorem ext_iff {a b : αˣ} : a = b ↔ (a : α) = b :=
  eq_iff.symm

@[to_additive]
instance [DecidableEq α] : DecidableEq αˣ := fun _ _ => decidable_of_iff' _ ext_iff

@[simp, to_additive]
theorem mk_coe (u : αˣ) (y h₁ h₂) : mk (u : α) y h₁ h₂ = u :=
  ext rfl

/-- Copy a unit, adjusting definition equalities. -/
@[to_additive "Copy an `add_unit`, adjusting definitional equalities.", simps]
def copy (u : αˣ) (val : α) (hv : val = u) (inv : α) (hi : inv = ↑u⁻¹) : αˣ :=
  { val, inv, inv_val := hv.symm ▸ hi.symm ▸ u.inv_val, val_inv := hv.symm ▸ hi.symm ▸ u.val_inv }

@[to_additive]
theorem copy_eq (u : αˣ) (val hv inv hi) : u.copy val hv inv hi = u :=
  ext hv

@[to_additive]
instance : MulOneClass αˣ where
  mul u₁ u₂ :=
    ⟨u₁.val * u₂.val, u₂.inv * u₁.inv,
      by rw [mul_assoc, ← mul_assoc u₂.val, val_inv, one_mul, val_inv],
      by rw [mul_assoc, ← mul_assoc u₁.inv, inv_val, one_mul, inv_val]⟩
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

@[to_additive]
instance {α} [CommMonoid α] : CommGroup αˣ :=
  { (inferInstance : Group αˣ) with
    mul_comm := fun _ _ => ext <| mul_comm _ _ }

@[to_additive]
instance : Inhabited αˣ :=
  ⟨1⟩

@[to_additive]
instance [Repr α] : Repr αˣ :=
  ⟨reprPrec ∘ val⟩

variable (a b c : αˣ) {u : αˣ}

-- Porting note: "norm_cast: badly shaped lemma, lhs must contain at least one coe"
-- so `@[norm_cast]` removed
@[simp, to_additive]
theorem coe_mul : (↑(a * b) : α) = a * b :=
  rfl

-- Porting note: "norm_cast: badly shaped lemma, lhs must contain at least one coe"
-- so `@[norm_cast]` removed
@[simp, to_additive]
theorem coe_one : ((1 : αˣ) : α) = 1 :=
  rfl

-- Porting note: "norm_cast: badly shaped lemma, lhs must contain at least one coe"
-- so `@[norm_cast]` removed
@[simp, to_additive]
theorem coe_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1 := by rw [← Units.coe_one, eq_iff]

@[simp, to_additive]
theorem inv_mk (x y : α) (h₁ h₂) : (mk x y h₁ h₂)⁻¹ = mk y x h₂ h₁ :=
  rfl

@[simp, to_additive]
theorem val_eq_coe : a.val = (↑a : α) :=
  rfl

@[simp, to_additive]
theorem inv_eq_coe_inv : a.inv = ((a⁻¹ : αˣ) : α) :=
  rfl

@[simp, to_additive]
theorem inv_mul : (↑a⁻¹ * a : α) = 1 :=
  inv_val _

@[simp, to_additive]
theorem mul_inv : (a * ↑a⁻¹ : α) = 1 :=
  val_inv _

@[to_additive]
theorem inv_mul_of_eq {a : α} (h : ↑u = a) : ↑u⁻¹ * a = 1 := by rw [← h, u.inv_mul]

@[to_additive]
theorem mul_inv_of_eq {a : α} (h : ↑u = a) : a * ↑u⁻¹ = 1 := by rw [← h, u.mul_inv]

@[simp, to_additive]
theorem mul_inv_cancel_left (a : αˣ) (b : α) : (a : α) * (↑a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv, one_mul]

@[simp, to_additive]
theorem inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ : α) * (a * b) = b := by
  rw [← mul_assoc, inv_mul, one_mul]

@[simp, to_additive]
theorem mul_inv_cancel_right (a : α) (b : αˣ) : a * b * ↑b⁻¹ = a := by
  rw [mul_assoc, mul_inv, mul_one]

@[simp, to_additive]
theorem inv_mul_cancel_right (a : α) (b : αˣ) : a * ↑b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul, mul_one]

@[simp, to_additive]
theorem mul_right_inj (a : αˣ) {b c : α} : (a : α) * b = a * c ↔ b = c :=
  ⟨fun h => by simpa only [inv_mul_cancel_left] using congr_arg (fun x : α => ↑(a⁻¹ : αˣ) * x) h,
    congr_arg _⟩

@[simp, to_additive]
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

@[simp, to_additive]
theorem mul_inv_eq_one {a : α} : a * ↑u⁻¹ = 1 ↔ a = u :=
  ⟨inv_inv u ▸ Units.eq_inv_of_mul_eq_one_right, fun h => mul_inv_of_eq h.symm⟩

@[simp, to_additive]
theorem inv_mul_eq_one {a : α} : ↑u⁻¹ * a = 1 ↔ ↑u = a :=
  ⟨inv_inv u ▸ Units.inv_eq_of_mul_eq_one_right, inv_mul_of_eq⟩

@[to_additive]
theorem mul_eq_one_iff_eq_inv {a : α} : a * u = 1 ↔ a = ↑u⁻¹ := by rw [← mul_inv_eq_one, inv_inv]

@[to_additive]
theorem mul_eq_one_iff_inv_eq {a : α} : ↑u * a = 1 ↔ ↑u⁻¹ = a := by rw [← inv_mul_eq_one, inv_inv]

@[to_additive]
theorem inv_unique {u₁ u₂ : αˣ} (h : (↑u₁ : α) = ↑u₂) : (↑u₁⁻¹ : α) = ↑u₂⁻¹ :=
  Units.inv_eq_of_mul_eq_one_right <| by rw [h, u₂.mul_inv]

@[simp, to_additive]
theorem coe_inv {M : Type _} [DivisionMonoid M] (u : Units M) : ↑u⁻¹ = (u⁻¹ : M) :=
  Eq.symm <| inv_eq_of_mul_eq_one_right u.mul_inv

end Units

/-- For `a, b` in a `comm_monoid` such that `a * b = 1`, makes a unit out of `a`. -/
@[to_additive
  "For `a, b` in an `add_comm_monoid` such that `a + b = 0`, makes an add_unit\nout of `a`."]
def Units.mkOfMulEqOne [CommMonoid α] (a b : α) (hab : a * b = 1) : αˣ :=
  ⟨a, b, hab, (mul_comm b a).trans hab⟩

@[simp, to_additive]
theorem Units.coe_mkOfMulEqOne [CommMonoid α] {a b : α} (h : a * b = 1) :
    (Units.mkOfMulEqOne a b h : α) = a :=
  rfl
#align units.coe_mk_of_mul_eq_one Units.coe_mkOfMulEqOne

section Monoid

variable [Monoid α] {a b c : α}

/-- Partial division. It is defined when the
  second argument is invertible, and unlike the division operator
  in `division_ring` it is not totalized at zero. -/
def divp (a : α) (u : Units α) : α :=
  a * (u⁻¹ : αˣ)

-- mathport name: «expr /ₚ »
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
  simp only [divp, mul_inv_rev, Units.coe_mul, mul_assoc]

@[field_simps]
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
theorem coe_div_eq_divp (u₁ u₂ : αˣ) : ↑(u₁ / u₂) = ↑u₁ /ₚ u₂ := by
  rw [divp, division_def, Units.coe_mul]

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

end CommMonoid

/-!
# `IsUnit` predicate

In this file we define the `IsUnit` predicate on a `MOnoid`, and
prove a few basic properties. For the bundled version see `Units`. See
also `Prime`, `Associated`, and `Irreducible` in `Algebra.Associated`.

-/


section IsUnit

variable {M : Type _} {N : Type _}

/-- An element `a : M` of a monoid is a unit if it has a two-sided inverse.
The actual definition says that `a` is equal to some `u : Mˣ`, where
`Mˣ` is a bundled version of `IsUnit`. -/
@[to_additive IsAddUnit
      "An element `a : M` of an AddMonoid is an `AddUnit` if it has\na two-sided additive inverse.
      The actual definition says that `a` is equal to some\n`u : add_units M`,
      where `AddUnits M` is a bundled version of `IsAddUnit`."]
def IsUnit [Monoid M] (a : M) : Prop :=
  ∃ u : Mˣ, (u : M) = a

@[nontriviality, to_additive isAddUnit_of_subsingleton]
theorem isUnit_of_subsingleton [Monoid M] [Subsingleton M] (a : M) : IsUnit a :=
  ⟨⟨a, a, Subsingleton.elim _ _, Subsingleton.elim _ _⟩, rfl⟩
#align is_unit_of_subsingleton isUnit_of_subsingleton
#align is_add_unit_of_subsingleton isAddUnit_of_subsingleton

attribute [nontriviality] isAddUnit_of_subsingleton

-- Porting note: removing the `CanLift` instance

@[to_additive]
instance [Monoid M] [Subsingleton M] : Unique Mˣ where
  default := 1
  uniq a := Units.coe_eq_one.mp <| Subsingleton.elim (a : M) 1

@[simp, to_additive isAddUnit_AddUnit]
protected theorem Units.isUnit [Monoid M] (u : Mˣ) : IsUnit (u : M) :=
  ⟨u, rfl⟩
#align units.is_unit Units.isUnit
#align is_add_unit_add_unit isAddUnit_Add_unit

@[simp, to_additive]
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
  exact ⟨b, hab⟩

@[to_additive IsAddUnit.exists_neg']
theorem IsUnit.exists_left_inv [Monoid M] {a : M} (h : IsUnit a) : ∃ b, b * a = 1 := by
  rcases h with ⟨⟨a, b, _, hba⟩, rfl⟩
  exact ⟨b, hba⟩

-- Porting note: have to explicitly tag `match_1` and give names
theorem isUnit_iff_exists_inv [CommMonoid M] {a : M} : IsUnit a ↔ ∃ b, a * b = 1 :=
  ⟨fun h => h.exists_right_inv, fun ⟨b, hab⟩ => isUnit_of_mul_eq_one _ b hab⟩
attribute [to_additive isAddUnit_iff_exists_neg.match_1] isUnit_iff_exists_inv.match_1
attribute [to_additive isAddUnit_iff_exists_neg] isUnit_iff_exists_inv
#align is_unit_iff_exists_inv isUnit_iff_exists_inv
#align is_add_unit_iff_exists_neg isAddUnit_iff_exists_neg

theorem isUnit_iff_exists_inv' [CommMonoid M] {a : M} : IsUnit a ↔ ∃ b, b * a = 1 := by
  simp [isUnit_iff_exists_inv, mul_comm]
#align is_unit_iff_exists_inv' isUnit_iff_exists_inv'

-- Porting note: manually added because `to_additive` complained
theorem isAddUnit_iff_exists_neg' [AddCommMonoid M] {a : M} : IsAddUnit a ↔ ∃ b, b + a = 0 := by
  simp [isAddUnit_iff_exists_neg, add_comm]
attribute [to_additive isAddUnit_iff_exists_neg'] isUnit_iff_exists_inv'
#align is_add_unit_iff_exists_neg' isAddUnit_iff_exists_neg'

@[to_additive]
theorem IsUnit.mul [Monoid M] {x y : M} : IsUnit x → IsUnit y → IsUnit (x * y) := by
  rintro ⟨x, rfl⟩ ⟨y, rfl⟩
  exact ⟨x * y, Units.coe_mul _ _⟩

-- Porting note: have to explicitly tag `match_1`
/-- Multiplication by a `u : Mˣ` on the right doesn't affect `IsUnit`. -/
@[simp]
theorem Units.isUnit_mul_units [Monoid M] (a : M) (u : Mˣ) : IsUnit (a * u) ↔ IsUnit a :=
  Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (a * ↑u * ↑u⁻¹) := by exists v * u⁻¹; rw [← hv, Units.coe_mul]
      rwa [mul_assoc, Units.mul_inv, mul_one] at this)
    fun v => v.mul u.isUnit
attribute [to_additive] Units.isUnit_mul_units.match_1
attribute [to_additive
  "Addition of a `u : add_units M` on the right doesn't\naffect `IsAddUnit`."]
  Units.isUnit_mul_units
#align units.is_unit_mul_units isUnit_mul_units
#align add_units.is_add_unit_add_add_units isAddUnit_add_addUnits

-- Porting note: have to explicitly tag `match_1`
/-- Multiplication by a `u : Mˣ` on the left doesn't affect `IsUnit`. -/
@[simp]
theorem Units.isUnit_units_mul {M : Type _} [Monoid M] (u : Mˣ) (a : M) :
    IsUnit (↑u * a) ↔ IsUnit a :=
  Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (↑u⁻¹ * (↑u * a)) := by exists u⁻¹ * v; rw [← hv, Units.coe_mul]
      rwa [← mul_assoc, Units.inv_mul, one_mul] at this)
    u.isUnit.mul
#align units.is_unit_units_mul Units.isUnit_units_mul
attribute [to_additive] Units.isUnit_units_mul.match_1
attribute [to_additive "Addition of a `u : add_units M` on the left doesn't affect `IsAddUnit`."]
  Units.isUnit_units_mul
#align add_units.is_add_unit_units_add AddUnits.isAddUnit_units_add

-- Porting note: have to explicitly tag `match_1` and give names
theorem isUnit_of_mul_isUnit_left [CommMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit x :=
  let ⟨z, hz⟩ := isUnit_iff_exists_inv.1 hu
  isUnit_iff_exists_inv.2 ⟨y * z, by rwa [← mul_assoc]⟩
#align is_unit_of_mul_is_unit_left isUnit_of_mul_isUnit_left
attribute [to_additive isAddUnit_of_add_isAddUnit_left.match_1] isUnit_of_mul_isUnit_left.match_1
attribute [to_additive isAddUnit_of_add_isAddUnit_left] isUnit_of_mul_isUnit_left
#align is_add_unit_of_add_is_unit_left isAddUnit_of_add_isAddUnit_left

@[to_additive]
theorem isUnit_of_mul_isUnit_right [CommMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit y :=
  @isUnit_of_mul_isUnit_left _ _ y x <| by rwa [mul_comm]
#align is_unit_of_mul_is_unit_right isUnit_of_mul_isUnit_right
#align is_add_unit_of_add_is_unit_right isAddUnit_of_add_isAddUnit_right

namespace IsUnit

@[simp, to_additive]
theorem mul_iff [CommMonoid M] {x y : M} : IsUnit (x * y) ↔ IsUnit x ∧ IsUnit y :=
  ⟨fun h => ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩,
   fun h => IsUnit.mul h.1 h.2⟩

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
#align is_add_unit.add_unit IsUnit.addUnit
attribute [to_additive IsAddUnit.addUnit] IsUnit.unit

@[simp, to_additive]
theorem unit_of_coe_units {a : Mˣ} (h : IsUnit (a : M)) : h.unit = a :=
  Units.ext <| rfl

@[simp, to_additive]
theorem unit_spec (h : IsUnit a) : ↑h.unit = a :=
  rfl

@[simp, to_additive]
theorem coe_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1 :=
  Units.mul_inv _

-- Porting note: mathlib3 proof used `convert`
@[simp, to_additive]
theorem mul_coe_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1 := by
  rw [←h.unit.mul_inv]; congr

/-- `IsUnit x` is decidable if we can decide if `x` comes from `Mˣ`. -/
instance (x : M) [h : Decidable (∃ u : Mˣ, ↑u = x)] : Decidable (IsUnit x) :=
  h

-- Porting note: have to explicitly tag `match_1`
theorem mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_left_inj
attribute [to_additive] mul_left_inj.match_1
attribute [to_additive] mul_left_inj

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
protected theorem mul_right_injective (h : IsUnit a) : Injective ((· * ·) a) :=
  fun _ _ => h.mul_left_cancel

@[to_additive]
protected theorem mul_left_injective (h : IsUnit b) : Injective (· * b) :=
  fun _ _ => h.mul_right_cancel

end Monoid

variable [DivisionMonoid M] {a : M}

@[simp, to_additive]
protected theorem inv_mul_cancel : IsUnit a → a⁻¹ * a = 1 := by
  rintro ⟨u, rfl⟩
  rw [← Units.coe_inv, Units.inv_mul]

@[simp, to_additive]
protected theorem mul_inv_cancel : IsUnit a → a * a⁻¹ = 1 := by
  rintro ⟨u, rfl⟩
  rw [← Units.coe_inv, Units.mul_inv]

end IsUnit

-- namespace
end IsUnit

-- section
section NoncomputableDefs

variable {M : Type _}

/-- Constructs a `group` structure on a `monoid` consisting only of units. -/
noncomputable def groupOfIsUnit [hM : Monoid M] (h : ∀ a : M, IsUnit a) : Group M :=
  { hM with
    inv := fun a => ↑(h a).unit⁻¹,
    mul_left_inv := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }

/-- Constructs a `comm_group` structure on a `comm_monoid` consisting only of units. -/
noncomputable def commGroupOfIsUnit [hM : CommMonoid M] (h : ∀ a : M, IsUnit a) : CommGroup M :=
  { hM with
    inv := fun a => ↑(h a).unit⁻¹,
    mul_left_inv := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }

end NoncomputableDefs
