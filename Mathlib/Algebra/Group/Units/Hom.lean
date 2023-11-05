/-
Copyright (c) 2018 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes, Kevin Buzzard
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Units

#align_import algebra.hom.units from "leanprover-community/mathlib"@"a07d750983b94c530ab69a726862c2ab6802b38c"

/-!
# Monoid homomorphisms and units

This file allows to lift monoid homomorphisms to group homomorphisms of their units subgroups. It
also contains unrelated results about `Units` that depend on `MonoidHom`.

## Main declarations

* `Units.map`: Turn a homomorphism from `α` to `β` monoids into a homomorphism from `αˣ` to `βˣ`.
* `MonoidHom.toHomUnits`: Turn a homomorphism from a group `α` to `β` into a homomorphism from
  `α` to `βˣ`.

## TODO

The results that don't mention homomorphisms should be proved (earlier?) in a different file and be
used to golf the basic `Group` lemmas.
-/


open Function

universe u v w

@[to_additive]
theorem Group.isUnit {G} [Group G] (g : G) : IsUnit g :=
  ⟨⟨g, g⁻¹, mul_inv_self g, inv_mul_self g⟩, rfl⟩

section MonoidHomClass

/-- If two homomorphisms from a division monoid to a monoid are equal at a unit `x`, then they are
equal at `x⁻¹`. -/
@[to_additive
  "If two homomorphisms from a subtraction monoid to an additive monoid are equal at an
  additive unit `x`, then they are equal at `-x`."]
theorem IsUnit.eq_on_inv {F G N} [DivisionMonoid G] [Monoid N] [MonoidHomClass F G N]
    {x : G} (hx : IsUnit x) (f g : F) (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
  left_inv_eq_right_inv (map_mul_eq_one f hx.inv_mul_cancel)
    (h.symm ▸ map_mul_eq_one g (hx.mul_inv_cancel))

/-- If two homomorphism from a group to a monoid are equal at `x`, then they are equal at `x⁻¹`. -/
@[to_additive
    "If two homomorphism from an additive group to an additive monoid are equal at `x`,
    then they are equal at `-x`."]
theorem eq_on_inv {F G M} [Group G] [Monoid M] [MonoidHomClass F G M]
    (f g : F) {x : G} (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
  (Group.isUnit x).eq_on_inv f g h

end MonoidHomClass

namespace Units

variable {α : Type*} {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

/-- The group homomorphism on units induced by a `MonoidHom`. -/
@[to_additive "The additive homomorphism on `AddUnit`s induced by an `AddMonoidHom`."]
def map (f : M →* N) : Mˣ →* Nˣ :=
  MonoidHom.mk'
    (fun u => ⟨f u.val, f u.inv,
      by rw [← f.map_mul, u.val_inv, f.map_one],
      by rw [← f.map_mul, u.inv_val, f.map_one]⟩)
    fun x y => ext (f.map_mul x y)

@[to_additive (attr := simp)]
theorem coe_map (f : M →* N) (x : Mˣ) : ↑(map f x) = f x := rfl

@[to_additive (attr := simp)]
theorem coe_map_inv (f : M →* N) (u : Mˣ) : ↑(map f u)⁻¹ = f ↑u⁻¹ := rfl

@[to_additive (attr := simp)]
theorem map_comp (f : M →* N) (g : N →* P) : map (g.comp f) = (map g).comp (map f) := rfl

variable (M)

@[to_additive (attr := simp)]
theorem map_id : map (MonoidHom.id M) = MonoidHom.id Mˣ := by ext; rfl

/-- Coercion `Mˣ → M` as a monoid homomorphism. -/
@[to_additive "Coercion `AddUnits M → M` as an AddMonoid homomorphism."]
def coeHom : Mˣ →* M where
  toFun := Units.val; map_one' := val_one; map_mul' := val_mul

variable {M}

@[to_additive (attr := simp)]
theorem coeHom_apply (x : Mˣ) : coeHom M x = ↑x := rfl

@[to_additive (attr := simp, norm_cast)]
theorem val_pow_eq_pow_val (u : Mˣ) (n : ℕ) : ((u ^ n : Mˣ) : M) = (u : M) ^ n :=
  (Units.coeHom M).map_pow u n

section DivisionMonoid

variable [DivisionMonoid α]

@[to_additive (attr := simp, norm_cast)]
theorem val_div_eq_div_val : ∀ u₁ u₂ : αˣ, ↑(u₁ / u₂) = (u₁ / u₂ : α) :=
  (Units.coeHom α).map_div

@[to_additive (attr := simp, norm_cast)]
theorem val_zpow_eq_zpow_val : ∀ (u : αˣ) (n : ℤ), ((u ^ n : αˣ) : α) = (u : α) ^ n :=
  (Units.coeHom α).map_zpow

@[field_simps]
theorem _root_.divp_eq_div (a : α) (u : αˣ) : a /ₚ u = a / u :=
  by rw [div_eq_mul_inv, divp, u.val_inv_eq_inv_val]

@[to_additive (attr := simp)]
theorem _root_.map_units_inv {F : Type*} [MonoidHomClass F M α] (f : F) (u : Units M) :
    f ↑u⁻¹ = (f u)⁻¹ := ((f : M →* α).comp (Units.coeHom M)).map_inv u

end DivisionMonoid

/-- If a map `g : M → Nˣ` agrees with a homomorphism `f : M →* N`, then
this map is a monoid homomorphism too. -/
@[to_additive
  "If a map `g : M → AddUnits N` agrees with a homomorphism `f : M →+ N`, then this map
  is an AddMonoid homomorphism too."]
def liftRight (f : M →* N) (g : M → Nˣ) (h : ∀ x, ↑(g x) = f x) : M →* Nˣ where
  toFun := g
  map_one' := by ext; dsimp only; rw [h 1]; exact f.map_one -- Porting note: why is `dsimp` needed?
  map_mul' x y := Units.ext <| by simp only [h, val_mul, f.map_mul]

@[to_additive (attr := simp)]
theorem coe_liftRight {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) :
    (liftRight f g h x : N) = f x := h x

@[to_additive (attr := simp)]
theorem mul_liftRight_inv {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) :
    f x * ↑(liftRight f g h x)⁻¹ = 1 :=
  by rw [Units.mul_inv_eq_iff_eq_mul, one_mul, coe_liftRight]

@[to_additive (attr := simp)]
theorem liftRight_inv_mul {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) :
    ↑(liftRight f g h x)⁻¹ * f x = 1 :=
  by rw [Units.inv_mul_eq_iff_eq_mul, mul_one, coe_liftRight]

end Units

namespace MonoidHom

/-- If `f` is a homomorphism from a group `G` to a monoid `M`,
then its image lies in the units of `M`,
and `f.toHomUnits` is the corresponding monoid homomorphism from `G` to `Mˣ`. -/
@[to_additive
  "If `f` is a homomorphism from an additive group `G` to an additive monoid `M`,
  then its image lies in the `AddUnits` of `M`,
  and `f.toHomUnits` is the corresponding homomorphism from `G` to `AddUnits M`."]
def toHomUnits {G M : Type*} [Group G] [Monoid M] (f : G →* M) : G →* Mˣ :=
  Units.liftRight f (fun g => ⟨f g, f g⁻¹, map_mul_eq_one f (mul_inv_self _),
    map_mul_eq_one f (inv_mul_self _)⟩)
    fun _ => rfl

@[to_additive (attr := simp)]
theorem coe_toHomUnits {G M : Type*} [Group G] [Monoid M] (f : G →* M) (g : G) :
    (f.toHomUnits g : M) = f g := rfl

end MonoidHom

namespace IsUnit

variable {F G α M N : Type*}

section Monoid

variable [Monoid M] [Monoid N]

@[to_additive]
theorem map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : IsUnit (f x) := by
  rcases h with ⟨y, rfl⟩; exact (Units.map (f : M →* N) y).isUnit

@[to_additive]
theorem of_leftInverse [MonoidHomClass F M N] [MonoidHomClass G N M] {f : F} {x : M} (g : G)
    (hfg : Function.LeftInverse g f) (h : IsUnit (f x)) : IsUnit x := by
  simpa only [hfg x] using h.map g

@[to_additive]
theorem _root_.isUnit_map_of_leftInverse [MonoidHomClass F M N] [MonoidHomClass G N M]
    {f : F} {x : M} (g : G) (hfg : Function.LeftInverse g f) :
    IsUnit (f x) ↔ IsUnit x := ⟨of_leftInverse g hfg, map _⟩

/-- If a homomorphism `f : M →* N` sends each element to an `IsUnit`, then it can be lifted
to `f : M →* Nˣ`. See also `Units.liftRight` for a computable version. -/
@[to_additive
  "If a homomorphism `f : M →+ N` sends each element to an `IsAddUnit`, then it can be
  lifted to `f : M →+ AddUnits N`. See also `AddUnits.liftRight` for a computable version."]
noncomputable def liftRight (f : M →* N) (hf : ∀ x, IsUnit (f x)) : M →* Nˣ :=
  (Units.liftRight f fun x => (hf x).unit) fun _ => rfl

@[to_additive]
theorem coe_liftRight (f : M →* N) (hf : ∀ x, IsUnit (f x)) (x) :
    (IsUnit.liftRight f hf x : N) = f x := rfl

@[to_additive (attr := simp)]
theorem mul_liftRight_inv (f : M →* N) (h : ∀ x, IsUnit (f x)) (x) :
    f x * ↑(IsUnit.liftRight f h x)⁻¹ = 1 := Units.mul_liftRight_inv (by intro; rfl) x

@[to_additive (attr := simp)]
theorem liftRight_inv_mul (f : M →* N) (h : ∀ x, IsUnit (f x)) (x) :
    ↑(IsUnit.liftRight f h x)⁻¹ * f x = 1 := Units.liftRight_inv_mul (by intro; rfl) x

end Monoid

section DivisionMonoid

variable [DivisionMonoid α] {a b c : α}

/-- The element of the group of units, corresponding to an element of a monoid which is a unit. As
opposed to `IsUnit.unit`, the inverse is computable and comes from the inversion on `α`. This is
useful to transfer properties of inversion in `Units α` to `α`. See also `toUnits`. -/
@[to_additive (attr := simps val)
  "The element of the additive group of additive units, corresponding to an element of
  an additive monoid which is an additive unit. As opposed to `IsAddUnit.addUnit`, the negation is
  computable and comes from the negation on `α`. This is useful to transfer properties of negation
  in `AddUnits α` to `α`. See also `toAddUnits`."]
def unit' (h : IsUnit a) : αˣ :=
  ⟨a, a⁻¹, h.mul_inv_cancel, h.inv_mul_cancel⟩

-- Porting note: TODO: `simps val_inv` fails
@[to_additive] theorem val_inv_unit' (h : IsUnit a) : ↑(h.unit'⁻¹) = a⁻¹ := rfl

@[to_additive (attr := simp)]
protected theorem mul_inv_cancel_left (h : IsUnit a) : ∀ b, a * (a⁻¹ * b) = b :=
  h.unit'.mul_inv_cancel_left

@[to_additive (attr := simp)]
protected theorem inv_mul_cancel_left (h : IsUnit a) : ∀ b, a⁻¹ * (a * b) = b :=
  h.unit'.inv_mul_cancel_left

@[to_additive (attr := simp)]
protected theorem mul_inv_cancel_right (h : IsUnit b) (a : α) : a * b * b⁻¹ = a :=
  h.unit'.mul_inv_cancel_right _

@[to_additive (attr := simp)]
protected theorem inv_mul_cancel_right (h : IsUnit b) (a : α) : a * b⁻¹ * b = a :=
  h.unit'.inv_mul_cancel_right _

@[to_additive]
protected theorem div_self (h : IsUnit a) : a / a = 1 := by rw [div_eq_mul_inv, h.mul_inv_cancel]

@[to_additive]
protected theorem eq_mul_inv_iff_mul_eq (h : IsUnit c) : a = b * c⁻¹ ↔ a * c = b :=
  h.unit'.eq_mul_inv_iff_mul_eq

@[to_additive]
protected theorem eq_inv_mul_iff_mul_eq (h : IsUnit b) : a = b⁻¹ * c ↔ b * a = c :=
  h.unit'.eq_inv_mul_iff_mul_eq

@[to_additive]
protected theorem inv_mul_eq_iff_eq_mul (h : IsUnit a) : a⁻¹ * b = c ↔ b = a * c :=
  h.unit'.inv_mul_eq_iff_eq_mul

@[to_additive]
protected theorem mul_inv_eq_iff_eq_mul (h : IsUnit b) : a * b⁻¹ = c ↔ a = c * b :=
  h.unit'.mul_inv_eq_iff_eq_mul

@[to_additive]
protected theorem mul_inv_eq_one (h : IsUnit b) : a * b⁻¹ = 1 ↔ a = b :=
  @Units.mul_inv_eq_one _ _ h.unit' _

@[to_additive]
protected theorem inv_mul_eq_one (h : IsUnit a) : a⁻¹ * b = 1 ↔ a = b :=
  @Units.inv_mul_eq_one _ _ h.unit' _

@[to_additive]
protected theorem mul_eq_one_iff_eq_inv (h : IsUnit b) : a * b = 1 ↔ a = b⁻¹ :=
  @Units.mul_eq_one_iff_eq_inv _ _ h.unit' _

@[to_additive]
protected theorem mul_eq_one_iff_inv_eq (h : IsUnit a) : a * b = 1 ↔ a⁻¹ = b :=
  @Units.mul_eq_one_iff_inv_eq _ _ h.unit' _

@[to_additive (attr := simp)]
protected theorem div_mul_cancel (h : IsUnit b) (a : α) : a / b * b = a := by
  rw [div_eq_mul_inv, h.inv_mul_cancel_right]

@[to_additive (attr := simp)]
protected theorem mul_div_cancel (h : IsUnit b) (a : α) : a * b / b = a := by
  rw [div_eq_mul_inv, h.mul_inv_cancel_right]

@[to_additive]
protected theorem mul_one_div_cancel (h : IsUnit a) : a * (1 / a) = 1 := by simp [h]

@[to_additive]
protected theorem one_div_mul_cancel (h : IsUnit a) : 1 / a * a = 1 := by simp [h]

@[to_additive]
theorem inv (h : IsUnit a) : IsUnit a⁻¹ := by
  rcases h with ⟨u, hu⟩
  rw [←hu, ← Units.val_inv_eq_inv_val]
  exact Units.isUnit _

@[to_additive]
theorem div (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a / b) := by
  rw [div_eq_mul_inv]
  exact ha.mul hb.inv

@[to_additive]
protected theorem div_left_inj (h : IsUnit c) : a / c = b / c ↔ a = b := by
  simp only [div_eq_mul_inv]
  exact Units.mul_left_inj h.inv.unit'

@[to_additive]
protected theorem div_eq_iff (h : IsUnit b) : a / b = c ↔ a = c * b := by
  rw [div_eq_mul_inv, h.mul_inv_eq_iff_eq_mul]

@[to_additive]
protected theorem eq_div_iff (h : IsUnit c) : a = b / c ↔ a * c = b := by
  rw [div_eq_mul_inv, h.eq_mul_inv_iff_mul_eq]

@[to_additive]
protected theorem div_eq_of_eq_mul (h : IsUnit b) : a = c * b → a / b = c :=
  h.div_eq_iff.2

@[to_additive]
protected theorem eq_div_of_mul_eq (h : IsUnit c) : a * c = b → a = b / c :=
  h.eq_div_iff.2

@[to_additive]
protected theorem div_eq_one_iff_eq (h : IsUnit b) : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun hab => hab.symm ▸ h.div_self⟩

/-- The `Group` version of this lemma is `div_mul_cancel'''` -/
@[to_additive "The `AddGroup` version of this lemma is `sub_add_cancel''`"]
protected theorem div_mul_left (h : IsUnit b) : b / (a * b) = 1 / a := by
  rw [div_eq_mul_inv, mul_inv_rev, h.mul_inv_cancel_left, one_div]

@[to_additive]
protected theorem mul_div_mul_right (h : IsUnit c) (a b : α) : a * c / (b * c) = a / b := by
  simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, h.mul_inv_cancel_left]

@[to_additive]
protected theorem mul_mul_div (a : α) (h : IsUnit b) : a * b * (1 / b) = a := by simp [h]

end DivisionMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid α] {a b c d : α}

@[to_additive]
protected theorem div_mul_right (h : IsUnit a) (b : α) : a / (a * b) = 1 / b := by
  rw [mul_comm, h.div_mul_left]

@[to_additive]
protected theorem mul_div_cancel_left (h : IsUnit a) (b : α) : a * b / a = b := by
  rw [mul_comm, h.mul_div_cancel]

@[to_additive]
protected theorem mul_div_cancel' (h : IsUnit a) (b : α) : a * (b / a) = b := by
  rw [mul_comm, h.div_mul_cancel]

@[to_additive]
protected theorem mul_div_mul_left (h : IsUnit c) (a b : α) : c * a / (c * b) = a / b := by
  rw [mul_comm c, mul_comm c, h.mul_div_mul_right]

@[to_additive]
protected theorem mul_eq_mul_of_div_eq_div (hb : IsUnit b) (hd : IsUnit d)
    (a c : α) (h : a / b = c / d) : a * d = c * b := by
  rw [← mul_one a, ← hb.div_self, ← mul_comm_div, h, div_mul_eq_mul_div, hd.div_mul_cancel]

@[to_additive]
protected theorem div_eq_div_iff (hb : IsUnit b) (hd : IsUnit d) :
    a / b = c / d ↔ a * d = c * b := by
  rw [← (hb.mul hd).mul_left_inj, ← mul_assoc, hb.div_mul_cancel, ← mul_assoc, mul_right_comm,
    hd.div_mul_cancel]

@[to_additive]
protected theorem div_div_cancel (h : IsUnit a) : a / (a / b) = b := by
  rw [div_div_eq_mul_div, h.mul_div_cancel_left]

@[to_additive]
protected theorem div_div_cancel_left (h : IsUnit a) : a / b / a = b⁻¹ := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, h.mul_inv_cancel, one_mul]

end DivisionCommMonoid

end IsUnit
