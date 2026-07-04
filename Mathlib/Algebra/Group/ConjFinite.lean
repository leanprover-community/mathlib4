/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Conjugacy of elements of finite groups
-/

public section

assert_not_exists Field

-- TODO: the following `assert_not_exists` should work, but does not
-- assert_not_exists MonoidWithZero

variable {α : Type*} [Monoid α]

attribute [local instance] IsConj.setoid

instance [Fintype α] [DecidableRel (IsConj : α → α → Prop)] : Fintype (ConjClasses α) :=
  Quotient.fintype (IsConj.setoid α)

instance [Finite α] : Finite (ConjClasses α) :=
  Quotient.finite _

instance [DecidableEq α] [Fintype α] : DecidableRel (IsConj : α → α → Prop) := fun a b =>
  inferInstanceAs (Decidable (∃ c : αˣ, c.1 * a = b * c.1))

instance conjugatesOf.fintype [Fintype α] [DecidableRel (IsConj : α → α → Prop)] {a : α} :
    Fintype (conjugatesOf a) :=
  @Subtype.fintype _ _ (‹DecidableRel IsConj› a) _

namespace ConjClasses

variable [Fintype α] [DecidableRel (IsConj : α → α → Prop)]

instance {x : ConjClasses α} : Fintype (carrier x) :=
  Quotient.recOnSubsingleton x fun _ => conjugatesOf.fintype

section Group

variable {G H : Type*} [Group G] [Fintype G] [DecidableEq G] [CommMonoid H] (g : G)

theorem mk_carrier_map_conj :
    (ConjClasses.mk g).carrier.toFinset.1.map (MulAut.conj g) =
    (ConjClasses.mk g).carrier.toFinset.1 := by
  have hbij := bijOn_conj g (ConjClasses.mk g)
  rw [← Finset.image_val_of_injOn <| hbij.injOn.mono <| Set.subset_toFinset.1 fun ⦃_⦄ x ↦ x,
    Finset.val_inj, ← Finset.coe_inj, Finset.coe_image, Set.coe_toFinset, hbij.image_eq]

theorem mk_carrier_map_mul_left :
    (ConjClasses.mk g).carrier.toFinset.1.map (fun h ↦ g * h) =
    (ConjClasses.mk g).carrier.toFinset.1.map (fun h ↦ h * g) := by
  conv_rhs => rw [← ConjClasses.mk_carrier_map_conj, Multiset.map_map]
  exact Multiset.map_congr rfl fun _ _ ↦ by simp [MulAut.conj_apply]

/-- Multiplying `f (g * h * g⁻¹)` over `h` in the conjugacy class of `g` equals multiplying
`f h` over `h`. -/
@[to_additive (dont_translate := G) ConjClasses.sum_carrier_mulAut
/-- Summing `f (g * h * g⁻¹)` over `h` in the conjugacy class of `g` equals summing
`f h` over `h`. -/]
theorem prod_carrier_mulAut (f : G → H) :
    ∏ h ∈ (ConjClasses.mk g).carrier, f (MulAut.conj g h) =
    ∏ h ∈ (ConjClasses.mk g).carrier, f h := by
  change ((ConjClasses.mk g).carrier.toFinset.1.map (f ∘ MulAut.conj g)).prod = _
  rw [← Multiset.map_map, mk_carrier_map_conj, Finset.prod_eq_multiset_prod]

/-- Multiplying `f (g * h)` over `h` in the conjugacy class of `g` equals multiplying
`f (h * g)` over `h`. -/
@[to_additive (dont_translate := G) ConjClasses.sum_carrier_mul_left
/-- Summing `f (g * h)` over `h` in the conjugacy class of `g` equals summing
`f (h * g)` over `h`. -/]
theorem prod_carrier_mul_left (f : G → H) :
    ∏ h ∈ (ConjClasses.mk g).carrier, f (g * h) =
    ∏ h ∈ (ConjClasses.mk g).carrier, f (h * g) := by
  change ((ConjClasses.mk g).carrier.toFinset.1.map (f ∘ (fun x ↦ g * x))).prod = _
  rw [← Multiset.map_map, mk_carrier_map_mul_left, Finset.prod_eq_multiset_prod,
    Multiset.map_map]; rfl

end Group

end ConjClasses
