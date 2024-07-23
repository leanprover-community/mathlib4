/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.TypeTags
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Unbundled monoid and group homomorphisms

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines predicates for unbundled monoid and group homomorphisms. Instead of using
this file, please use `MonoidHom`, defined in `Algebra.Hom.Group`, with notation `→*`, for
morphisms between monoids or groups. For example use `φ : G →* H` to represent a group
homomorphism between multiplicative groups, and `ψ : A →+ B` to represent a group homomorphism
between additive groups.

## Main Definitions

`IsMonoidHom` (deprecated), `IsGroupHom` (deprecated)

## Tags

IsGroupHom, IsMonoidHom

-/


universe u v

variable {α : Type u} {β : Type v}

/-- Predicate for maps which preserve an addition. -/
structure IsAddHom {α β : Type*} [Add α] [Add β] (f : α → β) : Prop where
  /-- The proposition that `f` preserves addition. -/
  map_add : ∀ x y, f (x + y) = f x + f y

/-- Predicate for maps which preserve a multiplication. -/
@[to_additive]
structure IsMulHom {α β : Type*} [Mul α] [Mul β] (f : α → β) : Prop where
  /-- The proposition that `f` preserves multiplication. -/
  map_mul : ∀ x y, f (x * y) = f x * f y

namespace IsMulHom

variable [Mul α] [Mul β] {γ : Type*} [Mul γ]

/-- The identity map preserves multiplication. -/
@[to_additive "The identity map preserves addition"]
theorem id : IsMulHom (id : α → α) :=
  { map_mul := fun _ _ => rfl }

/-- The composition of maps which preserve multiplication, also preserves multiplication. -/
@[to_additive "The composition of addition preserving maps also preserves addition"]
theorem comp {f : α → β} {g : β → γ} (hf : IsMulHom f) (hg : IsMulHom g) : IsMulHom (g ∘ f) :=
  { map_mul := fun x y => by simp only [Function.comp, hf.map_mul, hg.map_mul] }

/-- A product of maps which preserve multiplication,
preserves multiplication when the target is commutative. -/
@[to_additive
      "A sum of maps which preserves addition, preserves addition when the target
      is commutative."]
theorem mul {α β} [Semigroup α] [CommSemigroup β] {f g : α → β} (hf : IsMulHom f)
    (hg : IsMulHom g) : IsMulHom fun a => f a * g a :=
  { map_mul := fun a b => by
      simp only [hf.map_mul, hg.map_mul, mul_comm, mul_assoc, mul_left_comm] }

/-- The inverse of a map which preserves multiplication,
preserves multiplication when the target is commutative. -/
@[to_additive
      "The negation of a map which preserves addition, preserves addition when
      the target is commutative."]
theorem inv {α β} [Mul α] [CommGroup β] {f : α → β} (hf : IsMulHom f) : IsMulHom fun a => (f a)⁻¹ :=
  { map_mul := fun a b => (hf.map_mul a b).symm ▸ mul_inv _ _ }

end IsMulHom

/-- Predicate for additive monoid homomorphisms
(deprecated -- use the bundled `MonoidHom` version). -/
structure IsAddMonoidHom [AddZeroClass α] [AddZeroClass β] (f : α → β) extends IsAddHom f :
  Prop where
  /-- The proposition that `f` preserves the additive identity. -/
  map_zero : f 0 = 0

/-- Predicate for monoid homomorphisms (deprecated -- use the bundled `MonoidHom` version). -/
@[to_additive]
structure IsMonoidHom [MulOneClass α] [MulOneClass β] (f : α → β) extends IsMulHom f : Prop where
  /-- The proposition that `f` preserves the multiplicative identity. -/
  map_one : f 1 = 1

namespace MonoidHom

variable {M : Type*} {N : Type*} {mM : MulOneClass M} {mN : MulOneClass N}

/-- Interpret a map `f : M → N` as a homomorphism `M →* N`. -/
@[to_additive "Interpret a map `f : M → N` as a homomorphism `M →+ N`."]
def of {f : M → N} (h : IsMonoidHom f) : M →* N where
  toFun := f
  map_one' := h.2
  map_mul' := h.1.1

@[to_additive (attr := simp)]
theorem coe_of {f : M → N} (hf : IsMonoidHom f) : ⇑(MonoidHom.of hf) = f :=
  rfl

@[to_additive]
theorem isMonoidHom_coe (f : M →* N) : IsMonoidHom (f : M → N) :=
  { map_mul := f.map_mul
    map_one := f.map_one }

end MonoidHom

namespace MulEquiv

variable {M : Type*} {N : Type*} [MulOneClass M] [MulOneClass N]

/-- A multiplicative isomorphism preserves multiplication (deprecated). -/
@[to_additive "An additive isomorphism preserves addition (deprecated)."]
theorem isMulHom (h : M ≃* N) : IsMulHom h :=
  ⟨h.map_mul⟩

/-- A multiplicative bijection between two monoids is a monoid hom
  (deprecated -- use `MulEquiv.toMonoidHom`). -/
@[to_additive
      "An additive bijection between two additive monoids is an additive
      monoid hom (deprecated). "]
theorem isMonoidHom (h : M ≃* N) : IsMonoidHom h :=
  { map_mul := h.map_mul
    map_one := h.map_one }

end MulEquiv

namespace IsMonoidHom

variable [MulOneClass α] [MulOneClass β] {f : α → β} (hf : IsMonoidHom f)

/-- A monoid homomorphism preserves multiplication. -/
@[to_additive "An additive monoid homomorphism preserves addition."]
theorem map_mul' (x y) : f (x * y) = f x * f y :=
  hf.map_mul x y

/-- The inverse of a map which preserves multiplication,
preserves multiplication when the target is commutative. -/
@[to_additive
      "The negation of a map which preserves addition, preserves addition
      when the target is commutative."]
theorem inv {α β} [MulOneClass α] [CommGroup β] {f : α → β} (hf : IsMonoidHom f) :
    IsMonoidHom fun a => (f a)⁻¹ :=
  { map_one := hf.map_one.symm ▸ inv_one
    map_mul := fun a b => (hf.map_mul a b).symm ▸ mul_inv _ _ }

end IsMonoidHom

/-- A map to a group preserving multiplication is a monoid homomorphism. -/
@[to_additive "A map to an additive group preserving addition is an additive monoid
homomorphism."]
theorem IsMulHom.to_isMonoidHom [MulOneClass α] [Group β] {f : α → β} (hf : IsMulHom f) :
    IsMonoidHom f :=
  { map_one := mul_right_eq_self.1 <| by rw [← hf.map_mul, one_mul]
    map_mul := hf.map_mul }

namespace IsMonoidHom

variable [MulOneClass α] [MulOneClass β] {f : α → β}

/-- The identity map is a monoid homomorphism. -/
@[to_additive "The identity map is an additive monoid homomorphism."]
theorem id : IsMonoidHom (@id α) :=
  { map_one := rfl
    map_mul := fun _ _ => rfl }

/-- The composite of two monoid homomorphisms is a monoid homomorphism. -/
@[to_additive
      "The composite of two additive monoid homomorphisms is an additive monoid
      homomorphism."]
theorem comp (hf : IsMonoidHom f) {γ} [MulOneClass γ] {g : β → γ} (hg : IsMonoidHom g) :
    IsMonoidHom (g ∘ f) :=
  { IsMulHom.comp hf.toIsMulHom hg.toIsMulHom with
    map_one := show g _ = 1 by rw [hf.map_one, hg.map_one] }

end IsMonoidHom

namespace IsAddMonoidHom

/-- Left multiplication in a ring is an additive monoid morphism. -/
theorem isAddMonoidHom_mul_left {γ : Type*} [NonUnitalNonAssocSemiring γ] (x : γ) :
    IsAddMonoidHom fun y : γ => x * y :=
  { map_zero := mul_zero x
    map_add := fun y z => mul_add x y z }

/-- Right multiplication in a ring is an additive monoid morphism. -/
theorem isAddMonoidHom_mul_right {γ : Type*} [NonUnitalNonAssocSemiring γ] (x : γ) :
    IsAddMonoidHom fun y : γ => y * x :=
  { map_zero := zero_mul x
    map_add := fun y z => add_mul y z x }

end IsAddMonoidHom

/-- Predicate for additive group homomorphism (deprecated -- use bundled `MonoidHom`). -/
structure IsAddGroupHom [AddGroup α] [AddGroup β] (f : α → β) extends IsAddHom f : Prop

/-- Predicate for group homomorphisms (deprecated -- use bundled `MonoidHom`). -/
@[to_additive]
structure IsGroupHom [Group α] [Group β] (f : α → β) extends IsMulHom f : Prop

@[to_additive]
theorem MonoidHom.isGroupHom {G H : Type*} {_ : Group G} {_ : Group H} (f : G →* H) :
    IsGroupHom (f : G → H) :=
  { map_mul := f.map_mul }

@[to_additive]
theorem MulEquiv.isGroupHom {G H : Type*} {_ : Group G} {_ : Group H} (h : G ≃* H) :
    IsGroupHom h :=
  { map_mul := h.map_mul }

/-- Construct `IsGroupHom` from its only hypothesis. -/
@[to_additive "Construct `IsAddGroupHom` from its only hypothesis."]
theorem IsGroupHom.mk' [Group α] [Group β] {f : α → β} (hf : ∀ x y, f (x * y) = f x * f y) :
    IsGroupHom f :=
  { map_mul := hf }

namespace IsGroupHom

variable [Group α] [Group β] {f : α → β} (hf : IsGroupHom f)

open IsMulHom (map_mul)

theorem map_mul' : ∀ x y, f (x * y) = f x * f y :=
  hf.toIsMulHom.map_mul

/-- A group homomorphism is a monoid homomorphism. -/
@[to_additive "An additive group homomorphism is an additive monoid homomorphism."]
theorem to_isMonoidHom : IsMonoidHom f :=
  hf.toIsMulHom.to_isMonoidHom

/-- A group homomorphism sends 1 to 1. -/
@[to_additive "An additive group homomorphism sends 0 to 0."]
theorem map_one : f 1 = 1 :=
  hf.to_isMonoidHom.map_one

/-- A group homomorphism sends inverses to inverses. -/
@[to_additive "An additive group homomorphism sends negations to negations."]
theorem map_inv (hf : IsGroupHom f) (a : α) : f a⁻¹ = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by rw [← hf.map_mul, inv_mul_self, hf.map_one]

@[to_additive]
theorem map_div (hf : IsGroupHom f) (a b : α) : f (a / b) = f a / f b := by
  simp_rw [div_eq_mul_inv, hf.map_mul, hf.map_inv]

/-- The identity is a group homomorphism. -/
@[to_additive "The identity is an additive group homomorphism."]
theorem id : IsGroupHom (@id α) :=
  { map_mul := fun _ _ => rfl }

/-- The composition of two group homomorphisms is a group homomorphism. -/
@[to_additive
      "The composition of two additive group homomorphisms is an additive
      group homomorphism."]
theorem comp (hf : IsGroupHom f) {γ} [Group γ] {g : β → γ} (hg : IsGroupHom g) :
    IsGroupHom (g ∘ f) :=
  { IsMulHom.comp hf.toIsMulHom hg.toIsMulHom with }

/-- A group homomorphism is injective iff its kernel is trivial. -/
@[to_additive "An additive group homomorphism is injective if its kernel is trivial."]
theorem injective_iff {f : α → β} (hf : IsGroupHom f) :
    Function.Injective f ↔ ∀ a, f a = 1 → a = 1 :=
  ⟨fun h _ => by rw [← hf.map_one]; exact @h _ _, fun h x y hxy =>
    eq_of_div_eq_one <| h _ <| by rwa [hf.map_div, div_eq_one]⟩

/-- The product of group homomorphisms is a group homomorphism if the target is commutative. -/
@[to_additive
      "The sum of two additive group homomorphisms is an additive group homomorphism
      if the target is commutative."]
theorem mul {α β} [Group α] [CommGroup β] {f g : α → β} (hf : IsGroupHom f) (hg : IsGroupHom g) :
    IsGroupHom fun a => f a * g a :=
  { map_mul := (hf.toIsMulHom.mul hg.toIsMulHom).map_mul }

/-- The inverse of a group homomorphism is a group homomorphism if the target is commutative. -/
@[to_additive
      "The negation of an additive group homomorphism is an additive group homomorphism
      if the target is commutative."]
theorem inv {α β} [Group α] [CommGroup β] {f : α → β} (hf : IsGroupHom f) :
    IsGroupHom fun a => (f a)⁻¹ :=
  { map_mul := hf.toIsMulHom.inv.map_mul }

end IsGroupHom

namespace RingHom

/-!
These instances look redundant, because `Deprecated.Ring` provides `IsRingHom` for a `→+*`.
Nevertheless these are harmless, and helpful for stripping out dependencies on `Deprecated.Ring`.
-/


variable {R : Type*} {S : Type*}

section

variable [NonAssocSemiring R] [NonAssocSemiring S]

theorem to_isMonoidHom (f : R →+* S) : IsMonoidHom f :=
  { map_one := f.map_one
    map_mul := f.map_mul }

theorem to_isAddMonoidHom (f : R →+* S) : IsAddMonoidHom f :=
  { map_zero := f.map_zero
    map_add := f.map_add }

end

section

variable [Ring R] [Ring S]

theorem to_isAddGroupHom (f : R →+* S) : IsAddGroupHom f :=
  { map_add := f.map_add }

end

end RingHom

/-- Inversion is a group homomorphism if the group is commutative. -/
@[to_additive
      "Negation is an `AddGroup` homomorphism if the `AddGroup` is commutative."]
theorem Inv.isGroupHom [CommGroup α] : IsGroupHom (Inv.inv : α → α) :=
  { map_mul := mul_inv }

/-- The difference of two additive group homomorphisms is an additive group
homomorphism if the target is commutative. -/
theorem IsAddGroupHom.sub {α β} [AddGroup α] [AddCommGroup β] {f g : α → β} (hf : IsAddGroupHom f)
    (hg : IsAddGroupHom g) : IsAddGroupHom fun a => f a - g a := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

namespace Units

variable {M : Type*} {N : Type*} [Monoid M] [Monoid N]

/-- The group homomorphism on units induced by a multiplicative morphism. -/
abbrev map' {f : M → N} (hf : IsMonoidHom f) : Mˣ →* Nˣ :=
  map (MonoidHom.of hf)

@[simp]
theorem coe_map' {f : M → N} (hf : IsMonoidHom f) (x : Mˣ) : ↑((map' hf : Mˣ → Nˣ) x) = f x :=
  rfl

theorem coe_isMonoidHom : IsMonoidHom (↑· : Mˣ → M) :=
  (coeHom M).isMonoidHom_coe

end Units

namespace IsUnit

variable {M : Type*} {N : Type*} [Monoid M] [Monoid N] {x : M}

theorem map' {f : M → N} (hf : IsMonoidHom f) {x : M} (h : IsUnit x) : IsUnit (f x) :=
  h.map (MonoidHom.of hf)

end IsUnit

theorem Additive.isAddHom [Mul α] [Mul β] {f : α → β} (hf : IsMulHom f) :
    @IsAddHom (Additive α) (Additive β) _ _ f :=
  { map_add := hf.map_mul }

theorem Multiplicative.isMulHom [Add α] [Add β] {f : α → β} (hf : IsAddHom f) :
    @IsMulHom (Multiplicative α) (Multiplicative β) _ _ f :=
  { map_mul := hf.map_add }

-- defeq abuse
theorem Additive.isAddMonoidHom [MulOneClass α] [MulOneClass β] {f : α → β}
    (hf : IsMonoidHom f) : @IsAddMonoidHom (Additive α) (Additive β) _ _ f :=
  { Additive.isAddHom hf.toIsMulHom with map_zero := hf.map_one }

theorem Multiplicative.isMonoidHom [AddZeroClass α] [AddZeroClass β] {f : α → β}
    (hf : IsAddMonoidHom f) : @IsMonoidHom (Multiplicative α) (Multiplicative β) _ _ f :=
  { Multiplicative.isMulHom hf.toIsAddHom with map_one := hf.map_zero }

theorem Additive.isAddGroupHom [Group α] [Group β] {f : α → β} (hf : IsGroupHom f) :
    @IsAddGroupHom (Additive α) (Additive β) _ _ f :=
  { map_add := hf.toIsMulHom.map_mul }

theorem Multiplicative.isGroupHom [AddGroup α] [AddGroup β] {f : α → β} (hf : IsAddGroupHom f) :
    @IsGroupHom (Multiplicative α) (Multiplicative β) _ _ f :=
  { map_mul := hf.toIsAddHom.map_add }
