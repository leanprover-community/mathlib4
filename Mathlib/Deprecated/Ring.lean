/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module deprecated.ring
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Deprecated.Group

/-!
# Unbundled semiring and ring homomorphisms (deprecated)

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines predicates for unbundled semiring and ring homomorphisms. Instead of using
this file, please use `ring_hom`, defined in `algebra.hom.ring`, with notation `→+*`, for
morphisms between semirings or rings. For example use `φ : A →+* B` to represent a
ring homomorphism.

## Main Definitions

`is_semiring_hom` (deprecated), `is_ring_hom` (deprecated)

## Tags

is_semiring_hom, is_ring_hom

-/


universe u v w

variable {α : Type u}

/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`map_zero] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`map_one] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`map_add] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`map_mul] [] -/
/-- Predicate for semiring homomorphisms (deprecated -- use the bundled `ring_hom` version). -/
structure IsSemiringHom {α : Type u} {β : Type v} [Semiring α] [Semiring β] (f : α → β) : Prop where
  map_zero : f 0 = 0
  map_one : f 1 = 1
  map_add : ∀ {x y}, f (x + y) = f x + f y
  map_mul : ∀ {x y}, f (x * y) = f x * f y
#align is_semiring_hom IsSemiringHom

namespace IsSemiringHom

variable {β : Type v} [Semiring α] [Semiring β]

variable {f : α → β} (hf : IsSemiringHom f) {x y : α}

/-- The identity map is a semiring homomorphism. -/
theorem id : IsSemiringHom (@id α) := by refine' { .. } <;> intros <;> rfl
#align is_semiring_hom.id IsSemiringHom.id

/-- The composition of two semiring homomorphisms is a semiring homomorphism. -/
theorem comp (hf : IsSemiringHom f) {γ} [Semiring γ] {g : β → γ} (hg : IsSemiringHom g) :
    IsSemiringHom (g ∘ f) :=
  { map_zero := by simpa [map_zero hf] using map_zero hg
    map_one := by simpa [map_one hf] using map_one hg
    map_add := fun x y => by simp [map_add hf, map_add hg]
    map_mul := fun x y => by simp [map_mul hf, map_mul hg] }
#align is_semiring_hom.comp IsSemiringHom.comp

/-- A semiring homomorphism is an additive monoid homomorphism. -/
theorem to_is_add_monoid_hom (hf : IsSemiringHom f) : IsAddMonoidHom f :=
  { ‹IsSemiringHom f› with }
#align is_semiring_hom.to_is_add_monoid_hom IsSemiringHom.to_is_add_monoid_hom

/-- A semiring homomorphism is a monoid homomorphism. -/
theorem to_is_monoid_hom (hf : IsSemiringHom f) : IsMonoidHom f :=
  { ‹IsSemiringHom f› with }
#align is_semiring_hom.to_is_monoid_hom IsSemiringHom.to_is_monoid_hom

end IsSemiringHom

/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`map_one] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`map_mul] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`map_add] [] -/
/-- Predicate for ring homomorphisms (deprecated -- use the bundled `ring_hom` version). -/
structure IsRingHom {α : Type u} {β : Type v} [Ring α] [Ring β] (f : α → β) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ {x y}, f (x * y) = f x * f y
  map_add : ∀ {x y}, f (x + y) = f x + f y
#align is_ring_hom IsRingHom

namespace IsRingHom

variable {β : Type v} [Ring α] [Ring β]

/-- A map of rings that is a semiring homomorphism is also a ring homomorphism. -/
theorem of_semiring {f : α → β} (H : IsSemiringHom f) : IsRingHom f :=
  { H with }
#align is_ring_hom.of_semiring IsRingHom.of_semiring

variable {f : α → β} (hf : IsRingHom f) {x y : α}

/-- Ring homomorphisms map zero to zero. -/
theorem map_zero (hf : IsRingHom f) : f 0 = 0 :=
  calc
    f 0 = f (0 + 0) - f 0 := by rw [hf.map_add] <;> simp
    _ = 0 := by simp
    
#align is_ring_hom.map_zero IsRingHom.map_zero

/-- Ring homomorphisms preserve additive inverses. -/
theorem map_neg (hf : IsRingHom f) : f (-x) = -f x :=
  calc
    f (-x) = f (-x + x) - f x := by rw [hf.map_add] <;> simp
    _ = -f x := by simp [hf.map_zero]
    
#align is_ring_hom.map_neg IsRingHom.map_neg

/-- Ring homomorphisms preserve subtraction. -/
theorem map_sub (hf : IsRingHom f) : f (x - y) = f x - f y := by
  simp [sub_eq_add_neg, hf.map_add, hf.map_neg]
#align is_ring_hom.map_sub IsRingHom.map_sub

/-- The identity map is a ring homomorphism. -/
theorem id : IsRingHom (@id α) := by refine' { .. } <;> intros <;> rfl
#align is_ring_hom.id IsRingHom.id

-- see Note [no instance on morphisms]
/-- The composition of two ring homomorphisms is a ring homomorphism. -/
theorem comp (hf : IsRingHom f) {γ} [Ring γ] {g : β → γ} (hg : IsRingHom g) : IsRingHom (g ∘ f) :=
  { map_add := fun x y => by simp [map_add hf] <;> rw [map_add hg] <;> rfl
    map_mul := fun x y => by simp [map_mul hf] <;> rw [map_mul hg] <;> rfl
    map_one := by simp [map_one hf] <;> exact map_one hg }
#align is_ring_hom.comp IsRingHom.comp

/-- A ring homomorphism is also a semiring homomorphism. -/
theorem to_is_semiring_hom (hf : IsRingHom f) : IsSemiringHom f :=
  { ‹IsRingHom f› with map_zero := map_zero hf }
#align is_ring_hom.to_is_semiring_hom IsRingHom.to_is_semiring_hom

theorem to_is_add_group_hom (hf : IsRingHom f) : IsAddGroupHom f :=
  { map_add := fun _ _ => hf.map_add }
#align is_ring_hom.to_is_add_group_hom IsRingHom.to_is_add_group_hom

end IsRingHom

variable {β : Type v} {γ : Type w} [rα : Semiring α] [rβ : Semiring β]

namespace RingHom

section

include rα rβ

/-- Interpret `f : α → β` with `is_semiring_hom f` as a ring homomorphism. -/
def of {f : α → β} (hf : IsSemiringHom f) : α →+* β :=
  { MonoidHom.of hf.to_is_monoid_hom, AddMonoidHom.of hf.to_is_add_monoid_hom with toFun := f }
#align ring_hom.of RingHom.of

@[simp]
theorem coe_of {f : α → β} (hf : IsSemiringHom f) : ⇑(of hf) = f :=
  rfl
#align ring_hom.coe_of RingHom.coe_of

theorem to_is_semiring_hom (f : α →+* β) : IsSemiringHom f :=
  { map_zero := f.map_zero
    map_one := f.map_one
    map_add := f.map_add
    map_mul := f.map_mul }
#align ring_hom.to_is_semiring_hom RingHom.to_is_semiring_hom

end

theorem to_is_ring_hom {α γ} [Ring α] [Ring γ] (g : α →+* γ) : IsRingHom g :=
  IsRingHom.of_semiring g.to_is_semiring_hom
#align ring_hom.to_is_ring_hom RingHom.to_is_ring_hom

end RingHom

