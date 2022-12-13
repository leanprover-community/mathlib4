/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Data.Set.Basic
import Mathbin.Tactic.Monotonicity.Basic

/-!
# Typeclass for types with a set-like extensionality property

The `has_mem` typeclass is used to let terms of a type have elements.
Many instances of `has_mem` have a set-like extensionality property:
things are equal iff they have the same elements.  The `set_like`
typeclass provides a unified interface to define a `has_mem` that is
extensional in this way.

The main use of `set_like` is for algebraic subobjects (such as
`submonoid` and `submodule`), whose non-proof data consists only of a
carrier set.  In such a situation, the projection to the carrier set
is injective.

In general, a type `A` is `set_like` with elements of type `B` if it
has an injective map to `set B`.  This module provides standard
boilerplate for every `set_like`: a `coe_sort`, a `coe` to set, a
`partial_order`, and various extensionality and simp lemmas.

A typical subobject should be declared as:
```
structure my_subobject (X : Type*) [object_typeclass X] :=
(carrier : set X)
(op_mem' : ∀ {x : X}, x ∈ carrier → sorry ∈ carrier)

namespace my_subobject

variables {X : Type*} [object_typeclass X] {x : X}

instance : set_like (my_subobject X) X :=
⟨my_subobject.carrier, λ p q h, by cases p; cases q; congr'⟩

@[simp] lemma mem_carrier {p : my_subobject X} : x ∈ p.carrier ↔ x ∈ (p : set X) := iff.rfl

@[ext] theorem ext {p q : my_subobject X} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := set_like.ext h

/-- Copy of a `my_subobject` with a new `carrier` equal to the old one. Useful to fix definitional
equalities. See Note [range copy pattern]. -/
protected def copy (p : my_subobject X) (s : set X) (hs : s = ↑p) : my_subobject X :=
{ carrier := s,
  op_mem' := hs.symm ▸ p.op_mem' }

@[simp] lemma coe_copy (p : my_subobject X) (s : set X) (hs : s = ↑p) :
  (p.copy s hs : set X) = s := rfl

lemma copy_eq (p : my_subobject X) (s : set X) (hs : s = ↑p) : p.copy s hs = p :=
set_like.coe_injective hs

end my_subobject
```

An alternative to `set_like` could have been an extensional `has_mem` typeclass:
```
class has_ext_mem (α : out_param $ Type u) (β : Type v) extends has_mem α β :=
(ext_iff : ∀ {s t : β}, s = t ↔ ∀ (x : α), x ∈ s ↔ x ∈ t)
```
While this is equivalent, `set_like` conveniently uses a carrier set projection directly.

## Tags

subobjects
-/


/-- A class to indicate that there is a canonical injection between `A` and `set B`.

This has the effect of giving terms of `A` elements of type `B` (through a `has_mem`
instance) and a compatible coercion to `Type*` as a subtype.

Note: if `set_like.coe` is a projection, implementers should create a simp lemma such as
```
@[simp] lemma mem_carrier {p : my_subobject X} : x ∈ p.carrier ↔ x ∈ (p : set X) := iff.rfl
```
to normalize terms.
-/
@[protect_proj]
class SetLike (A : Type _) (B : outParam <| Type _) where
  coe : A → Set B
  coe_injective' : Function.Injective coe
#align set_like SetLike

namespace SetLike

variable {A : Type _} {B : Type _} [i : SetLike A B]

include i

instance : CoeTC A (Set B) :=
  ⟨SetLike.coe⟩

instance (priority := 100) : Membership B A :=
  ⟨fun x p => x ∈ (p : Set B)⟩

-- `dangerous_instance` does not know that `B` is used only as an `out_param`
@[nolint dangerous_instance]
instance (priority := 100) : CoeSort A (Type _) :=
  ⟨fun p => { x : B // x ∈ p }⟩

variable (p q : A)

@[simp, norm_cast]
theorem coe_sort_coe : ((p : Set B) : Type _) = p :=
  rfl
#align set_like.coe_sort_coe SetLike.coe_sort_coe

variable {p q}

protected theorem exists {q : p → Prop} : (∃ x, q x) ↔ ∃ x ∈ p, q ⟨x, ‹_›⟩ :=
  SetCoe.exists
#align set_like.exists SetLike.exists

protected theorem forall {q : p → Prop} : (∀ x, q x) ↔ ∀ x ∈ p, q ⟨x, ‹_›⟩ :=
  SetCoe.forall
#align set_like.forall SetLike.forall

theorem coe_injective : Function.Injective (coe : A → Set B) := fun x y h =>
  SetLike.coe_injective' h
#align set_like.coe_injective SetLike.coe_injective

@[simp, norm_cast]
theorem coe_set_eq : (p : Set B) = q ↔ p = q :=
  coe_injective.eq_iff
#align set_like.coe_set_eq SetLike.coe_set_eq

theorem ext' (h : (p : Set B) = q) : p = q :=
  coe_injective h
#align set_like.ext' SetLike.ext'

theorem ext'_iff : p = q ↔ (p : Set B) = q :=
  coe_set_eq.symm
#align set_like.ext'_iff SetLike.ext'_iff

/-- Note: implementers of `set_like` must copy this lemma in order to tag it with `@[ext]`. -/
theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  coe_injective <| Set.ext h
#align set_like.ext SetLike.ext

theorem ext_iff : p = q ↔ ∀ x, x ∈ p ↔ x ∈ q :=
  coe_injective.eq_iff.symm.trans Set.ext_iff
#align set_like.ext_iff SetLike.ext_iff

@[simp]
theorem mem_coe {x : B} : x ∈ (p : Set B) ↔ x ∈ p :=
  Iff.rfl
#align set_like.mem_coe SetLike.mem_coe

@[simp, norm_cast]
theorem coe_eq_coe {x y : p} : (x : B) = y ↔ x = y :=
  Subtype.ext_iff_val.symm
#align set_like.coe_eq_coe SetLike.coe_eq_coe

@[simp, norm_cast]
theorem coe_mk (x : B) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : B) = x :=
  rfl
#align set_like.coe_mk SetLike.coe_mk

@[simp]
theorem coe_mem (x : p) : (x : B) ∈ p :=
  x.2
#align set_like.coe_mem SetLike.coe_mem

@[simp]
protected theorem eta (x : p) (hx : (x : B) ∈ p) : (⟨x, hx⟩ : p) = x :=
  Subtype.eta x hx
#align set_like.eta SetLike.eta

-- `dangerous_instance` does not know that `B` is used only as an `out_param`
@[nolint dangerous_instance]
instance (priority := 100) : PartialOrder A :=
  { PartialOrder.lift (coe : A → Set B) coe_injective with le := fun H K => ∀ ⦃x⦄, x ∈ H → x ∈ K }

theorem le_def {S T : A} : S ≤ T ↔ ∀ ⦃x : B⦄, x ∈ S → x ∈ T :=
  Iff.rfl
#align set_like.le_def SetLike.le_def

@[simp, norm_cast]
theorem coe_subset_coe {S T : A} : (S : Set B) ⊆ T ↔ S ≤ T :=
  Iff.rfl
#align set_like.coe_subset_coe SetLike.coe_subset_coe

@[mono]
theorem coe_mono : Monotone (coe : A → Set B) := fun a b => coe_subset_coe.mpr
#align set_like.coe_mono SetLike.coe_mono

@[simp, norm_cast]
theorem coe_ssubset_coe {S T : A} : (S : Set B) ⊂ T ↔ S < T :=
  Iff.rfl
#align set_like.coe_ssubset_coe SetLike.coe_ssubset_coe

@[mono]
theorem coe_strict_mono : StrictMono (coe : A → Set B) := fun a b => coe_ssubset_coe.mpr
#align set_like.coe_strict_mono SetLike.coe_strict_mono

theorem not_le_iff_exists : ¬p ≤ q ↔ ∃ x ∈ p, x ∉ q :=
  Set.not_subset
#align set_like.not_le_iff_exists SetLike.not_le_iff_exists

theorem exists_of_lt : p < q → ∃ x ∈ q, x ∉ p :=
  Set.exists_of_ssubset
#align set_like.exists_of_lt SetLike.exists_of_lt

theorem lt_iff_le_and_exists : p < q ↔ p ≤ q ∧ ∃ x ∈ q, x ∉ p := by
  rw [lt_iff_le_not_le, not_le_iff_exists]
#align set_like.lt_iff_le_and_exists SetLike.lt_iff_le_and_exists

end SetLike

