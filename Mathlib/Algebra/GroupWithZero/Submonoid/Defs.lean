/-
Copyright (c) 2026 Edison Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xu
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.InjSurj

/-!
# Submonoids with zero

This file defines bundled submonoids with zero: subsets of a monoid with zero `M₀` containing
`0` and `1` and closed under multiplication.

## Main definitions

* `SubmonoidWithZeroClass S M₀`: the typeclass saying that `S` is a type of subsets of `M₀`
  containing `0` and `1` and closed under `(*)`. It is the conjunction of `SubmonoidClass` and
  `ZeroMemClass`, and is what powers the `MulZeroOneClass` / `MonoidWithZero` /
  `CommMonoidWithZero` instances on the coercion to `Sort`.
* `SubmonoidWithZero M₀`: the type of bundled submonoids with zero of `M₀`.
* `SubmonoidWithZeroClass.subtype`: the natural `M₀ →*₀ M₀` inclusion of a submonoid with zero.

## Implementation notes

There is no additive analogue of a monoid with zero, so nothing in this file is tagged
`@[to_additive]`.

Note that `SubmonoidWithZero M₀` does not require `MonoidWithZero M₀`, only the weaker
`MulZeroOneClass M₀`, matching `Submonoid`'s use of `MulOneClass`.

Beware that the bottom element of the (not yet defined) lattice of submonoids with zero is
`{0, 1}` rather than `{1}`: every submonoid with zero contains both.

## Tags
submonoid with zero
-/

@[expose] public section

assert_not_exists RelIso CompleteLattice Ring

variable {M₀ S : Type*}

/-- `SubmonoidWithZeroClass S M₀` says `S` is a type of subsets `s ⊆ M₀` containing `0` and `1`
and closed under `(*)`. -/
class SubmonoidWithZeroClass (S : Type*) (M₀ : outParam Type*) [MulZeroOneClass M₀]
    [SetLike S M₀] : Prop extends SubmonoidClass S M₀, ZeroMemClass S M₀

namespace SubmonoidWithZeroClass

variable [SetLike S M₀]

section MulZeroOneClass

variable [MulZeroOneClass M₀] [SubmonoidWithZeroClass S M₀] (s : S)

-- See note [lower instance priority]
/-- A submonoid with zero of a `MulZeroOneClass` inherits a `MulZeroOneClass` structure. -/
instance (priority := 75) toMulZeroOneClass : MulZeroOneClass s := fast_instance%
  Subtype.coe_injective.mulZeroOneClass Subtype.val rfl rfl fun _ _ ↦ rfl

/-- The natural monoid with zero hom from a submonoid with zero of `M₀` to `M₀`. -/
def subtype : s →*₀ M₀ where
  __ := SubmonoidClass.subtype s
  map_zero' := rfl

variable {s} in
@[simp]
lemma subtype_apply (x : s) : subtype s x = x := rfl

lemma subtype_injective : Function.Injective (subtype s) := Subtype.coe_injective

@[simp]
lemma coe_subtype : (subtype s : s → M₀) = Subtype.val := rfl

end MulZeroOneClass

-- See note [lower instance priority]
/-- A submonoid with zero of a monoid with zero inherits a monoid with zero structure. -/
instance (priority := 75) toMonoidWithZero [MonoidWithZero M₀] [SubmonoidWithZeroClass S M₀]
    (s : S) : MonoidWithZero s := fast_instance%
  Subtype.coe_injective.monoidWithZero Subtype.val rfl rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

-- See note [lower instance priority]
/-- A submonoid with zero of a commutative monoid with zero inherits a commutative monoid with
zero structure. -/
instance (priority := 75) toCommMonoidWithZero [CommMonoidWithZero M₀]
    [SubmonoidWithZeroClass S M₀] (s : S) : CommMonoidWithZero s := fast_instance%
  Subtype.coe_injective.commMonoidWithZero Subtype.val rfl rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

end SubmonoidWithZeroClass

/-- A submonoid with zero of a monoid with zero `M₀` is a subset containing `0` and `1` and
closed under multiplication. -/
structure SubmonoidWithZero (M₀ : Type*) [MulZeroOneClass M₀] extends Submonoid M₀ where
  /-- A submonoid with zero contains `0`. -/
  zero_mem' : (0 : M₀) ∈ carrier

/-- Reinterpret a `SubmonoidWithZero` as a `Submonoid`. -/
add_decl_doc SubmonoidWithZero.toSubmonoid

namespace SubmonoidWithZero

variable [MulZeroOneClass M₀]

instance : SetLike (SubmonoidWithZero M₀) M₀ where
  coe s := s.carrier
  coe_injective p q h := by
    obtain ⟨⟨⟨hp, _⟩, _⟩, _⟩ := p
    obtain ⟨⟨⟨hq, _⟩, _⟩, _⟩ := q
    congr

instance : PartialOrder (SubmonoidWithZero M₀) := .ofSetLike (SubmonoidWithZero M₀) M₀

initialize_simps_projections SubmonoidWithZero (carrier → coe, as_prefix coe)

instance : SubmonoidWithZeroClass (SubmonoidWithZero M₀) M₀ where
  zero_mem s := s.zero_mem'
  one_mem s := s.one_mem'
  mul_mem {s} := s.mul_mem'

/-- The actual `SubmonoidWithZero` obtained from an element of a `SubmonoidWithZeroClass`. -/
@[simps]
def ofClass {S M₀ : Type*} [MulZeroOneClass M₀] [SetLike S M₀] [SubmonoidWithZeroClass S M₀]
    (s : S) : SubmonoidWithZero M₀ :=
  ⟨⟨⟨s, MulMemClass.mul_mem⟩, OneMemClass.one_mem s⟩, ZeroMemClass.zero_mem s⟩

instance (priority := 100) : CanLift (Set M₀) (SubmonoidWithZero M₀) (↑)
    (fun s ↦ 0 ∈ s ∧ 1 ∈ s ∧ ∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) where
  prf s h := ⟨{ carrier := s, zero_mem' := h.1, one_mem' := h.2.1, mul_mem' := h.2.2 }, rfl⟩

variable {s : SubmonoidWithZero M₀} {x : M₀}

@[simp]
theorem mem_toSubmonoid : x ∈ s.toSubmonoid ↔ x ∈ s := Iff.rfl

@[simp]
theorem coe_toSubmonoid (s : SubmonoidWithZero M₀) : (s.toSubmonoid : Set M₀) = s := rfl

theorem toSubmonoid_injective :
    Function.Injective (toSubmonoid : SubmonoidWithZero M₀ → Submonoid M₀) :=
  fun p q h ↦ by
    have := SetLike.ext'_iff.1 h
    rw [coe_toSubmonoid, coe_toSubmonoid] at this
    exact SetLike.ext'_iff.2 this

@[simp]
theorem toSubmonoid_le_toSubmonoid {s t : SubmonoidWithZero M₀} :
    s.toSubmonoid ≤ t.toSubmonoid ↔ s ≤ t := Iff.rfl

@[simp]
theorem mem_mk {s : Submonoid M₀} (h_zero) : x ∈ mk s h_zero ↔ x ∈ s := Iff.rfl

@[simp]
theorem coe_set_mk {s : Submonoid M₀} (h_zero) : (mk s h_zero : Set M₀) = s := rfl

@[ext]
theorem ext {s t : SubmonoidWithZero M₀} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := SetLike.ext h

/-- Copy of a `SubmonoidWithZero` with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (s : SubmonoidWithZero M₀) (t : Set M₀) (ht : t = s) :
    SubmonoidWithZero M₀ where
  carrier := t
  zero_mem' := ht.symm ▸ s.zero_mem'
  one_mem' := ht.symm ▸ s.one_mem'
  mul_mem' := ht.symm ▸ s.mul_mem'

@[simp, norm_cast]
theorem coe_copy {t : Set M₀} (ht : t = s) : (s.copy t ht : Set M₀) = t := rfl

theorem copy_eq {t : Set M₀} (ht : t = s) : s.copy t ht = s := SetLike.coe_injective ht

end SubmonoidWithZero
