/-
Copyright (c) 2026 Edison Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Edison Xie
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Submonoid.Defs

/-!
# Subgroups with zero

This file defines bundled subgroups with zero: subsets of a group with zero `G₀` containing `0`
and `1`, closed under multiplication, and closed under inversion.

## Main definitions

* `SubgroupWithZeroClass S G₀`: the typeclass saying that `S` is a type of subsets of `G₀` that
  are subgroups with zero.
* `SubgroupWithZero G₀`: the type of bundled subgroups with zero of `G₀`.

## Implementation notes

Beware that the bottom element of the (not yet defined) lattice of subgroups with zero is
`{0, 1}` rather than `{1}`.

## Tags
subgroup with zero
-/

@[expose] public section

assert_not_exists RelIso CompleteLattice Ring

variable {G₀ S : Type*}

/-- `SubgroupWithZeroClass S G₀` says `S` is a type of subsets `s ⊆ G₀` that are subgroups with
zero of `G₀`: they contain `0` and `1` and are closed under `(*)` and `(·)⁻¹`. -/
class SubgroupWithZeroClass (S : Type*) (G₀ : outParam Type*) [GroupWithZero G₀]
    [SetLike S G₀] : Prop extends SubmonoidWithZeroClass S G₀, InvMemClass S G₀

namespace SubgroupWithZeroClass

variable [GroupWithZero G₀] [SetLike S G₀] [SubgroupWithZeroClass S G₀]

-- See note [lower instance priority]
/-- A subgroup with zero is closed under `1`, `(*)` and `(·)⁻¹`.

Be assured that we're not actually proving that subgroups with zero are subgroups:
`SubgroupClass` is really an abbreviation of `SubgroupWithOrWithoutZeroClass`. -/
instance (priority := 100) toSubgroupClass : SubgroupClass S G₀ where
  mul_mem := MulMemClass.mul_mem
  one_mem := OneMemClass.one_mem
  inv_mem := InvMemClass.inv_mem

-- See note [lower instance priority]
/-- A subgroup with zero of a group with zero inherits a group with zero structure. -/
instance (priority := 75) toGroupWithZero (s : S) : GroupWithZero s := fast_instance%
  Subtype.coe_injective.groupWithZero Subtype.val rfl rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun _ _ ↦ rfl

-- See note [lower instance priority]
/-- A subgroup with zero of a commutative group with zero inherits a commutative group with zero
structure. -/
instance (priority := 75) toCommGroupWithZero {G₀ : Type*} [CommGroupWithZero G₀] [SetLike S G₀]
    [SubgroupWithZeroClass S G₀] (s : S) : CommGroupWithZero s := fast_instance%
  Subtype.coe_injective.commGroupWithZero Subtype.val rfl rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun _ _ ↦ rfl

end SubgroupWithZeroClass

/-- A subgroup with zero of a group with zero `G₀` is a submonoid with zero which is closed
under inversion.

Note that the closure condition is stated unconditionally: the case `x = 0` is harmless, since
`0⁻¹ = 0` and `0` belongs to every submonoid with zero. -/
structure SubgroupWithZero (G₀ : Type*) [GroupWithZero G₀] extends SubmonoidWithZero G₀ where
  /-- A subgroup with zero is closed under inverses. -/
  inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier

/-- Reinterpret a `SubgroupWithZero` as a `SubmonoidWithZero`. -/
add_decl_doc SubgroupWithZero.toSubmonoidWithZero

namespace SubgroupWithZero

variable [GroupWithZero G₀]

instance : SetLike (SubgroupWithZero G₀) G₀ where
  coe s := s.carrier
  coe_injective p q h := by
    obtain ⟨⟨⟨⟨hp, _⟩, _⟩, _⟩, _⟩ := p
    obtain ⟨⟨⟨⟨hq, _⟩, _⟩, _⟩, _⟩ := q
    congr

instance : PartialOrder (SubgroupWithZero G₀) := .ofSetLike (SubgroupWithZero G₀) G₀

initialize_simps_projections SubgroupWithZero (carrier → coe, as_prefix coe)

instance : SubgroupWithZeroClass (SubgroupWithZero G₀) G₀ where
  zero_mem s := s.zero_mem'
  one_mem s := s.one_mem'
  mul_mem {s} := s.mul_mem'
  inv_mem {s} := s.inv_mem'

/-- The actual `SubgroupWithZero` obtained from an element of a `SubgroupWithZeroClass`. -/
@[simps]
def ofClass {S G₀ : Type*} [GroupWithZero G₀] [SetLike S G₀] [SubgroupWithZeroClass S G₀]
    (s : S) : SubgroupWithZero G₀ :=
  ⟨⟨⟨⟨s, MulMemClass.mul_mem⟩, OneMemClass.one_mem s⟩, ZeroMemClass.zero_mem s⟩,
    InvMemClass.inv_mem⟩

instance (priority := 100) : CanLift (Set G₀) (SubgroupWithZero G₀) (↑)
    (fun s ↦ 0 ∈ s ∧ 1 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧ ∀ {x}, x ∈ s → x⁻¹ ∈ s) where
  prf s h :=
    ⟨{ carrier := s
       zero_mem' := h.1
       one_mem' := h.2.1
       mul_mem' := h.2.2.1
       inv_mem' := h.2.2.2 }, rfl⟩

variable {s : SubgroupWithZero G₀} {x : G₀}

@[simp]
theorem mem_toSubmonoidWithZero : x ∈ s.toSubmonoidWithZero ↔ x ∈ s := Iff.rfl

@[simp]
theorem coe_toSubmonoidWithZero (s : SubgroupWithZero G₀) :
    (s.toSubmonoidWithZero : Set G₀) = s := rfl

theorem toSubmonoidWithZero_injective :
    Function.Injective (toSubmonoidWithZero : SubgroupWithZero G₀ → SubmonoidWithZero G₀) :=
  fun p q h ↦ by
    have := SetLike.ext'_iff.1 h
    rw [coe_toSubmonoidWithZero, coe_toSubmonoidWithZero] at this
    exact SetLike.ext'_iff.2 this

@[simp]
theorem toSubmonoidWithZero_le_toSubmonoidWithZero {s t : SubgroupWithZero G₀} :
    s.toSubmonoidWithZero ≤ t.toSubmonoidWithZero ↔ s ≤ t := Iff.rfl

@[simp]
theorem mem_mk {s : SubmonoidWithZero G₀} (h_inv) : x ∈ mk s h_inv ↔ x ∈ s := Iff.rfl

@[simp]
theorem coe_set_mk {s : SubmonoidWithZero G₀} (h_inv) : (mk s h_inv : Set G₀) = s := rfl

@[ext]
theorem ext {s t : SubgroupWithZero G₀} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := SetLike.ext h

/-- Copy of a `SubgroupWithZero` with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (s : SubgroupWithZero G₀) (t : Set G₀) (ht : t = s) : SubgroupWithZero G₀ where
  carrier := t
  zero_mem' := ht.symm ▸ s.zero_mem'
  one_mem' := ht.symm ▸ s.one_mem'
  mul_mem' := ht.symm ▸ s.mul_mem'
  inv_mem' := ht.symm ▸ s.inv_mem'

@[simp, norm_cast]
theorem coe_copy {t : Set G₀} (ht : t = s) : (s.copy t ht : Set G₀) = t := rfl

theorem copy_eq {t : Set G₀} (ht : t = s) : s.copy t ht = s := SetLike.coe_injective ht

end SubgroupWithZero
