/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.RingTheory.Ideal.Defs

/-!
# Supports of submonoids

Let `G` be an (additive) group, and let `M` be a submonoid of `G`.
The *support* of `M` is `M ∩ -M`, the largest subgroup of `M`.

## Main definitions

* `AddSubmonoid.support`: the support of a submonoid as a subgroup.
* `Subsemiring.support`: the support of a subsemiring as an ideal.

-/

@[expose] public section

namespace Submonoid

variable {G : Type*} [Group G] (M : Submonoid G)

/--
The support of a submonoid `M` of a group `G` is `M ∩ M⁻¹`,
the largest subgroup contained in `M`.
-/
@[to_additive
/-- The support of a submonoid `M` of a group `G` is `M ∩ -M`,
the largest subgroup contained in `M`. -/]
def mulSupport : Subgroup G where
  carrier := M ∩ M⁻¹
  one_mem' := by aesop
  mul_mem' := by aesop
  inv_mem' := by aesop

set_option backward.privateInPublic true in
variable {M} in
@[to_additive (attr := aesop simp)]
theorem mem_mulSupport {x} : x ∈ M.mulSupport ↔ x ∈ M ∧ x⁻¹ ∈ M := .rfl

@[to_additive]
theorem coe_mulSupport : M.mulSupport = (M ∩ M⁻¹ : Set G) := rfl

end Submonoid

namespace Subsemiring

variable {R : Type*} [Ring R] (S : Subsemiring R)

/-- Typeclass to track when the support of a subsemiring forms an ideal. -/
class HasIdealSupport : Prop where
  smul_mem_support (x : R) {a : R} (ha : a ∈ S.support) :
    x * a ∈ S.support := by aesop

export HasIdealSupport (smul_mem_support)

variable {M} in
theorem hasIdealSupport_iff :
    S.HasIdealSupport ↔ ∀ x a : R, a ∈ S → -a ∈ S → x * a ∈ S ∧ -(x * a) ∈ S where
  mp _ := have := S.smul_mem_support; by aesop
  mpr _ := { }

section HasIdealSupport

variable [S.HasIdealSupport]

@[aesop 80% (rule_sets := [SetLike])]
theorem smul_mem (x : R) {a : R} (h₁a : a ∈ S) (h₂a : -a ∈ S) : x * a ∈ S := by
  have := S.smul_mem_support
  aesop

@[aesop 80% (rule_sets := [SetLike])]
theorem neg_smul_mem (x : R) {a : R} (h₁a : a ∈ S) (h₂a : -a ∈ S) : -(x * a) ∈ S := by
  have := S.smul_mem_support
  aesop

/-- The support `S ∩ -S` of a subsemiring `S` of a ring `R`, as an ideal. -/
def support : Ideal R where
  __ := S.toAddSubmonoid.support
  smul_mem' := by aesop

set_option backward.privateInPublic true in
variable {M} in
@[aesop simp]
theorem mem_support {x} : x ∈ S.support ↔ x ∈ S ∧ -x ∈ S := .rfl

theorem coe_support : S.support = (S : Set R) ∩ -(S : Set R) := rfl

@[simp]
theorem toAddSubmonoid_support : S.toAddSubmonoid.support = S.support.toAddSubgroup := rfl

end HasIdealSupport

instance (M : Subsemiring R) [HasMemOrNegMem M] : M.HasIdealSupport where
  smul_mem_support x a ha := by
    have := mem_or_neg_mem M x
    have : ∀ x y, -x ∈ M → -y ∈ M → x * y ∈ M := fun _ _ hx hy ↦ by simpa using mul_mem hx hy
    aesop (add 80% this)

end Subsemiring
