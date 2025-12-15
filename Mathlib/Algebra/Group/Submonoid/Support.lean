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
When `M ∪ -M = G`, the support of `M` forms an ideal.
We define supports and prove how they interact with operations.

## Main definitions

* `AddSubmonoid.supportAddSubgroup`: the support of a submonoid as a subgroup.
* `AddSubmonoid.support`: the support of a submonoid as an ideal.

-/

@[expose] public section

namespace AddSubmonoid

variable {G : Type*} [AddGroup G] (M : AddSubmonoid G)

end AddSubmonoid

namespace Submonoid

variable {G : Type*} [Group G] (M : Submonoid G)

/--
The support of a submonoid `M` of a group `G` is `M ∩ M⁻¹`, the largest subgroup contained in `M`.
-/
@[to_additive
  /-- The support of a submonoid `M` of a group `G` is `M ∩ -M`,
  the largest subgroup contained in `M`. -/]
def supportSubgroup : Subgroup G where
  carrier := M ∩ M⁻¹
  one_mem' := by aesop
  mul_mem' := by aesop
  inv_mem' := by aesop

variable {M} in
@[to_additive (attr := aesop simp)]
theorem mem_supportSubgroup {x} : x ∈ M.supportSubgroup ↔ x ∈ M ∧ x⁻¹ ∈ M := .rfl

@[to_additive]
theorem coe_supportSubgroup : M.supportSubgroup = (M ∩ M⁻¹ : Set G) := rfl

end Submonoid

section Ring

variable {R : Type*} [Ring R]

namespace AddSubmonoid

variable (M : AddSubmonoid R)

/-- Typeclass to track when the support of a submonoid forms an ideal. -/
class HasIdealSupport : Prop where
  smul_mem_support (x : R) {a : R} (ha : a ∈ M.supportAddSubgroup) :
    x * a ∈ M.supportAddSubgroup := by aesop

export HasIdealSupport (smul_mem_support)

variable {M} in
theorem hasIdealSupport_iff :
    M.HasIdealSupport ↔ ∀ x a : R, a ∈ M → -a ∈ M → x * a ∈ M ∧ -(x * a) ∈ M where
  mp _ := have := M.smul_mem_support; by aesop
  mpr _ := { }

section HasIdealSupport

variable [M.HasIdealSupport]

@[aesop unsafe 80% apply]
theorem smul_mem (x : R) {a : R} (h₁a : a ∈ M) (h₂a : -a ∈ M) : x * a ∈ M := by
  have := M.smul_mem_support
  aesop

@[aesop unsafe 80% apply]
theorem neg_smul_mem (x : R) {a : R} (h₁a : a ∈ M) (h₂a : -a ∈ M) : -(x * a) ∈ M := by
  have := M.smul_mem_support
  aesop

/--
The support of a subsemiring `S` of a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def support : Ideal R where
  __ := supportAddSubgroup M
  smul_mem' := have := M.smul_mem_support; by aesop

variable {M} in
@[aesop simp]
theorem mem_support {x} : x ∈ M.support ↔ x ∈ M ∧ -x ∈ M := .rfl

theorem coe_support : M.support = (M : Set R) ∩ -(M : Set R) := rfl

@[simp]
theorem supportAddSubgroup_eq : M.supportAddSubgroup = M.support.toAddSubgroup := rfl

end HasIdealSupport

end AddSubmonoid

namespace Subsemiring

instance (M : Subsemiring R) [HasMemOrNegMem M] : M.HasIdealSupport where
  smul_mem_support x a ha := by
    have := mem_or_neg_mem M x
    have : ∀ x y, -x ∈ M → -y ∈ M → x * y ∈ M := fun _ _ hx hy ↦ by simpa using mul_mem hx hy
    aesop (add unsafe 80% apply this)

end Subsemiring

end Ring
