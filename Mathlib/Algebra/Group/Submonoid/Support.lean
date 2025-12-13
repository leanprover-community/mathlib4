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
@[to_additive]
theorem mem_supportSubgroup {x} : x ∈ M.supportSubgroup ↔ x ∈ M ∧ x⁻¹ ∈ M := .rfl

@[to_additive]
theorem coe_supportSubgroup : M.supportSubgroup = (M ∩ M⁻¹ : Set G) := rfl

end Submonoid

section Ring

variable {R : Type*} [Ring R]

namespace AddSubmonoid

variable (M : AddSubmonoid R)

/-- Typeclass to track when the support of a submonoid forms an ideal. -/
class HasIdealSupport (M : AddSubmonoid R) : Prop where
  smul_mem_support (M) (x : R) {a : R} (ha : a ∈ M.supportAddSubgroup) :
    x * a ∈ M.supportAddSubgroup

export HasIdealSupport (smul_mem_support)

variable {M} in
theorem hasIdealSupport_iff :
    M.HasIdealSupport ↔ ∀ x a : R, a ∈ M → -a ∈ M → x * a ∈ M ∧ -(x * a) ∈ M where
  mp _ := by simpa [mem_supportAddSubgroup] using smul_mem_support M
  mpr _ := ⟨by simpa [mem_supportAddSubgroup]⟩

section HasIdealSupport

variable [M.HasIdealSupport]

/--
The support of a subsemiring `S` of a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def support : Ideal R where
  __ := supportAddSubgroup M
  smul_mem' := by simpa [mem_supportAddSubgroup] using smul_mem_support M

variable {M} in
theorem mem_support {x} : x ∈ M.support ↔ x ∈ M ∧ -x ∈ M := .rfl

theorem coe_support : M.support = (M : Set R) ∩ -(M : Set R) := rfl

@[simp]
theorem supportAddSubgroup_eq : M.supportAddSubgroup = M.support.toAddSubgroup := rfl

end HasIdealSupport

end AddSubmonoid

namespace Subsemiring

instance (M : Subsemiring R) [HasMemOrNegMem M] : M.HasIdealSupport where
  smul_mem_support x a ha :=
    match mem_or_neg_mem M x with
    | .inl hx => ⟨by simpa using Subsemiring.mul_mem M hx ha.1,
                  by simpa using Subsemiring.mul_mem M hx ha.2⟩
    | .inr hx => ⟨by simpa using Subsemiring.mul_mem M hx ha.2,
                  by simpa using Subsemiring.mul_mem M hx ha.1⟩

end Subsemiring

end Ring
