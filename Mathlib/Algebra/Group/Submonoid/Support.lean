/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Tactic.ApplyFun

/-!
# Supports of submonoids

Let `G` be an (additive) group, and let `M` be a submonoid of `G`.
The *support* of `M` is `M ∩ -M`, the largest subgroup of `G` contained in `M`.
A submonoid `C` is *pointed*, or a *positive cone*, if it has zero support.
A submonoid `C` is *spanning* if the subgroup it generates is `G` itself.

The names for these concepts are taken from the theory of convex cones.

## Main definitions

* `AddSubmonoid.support`: the support of a submonoid.
* `AddSubmonoid.IsPointed`: typeclass for submonoids with zero support.
* `AddSubmonoid.IsSpanning`: typeclass for submonoids generating the whole group.

## Tags

support, positive cone, group cone

-/

@[expose] public section

namespace AddSubmonoid

variable {G : Type*} [AddGroup G] (M : AddSubmonoid G)

/-- Typeclass for submonoids of a group with zero support. -/
class IsPointed (M : AddSubmonoid G) : Prop where
  eq_zero_of_mem_of_neg_mem {x} (hx₁ : x ∈ M) (hx₂ : -x ∈ M) : x = 0 := by aesop

export IsPointed (eq_zero_of_mem_of_neg_mem)

attribute [aesop 50%, aesop safe forward (immediate := [hx₁])] eq_zero_of_mem_of_neg_mem

/-- Typeclass for submonoids `M` of a group `G` such that `M` generates `G` as a subgroup. -/
class IsSpanning (M : AddSubmonoid G) : Prop where
  mem_or_neg_mem (M) (a : G) : a ∈ M ∨ -a ∈ M := by aesop

export IsSpanning (mem_or_neg_mem)

attribute [aesop safe, aesop safe forward] mem_or_neg_mem

end AddSubmonoid

namespace Submonoid

variable {G : Type*} [Group G] (M : Submonoid G)

/--
The support of a submonoid `M` of a group `G` is `M ∩ M⁻¹`,
the largest subgroup of `G` contained in `M`.
-/
@[to_additive
/-- The support of a submonoid `M` of a group `G` is `M ∩ -M`,
the largest subgroup of `G` contained in `M`. -/]
def mulSupport : Subgroup G where
  carrier := M ∩ M⁻¹
  one_mem' := by aesop
  mul_mem' := by aesop
  inv_mem' := by aesop

variable {M} in
@[to_additive (attr := aesop simp)]
theorem mem_mulSupport {x} : x ∈ M.mulSupport ↔ x ∈ M ∧ x⁻¹ ∈ M := .rfl

@[to_additive]
theorem coe_mulSupport : M.mulSupport = (M ∩ M⁻¹ : Set G) := rfl

variable {G : Type*} [Group G] (M : Submonoid G)

/-- Typeclass for submonoids of a group with zero support. -/
@[to_additive]
class IsMulPointed (M : Submonoid G) : Prop where
  eq_one_of_mem_of_inv_mem {x} (hx₁ : x ∈ M) (hx₂ : x⁻¹ ∈ M) : x = 1 := by aesop

export IsMulPointed (eq_one_of_mem_of_inv_mem)

attribute [aesop 50% apply, aesop safe forward (immediate := [hx₁])] eq_one_of_mem_of_inv_mem

@[to_additive (attr := aesop safe forward (immediate := [hx₂]))]
alias eq_one_of_mem_of_inv_mem₂ := eq_one_of_mem_of_inv_mem -- for Aesop

@[to_additive (attr := simp)]
theorem mulSupport_eq_bot [M.IsMulPointed] : M.mulSupport = ⊥ := by ext; aesop

@[to_additive]
theorem IsMulPointed.of_mulSupport_eq_bot (h : M.mulSupport = ⊥) : M.IsMulPointed where
  eq_one_of_mem_of_inv_mem {x} := by
    apply_fun (x ∈ ·) at h
    aesop

/-- Typeclass for submonoids `M` of a group `G` such that `M` generates `G` as a subgroup. -/
@[to_additive]
class IsMulSpanning {G : Type*} [Group G] (M : Submonoid G) : Prop where
  mem_or_inv_mem (M) (a : G) : a ∈ M ∨ a⁻¹ ∈ M := by aesop

export IsMulSpanning (mem_or_inv_mem)

attribute [aesop safe forward, aesop safe apply] mem_or_inv_mem

@[to_additive (attr := aesop 80%)]
theorem inv_mem_of_notMem [M.IsMulSpanning] (x : G) (h : x ∉ M) : x⁻¹ ∈ M := by aesop

@[to_additive (attr := aesop 50%)]
theorem mem_of_inv_notMem [M.IsMulSpanning] (x : G) (h : x⁻¹ ∉ M) : x ∈ M := by aesop

@[to_additive]
theorem IsMulSpanning.of_le {M N : Submonoid G} [M.IsMulSpanning] (h : M ≤ N) :
    N.IsMulSpanning where

@[to_additive]
theorem IsMulSpanning.maximal_isMulPointed [M.IsMulPointed] [M.IsMulSpanning] :
    Maximal IsMulPointed M :=
  ⟨inferInstance, fun N hN h ↦ by rw [SetLike.le_def] at h ⊢; aesop⟩

end Submonoid
