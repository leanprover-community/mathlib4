/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Lattice

import Mathlib.Tactic.ApplyFun

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

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace Submonoid

open scoped Pointwise

variable {G : Type*} [Group G] (M : Submonoid G)

/--
The support of a submonoid `M` of a group `G` is `M ∩ M⁻¹`,
the largest subgroup of `G` contained in `M`.
-/
@[to_additive (attr := simps!)
/-- The support of a submonoid `M` of a group `G` is `M ∩ -M`,
the largest subgroup of `G` contained in `M`. -/]
def mulSupport : Subgroup G where
  toSubmonoid := M ⊓ M⁻¹
  inv_mem' := by aesop

variable {M} in
@[to_additive (attr := simp)]
theorem mem_mulSupport {x} : x ∈ M.mulSupport ↔ x ∈ M ∧ x⁻¹ ∈ M := .rfl

@[to_additive (attr := simp)]
theorem mulSupport_toSubmonoid : M.mulSupport.toSubmonoid = M ⊓ M⁻¹ := rfl

@[to_additive]
/- The support of a submonoid is the largest subgroup it contains. -/
theorem _root_.Subgroup.gc_toSubmonoid_mulSupport :
    GaloisConnection (α := Subgroup G) Subgroup.toSubmonoid mulSupport :=
  fun _ _ ↦ ⟨fun _ _ ↦ by aesop, fun h _ hx ↦ (h hx).1⟩

variable {M}

variable (M) in
/-- A submonoid is pointed if it has zero support. -/
@[to_additive /-- A submonoid is pointed if it has zero support. -/]
def IsMulPointed := ∀ x ∈ M, x⁻¹ ∈ M → x = 1

namespace IsMulPointed

@[to_additive (attr := aesop 90%)]
theorem mk (h : ∀ x ∈ M, x⁻¹ ∈ M → x = 1) : M.IsMulPointed := h -- for Aesop

@[to_additive (attr := aesop safe forward (immediate := [hM, hx₁]))]
theorem eq_one_of_mem_of_inv_mem (hM : M.IsMulPointed)
    {x : G} (hx₁ : x ∈ M) (hx₂ : x⁻¹ ∈ M) : x = 1 := hM _ hx₁ hx₂

@[to_additive (attr := aesop safe forward (immediate := [hM, hx₂]))]
alias eq_one_of_mem_of_inv_mem₂ := eq_one_of_mem_of_inv_mem -- for Aesop

@[to_additive]
theorem _root_.isMulPointed_iff_mulSupport_eq_bot : M.IsMulPointed ↔ M.mulSupport = ⊥ where
  mp := by aesop
  mpr h := fun x ↦ by
    apply_fun (x ∈ ·) at h
    aesop

@[to_additive (attr := simp)]
alias ⟨mulSupport_eq_bot, _⟩ := isMulPointed_iff_mulSupport_eq_bot

@[to_additive]
alias ⟨_, of_mulSupport_eq_bot⟩ := isMulPointed_iff_mulSupport_eq_bot

end IsMulPointed

variable (M) in
/-- A submonoid `M` of a group `G` is spanning if `M` generates `G` as a subgroup. -/
@[to_additive
/-- A submonoid `M` of a group `G` is spanning if `M` generates `G` as a subgroup. -/]
def IsMulSpanning := ∀ a : G, a ∈ M ∨ a⁻¹ ∈ M

namespace IsMulSpanning

@[to_additive (attr := aesop 90%)]
theorem mk (h : ∀ a : G, a ∈ M ∨ a⁻¹ ∈ M) : M.IsMulSpanning := h -- for Aesop

@[to_additive (attr := aesop safe forward)]
theorem mem_or_inv_mem (hM : M.IsMulSpanning) (a : G) : a ∈ M ∨ a⁻¹ ∈ M := by aesop

@[to_additive]
theorem of_le {N : Submonoid G} (hM : M.IsMulSpanning) (h : M ≤ N) :
    N.IsMulSpanning := by aesop

@[to_additive]
theorem maximal_isMulPointed (hMp : M.IsMulPointed) (hMs : M.IsMulSpanning) :
    Maximal IsMulPointed M :=
  ⟨hMp, fun N hN h ↦ by rw [SetLike.le_def] at h ⊢; aesop⟩

end Submonoid.IsMulSpanning
