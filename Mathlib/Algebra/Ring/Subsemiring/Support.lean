/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Group.Submonoid.Support
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.RingTheory.Ideal.Defs

/-!
# Supports of subsemirings

Let `R` be a ring, and let `S` be a subsemiring of `R`.
If `S` generates `R` as a subring, then the support of `S` forms an ideal.

## Main definitions

* `Subsemiring.support`: the support of a subsemiring, as an ideal.

-/

@[expose] public section

variable {R : Type*} [Ring R]

namespace Subsemiring

variable {S : Subsemiring R}

@[aesop safe forward (immediate := [hS, hx₁])]
theorem eq_zero_of_mem_of_neg_mem (hS : S.IsPointed) {x : R}
    (hx₁ : x ∈ S) (hx₂ : -x ∈ S) : x = 0 := hS.eq_zero_of_mem_of_neg_mem hx₁ hx₂

@[aesop safe forward (immediate := [hS, hx₂])]
alias eq_zero_of_mem_of_neg_mem₂ := eq_zero_of_mem_of_neg_mem -- for Aesop

@[aesop safe forward]
theorem mem_or_neg_mem (hS : S.IsSpanning) : ∀ a, a ∈ S ∨ -a ∈ S :=
  hS.mem_or_neg_mem

variable (S) in
/-- Typeclass to track when the support of a subsemiring forms an ideal. -/
class HasIdealSupport : Prop where
  smul_mem_support (x : R) {a : R} (ha : a ∈ S.support) :
    x * a ∈ S.support := by aesop

export HasIdealSupport (smul_mem_support)

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

variable (S) in
/-- The support `S ∩ -S` of a subsemiring `S` of a ring `R`, as an ideal. -/
@[simps!]
def support : Ideal R where
  __ := S.toAddSubmonoid.support
  smul_mem' := by aesop

@[aesop simp]
theorem mem_support {x} : x ∈ S.support ↔ x ∈ S ∧ -x ∈ S := .rfl

variable (S) in
@[simp]
theorem toAddSubmonoid_support : S.toAddSubmonoid.support = S.support.toAddSubgroup := rfl

end HasIdealSupport

@[aesop safe forward, aesop 50%]
theorem _root_.AddSubmonoid.IsSpanning.hasIdealSupport (hS : S.IsSpanning) : S.HasIdealSupport where
  smul_mem_support x a ha := by
    have := S.mem_or_neg_mem hS x
    have : ∀ x y, -x ∈ S → -y ∈ S → x * y ∈ S := fun _ _ hx hy ↦ by simpa using mul_mem hx hy
    aesop (add 80% this)

@[aesop safe forward, aesop 50%]
theorem _root_.AddSubmonoid.IsPointed.hasIdealSupport (hS : S.IsPointed) : S.HasIdealSupport where

@[simp]
theorem support_eq_bot (hS : S.IsPointed) :
    have := hS.hasIdealSupport
    S.support = ⊥ := by
  apply_fun Submodule.toAddSubgroup using Submodule.toAddSubgroup_injective
  rw [← toAddSubmonoid_support, hS.support_eq_bot, Submodule.bot_toAddSubgroup]

end Subsemiring
