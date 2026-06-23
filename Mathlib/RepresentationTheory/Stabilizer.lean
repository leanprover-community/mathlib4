/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.RepresentationTheory.Intertwining

import Mathlib.Tactic.Group

/-!
# Stabilizers in representations

This file defines the stabilizer of a vector in a representation and proves basic lemmas about
stabilizers of zero vectors, scalar multiplies, sums, intertwining maps, and actions by group
elements.

## Main definitions

* `Representation.stabilizer`: the subgroup fixing a vector in a representation.

## Main statements

* `Representation.mem_stabilizer`
* `Representation.stabilizer_zero`
* `Representation.stabilizer_smul`
* `Representation.stabilizer_add`
* `Representation.stabilizer_sum`
* `Representation.stabilizer_intertwining`
* `Representation.stabilizer_conj`
* `Representation.stabilizer_conj_coe`
-/

@[expose] public section


open Set
open scoped Pointwise
open MulOpposite

namespace Representation

variable {k G : Type*} [Group G] [Semiring k]
variable {V V' : Type*} [AddCommMonoid V] [Module k V] [AddCommMonoid V'] [Module k V']

/-- The stabilizer of a vector in a representation. -/
def stabilizer (ρ : Representation k G V) (v : V) : Subgroup G where
  carrier := {g : G | ρ g v = v}
  mul_mem' := by
    intro a b ha hb
    rw [mem_setOf_eq, map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    rw [mem_setOf_eq, ← hg, inv_self_apply, hg]

@[simp]
lemma mem_stabilizer (ρ : Representation k G V) (v : V) (g : G) :
    (g ∈ stabilizer ρ v) ↔ (ρ g v = v) := by
  rfl

lemma stabilizer_zero (ρ : Representation k G V) : stabilizer ρ 0 = ⊤ := by
  ext x
  simp only [mem_stabilizer, map_zero, Subgroup.mem_top]

lemma stabilizer_smul (ρ : Representation k G V) (c : k) (v : V) :
    stabilizer ρ v ≤ stabilizer ρ (c • v) := by
  intro g hg_stab
  rw [mem_stabilizer] at hg_stab
  rw [mem_stabilizer, map_smul, hg_stab]

lemma stabilizer_add (ρ : Representation k G V) (v1 v2 : V) :
    (stabilizer ρ v1) ⊓ (stabilizer ρ v2) ≤ stabilizer ρ (v1 + v2) := by
  intro g hg_stab
  rw [mem_stabilizer, map_add, hg_stab.1, hg_stab.2]

lemma stabilizer_sum (ρ : Representation k G V) (n : ℕ) (v : Fin n → V) :
    ⨅ i, (stabilizer ρ (v i)) ≤ stabilizer ρ (∑ i, v i) := by
  intro g hg_stab
  simp only [Subgroup.mem_iInf, mem_stabilizer] at hg_stab
  simp only [mem_stabilizer, map_sum, hg_stab]

lemma stabilizer_intertwining (ρ : Representation k G V) (v : V) (ρ' : Representation k G V')
    (f : ρ.IntertwiningMap ρ') : stabilizer ρ v ≤ stabilizer ρ' (f v) := by
  intro x hx_stab
  rw [mem_stabilizer] at hx_stab
  rw [mem_stabilizer, ← IntertwiningMap.isIntertwining, hx_stab]

/-- The stabilizer of `ρ g v` is the conjugate of the stabilizer of `v`. -/
lemma stabilizer_conj (ρ : Representation k G V) (g : G) (v : V) :
    ρ.stabilizer (ρ g v) = (stabilizer ρ v).map (MulAut.conj g) := by
  ext x
  simp only [mem_stabilizer, Subgroup.mem_map, MonoidHom.coe_coe, MulAut.conj_apply]
  constructor
  · intro hx_stab
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · simp only [map_mul, Module.End.mul_apply, hx_stab, inv_self_apply]
    · group
  · rintro ⟨y, hy_stab, hy_conj⟩
    simp only [← hy_conj, map_mul, Module.End.mul_apply, inv_self_apply, hy_stab]

/-- A set-level version of `stabilizer_conj`, useful for topological arguments. -/
lemma stabilizer_conj_coe (ρ : Representation k G V) (g : G) (v : V) :
    (ρ.stabilizer (ρ g v)).carrier = (op g⁻¹) • (g • (stabilizer ρ v).carrier) := by
  ext x
  simp only [stabilizer, mem_setOf_eq]
  apply Iff.intro
  · intro hx_stab
    use x * g
    simp only [smul_eq_mul_unop, MulOpposite.unop_op, mul_inv_cancel_right, and_true]
    use g⁻¹ * x * g
    constructor
    · simp only [mem_setOf_eq, map_mul, Module.End.mul_apply, hx_stab, inv_self_apply]
    · simp only [smul_eq_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  · rintro ⟨y, h, hy⟩
    obtain ⟨z, hz_stab, hz_conj⟩ := h
    simp only [smul_eq_mul_unop, MulOpposite.unop_op] at hy
    rw [← hy, map_mul, Module.End.mul_apply, inv_self_apply, ← hz_conj]
    rw [mem_setOf_eq] at hz_stab
    simp only [smul_eq_mul, map_mul, Module.End.mul_apply, hz_stab]

end Representation
