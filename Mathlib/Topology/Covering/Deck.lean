/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Deck transformations

For a map `p : E → X`, the **deck transformation group** `deck p` is the subgroup of
`E ≃ₜ E` consisting of self-homeomorphisms `h` with `p ∘ h = p`. No topology on `X` or
continuity of `p` is assumed.

The definition is stated for an arbitrary `p`; no `IsCoveringMap` hypothesis is needed
for the basic group structure or the canonical action. Theorems characterising deck
transformations via path lifting (when `p` is a covering map of a path-connected,
locally path-connected base) belong to follow-up files.

## Main definitions

* `deck p`: the subgroup of `E ≃ₜ E` consisting of homeomorphisms commuting with `p`.

## Main results

* `deck p` is a `Group`, acts on `E` via `MulAction`, the action is faithful and
  continuous in the second variable; these all follow automatically from the
  `Subgroup`-action transfers together with `Homeomorph.applyMulAction`.
* `deck.proj_smul`: deck transformations commute with `p`.
-/

@[expose] public section

variable {E X : Type*} [TopologicalSpace E]

/-- The deck transformation group of a map `p : E → X`: the subgroup of self-homeomorphisms
of `E` commuting with `p`. -/
def deck (p : E → X) : Subgroup (E ≃ₜ E) where
  carrier := { h | p ∘ h = p }
  one_mem' := rfl
  mul_mem' {f g} hf hg := by ext e; exact (congrFun hf (g e)).trans (congrFun hg e)
  inv_mem' {f} hf := by ext e; simpa using (congrFun hf (f.symm e)).symm

namespace deck

variable {p : E → X}

theorem mem_iff {h : E ≃ₜ E} : h ∈ deck p ↔ p ∘ h = p := Iff.rfl

@[simp]
theorem comp_eq (h : deck p) : p ∘ (h : E ≃ₜ E) = p := h.2

theorem proj_smul (h : deck p) (e : E) : p (h • e) = p e :=
  congrFun h.2 e

instance : ContinuousConstSMul (deck p) E :=
  ⟨fun h ↦ (h : E ≃ₜ E).continuous⟩

end deck
