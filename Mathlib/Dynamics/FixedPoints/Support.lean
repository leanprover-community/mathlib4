/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Topology.Separation.Basic

/-!
# Support of a self-map

In this file we define the fixed support of a self-map `f : α → α` to be the closure of the set of
non-fixed points of `f`.
-/

@[expose] public section

namespace Function

variable {α : Type*} [TopologicalSpace α] {x : α} {f g : α → α}

/-- The fixed support of a self-map `f : α → α` is the closure of the set of non-fixed points. -/
def fixedSupport (f : α → α) : Set α :=
  closure (fixedPoints f)ᶜ

/-- A self-map `f : α → α` has compact fixed support if its fixed support is compact. -/
def HasCompactFixedSupport (f : α → α) : Prop :=
  IsCompact (fixedSupport f)

/-- A self-map `f : α → α` has compact fixed support if and only if `f` fixes the complement of a
closed compact set. If `α` is preregular, then use `compactSupport_iff` instead. -/
theorem HasCompactFixedSupport_iff' :
    HasCompactFixedSupport f ↔ ∃ K, IsClosed K ∧ IsCompact K ∧ (fixedPoints f)ᶜ ⊆ K := by
  refine ⟨fun hf ↦ ?_, fun ⟨K, hK₁, hK₂, hf⟩ ↦ ?_⟩
  · exact ⟨closure (fixedPoints f)ᶜ, isClosed_closure, hf, subset_closure⟩
  · exact hK₂.of_isClosed_subset isClosed_closure (hK₁.closure_subset_iff.mpr hf)

/-- A self-map `f : α → α` of a preregular space `α` has compact fixed support if and only if `f`
fixes the complement of a compact set. -/
theorem HasCompactFixedSupport_iff [R1Space α] :
    HasCompactFixedSupport f ↔ ∃ K, IsCompact K ∧ (fixedPoints f)ᶜ ⊆ K := by
  rw [HasCompactFixedSupport_iff']
  refine ⟨fun ⟨K, hK₁, hK₂, hf⟩ ↦ ⟨K, hK₂, hf⟩, fun ⟨K, hK, hf⟩ ↦ ?_⟩
  exact ⟨closure K, isClosed_closure, hK.closure, hf.trans subset_closure⟩

/-- If `f` and `g` have compact fixed support, then so does their composition `f ∘ g`. -/
theorem HasCompactFixedSupport.comp (hf : HasCompactFixedSupport f)
    (hg : HasCompactFixedSupport g) : HasCompactFixedSupport (f ∘ g) := by
  rw [HasCompactFixedSupport_iff'] at *
  obtain ⟨K, hK₁, hK₂, hf⟩ := hf
  obtain ⟨L, hL₁, hL₂, hg⟩ := hg
  refine ⟨K ∪ L, hK₁.union hL₁, hK₂.union hL₂, ?_⟩
  grw [← inter_subset_fixedPoints_comp, Set.compl_inter, hf, hg]

theorem HasCompactFixedSupport.symm {f : α ≃ α} (hf : HasCompactFixedSupport f) :
    HasCompactFixedSupport f.symm := by
  rw [HasCompactFixedSupport_iff'] at *
  rwa [fixedPoints_symm]


end Function
