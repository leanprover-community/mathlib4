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

Given a self-map `f : X → X` of a topological space `X`, the closure of the non-fixed points of `f`
is often called the support of `f`. Since the word "support" is used to label various concepts
throughout mathematics, we will use the term "fixed support" for the concept described above.
This file contains basic definitions and API for the fixed support.
-/

namespace Function

variable {X : Type*} [TopologicalSpace X] {x : X} {f g : X → X}

/-- The fixed support of a self-map `f : X → X` is the closure of the set of non-fixed points, often
called the support of `f`, but we use the term "fixed support" to disamiguate from other notions. -/
public def fixedSupport (f : X → X) : Set X :=
  closure (fixedPoints f)ᶜ

public lemma fixedSupport_def (f : X → X) : fixedSupport f = closure (fixedPoints f)ᶜ := by
  rfl

/-- A self-map `f : X → X` has compact fixed support if its fixed support is compact. -/
public def HasCompactFixedSupport (f : X → X) : Prop :=
  IsCompact (fixedSupport f)

/-- A self-map `f : X → X` has compact fixed support if and only if `f` fixes the complement of a
closed compact set. If `X` is preregular, then use `compactSupport_iff` instead. -/
public theorem HasCompactFixedSupport_iff' :
    HasCompactFixedSupport f ↔ ∃ K, IsClosed K ∧ IsCompact K ∧ (fixedPoints f)ᶜ ⊆ K := by
  refine ⟨fun hf ↦ ?_, fun ⟨K, hK₁, hK₂, hf⟩ ↦ ?_⟩
  · exact ⟨closure (fixedPoints f)ᶜ, isClosed_closure, hf, subset_closure⟩
  · exact hK₂.of_isClosed_subset isClosed_closure (hK₁.closure_subset_iff.mpr hf)

/-- A self-map `f : X → X` of a preregular space `X` has compact fixed support if and only if `f`
fixes the complement of a compact set. -/
public theorem HasCompactFixedSupport_iff [R1Space X] :
    HasCompactFixedSupport f ↔ ∃ K, IsCompact K ∧ (fixedPoints f)ᶜ ⊆ K := by
  rw [HasCompactFixedSupport_iff']
  refine ⟨fun ⟨K, hK₁, hK₂, hf⟩ ↦ ⟨K, hK₂, hf⟩, fun ⟨K, hK, hf⟩ ↦ ?_⟩
  exact ⟨closure K, isClosed_closure, hK.closure, hf.trans subset_closure⟩

variable (X) in
public theorem hasCompactFixedSupport_id : HasCompactFixedSupport (id : X → X) := by
  simp [HasCompactFixedSupport, fixedSupport]

/-- If `f` and `g` have compact fixed support, then so does their composition `f ∘ g`. -/
public theorem HasCompactFixedSupport.comp (hf : HasCompactFixedSupport f)
    (hg : HasCompactFixedSupport g) : HasCompactFixedSupport (f ∘ g) := by
  rw [HasCompactFixedSupport_iff'] at *
  obtain ⟨K, hK₁, hK₂, hf⟩ := hf
  obtain ⟨L, hL₁, hL₂, hg⟩ := hg
  refine ⟨K ∪ L, hK₁.union hL₁, hK₂.union hL₂, ?_⟩
  grw [← inter_subset_fixedPoints_comp, Set.compl_inter, hf, hg]

public theorem HasCompactFixedSupport.symm {f : X ≃ X} (hf : HasCompactFixedSupport f) :
    HasCompactFixedSupport f.symm := by
  rwa [HasCompactFixedSupport, fixedSupport, fixedPoints_symm]

end Function
