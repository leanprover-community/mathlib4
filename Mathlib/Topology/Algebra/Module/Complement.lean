/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Algebra.Module.LinearMap

@[expose] public section

open LinearMap (ker range)
open Topology ContinuousLinearMap

namespace Submodule

variable {R : Type*} [Ring R] {M : Type*} [TopologicalSpace M] [AddCommGroup M] [Module R M]

open ContinuousLinearMap

/-- Two submodules `p` and `q` are *topological complements* if they are algebraic complements and
the projection on `p` parallel to `q` is continuous -/
structure IsTopCompl (p q : Submodule R M) : Prop where
  isCompl : IsCompl p q
  continuous_projection : Continuous (IsCompl.projection isCompl)

/-- A submodule `p` is called *complemented* if there exists a continuous projection `M →ₗ[R] p`. -/
def ClosedComplemented (p : Submodule R M) : Prop :=
  ∃ f : M →L[R] p, ∀ x : p, f x = x

variable {p q : Submodule R M}

namespace IsTopCompl

theorem _root_.IsCompl.isTopCompl_iff (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous (IsCompl.projection h) :=
  ⟨IsTopCompl.continuous_projection, fun h' ↦ ⟨h, h'⟩⟩

protected theorem symm (h : IsTopCompl p q) : IsTopCompl q p where
  isCompl := h.isCompl.symm
  continuous_projection := .congr _ (fun x ↦ IsCompl.projection_eq_self_sub_projection h.isCompl x)

end IsTopCompl

namespace ClosedComplemented

variable [T1Space p]

theorem exists_isClosed_isCompl (h : ClosedComplemented p) :
    ∃ q : Submodule R M, IsClosed (q : Set M) ∧ IsCompl p q :=
  Exists.elim h fun f hf => ⟨ker f, isClosed_ker f, LinearMap.isCompl_of_proj hf⟩

/-- An arbitrary choice of closed complement of a closed complemented submodule. -/
noncomputable def complement (h : ClosedComplemented p) : Submodule R M :=
  Classical.choose h.exists_isClosed_isCompl

theorem isClosed_complement (h : ClosedComplemented p) : IsClosed (h.complement : Set M) :=
  Classical.choose_spec (h.exists_isClosed_isCompl) |>.1

theorem isCompl_complement (h : ClosedComplemented p) : IsCompl p h.complement :=
  Classical.choose_spec (h.exists_isClosed_isCompl) |>.2

protected theorem isClosed [IsTopologicalAddGroup M] [T1Space M]
    {p : Submodule R M} (h : ClosedComplemented p) : IsClosed (p : Set M) := by
  rcases h with ⟨f, hf⟩
  have : (ContinuousLinearMap.id R M - p.subtypeL.comp f).ker = p :=
    LinearMap.ker_id_sub_eq_of_proj hf
  exact this ▸ isClosed_ker _

end ClosedComplemented

@[simp]
theorem closedComplemented_bot : ClosedComplemented (⊥ : Submodule R M) :=
  ⟨0, fun x => by simp only [zero_apply, eq_zero_of_bot_submodule x]⟩

@[simp]
theorem closedComplemented_top : ClosedComplemented (⊤ : Submodule R M) :=
  ⟨(ContinuousLinearMap.id R M).codRestrict ⊤ fun _x => trivial,
    fun x => Subtype.ext_iff.2 <| by simp⟩

end Submodule

theorem ContinuousLinearMap.closedComplemented_ker_of_rightInverse {R : Type*} [Ring R]
    {M : Type*} [TopologicalSpace M] [AddCommGroup M] {M₂ : Type*} [TopologicalSpace M₂]
    [AddCommGroup M₂] [Module R M] [Module R M₂] [IsTopologicalAddGroup M] (f₁ : M →L[R] M₂)
    (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁) : f₁.ker.ClosedComplemented :=
  ⟨f₁.projKerOfRightInverse f₂ h, f₁.projKerOfRightInverse_apply_idem f₂ h⟩

end
