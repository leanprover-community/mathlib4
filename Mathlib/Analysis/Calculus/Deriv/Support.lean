/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Support of the derivative of a function

In this file we prove that the (topological) support of a function includes the support of its
derivative. As a corollary, we show that the derivative of a function with compact support has
compact support.

## Keywords

derivative, support
-/

public section


universe u v

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : 𝕜 → E} {x : 𝕜}

/-! ### Support of derivatives -/


section Support

open Function

theorem HasStrictDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) : HasStrictDerivAt f 0 x := by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  exact (hasStrictDerivAt_const x 0).congr_of_eventuallyEq h.symm

theorem HasDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) : HasDerivAt f 0 x :=
  (HasStrictDerivAt.of_notMem_tsupport h).hasDerivAt

theorem HasDerivWithinAt.of_notMem_tsupport {s : Set 𝕜} (h : x ∉ tsupport f) :
    HasDerivWithinAt f 0 s x :=
  (HasDerivAt.of_notMem_tsupport h).hasDerivWithinAt

theorem deriv_of_notMem_tsupport (h : x ∉ tsupport f) : deriv f x = 0 := by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  simp [h.deriv_eq]

theorem support_deriv_subset : support (deriv f) ⊆ tsupport f := fun x ↦ by
  rw [← not_imp_not, notMem_support]
  exact deriv_of_notMem_tsupport

theorem tsupport_deriv_subset : tsupport (deriv f) ⊆ tsupport f :=
  closure_minimal support_deriv_subset isClosed_closure

protected theorem HasCompactSupport.deriv (hf : HasCompactSupport f) :
    HasCompactSupport (deriv f) :=
  hf.mono' support_deriv_subset

end Support
