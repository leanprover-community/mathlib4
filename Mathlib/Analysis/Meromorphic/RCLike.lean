/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.RCLike.Basic

/-!
# Meromorphic Functions over the Real and Complex Numbers

This file gathers results on meromorphic functions specifict to the real and complex numbers.
-/

public section

open Filter Set

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
If `f` is meromorphic function on `ℝ` or `ℂ`, then there exists a point where a meromorphic function
`f` has finite order iff `f` has finite order at every point.
-/
theorem Meromorphic.exists_meromorphicOrderAt_ne_top_iff_forall {f : 𝕜 → E} (hf : Meromorphic f) :
    (∃ u, meromorphicOrderAt f u ≠ ⊤) ↔ (∀ u, meromorphicOrderAt f u ≠ ⊤) := by
  simpa using (meromorphicOn_univ.2 hf).exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ

/--
If `f` is a meromorphic function on `ℝ` or `ℂ`, then `f` has infinite order at some point iff `f`
has infinite order at every point.  This is the counterpart of
`Meromorphic.exists_meromorphicOrderAt_ne_top_iff_forall` for infinite order.
-/
theorem Meromorphic.exists_meromorphicOrderAt_eq_top_iff_forall {f : 𝕜 → E} (hf : Meromorphic f) :
    (∃ u, meromorphicOrderAt f u = ⊤) ↔ (∀ u, meromorphicOrderAt f u = ⊤) := by
  have := hf.exists_meromorphicOrderAt_ne_top_iff_forall.not.symm
  aesop

/--
A meromorphic function on `ℝ` or `ℂ` has infinite order at some point iff it vanishes outside a
discrete set, i.e. iff it is eventually zero along the codiscrete filter.
-/
theorem Meromorphic.exists_meromorphicOrderAt_eq_top_iff_eventually_zero {f : 𝕜 → E}
    (hf : Meromorphic f) :
    (∃ u, meromorphicOrderAt f u = ⊤) ↔ (f =ᶠ[codiscrete 𝕜] 0) := by
  rw [hf.exists_meromorphicOrderAt_eq_top_iff_forall]
  constructor <;> intro h
  · apply eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.2
      (fun x ↦meromorphicOrderAt_eq_top_iff.1 (h x))
  · intro _
    rw [meromorphicOrderAt_eq_top_iff, Filter.Eventually]
    apply mem_codiscrete_iff_forall_mem_nhdsNE.1 h
