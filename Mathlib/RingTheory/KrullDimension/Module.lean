/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Support

/-!

# Dimension of Module

In this file we defined `dim(M)` for a `R`-module `M`.

-/

namespace Module

open Order

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- The dimension of module, defined as `krullDim` of its support. -/
noncomputable def supportDim : WithBot ℕ∞ :=
  krullDim (Module.support R M)

lemma supportDim_ne_bot_of_nontrivial [Nontrivial M] : supportDim R M ≠ ⊥ := by
  simpa [supportDim, Module.support_eq_empty_iff, not_subsingleton_iff_nontrivial]

lemma supportDim_eq_ringKrullDim_quotient_ann [Module.Finite R M] :
    supportDim R M = ringKrullDim (R ⧸ (Module.annihilator R M)) := by
  simp only [supportDim]
  rw [Module.support_eq_zeroLocus, ringKrullDim_quotient]

end Module
