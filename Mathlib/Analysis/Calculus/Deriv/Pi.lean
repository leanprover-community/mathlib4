/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# One-dimensional derivatives on pi-types.
-/

variable {𝕜 ι : Type*} [DecidableEq ι] [Fintype ι] [NontriviallyNormedField 𝕜]

theorem hasDerivAt_update {x : ι → 𝕜} {i : ι} (y : 𝕜) :
    HasDerivAt (Function.update x i) (Pi.single i (1:𝕜)) y := by
  convert (hasFDerivAt_update (E := fun _ ↦ 𝕜) y).hasDerivAt
  ext z j
  rw [Pi.single, Function.update_apply]
  split_ifs with h
  · simp [h]
  · simp [Function.update_noteq h]

theorem deriv_update {x : ι → 𝕜} {i : ι} (y : 𝕜) :
    deriv (Function.update x i) y = (Pi.single i (1:𝕜)) :=
  (hasDerivAt_update y).deriv
