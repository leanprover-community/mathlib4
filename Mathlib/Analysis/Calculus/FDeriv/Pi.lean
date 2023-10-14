/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Derivatives on pi-types.
-/

noncomputable section

variable {𝕜 ι : Type*} [DecidableEq ι] [Fintype ι] [NontriviallyNormedField 𝕜]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem hasFDerivAt_update {x : ∀ i, E i} {i : ι} (y : E i) :
    HasFDerivAt (Function.update x i)
      (ContinuousLinearMap.pi (Function.update 0 i (ContinuousLinearMap.id 𝕜 (E i)))) y := by
  set l := (ContinuousLinearMap.pi (Function.update 0 i (ContinuousLinearMap.id 𝕜 (E i))))
  have update_eq : Function.update x i = (fun _ ↦ x) + l ∘ (· - x i)
  · ext t j
    dsimp [Function.update]
    split_ifs with hji
    · subst hji
      simp
    · simp
  rw [update_eq]
  convert (hasFDerivAt_const _ _).add (l.hasFDerivAt.comp y (hasFDerivAt_sub_const (x i)))
  rw [zero_add, ContinuousLinearMap.comp_id]

theorem fderiv_update {x : ∀ i, E i} {i : ι} (y : E i) :
    fderiv 𝕜 (Function.update x i) y =
      ContinuousLinearMap.pi (Function.update 0 i (ContinuousLinearMap.id 𝕜 (E i))) :=
  (hasFDerivAt_update y).fderiv
