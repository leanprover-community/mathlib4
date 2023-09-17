/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Analysis.Calculus.ContDiff

/-!
A supplement to the file
# Higher differentiability of usual operations
# One-dimensional derivatives
-/


open Classical Function
set_option autoImplicit true

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem hasFDerivAt_sub_const {x : F} (c : F) :
    HasFDerivAt (· - c) (ContinuousLinearMap.id 𝕜 (F)) x :=
  (hasFDerivAt_id x).sub_const c

theorem contDiff_update (k : ℕ∞) (x : ∀ i, E i) (i : ι) : ContDiff 𝕜 k (Function.update x i) := by
  rw [contDiff_pi]
  intro j
  dsimp [Function.update]
  split_ifs with h
  · subst h
    exact contDiff_id
  · exact contDiff_const

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
