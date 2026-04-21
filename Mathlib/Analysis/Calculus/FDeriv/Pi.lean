/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Derivatives on pi-types.
-/
set_option backward.defeqAttrib.useBackward true

public section

variable {𝕜 ι : Type*} [DecidableEq ι] [NontriviallyNormedField 𝕜]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

@[fun_prop]
theorem hasFDerivAt_update (x : ∀ i, E i) {i : ι} (y : E i) :
    HasFDerivAt (Function.update x i) (.pi (Pi.single i (.id 𝕜 (E i)))) y := by
  rw [hasFDerivAt_pi]
  intro j
  rcases eq_or_ne j i with rfl | hij
  · simpa using hasFDerivAt_id _
  · simpa [hij] using hasFDerivAt_const _ _

@[fun_prop]
theorem hasFDerivAt_single {i : ι} (y : E i) :
    HasFDerivAt (Pi.single i) (.pi (Pi.single i (.id 𝕜 (E i)))) y :=
  hasFDerivAt_update 0 y

theorem fderiv_update (x : ∀ i, E i) {i : ι} (y : E i) :
    fderiv 𝕜 (Function.update x i) y = .pi (Pi.single i (.id 𝕜 (E i))) :=
  (hasFDerivAt_update x y).fderiv

theorem fderiv_single {i : ι} (y : E i) :
    fderiv 𝕜 (Pi.single i) y = .pi (Pi.single i (.id 𝕜 (E i))) :=
  fderiv_update 0 y
