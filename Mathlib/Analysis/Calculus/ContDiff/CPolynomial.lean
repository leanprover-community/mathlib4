/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Higher smoothness of continuously polynomial functions

We prove that continuously polynomial functions are `C^∞`. In particular, this is the case
of continuous multilinear maps.
-/

open Filter Asymptotics

open scoped ENNReal ContDiff

universe u v

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section fderiv

variable {p : FormalMultilinearSeries 𝕜 E F} {r : ℝ≥0∞} {n : ℕ}
variable {f : E → F} {x : E} {s : Set E}

/-- A polynomial function is infinitely differentiable. -/
theorem CPolynomialOn.contDiffOn (h : CPolynomialOn 𝕜 f s) {n : WithTop ℕ∞} :
    ContDiffOn 𝕜 n f s := by
  let t := { x | CPolynomialAt 𝕜 f x }
  suffices ContDiffOn 𝕜 ω f t from (this.of_le le_top).mono h
  rw [← contDiffOn_infty_iff_contDiffOn_omega]
  have H : CPolynomialOn 𝕜 f t := fun _x hx ↦ hx
  have t_open : IsOpen t := isOpen_cPolynomialAt 𝕜 f
  exact contDiffOn_of_continuousOn_differentiableOn
    (fun m _ ↦ (H.iteratedFDeriv m).continuousOn.congr
      fun  _ hx ↦ iteratedFDerivWithin_of_isOpen _ t_open hx)
    (fun m _ ↦ (H.iteratedFDeriv m).analyticOnNhd.differentiableOn.congr
      fun _ hx ↦ iteratedFDerivWithin_of_isOpen _ t_open hx)

theorem CPolynomialAt.contDiffAt (h : CPolynomialAt 𝕜 f x) {n : WithTop ℕ∞} :
    ContDiffAt 𝕜 n f x :=
  let ⟨_, hs, hf⟩ := h.exists_mem_nhds_cPolynomialOn
  hf.contDiffOn.contDiffAt hs

end fderiv

namespace ContinuousMultilinearMap

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [Fintype ι] (f : ContinuousMultilinearMap 𝕜 E F) {n : WithTop ℕ∞} {x : Π i, E i}

open FormalMultilinearSeries

lemma contDiffAt : ContDiffAt 𝕜 n f x := f.cpolynomialAt.contDiffAt

lemma contDiff : ContDiff 𝕜 n f := contDiff_iff_contDiffAt.mpr (fun _ ↦ f.contDiffAt)

end ContinuousMultilinearMap
