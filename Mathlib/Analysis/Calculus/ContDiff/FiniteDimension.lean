/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.NormedSpace.FiniteDimension



/-!
# Higher differentiability in finite dimensions.

-/


noncomputable section

universe uD uE uF uG

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {D : Type uD} [NormedAddCommGroup D]
  [NormedSpace 𝕜 D] {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type uF}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-! ### Finite dimensional results -/

section FiniteDimensional

open Function FiniteDimensional

variable [CompleteSpace 𝕜]

/-- A family of continuous linear maps is `C^n` on `s` if all its applications are. -/
theorem contDiffOn_clm_apply {n : ℕ∞} {f : E → F →L[𝕜] G} {s : Set E} [FiniteDimensional 𝕜 F] :
    ContDiffOn 𝕜 n f s ↔ ∀ y, ContDiffOn 𝕜 n (fun x => f x y) s := by
  refine ⟨fun h y => h.clm_apply contDiffOn_const, fun h => ?_⟩
  let d := finrank 𝕜 F
  have hd : d = finrank 𝕜 (Fin d → 𝕜) := (finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : G ≃L[𝕜] G)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.comp_contDiffOn (contDiffOn_pi.mpr fun i => h _)

theorem contDiff_clm_apply_iff {n : ℕ∞} {f : E → F →L[𝕜] G} [FiniteDimensional 𝕜 F] :
    ContDiff 𝕜 n f ↔ ∀ y, ContDiff 𝕜 n fun x => f x y := by
  simp_rw [← contDiffOn_univ, contDiffOn_clm_apply]

/-- This is a useful lemma to prove that a certain operation preserves functions being `C^n`.
When you do induction on `n`, this gives a useful characterization of a function being `C^(n+1)`,
assuming you have already computed the derivative. The advantage of this version over
`contDiff_succ_iff_fderiv` is that both occurrences of `ContDiff` are for functions with the same
domain and codomain (`E` and `F`). This is not the case for `contDiff_succ_iff_fderiv`, which
often requires an inconvenient need to generalize `F`, which results in universe issues
(see the discussion in the section of `ContDiff.comp`).

This lemma avoids these universe issues, but only applies for finite dimensional `E`. -/
theorem contDiff_succ_iff_fderiv_apply [FiniteDimensional 𝕜 E] {n : ℕ} {f : E → F} :
    ContDiff 𝕜 (n + 1 : ℕ) f ↔ Differentiable 𝕜 f ∧ ∀ y, ContDiff 𝕜 n fun x => fderiv 𝕜 f x y := by
  rw [contDiff_succ_iff_fderiv, contDiff_clm_apply_iff]

theorem contDiffOn_succ_of_fderiv_apply [FiniteDimensional 𝕜 E] {n : ℕ} {f : E → F} {s : Set E}
    (hf : DifferentiableOn 𝕜 f s) (h : ∀ y, ContDiffOn 𝕜 n (fun x => fderivWithin 𝕜 f s x y) s) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f s :=
  contDiffOn_succ_of_fderivWithin hf <| contDiffOn_clm_apply.mpr h

theorem contDiffOn_succ_iff_fderiv_apply [FiniteDimensional 𝕜 E] {n : ℕ} {f : E → F} {s : Set E}
    (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f s ↔
      DifferentiableOn 𝕜 f s ∧ ∀ y, ContDiffOn 𝕜 n (fun x => fderivWithin 𝕜 f s x y) s := by
  rw [contDiffOn_succ_iff_fderivWithin hs, contDiffOn_clm_apply]

end FiniteDimensional
