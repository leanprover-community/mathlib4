/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.LinearIsometry
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Smoothness of precomposition on continuous alternating maps

We show that a continuous alternating map is `C^n`, and that precomposition
`f ↦ (m ↦ m ∘ (f, …, f))` on spaces of continuous alternating maps
(`ContinuousAlternatingMap.compContinuousLinearMapCLM`) is `C^n` for every `n : ℕ∞`, over any
nontrivially normed field and with no completeness assumptions.

On spaces of continuous multilinear maps, precomposition is the diagonal of a continuous
multilinear map, hence polynomial. The alternating case follows by reflecting smoothness along
the isometric embedding of alternating maps into multilinear maps, whose range is closed.
This route does not reach the analytic case `n = ω`, which in positive characteristic and
infinite dimension is not known to hold; in characteristic zero it does, by alternatization.
-/

public section

open ContinuousMultilinearMap
open scoped ContDiff

namespace ContinuousAlternatingMap

variable {𝕜 ι E E' F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞}

theorem contDiff (f : E [⋀^ι]→L[𝕜] F) : ContDiff 𝕜 n f :=
  f.toContinuousMultilinearMap.contDiff

/-- Precomposition on spaces of continuous alternating maps, `f ↦ (m ↦ m ∘ (f, …, f))`, is `C^n`
for every `n : ℕ∞`. -/
theorem contDiff_compContinuousLinearMapCLM {n : ℕ∞} :
    ContDiff 𝕜 n (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) := by
  have h : ContDiff 𝕜 n fun f : E →L[𝕜] E' ↦
      (compContinuousLinearMapL (F := F) fun _ : ι ↦ f).comp (toContinuousMultilinearMapCLM 𝕜) :=
    ((compContinuousLinearMapContinuousMultilinear 𝕜 (fun _ : ι ↦ E) (fun _ ↦ E') F).contDiff.comp
      (contDiff_pi.2 fun _ ↦ contDiff_id)).clm_comp contDiff_const
  have hΦ := (toContinuousMultilinearMapLI (𝕜 := 𝕜) (ι := ι) (E := E) (F := F))
    |>.isClosed_range_postcomp (G := E' [⋀^ι]→L[𝕜] F) isClosed_range_toContinuousMultilinearMap
  exact (LinearIsometry.comp_contDiff_iff _ hΦ).1 h

end ContinuousAlternatingMap
