/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.NormedSpace.AddTorsorBases

#align_import analysis.normed_space.add_torsor_bases from "leanprover-community/mathlib"@"2f4cdce0c2f2f3b8cd58f05d556d03b468e1eb2e"

/-!
# Barycentric coordinates are smooth
-/

variable {ι 𝕜 E P : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [MetricSpace P] [NormedAddTorsor E P]
variable [FiniteDimensional 𝕜 E]

theorem smooth_barycentric_coord (b : AffineBasis ι 𝕜 E) (i : ι) : ContDiff 𝕜 ⊤ (b.coord i) :=
  (⟨b.coord i, continuous_barycentric_coord b i⟩ : E →ᴬ[𝕜] 𝕜).contDiff
#align smooth_barycentric_coord smooth_barycentric_coord
