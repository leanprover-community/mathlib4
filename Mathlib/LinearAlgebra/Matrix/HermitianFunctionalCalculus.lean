/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus.Restrict
import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus
import Mathlib.Analysis.NormedSpace.Star.Spectrum
import Mathlib.Topology.ContinuousFunction.UniqueCFC
/-
This file defines an instance of the continuous functional calculus for Hermitian matrices over an
RCLike field 𝕜.

## Tags

spectral theorem, diagonalization theorem, continuous functional calculus
-/

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
variable {A : Matrix n n 𝕜}

open scoped BigOperators

namespace IsHermitian

section DecidableEq

variable [DecidableEq n]
variable (hA : A.IsHermitian)

instance instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus 𝕜 (IsHermitian : Matrix n n 𝕜 → Prop) where
exists_cfc_of_predicate a ha := by
  use fun (f : C(spectrum 𝕜 a, 𝕜)) =>
  (eigenvectorUnitary hA : Matrix n n 𝕜) * diagonal ( f ∘ RCLike.ofReal ∘ hA.eigenvalues)
      * (star (eigenvectorUnitary hA : Matrix n n 𝕜))


--
