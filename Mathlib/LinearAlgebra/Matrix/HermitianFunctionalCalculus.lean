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

open scoped BigOperators
namespace IsHermitian
section DecidableEq

variable [DecidableEq n]

variable {A : Matrix n n 𝕜} (hA : IsHermitian A)

instance:
StarAlgHomClass (C(spectrum 𝕜 A, 𝕜) →⋆ₐ[𝕜] Matrix n n 𝕜) 𝕜 C(spectrum 𝕜 A, 𝕜) (Matrix n n 𝕜)
    where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨⟨g, _⟩, _⟩, _⟩, _⟩, _⟩ h; congr
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  commutes f := f.commutes'
  map_star f := f.map_star'

instance instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus 𝕜 (IsHermitian : Matrix n n 𝕜 → Prop) where
exists_cfc_of_predicate a ha := by
  use fun (f : C(spectrum 𝕜 a, 𝕜)) =>
  (eigenvectorUnitary ha : Matrix n n 𝕜) * diagonal (f ∘ RCLike.ofReal ∘ ha.eigenvalues)
      * (star (eigenvectorUnitary ha : Matrix n n 𝕜))
  constructor
  constructor


--
