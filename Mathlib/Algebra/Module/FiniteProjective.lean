/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.Dual

/-!
# Finite projective modules

The eventual goal is to formalize
[Stacks: Finite projective modules](https://stacks.math.columbia.edu/tag/00NV).

-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Module.Projective

theorem finite_iff_finitePresentation [Projective R M] :
    Module.Finite R M ↔ FinitePresentation R M := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  have ⟨n, f, g, surj, _, hfg⟩ := exists_comp_eq_id R M
  exact Module.finitePresentation_of_surjective _ surj
    (Finite.iff_fg.mp <| LinearMap.ker_eq_range_of_comp_eq_id hfg ▸ inferInstance)

end Module.Projective
