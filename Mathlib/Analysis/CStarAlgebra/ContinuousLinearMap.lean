/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # `E →L[ℂ] E` as a C⋆-algebra

We place this here because, for reasons related to the import hierarchy, it should not be placed
in earlier files.
-/

#adaptation_note /-- 2025-03-29 for lean4#7717 had to add `norm_mul_self_le` field. -/
noncomputable
instance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :
    CStarAlgebra (E →L[ℂ] E) where
  norm_mul_self_le := CStarRing.norm_mul_self_le
