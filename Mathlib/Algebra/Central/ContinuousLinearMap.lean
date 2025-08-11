/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Central.Defs
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual

/-!
# The set of continuous linear maps is a central algebra
-/

variable {R V : Type*} [Field R] [AddCommGroup V] [TopologicalSpace R] [TopologicalSpace V]
  [IsTopologicalRing R] [Module R V] [SeparatingDual R V] [IsTopologicalAddGroup V]
  [ContinuousSMul R V]

/-- The center of continuous linear maps on a topological vector space
with separating dual is trivial, in other words, it is a central algebra. -/
instance Algebra.IsCentral.continuousLinearMap :
    Algebra.IsCentral R (V →L[R] V) where
  out := fun T hT => by
    have h' (f : V →L[R] R) (y v : V) : f (T v) • y = f v • T y := by
      simpa [ContinuousLinearMap.ext_iff, Function.comp_apply, map_smul]
        using congr($(Subalgebra.mem_center_iff.mp hT <| f.smulRight y) v)
    by_cases H : ∀ a : V, a = 0
    · use 0; simp [ContinuousLinearMap.ext_iff, H]
    obtain ⟨x, hx⟩ := not_forall.mp H
    obtain ⟨f, hf⟩ := SeparatingDual.exists_eq_one (R := R) hx
    use f (T x)
    ext y
    simp [h', hf]
