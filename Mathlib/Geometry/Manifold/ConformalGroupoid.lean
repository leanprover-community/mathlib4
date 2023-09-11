/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import Mathlib.Analysis.Calculus.Conformal.NormedSpace
import Mathlib.Geometry.Manifold.ChartedSpace

#align_import geometry.manifold.conformal_groupoid from "leanprover-community/mathlib"@"d1bd9c5df2867c1cb463bc6364446d57bdd9f7f1"

/-!
# Conformal Groupoid

In this file we define the groupoid of conformal maps on normed spaces.

## Main definitions

* `conformalGroupoid`: the groupoid of conformal local homeomorphisms.

## Tags

conformal, groupoid
-/


variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The pregroupoid of conformal maps. -/
def conformalPregroupoid : Pregroupoid X where
  property f u := ∀ x, x ∈ u → ConformalAt f x
  comp {f _} _ _ hf hg _ _ _ x hx := (hg (f x) hx.2).comp x (hf x hx.1)
  id_mem x _ := conformalAt_id x
  locality _ h x hx :=
    let ⟨_, _, h₂, h₃⟩ := h x hx
    h₃ x ⟨hx, h₂⟩
  congr hu h hf x hx := (hf x hx).congr hx hu h
#align conformal_pregroupoid conformalPregroupoid

/-- The groupoid of conformal maps. -/
def conformalGroupoid : StructureGroupoid X :=
  conformalPregroupoid.groupoid
#align conformal_groupoid conformalGroupoid
