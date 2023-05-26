/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang

! This file was ported from Lean 3 source module geometry.manifold.conformal_groupoid
! leanprover-community/mathlib commit d1bd9c5df2867c1cb463bc6364446d57bdd9f7f1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Conformal.NormedSpace
import Mathbin.Geometry.Manifold.ChartedSpace

/-!
# Conformal Groupoid

In this file we define the groupoid of conformal maps on normed spaces.

## Main definitions

* `conformal_groupoid`: the groupoid of conformal local homeomorphisms.

## Tags

conformal, groupoid
-/


variable {X : Type _} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The pregroupoid of conformal maps. -/
def conformalPregroupoid : Pregroupoid X
    where
  property f u := ∀ x, x ∈ u → ConformalAt f x
  comp f g u v hf hg hu hv huv x hx := (hg (f x) hx.2).comp x (hf x hx.1)
  id_mem x hx := conformalAt_id x
  locality f u hu h x hx :=
    let ⟨v, h₁, h₂, h₃⟩ := h x hx
    h₃ x ⟨hx, h₂⟩
  congr f g u hu h hf x hx := (hf x hx).congr hx hu h
#align conformal_pregroupoid conformalPregroupoid

/-- The groupoid of conformal maps. -/
def conformalGroupoid : StructureGroupoid X :=
  conformalPregroupoid.groupoid
#align conformal_groupoid conformalGroupoid

