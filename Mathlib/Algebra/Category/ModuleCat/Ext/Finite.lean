/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Noetherian.Basic

/-!

# `Ext`-modules between finitely generated modules over Noetherian rings are finitely generated

-/

@[expose] public section

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory Abelian

instance ModuleCat.finite_ext [Small.{v} R] [IsNoetherianRing R] (N M : ModuleCat.{v} R)
    [Module.Finite R N] [Module.Finite R M] (i : ℕ) : Module.Finite R (Ext N M i) := by
  induction i generalizing N with
  | zero => exact Module.Finite.equiv (Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv).symm
  | succ n ih =>
    obtain ⟨N, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R N
    let exac := LinearMap.shortExact_shortComplexKer surjf
    exact Module.Finite.of_surjective (exac.extClass.precompOfLinear R M (add_comm 1 n))
      (precomp_extClass_surjective_of_projective_X₂ M exac n)
