/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.Homotopy.TopCat.Basic

/-!
# The singular simplicial sets functor preserves homotopies

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.Monoidal Simplicial

section -- to be moved

namespace TopCat

instance : toSSet.{u}.IsRightAdjoint := sSetTopAdj.isRightAdjoint

noncomputable instance : toSSet.{u}.Monoidal := .ofChosenFiniteProducts _

end TopCat

scoped [Simplicial] notation "|" X "|" => SSet.toTop.obj X

namespace SSet.stdSimplex

-- these sorries are filled in https://github.com/joelriou/topcat-model-category

noncomputable def toTopObjHomeoUnitInterval :
    |(Δ[1] : SSet.{u})| ≃ₜ TopCat.I.{u} :=
  sorry

noncomputable def toSSetObjI : Δ[1] ⟶ TopCat.toSSet.obj TopCat.I.{u} :=
  sSetTopAdj.homEquiv _ _ (TopCat.ofHom (toContinuousMap toTopObjHomeoUnitInterval))

@[reassoc (attr := simp)]
lemma sSetι₀_whiskerLeft_toSSetObjI_μIso_hom (X : TopCat.{u}) :
    SSet.ι₀ ≫ TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
      Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I = TopCat.toSSet.map TopCat.ι₀ := by
  sorry

@[reassoc (attr := simp)]
lemma sSetι₁_whiskerLeft_toSSetObjI_μIso_hom (X : TopCat.{u}) :
    SSet.ι₁ ≫ TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
      Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I = TopCat.toSSet.map TopCat.ι₁ := by
  sorry

end SSet.stdSimplex

end


namespace TopCat

variable {X Y : TopCat.{u}} {f g : X ⟶ Y}

noncomputable def Homotopy.toSSet {X Y : TopCat.{u}} {f g : X ⟶ Y} (h : Homotopy f g) :
    SSet.Homotopy (toSSet.map f) (toSSet.map g) where
  h := _ ◁ SSet.stdSimplex.toSSetObjI ≫ μ TopCat.toSSet _ _ ≫ TopCat.toSSet.map h.h
  h₀ := by simp [← Functor.map_comp]
  h₁ := by simp [← Functor.map_comp]
  rel := by
    ext _ ⟨⟨_, h⟩, _⟩
    simp at h

end TopCat
