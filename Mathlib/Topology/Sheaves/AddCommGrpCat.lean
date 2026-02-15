/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Sheaves of abelian groups.

Results for sheaves of abelian groups on topological spaces, in preparation for sheaf cohomology.
- `TopCat.Sheaf.AddCommGrpCat.Γ` : (Γ U) is the functor `(Sheaf AddCommGrpCat X) ⥤ AddCommGrpCat`
  that sends 𝓕 to 𝓕(U) and and sends a morphism f: 𝓕 ⟶ 𝓖 to f(U): 𝓕(U) ⟶ 𝓖(U)
-/

@[expose] public section

universe u

noncomputable section

open TopologicalSpace Opposite CategoryTheory AlgebraicGeometry

namespace TopCat

variable {X : TopCat.{u}} {U V : Opens X}

instance : HasExt.{u} (Sheaf AddCommGrpCat.{u} X) :=
  hasExt_of_enoughInjectives (Sheaf AddCommGrpCat X)

namespace Sheaf.AddCommGrpCat

/-- Given an open subset U of X, Γ U is the functor that sends a sheaf 𝓕 to 𝓕(U) and sends a
  morphism f: 𝓕 ⟶ 𝓖 to f(U): 𝓕(U) ⟶ 𝓖(U) -/
abbrev Γ (U : Opens X) : (Sheaf AddCommGrpCat X) ⥤ AddCommGrpCat :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op U)

lemma Γ.map_app {F G : Sheaf AddCommGrpCat X} (g : F ⟶ G) :
    (Γ U).map g = g.val.app (op U) := rfl

lemma restrict_sum {F : Sheaf AddCommGrpCat X} (h : V ≤ U) (s t : F.val.obj (op U)) :
    (s + t) |_ V = s |_V + t |_V := by
  delta Presheaf.restrictOpen Presheaf.restrict
  cat_disch

end TopCat.Sheaf.AddCommGrpCat
