/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Condensed.Light.Basic

/-!

# Discrete-underlying adjunction

Given a category `C` with sheafification with respect to the coherent topology on light profinite
sets, we define a functor `C ⥤ LightCondensed C` which associates to an object of `C` the
corresponding "discrete" light condensed object (see `LightCondensed.discrete`).

In `LightCondensed.discreteUnderlyingAdj` we prove that this functor is left adjoint to the
forgetful functor from `Condensed C` to `C`.
-/

universe u v w

open CategoryTheory Limits Opposite GrothendieckTopology

variable (C : Type w) [Category.{u} C] [HasSheafify (coherentTopology LightProfinite.{u}) C]

/--
The discrete condensed object associated to an object of `C` is the constant sheaf at that object.
-/
@[simps!]
noncomputable def LightCondensed.discrete : C ⥤ LightCondensed.{u} C := constantSheaf _ C

/--
The underlying object of a condensed object in `C` is the condensed object evaluated at a point.
This can be viewed as a sort of forgetful functor from `Condensed C` to `C`
-/
@[simps!]
noncomputable def LightCondensed.underlying : LightCondensed.{u} C ⥤ C :=
  (sheafSections _ _).obj (op (⊤_ _))

/--
Discreteness is left adjoint to the forgetful functor. When `C` is `Type*`, this is analogous to
`TopCat.adj₁ : TopCat.discrete ⊣ forget TopCat`.  
-/
noncomputable def LightCondensed.discreteUnderlyingAdj : discrete C ⊣ underlying C :=
  constantSheafAdj _ _ terminalIsTerminal

/-- A version of `LightCondensed.discrete` in the `LightCondSet` namespace -/
noncomputable abbrev LightCondSet.discrete := LightCondensed.discrete (Type u)

/-- A version of `LightCondensed.underlying` in the `LightCondSet` namespace -/
noncomputable abbrev LightCondSet.underlying := LightCondensed.underlying (Type u)

/-- A version of `LightCondensed.discrete_underlying_adj` in the `LightCondSet` namespace -/
noncomputable abbrev LightCondSet.discreteUnderlyingAdj : discrete ⊣ underlying :=
  LightCondensed.discreteUnderlyingAdj _
