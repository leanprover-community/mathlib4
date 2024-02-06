/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Condensed.Basic

/-!

# Discrete-underlying adjunction

Given a well-behaved concrete category `C`, we define a functor `C ⥤ Condensed C` which associates
to an object of `C` the corresponding "discrete" condensed object (see `Condensed.discrete`).

In `Condensed.discrete_underlying_adj` we prove that this functor is left adjoint to the forgetful
functor from `Condensed C` to `C`.
-/

universe u v w

open CategoryTheory Limits Opposite GrothendieckTopology

variable (C : Type w) [Category.{u+1} C] [HasWeakSheafify (coherentTopology CompHaus) C]

/--
The discrete condensed object associated to an object of `C` is the constant sheaf at that object.
-/
@[simps!]
noncomputable def Condensed.discrete : C ⥤ Condensed.{u} C := constantSheaf _ C

/--
The underlying object of a condensed object in `C` is the condensed object evaluated at a point.
This can be viewed as a sort of forgetful functor from `Condensed C` to `C`
-/
@[simps!]
noncomputable def Condensed.underlying : Condensed.{u} C ⥤ C := (sheafSections _ _).obj (op (⊤_ _))

/--
Discreteness is left adjoint to the forgetful functor. When `C` is `Type*`, this is analogous to
`TopCat.adj₁ : TopCat.discrete ⊣ forget TopCat`.  
-/
noncomputable def Condensed.discrete_underlying_adj : discrete C ⊣ underlying C :=
  constantSheafAdj _ _ terminalIsTerminal
