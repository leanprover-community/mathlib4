/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Condensed.Basic
import Mathlib.Condensed.Light.Basic
/-!

# Discrete-underlying adjunction

Given a category `C` with sheafification with respect to the coherent topology on compact Hausdorff
spaces, we define a functor `C ⥤ Condensed C` which associates to an object of `C` the
corresponding "discrete" condensed object (see `Condensed.discrete`).

In `Condensed.discreteUnderlyingAdj` we prove that this functor is left adjoint to the forgetful
functor from `Condensed C` to `C`.

We also give the variant `LightCondensed.discreteUnderlyingAdj` for light condensed objects.

The file `Mathlib/Condensed/Discrete/Characterization.lean` defines a predicate `IsDiscrete` on
condensed and light condensed objects, and provides several conditions on a (light) condensed
set or module that characterize it as discrete.
-/

universe u v w

open CategoryTheory Limits Opposite GrothendieckTopology

namespace Condensed

variable (C : Type w) [Category.{u + 1} C] [HasWeakSheafify (coherentTopology CompHaus.{u}) C]

/--
The discrete condensed object associated to an object of `C` is the constant sheaf at that object.
-/
@[simps!]
noncomputable def discrete : C ⥤ Condensed.{u} C := constantSheaf _ C

/--
The underlying object of a condensed object in `C` is the condensed object evaluated at a point.
This can be viewed as a sort of forgetful functor from `Condensed C` to `C`
-/
@[simps!]
noncomputable def underlying : Condensed.{u} C ⥤ C :=
  (sheafSections _ _).obj ⟨CompHaus.of PUnit.{u + 1}⟩

/--
Discreteness is left adjoint to the forgetful functor. When `C` is `Type*`, this is analogous to
`TopCat.adj₁ : TopCat.discrete ⊣ forget TopCat`.
-/
noncomputable def discreteUnderlyingAdj : discrete C ⊣ underlying C :=
  constantSheafAdj _ _ CompHaus.isTerminalPUnit

end Condensed

namespace LightCondensed

variable (C : Type w) [Category.{u} C] [HasSheafify (coherentTopology LightProfinite.{u}) C]

/--
The discrete light condensed object associated to an object of `C` is the constant sheaf at that
object.
-/
@[simps!]
noncomputable def discrete : C ⥤ LightCondensed.{u} C := constantSheaf _ C

/--
The underlying object of a condensed object in `C` is the light condensed object evaluated at a
point. This can be viewed as a sort of forgetful functor from `LightCondensed C` to `C`
-/
@[simps!]
noncomputable def underlying : LightCondensed.{u} C ⥤ C :=
  (sheafSections _ _).obj (op (LightProfinite.of PUnit))

/--
Discreteness is left adjoint to the forgetful functor. When `C` is `Type*`, this is analogous to
`TopCat.adj₁ : TopCat.discrete ⊣ forget TopCat`.
-/
noncomputable def discreteUnderlyingAdj : discrete C ⊣ underlying C :=
  constantSheafAdj _ _ CompHausLike.isTerminalPUnit

end LightCondensed

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
/-- A version of `LightCondensed.discrete` in the `LightCondSet` namespace -/
noncomputable abbrev LightCondSet.discrete := LightCondensed.discrete (Type u)

/-- A version of `LightCondensed.underlying` in the `LightCondSet` namespace -/
noncomputable abbrev LightCondSet.underlying := LightCondensed.underlying (Type u)

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
/-- A version of `LightCondensed.discrete_underlying_adj` in the `LightCondSet` namespace -/
noncomputable abbrev LightCondSet.discreteUnderlyingAdj : discrete ⊣ underlying :=
  LightCondensed.discreteUnderlyingAdj _
