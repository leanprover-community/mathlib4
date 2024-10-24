/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# The pseudofunctor(s) which send a ring to its category of modules

In this file, we construct the pseudofunctor
`ModuleCat.restrictScalarsPseudofunctor : Pseudofunctor (LocallyDiscrete RingCatᵒᵖ) Cat`
which sends a ring `R` to its category of modules: the functoriality is given
by the restriction of scalars functors.

TODO: Define
`ModuleCat.extendScalarsPseudofunctor : Pseudofunctor (LocallyDiscrete CommRingCat) Cat`.

-/

universe v u

open CategoryTheory

namespace ModuleCat

/-- The pseudofunctor from `LocallyDiscrete RingCatᵒᵖ` to `Cat` which sends a ring `R`
to its category of modules. The functoriality is given by the restriction of scalars. -/
@[simps! obj map mapId mapComp]
noncomputable def restrictScalarsPseudofunctor :
    Pseudofunctor (LocallyDiscrete RingCat.{u}ᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of (ModuleCat.{v} R.unop))
    (fun f ↦ restrictScalars f.unop)
    (fun R ↦ restrictScalarsId R.unop)
    (fun f g ↦ restrictScalarsComp g.unop f.unop)

/-- The pseudofunctor from `LocallyDiscrete CommRingCat` to `Cat` which sends
a commutative ring `R` to its category of modules. The functoriality is given by
the extension of scalars. -/
noncomputable def extendScalarsPseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of (ModuleCat.{u} R))
    (fun f ↦ extendScalars f)
    (fun R ↦ sorry) sorry sorry sorry sorry

end ModuleCat
