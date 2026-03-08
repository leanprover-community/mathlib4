/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial

/-!
# `Over X` when `C` has strict initial objects

In this file we define the canonical equivalence of `Over X` with `Discrete PUnit` when
`C` has strict initial objects. We also provide the variants for `P.Over Q X`
and the dual versions.
-/

@[expose] public section

universe w

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

set_option backward.isDefEq.respectTransparency false in
/-- If `C` has strict initial objects and `X` is an initial object, the category
`Over X` is equivalent to a point. -/
@[pp_with_univ]
noncomputable
def overEquivOfIsInitial [HasStrictInitialObjects C] (X : C) (h : IsInitial X) :
    Over X ≌ Discrete PUnit.{w + 1} where
  functor := Functor.star _
  inverse := Functor.fromPUnit (.mk (𝟙 X))
  unitIso := NatIso.ofComponents fun A ↦
    haveI := h.isIso_to A.hom
    Over.isoMk (asIso A.hom)
  counitIso := Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- If `C` has strict terminal objects and `X` is a terminal object, the category
`Under X` is equivalent to a point. -/
@[pp_with_univ]
noncomputable
def underEquivOfIsInitial [HasStrictTerminalObjects C] (X : C) (h : IsTerminal X) :
    Under X ≌ Discrete PUnit.{w + 1} where
  functor := Functor.star _
  inverse := Functor.fromPUnit (.mk (𝟙 X))
  counitIso := Iso.refl _
  unitIso := NatIso.ofComponents fun A ↦
    haveI := h.isIso_from A.hom
    Under.isoMk (asIso A.hom).symm

variable (P Q : MorphismProperty C) [P.ContainsIdentities] [Q.IsMultiplicative] [Q.RespectsIso]

set_option backward.isDefEq.respectTransparency false in
/-- If `C` has strict initial objects and `X` is an initial object, the category
`P.Over Q X` is equivalent to a point. -/
@[pp_with_univ]
noncomputable
def MorphismProperty.overEquivOfIsInitial [HasStrictInitialObjects C] (X : C) (h : IsInitial X) :
    P.Over Q X ≌ Discrete PUnit.{w + 1} where
  functor := Functor.star _
  inverse := Functor.fromPUnit (.mk _ (𝟙 X) (P.id_mem _))
  unitIso := NatIso.ofComponents fun A ↦
    haveI := h.isIso_to A.hom
    Over.isoMk (asIso A.hom)
  counitIso := Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- If `C` has strict terminal objects and `X` is a terminal object, the category
`P.Under Q X` is equivalent to a point. -/
@[pp_with_univ]
noncomputable
def MorphismProperty.underEquivOfIsInitial [HasStrictTerminalObjects C] (X : C) (h : IsTerminal X) :
    P.Under Q X ≌ Discrete PUnit.{w + 1} where
  functor := Functor.star _
  inverse := Functor.fromPUnit (.mk _ (𝟙 X) (P.id_mem _))
  counitIso := Iso.refl _
  unitIso := NatIso.ofComponents fun A ↦
    haveI := h.isIso_from A.hom
    Under.isoMk (asIso A.hom).symm

end CategoryTheory
