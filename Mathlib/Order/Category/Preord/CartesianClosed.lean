/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
public import Mathlib.CategoryTheory.Monoidal.Closed.Ideal
public import Mathlib.Order.Category.Preord.Reflective

/-!
# Cartesian closed structure on `Preord`

`Preord` is a reflective exponential ideal in `Cat`: functor categories with thin codomain
are thin. Hence `Preord` is cartesian closed.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CartesianClosed MonoidalCategory

noncomputable section

instance : ExponentialIdeal preordToCat.{u} := by
  apply ExponentialIdeal.mk'
  intro P C
  exact ⟨Preord.ofCat (C ⥤ P), ⟨Preord.ofCatIso (C ⥤ P)⟩⟩

namespace Preord

/-- The one-element preorder is terminal. -/
def isTerminalPUnit : IsTerminal (of PUnit.{u + 1}) :=
  .ofUniqueHom (fun X ↦ ofHom (OrderHom.const X PUnit.unit))
    (fun _ _ ↦ by ext)

/-- The product cone of preorders, with the usual product preorder. -/
def prodCone (X Y : Preord.{u}) : BinaryFan X Y :=
  .mk (P := of (X × Y)) (ofHom OrderHom.fst) (ofHom OrderHom.snd)

/-- The usual product preorder is a categorical product. -/
def isLimitProdCone (X Y : Preord.{u}) : IsLimit (prodCone X Y) := by
  refine BinaryFan.isLimitMk (fun s ↦ ofHom (s.fst.hom.prod s.snd.hom))
    (fun _ ↦ rfl) (fun _ ↦ rfl) fun s m h₁ h₂ ↦ ?_
  ext x
  exacts [congr($h₁ _), congr($h₂ _)]

instance : CartesianMonoidalCategory Preord.{u} :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩ fun X Y ↦
    ⟨prodCone X Y, isLimitProdCone X Y⟩

lemma tensorObj (X Y : Preord.{u}) : X ⊗ Y = of (X × Y) := rfl

lemma tensorUnit : 𝟙_ Preord.{u} = of PUnit.{u + 1} := rfl

instance : BraidedCategory Preord.{u} := .ofCartesianMonoidalCategory

instance : MonoidalClosed Preord.{u} :=
  cartesianClosedOfReflective preordToCat

end Preord

instance : Limits.PreservesFiniteProducts catToPreord.{u} :=
  .of_exponentialIdeal preordToCat
