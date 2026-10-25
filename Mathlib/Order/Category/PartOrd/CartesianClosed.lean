/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Order.Category.PartOrd.Reflective
public import Mathlib.Order.Category.Preord.CartesianClosed

/-!
# Cartesian closed structure on `PartOrd`

`PartOrd` is a reflective exponential ideal in `Preord`: functor categories with thin,
skeletal codomain are thin and skeletal. Hence `PartOrd` is cartesian closed.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CartesianClosed MonoidalCategory

noncomputable section

instance : ExponentialIdeal (forget₂ PartOrd.{u} Preord.{u}) := by
  apply ExponentialIdeal.mk'
  intro P A
  let B := (ihom A).obj ((forget₂ PartOrd Preord).obj P)
  let : PartialOrder B :=
    { B.str with
      le_antisymm F G hFG hGF :=
        CategoryTheory.Functor.eq_of_iso (C := P) (D := A) (fun _ _ h ↦ h.some.to_eq)
          (iso_of_both_ways (C := A ⥤ P) hFG.some hGF.some) }
  exact ⟨.of B, ⟨.refl _⟩⟩

namespace PartOrd

/-- The one-element partial order is terminal. -/
def isTerminalPUnit : IsTerminal (of PUnit.{u + 1}) :=
  .ofUniqueHom (fun X ↦ ofHom (.const X .unit))
    (fun _ _ ↦ by ext)

/-- The category of partial orders has `PUnit` as a terminal object. -/
def terminalLimitCone : LimitCone (Functor.empty.{0} PartOrd.{u}) :=
  ⟨_, isTerminalPUnit⟩

/-- The product cone of partial orders, with the usual product partial order. -/
def prodCone (X Y : PartOrd.{u}) : BinaryFan X Y :=
  .mk (P := of (X × Y)) (ofHom .fst) (ofHom .snd)

/-- The usual product partial order is a categorical product. -/
def isLimitProdCone (X Y : PartOrd.{u}) : IsLimit (prodCone X Y) := by
  refine BinaryFan.isLimitMk (fun s ↦ ofHom (s.fst.hom.prod s.snd.hom))
    (fun _ ↦ rfl) (fun _ ↦ rfl) fun s m h₁ h₂ ↦ ?_
  ext x
  exacts [congr($h₁ _), congr($h₂ _)]

/-- The category of partial orders has `X × Y`, the usual Cartesian product,
as the binary product of `X` and `Y`.
-/
def binaryProductLimitCone (X Y : PartOrd.{u}) : LimitCone (pair X Y) :=
  ⟨prodCone X Y, isLimitProdCone X Y⟩

instance : CartesianMonoidalCategory PartOrd.{u} :=
  .ofChosenFiniteProducts terminalLimitCone binaryProductLimitCone

lemma tensorObj (X Y : PartOrd.{u}) : X ⊗ Y = of (X × Y) := rfl

lemma tensorUnit : 𝟙_ PartOrd.{u} = of PUnit.{u + 1} := rfl

instance : BraidedCategory PartOrd.{u} := .ofCartesianMonoidalCategory

instance : MonoidalClosed PartOrd.{u} :=
  cartesianClosedOfReflective (forget₂ PartOrd Preord)

end PartOrd

instance : PreservesFiniteProducts preordToPartOrd.{u} :=
  .of_exponentialIdeal (forget₂ PartOrd Preord)
