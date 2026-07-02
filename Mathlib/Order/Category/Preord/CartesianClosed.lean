/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Category.Preord
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The Cartesian closed structure on `Preord`

`Preord`, the category of preorders, has finite products given by the product order, so it is a
`CartesianMonoidalCategory`. Moreover it is `MonoidalClosed`: the internal hom `A ⟹ B` is the
preorder `A →o B` of monotone maps under the pointwise order.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe u

namespace Preord

/-- The chosen terminal object of `Preord`, the one-element preorder. -/
def isTerminalPUnit : IsTerminal (of PUnit.{u + 1}) :=
  .ofUniqueHom (fun _ => ofHom ⟨fun _ => ⟨⟩, fun _ _ _ => le_rfl⟩)
    fun _ _ => ext fun _ => Subsingleton.elim _ _

/-- The chosen terminal cone of `Preord`. -/
def terminalCone : LimitCone (Functor.empty Preord.{u}) :=
  ⟨_, isTerminalPUnit⟩

/-- The binary product of preorders is their product order. -/
def binaryProductLimitCone (A B : Preord.{u}) : LimitCone (pair A B) where
  cone := BinaryFan.mk (P := of (A × B)) (ofHom OrderHom.fst) (ofHom OrderHom.snd)
  isLimit := BinaryFan.IsLimit.mk _
    (fun f g => ofHom (f.hom.prod g.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

instance : CartesianMonoidalCategory Preord.{u} :=
  .ofChosenFiniteProducts terminalCone binaryProductLimitCone

instance : BraidedCategory Preord.{u} := .ofCartesianMonoidalCategory

theorem tensorObj_eq (A B : Preord.{u}) : A ⊗ B = of (A × B) := rfl

/-- The internal hom `A ⟹ -` on `Preord`, sending `B` to the preorder `A →o B` of monotone maps
with the pointwise order, and a morphism to postcomposition. -/
def ihomFunctor (A : Preord.{u}) : Preord.{u} ⥤ Preord.{u} where
  obj B := of (A →o B)
  map f := ofHom ⟨(f.hom.comp ·), fun _ _ h a => f.hom.monotone (h a)⟩

/-- Currying: monotone maps `A × B → C` correspond to monotone maps `B → (A →o C)`. -/
def ihomEquiv (A B C : Preord.{u}) : (A ⊗ B ⟶ C) ≃ (B ⟶ (ihomFunctor A).obj C) where
  toFun h := ofHom
    ⟨fun b => ⟨fun a => h.hom (a, b), fun _ _ ha => h.hom.monotone ⟨ha, le_rfl⟩⟩,
      fun _ _ hb _ => h.hom.monotone ⟨le_rfl, hb⟩⟩
  invFun k :=
    let κ : (B : Type u) →o (A : Type u) →o (C : Type u) := k.hom
    ofHom ⟨fun (a, b) => κ b a, fun _ _ ⟨h₁, h₂⟩ => ((κ _).monotone h₁).trans (κ.monotone h₂ _)⟩

instance : MonoidalClosed Preord.{u} where
  closed A :=
    { rightAdj := ihomFunctor A
      adj := Adjunction.mkOfHomEquiv { homEquiv := ihomEquiv A } }

@[simp]
theorem ihom_obj (A B : Preord.{u}) : (ihom A).obj B = of (A →o B) := rfl

end Preord
