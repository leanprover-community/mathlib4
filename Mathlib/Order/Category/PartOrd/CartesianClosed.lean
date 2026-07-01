/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Category.PartOrd
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The Cartesian closed structure on `PartOrd`

`PartOrd`, the category of partial orders, has finite products given by the product order, so it is
a `CartesianMonoidalCategory`. Moreover it is `MonoidalClosed`: the internal hom `A ⟹ B` is the
partial order `A →o B` of monotone maps under the pointwise order.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe u

namespace PartOrd

/-- The chosen terminal object of `PartOrd`, the one-element partial order. -/
def isTerminalPUnit : IsTerminal (of PUnit.{u + 1}) :=
  .ofUniqueHom (fun _ => ofHom ⟨fun _ => ⟨⟩, fun _ _ _ => le_rfl⟩)
    fun _ _ => ext fun _ => Subsingleton.elim _ _

/-- The chosen terminal cone of `PartOrd`. -/
def terminalCone : LimitCone (Functor.empty.{0} PartOrd.{u}) :=
  ⟨_, isTerminalPUnit⟩

/-- The binary product of partial orders is their product order. -/
def binaryProductLimitCone (A B : PartOrd.{u}) : LimitCone (pair A B) where
  cone := BinaryFan.mk (P := of (A × B)) (ofHom OrderHom.fst) (ofHom OrderHom.snd)
  isLimit := BinaryFan.IsLimit.mk _
    (fun f g => ofHom (f.hom.prod g.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

instance : CartesianMonoidalCategory PartOrd.{u} :=
  .ofChosenFiniteProducts terminalCone binaryProductLimitCone

instance : BraidedCategory PartOrd.{u} := .ofCartesianMonoidalCategory

theorem tensorObj_eq (A B : PartOrd.{u}) : A ⊗ B = of (A × B) := rfl

/-- The internal hom `A ⟹ -` on `PartOrd`, sending `B` to the partial order `A →o B` of monotone
maps with the pointwise order, and a morphism to postcomposition. -/
def ihomFunctor (A : PartOrd.{u}) : PartOrd.{u} ⥤ PartOrd.{u} where
  obj B := of (A →o B)
  map f := ofHom ⟨(f.hom.comp ·), fun _ _ h a => f.hom.monotone (h a)⟩

/-- Currying: monotone maps `A × B → C` correspond to monotone maps `B → (A →o C)`. -/
def ihomEquiv (A B C : PartOrd.{u}) : (A ⊗ B ⟶ C) ≃ (B ⟶ (ihomFunctor A).obj C) where
  toFun h := ofHom
    ⟨fun b => ⟨fun a => h.hom (a, b), fun _ _ ha => h.hom.monotone ⟨ha, le_rfl⟩⟩,
      fun _ _ hb _ => h.hom.monotone ⟨le_rfl, hb⟩⟩
  invFun k :=
    let κ : (B : Type u) →o (A : Type u) →o (C : Type u) := k.hom
    ofHom ⟨fun (a, b) => κ b a, fun _ _ ⟨h₁, h₂⟩ => ((κ _).monotone h₁).trans (κ.monotone h₂ _)⟩

instance : MonoidalClosed PartOrd.{u} where
  closed A :=
    { rightAdj := ihomFunctor A
      adj := Adjunction.mkOfHomEquiv { homEquiv := ihomEquiv A } }

@[simp]
theorem ihom_obj (A B : PartOrd.{u}) : (ihom A).obj B = of (A →o B) := rfl

end PartOrd
