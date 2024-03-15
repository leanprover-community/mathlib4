/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib

open CategoryTheory Limits

namespace CommRingCat

universe u

def _root_.Quiver.Hom.IsBasicOpen
    {X B : CommRingCat.{u}ᵒᵖ} (f : X ⟶ B) (x : B.unop) : Prop :=
  letI : Algebra _ _ := f.unop.toAlgebra
  IsLocalization.Away x X.unop

def _root_.Quiver.Hom.IsBasicOpen.basechange
    {P X Y B : CommRingCat.{u}ᵒᵖ}
    {f : X ⟶ B} {g : Y ⟶ B}
    {fst : P ⟶ X} {snd : P ⟶ Y}
    {x : B.unop}
    (hf : f.IsBasicOpen x) (hP : IsPullback fst snd f g) :
    snd.IsBasicOpen (g.unop x) := sorry

def zariskiCoverage : Coverage CommRingCat.{u}ᵒᵖ where
  covering B := { S |
    ∃ (α : Type u)
      (X : α → CommRingCat.{u}ᵒᵖ)
      (π : (a : α) → (X a ⟶ B))
      (f : α → B.unop)
      (hπ : ∀ (a : α), (π a).IsBasicOpen (f a))
      (hf : Ideal.span (Set.range f) = ⊤),
      S = Presieve.ofArrows X π }
  pullback := sorry

def zariskiTopology : GrothendieckTopology CommRingCat.{u}ᵒᵖ :=
  zariskiCoverage.toGrothendieck

structure FinitelyPresentedRing where
  generators : ℕ
  relations : Ideal <| MvPolynomial (Fin generators) ℤ

noncomputable
def toCommRingCat : FinitelyPresentedRing → CommRingCat.{u} := fun P =>
  .of <| ULift <| MvPolynomial (Fin P.generators) ℤ ⧸ P.relations

noncomputable
instance : Category.{u} FinitelyPresentedRing :=
  InducedCategory.category toCommRingCat.{u}

end CommRingCat
