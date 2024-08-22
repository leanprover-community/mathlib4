
import Mathlib.Tactic.CategoryTheory.ToApp
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

open CategoryTheory Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

-- #check Lean.Elab.Term.elabTermAndSynthesize

@[reassoc, to_app]
lemma mapComp_assoc_right_hom (F : Pseudofunctor B C) {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom = F.map₂ (α_ f g h).inv ≫
    (F.mapComp (f ≫ g) h).hom ≫ (F.mapComp f g).hom ▷ F.map h ≫
    (α_ (F.map f) (F.map g) (F.map h)).hom :=
  F.toOplax.mapComp_assoc_right f g h
