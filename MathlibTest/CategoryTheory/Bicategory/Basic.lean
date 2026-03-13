import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Bicategory.Modification.Oplax

open CategoryTheory Mathlib.Tactic BicategoryLike
open Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]
variable {a b c d : B}

example {f j : a ⟶ d} {g : a ⟶ b} {h : b ⟶ c} {i : c ⟶ d}
    (η : f ⟶ g ≫ (h ≫ i)) (θ : (g ≫ h) ≫ i ⟶ j) :
    η ⊗≫ θ = η ≫ (α_ _ _ _).inv ≫ θ := by
  bicategory

example {f : a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} (η : h ⟶ i) :
    (f ≫ g) ◁ η = (α_ _ _ _).hom ≫ f ◁ g ◁ η ≫ (α_ _ _ _).inv := by
  bicategory

example {f g h : a ⟶ b} {η : f ⟶ g} {θ : g ⟶ h} : η ≫ θ = η ≫ θ := by
  bicategory

section

variable {B : Type u} [Bicategory.{w, v} B] {C : Type u} [Bicategory.{w, v} C]
variable {F G H I : B ⥤ᵒᵖᴸ C}

open Oplax.OplaxTrans

example (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where
  as := {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp only [categoryStruct_comp_app, categoryStruct_comp_naturality]
      calc
        _ =  𝟙 _ ⊗≫ ((F.map f ≫ η.app b) ◁ Γ.as.app b ≫ η.naturality f ▷ ι.app b) ⊗≫
            η.app a ◁ ι.naturality f ⊗≫ 𝟙 _  := by
          bicategory
        _ = 𝟙 _ ⊗≫ η.naturality f ▷ _ ⊗≫ η.app a ◁ (G.map f ◁ Γ.as.app b ≫
            ι.naturality f) ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]
          bicategory
        _ = _ := by
          rw [Γ.as.naturality]
          bicategory }

end
