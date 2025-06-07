import Mathlib.CategoryTheory.Bicategory.Functor.Lax
import Mathlib.Tactic.Widget.StringDiagram
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

open Mathlib.Tactic.Widget


namespace CategoryTheory.Lax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- op -/
structure OplaxTrans (F G : LaxFunctor B C) where
  /-- The component 1-morphisms of an oplax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the oplax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ⟶ app a ≫ G.map f
  /-- Naturality of the oplax naturality constraint. -/
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      F.map₂ η ▷ app b ≫ naturality g = naturality f ≫ app a ◁ G.map₂ η := by
    aesop_cat
  /-- Oplax unity. -/
  naturality_id (a : B) :
      F.mapId a ▷ app a ≫ naturality (𝟙 a) =
        (λ_ (app a)).hom ≫ (ρ_ (app a)).inv ≫ app a ◁ G.mapId a := by
    aesop_cat
  /-- Oplax functoriality. -/
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      F.mapComp f g ▷ app c ≫ naturality (f ≫ g) =
        (α_ _ _ _).hom ≫ F.map f ◁ naturality g ≫
          (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫
            app a ◁ G.mapComp f g := by
    aesop_cat

/-- lax -/
structure LaxTrans (F G : LaxFunctor B C) where
  /-- The component 1-morphisms of a lax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the lax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : app a ≫ G.map f ⟶ F.map f ≫ app b
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      naturality f ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ naturality g := by
    aesop_cat
  naturality_id (a : B) :
      app a ◁ G.mapId a ≫ naturality (𝟙 a) =
        (ρ_ (app a)).hom ≫ (λ_ (app a)).inv  ≫ F.mapId a ▷ app a := by
    aesop_cat
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      app a ◁ G.mapComp f g ≫ naturality (f ≫ g) =
        (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫
          (α_ _ _ _).hom ≫  F.map f ◁ naturality g ≫
            (α_ _ _ _).inv ≫ F.mapComp f g ▷ app c := by
    aesop_cat

attribute [reassoc (attr := simp)] LaxTrans.naturality_naturality
  LaxTrans.naturality_id
  LaxTrans.naturality_comp

/-- strong -/
structure StrongTrans (F G : LaxFunctor B C) where
  /-- The component 1-morphisms of an oplax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the oplax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ≅ app a ≫ G.map f
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η := by
    aesop_cat
  naturality_id (a : B) :
      F.mapId a ▷ app a ≫ (naturality (𝟙 a)).hom =
        (λ_ (app a)).hom ≫ (ρ_ (app a)).inv ≫ app a ◁ G.mapId a := by
    aesop_cat
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      F.mapComp f g ▷ app c ≫ (naturality (f ≫ g)).hom =
        (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫
          (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom ≫
            app a ◁ G.mapComp f g := by
    aesop_cat

namespace LaxTrans

variable {F G H : LaxFunctor B C}
variable (η : LaxTrans F G) (θ : LaxTrans G H)

variable (F) in
def id : LaxTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {_ _} f := (λ_ (F.map f)).hom ≫ (ρ_ (F.map f)).inv

instance : Inhabited (LaxTrans F F ) :=
  ⟨id F⟩

-- #string_diagram naturality_naturality

abbrev vCompApp (a : B) : F.obj a ⟶ H.obj a :=
  η.app a ≫ θ.app a

abbrev vCompNaturality {a b : B} (f : a ⟶ b) :
    (η.app a ≫ θ.app a) ≫ H.map f ⟶ F.map f ≫ η.app b ≫ θ.app b :=
  (α_ _ _ _).hom ≫ η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv ≫
    η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom

theorem vComp_naturality_naturality {a b : B} {f g : a ⟶ b} (β : f ⟶ g) :
    η.vCompNaturality θ f ≫ F.map₂ β ▷ η.vCompApp θ b =
      η.vCompApp θ a ◁ H.map₂ β ≫ η.vCompNaturality θ g :=
  calc
    _ = 𝟙 _ ⊗≫ η.app a ◁ θ.naturality f ⊗≫
          (η.naturality f ≫ F.map₂ β ▷ η.app b) ▷ θ.app b ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.naturality f ≫ G.map₂ β ▷ θ.app b) ⊗≫
          η.naturality g ▷ θ.app b ⊗≫ 𝟙 _ := by
      rw [naturality_naturality]
      bicategory
    _ = _ := by
      rw [naturality_naturality]
      bicategory

theorem vComp_naturality_id (a : B) :
    η.vCompApp θ a ◁ H.mapId a ≫ η.vCompNaturality θ (𝟙 a) =
      (ρ_ (η.vCompApp θ a)).hom ≫ (λ_ (η.vCompApp θ a)).inv ≫ F.mapId a ▷ η.vCompApp θ a :=
  calc
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.app a ◁ H.mapId a ≫ θ.naturality (𝟙 a)) ⊗≫
          η.naturality (𝟙 a) ▷ θ.app a ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (η.app a ◁ G.mapId a ≫ η.naturality (𝟙 a)) ▷ θ.app a ⊗≫ 𝟙 _ := by
      rw [naturality_id]
      bicategory
    _ = _ := by
      rw [naturality_id]
      bicategory

theorem vComp_naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    η.vCompApp θ a ◁ H.mapComp f g ≫ η.vCompNaturality θ (f ≫ g) =
      (α_ (η.vCompApp θ a) (H.map f) (H.map g)).inv ≫
        η.vCompNaturality θ f ▷ H.map g ≫
          (α_ (F.map f) (η.vCompApp θ b) (H.map g)).hom ≫
            F.map f ◁ η.vCompNaturality θ g ≫
              (α_ (F.map f) (F.map g) (η.vCompApp θ c)).inv ≫ F.mapComp f g ▷ η.vCompApp θ c :=
  calc
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.app a ◁ H.mapComp f g ≫ θ.naturality (f ≫ g)) ⊗≫
          η.naturality (f ≫ g) ▷ θ.app c ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.naturality f ▷ (H.map g) ⊗≫ G.map f ◁ θ.naturality g) ⊗≫
          (η.app a ◁ G.mapComp f g ≫ η.naturality (f ≫ g)) ▷ θ.app c ⊗≫ 𝟙 _ := by
      rw [naturality_comp θ]
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ θ.naturality f ▷ H.map g ⊗≫
          ((η.app a ≫ G.map f) ◁ θ.naturality g ≫ η.naturality f ▷ (G.map g ≫ θ.app c)) ⊗≫
            F.map f ◁ η.naturality g ▷ θ.app c ⊗≫
              F.mapComp f g ▷ η.app c ▷ θ.app c ⊗≫ 𝟙 _ := by
      rw [naturality_comp η]
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

def vComp (η : LaxTrans F G) (θ : LaxTrans G H) : LaxTrans F H where
  app a := vCompApp η θ a
  naturality := vCompNaturality η θ
  naturality_naturality := vComp_naturality_naturality η θ
  naturality_id := vComp_naturality_id η θ
  naturality_comp := vComp_naturality_comp η θ

@[simps! id_app id_naturality comp_app comp_naturality]
scoped instance : CategoryStruct (LaxFunctor B C) where
  Hom := LaxTrans
  id := LaxTrans.id
  comp := LaxTrans.vComp

end LaxTrans

namespace OplaxTrans

variable {F G H : LaxFunctor B C} (η : OplaxTrans F G) (θ : OplaxTrans G H)

def vCompApp (a : B) : F.obj a ⟶ H.obj a := η.app a ≫ θ.app a

def vComp (η : OplaxTrans F G) (θ : OplaxTrans G H) : OplaxTrans F H where
  app := vCompApp η θ
  naturality := sorry
  naturality_naturality := sorry
  naturality_id := sorry
  naturality_comp := sorry


end OplaxTrans

end Lax
end CategoryTheory
