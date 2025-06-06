import Mathlib.CategoryTheory.Bicategory.Functor.Lax


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

end Lax
end CategoryTheory

#lint
