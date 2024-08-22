import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

universe v v' v'' u u' u''

namespace CategoryTheory

open Category Limits Opposite

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Functor

namespace end_

@[simps]
def multicospanIndex (F : Cᵒᵖ ⥤ C ⥤ D) : MulticospanIndex D where
  L := ULift C
  R := Arrow C
  fstTo f := ULift.up f.left
  sndTo f := ULift.up f.right
  left := fun ⟨X⟩ ↦ (F.obj (op X)).obj X
  right f := (F.obj (op f.left)).obj f.right
  fst f := (F.obj _).map f.hom
  snd f := (F.map f.hom.op).app f.right

end end_

section

variable (F : Cᵒᵖ ⥤ C ⥤ D)

abbrev HasEnd := HasMultiequalizer (end_.multicospanIndex F)

variable [F.HasEnd]

noncomputable def end_ : D := multiequalizer (end_.multicospanIndex F)

namespace end_

noncomputable def π (X : C) : F.end_ ⟶ (F.obj (op X)).obj X :=
  Multiequalizer.ι (end_.multicospanIndex F) ⟨X⟩

@[reassoc]
lemma condition {X Y : C} (f : X ⟶ Y) :
    π F X ≫ (F.obj (op X)).map f = π F Y ≫ (F.map f.op).app Y :=
  Multiequalizer.condition (end_.multicospanIndex F) (Arrow.mk f)

variable {F} in
lemma hom_ext {Z : D} {φ φ' : Z ⟶ F.end_} (h : ∀ (X : C), φ ≫ π F X = φ' ≫ π F X) :
    φ = φ' :=
  Multiequalizer.hom_ext _ _ _ (fun ⟨X⟩ ↦ h X)

section

variable {Z : D} (φ : ∀ (X : C), Z ⟶ (F.obj (op X)).obj X)
  (hφ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), φ X ≫ (F.obj (op X)).map f = φ Y ≫ (F.map f.op).app Y)

noncomputable def lift : Z ⟶ F.end_ :=
  Multiequalizer.lift _ _ (fun ⟨X⟩ ↦ φ X) (fun f ↦ hφ f.hom)

@[reassoc (attr := simp)]
lemma lift_π (X : C) : lift F φ hφ ≫ π F X = φ X := by simp [lift, π]

end

end end_

end

end Functor

open MonoidalCategory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [MonoidalCategory D] [MonoidalClosed D]

section

lemma MonoidalClosed.curry_natural_right'
    {X Y Z T : D} (f : X ⟶ Y) (g : Y ⊗ Z ⟶ T) :
    curry (f ▷ Z ≫ g) = curry g ≫ (pre f).app T := by
  obtain ⟨h, rfl⟩ : ∃ h, g = uncurry h := ⟨curry g, by simp⟩
  apply uncurry_injective
  rw [uncurry_curry, curry_uncurry, uncurry_natural_left, uncurry_pre,
    whisker_exchange_assoc, uncurry_eq]

def ihom.id (X : D) : 𝟙_ D ⟶ (ihom X).obj X :=
  MonoidalClosed.curry (ρ_ _).hom

def ihom.comp (X Y Z : D) : (ihom X).obj Y ⊗ (ihom Y).obj Z ⟶ (ihom X).obj Z :=
  MonoidalClosed.curry ((α_ _ _ _).inv ≫ (ihom.ev _).app _ ▷ _ ≫ (ihom.ev _).app _)

@[reassoc]
lemma ihom.id_pre_app {X Y : D} (f : X ⟶ Y) :
    ihom.id Y ≫ (MonoidalClosed.pre f).app Y =
      ihom.id X ≫ (ihom _).map f := by
  dsimp [id]
  rw [← MonoidalClosed.curry_natural_right, ← MonoidalCategory.rightUnitor_naturality,
    ← MonoidalClosed.curry_natural_right']

-- is it what it actually needed?
@[reassoc]
lemma ihom.map_tensor_comp_pre_app {X₁ X₂ X₃ Y₁ Y₂ Y₃ : D}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((ihom Y₁).map f₂ ⊗ (ihom Y₂).map f₃) ≫
    ihom.comp Y₁ Y₂ Y₃ ≫ (MonoidalClosed.pre f₁).app Y₃ =
      ((MonoidalClosed.pre f₁).app X₂ ⊗ (MonoidalClosed.pre f₂).app X₃) ≫
        ihom.comp X₁ X₂ X₃ ≫ (ihom X₁).map f₃ :=
  sorry

end

namespace Functor

section

variable (F G : C ⥤ D)

abbrev HasEnrichedHom := (F.op ⋙ ((whiskeringRight Dᵒᵖ _ _).obj
      ((whiskeringLeft C D D).obj G)).obj MonoidalClosed.internalHom).HasEnd

noncomputable def enrichedHom [HasEnrichedHom F G] : D :=
  (F.op ⋙ ((whiskeringRight Dᵒᵖ _ _).obj
      ((whiskeringLeft C D D).obj G)).obj MonoidalClosed.internalHom).end_

end

namespace enrichedHom

section

variable (F G : C ⥤ D) [HasEnrichedHom F G]

noncomputable abbrev app (X : C) : enrichedHom F G ⟶ (ihom (F.obj X)).obj (G.obj X) :=
  end_.π (F.op ⋙ ((whiskeringRight Dᵒᵖ _ _).obj
      ((whiskeringLeft C D D).obj G)).obj MonoidalClosed.internalHom) X

@[reassoc]
lemma naturality {X Y : C} (f : X ⟶ Y) :
    app F G Y ≫ (MonoidalClosed.pre (F.map f)).app (G.obj Y) =
      app F G X ≫ (ihom (F.obj X)).map (G.map f) :=
  (end_.condition (F.op ⋙ ((whiskeringRight Dᵒᵖ _ _).obj
      ((whiskeringLeft C D D).obj G)).obj MonoidalClosed.internalHom) f).symm

variable {F G} in
@[ext]
lemma hom_ext {Z : D} {φ φ' : Z ⟶ enrichedHom F G}
    (h : ∀ (X : C), φ ≫ app _ _ X = φ' ≫ app _ _ X) : φ = φ' :=
  end_.hom_ext h

end

noncomputable def id (F : C ⥤ D) [HasEnrichedHom F F] : 𝟙_ D ⟶ enrichedHom F F :=
  end_.lift _ (fun X ↦ ihom.id (F.obj X))
    (by intros; dsimp; rw [ihom.id_pre_app])

section

variable (F G H : C ⥤ D) [HasEnrichedHom F G] [HasEnrichedHom G H] [HasEnrichedHom F H]

noncomputable def comp  :
    F.enrichedHom G ⊗ G.enrichedHom H ⟶ F.enrichedHom H :=
  end_.lift _ (fun X ↦ (app F G X ⊗ app G H X) ≫ ihom.comp _ _ _) sorry

@[reassoc (attr := simp)]
lemma comp_π (X : C) : comp F G H ≫ app F H X = (app F G X ⊗ app G H X) ≫ ihom.comp _ _ _ := by
  simp [comp, app]

end

@[reassoc (attr := simp)]
lemma id_comp (F G : C ⥤ D) [HasEnrichedHom F G] [HasEnrichedHom F F] :
    (λ_ _).inv ≫ enrichedHom.id F ▷ _ ≫ enrichedHom.comp F F G = 𝟙 (F.enrichedHom G) := by
  ext X
  simp
  sorry

@[reassoc (attr := simp)]
lemma comp_id (F G : C ⥤ D) [HasEnrichedHom F G] [HasEnrichedHom G G] :
    (ρ_ _).inv ≫ _ ◁ enrichedHom.id G ≫ enrichedHom.comp F G G = 𝟙 (F.enrichedHom G) := by
  sorry

@[reassoc (attr := simp)]
lemma assoc (F₁ F₂ F₃ F₄ : C ⥤ D)
    [HasEnrichedHom F₁ F₂] [HasEnrichedHom F₂ F₃] [HasEnrichedHom F₃ F₄] [HasEnrichedHom F₁ F₃]
    [HasEnrichedHom F₁ F₄] [HasEnrichedHom F₂ F₄] :
    (α_ (F₁.enrichedHom F₂) (F₂.enrichedHom F₃) (F₃.enrichedHom F₄)).inv ≫
    enrichedHom.comp F₁ F₂ F₃ ▷ F₃.enrichedHom F₄ ≫ enrichedHom.comp F₁ F₃ F₄ =
  F₁.enrichedHom F₂ ◁ enrichedHom.comp F₂ F₃ F₄ ≫ enrichedHom.comp F₁ F₂ F₄ := sorry

end enrichedHom

variable [∀ (F G : C ⥤ D), HasEnrichedHom F G]

noncomputable instance : EnrichedCategory D (C ⥤ D) where
  Hom F G := enrichedHom F G
  id F := enrichedHom.id F
  comp F G H := enrichedHom.comp F G H

end Functor

end CategoryTheory
