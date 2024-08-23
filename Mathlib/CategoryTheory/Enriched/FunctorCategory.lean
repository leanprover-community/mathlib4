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

lemma ihom.comp_naturality₁ {X₁ Y₁ : D} (f₁ : X₁ ⟶ Y₁) (X₂ X₃ : D) :
    (MonoidalClosed.pre f₁).app X₂ ▷ _ ≫ ihom.comp X₁ X₂ X₃ =
    ihom.comp Y₁ X₂ X₃ ≫ (MonoidalClosed.pre f₁).app X₃ := by
  dsimp [comp]
  rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_right',
    associator_inv_naturality_left_assoc, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
    MonoidalClosed.id_tensor_pre_app_comp_ev]

@[reassoc]
lemma ihom.comp_naturality₂ (X₁ : D) {X₂ Y₂ : D} (f₂ : X₂ ⟶ Y₂) (X₃ : D) :
    _ ◁ (MonoidalClosed.pre f₂).app X₃ ≫ ihom.comp X₁ X₂ X₃ =
      (ihom X₁).map f₂ ▷ _ ≫ ihom.comp X₁ Y₂ X₃ := sorry

@[reassoc]
lemma ihom.comp_naturality₃ (X₁ X₂ : D) {X₃ Y₃ : D} (f₃ : X₃ ⟶ Y₃) :
    (_ ◁ (ihom X₂).map f₃) ≫ ihom.comp X₁ X₂ Y₃ =
      ihom.comp X₁ X₂ X₃ ≫ (ihom X₁).map f₃ := sorry

@[reassoc (attr := simp)]
protected lemma ihom.id_comp (X₁ X₂ : D) :
    ihom.id X₁ ▷ _ ≫ ihom.comp X₁ X₁ X₂ = (λ_ _).hom := by
  dsimp [id, comp]
  sorry

@[reassoc (attr := simp)]
protected lemma ihom.comp_id (X₁ X₂ : D) :
    _ ◁ ihom.id X₂ ≫ ihom.comp X₁ X₂ X₂ = (ρ_ _).hom := by
  dsimp [id, comp]
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

section

variable (F : C ⥤ D) [HasEnrichedHom F F]

noncomputable def id : 𝟙_ D ⟶ enrichedHom F F :=
  end_.lift _ (fun X ↦ ihom.id (F.obj X))
    (by intros; dsimp; rw [ihom.id_pre_app])

@[reassoc (attr := simp)]
lemma id_app (X : C) : id F ≫ app F F X = ihom.id (F.obj X) := by
  simp [id, app]

end

section

variable (F G H : C ⥤ D) [HasEnrichedHom F G] [HasEnrichedHom G H] [HasEnrichedHom F H]

noncomputable def comp  :
    F.enrichedHom G ⊗ G.enrichedHom H ⟶ F.enrichedHom H :=
  end_.lift _ (fun X ↦ (app F G X ⊗ app G H X) ≫ ihom.comp _ _ _) (fun X Y f ↦ by
    dsimp
    conv_lhs => rw [assoc,  ← ihom.comp_naturality₃,
      tensorHom_def_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← naturality, MonoidalCategory.whiskerLeft_comp_assoc, ← tensorHom_def_assoc,
      ihom.comp_naturality₂]
    conv_rhs => rw [assoc, tensorHom_def_assoc, ← ihom.comp_naturality₁,
      ← whisker_exchange_assoc, ← comp_whiskerRight_assoc,
      naturality, comp_whiskerRight_assoc, whisker_exchange_assoc, ← tensorHom_def_assoc])

@[reassoc (attr := simp)]
lemma comp_app (X : C) : comp F G H ≫ app F H X = (app F G X ⊗ app G H X) ≫ ihom.comp _ _ _ := by
  simp [comp, app]

end

@[reassoc (attr := simp)]
protected lemma id_comp (F G : C ⥤ D) [HasEnrichedHom F G] [HasEnrichedHom F F] :
    (λ_ _).inv ≫ enrichedHom.id F ▷ _ ≫ enrichedHom.comp F F G = 𝟙 (F.enrichedHom G) := by
  ext X
  rw [assoc, assoc, comp_app, id_comp, tensorHom_def_assoc,
    ← comp_whiskerRight_assoc, id_app, ← whisker_exchange_assoc,
    ← leftUnitor_inv_naturality_assoc, ihom.id_comp, Iso.inv_hom_id, comp_id]

@[reassoc (attr := simp)]
protected lemma comp_id (F G : C ⥤ D) [HasEnrichedHom F G] [HasEnrichedHom G G] :
    (ρ_ _).inv ≫ _ ◁ enrichedHom.id G ≫ enrichedHom.comp F G G = 𝟙 (F.enrichedHom G) := by
  ext X
  rw [assoc, assoc, comp_app, id_comp, tensorHom_def_assoc, ← whisker_exchange_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, id_app, whisker_exchange_assoc,
    ← rightUnitor_inv_naturality_assoc, ihom.comp_id, Iso.inv_hom_id, comp_id]

@[reassoc (attr := simp)]
protected lemma assoc (F₁ F₂ F₃ F₄ : C ⥤ D)
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
