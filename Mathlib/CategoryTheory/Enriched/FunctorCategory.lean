import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

universe v v' v'' u u' u''

namespace CategoryTheory

open Limits MonoidalCategory

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

@[simps]
def enrichedHom.multicospanIndex : MulticospanIndex D where
  L := ULift C
  R := Arrow C
  fstTo f := ULift.up f.left
  sndTo f := ULift.up f.right
  left := fun ⟨X⟩ ↦ (ihom (F.obj X)).obj (G.obj X)
  right f := (ihom (F.obj f.left)).obj (G.obj f.right)
  fst f := (ihom _).map (G.map f.hom)
  snd f := (MonoidalClosed.pre (F.map f.hom)).app (G.obj f.right)

abbrev HasEnrichedHom := HasMultiequalizer (enrichedHom.multicospanIndex F G)

noncomputable def enrichedHom [HasEnrichedHom F G] : D :=
  multiequalizer (enrichedHom.multicospanIndex F G)

end

namespace enrichedHom

section

variable (F G : C ⥤ D) [HasEnrichedHom F G] (X : C)

noncomputable abbrev app : enrichedHom F G ⟶ (ihom (F.obj X)).obj (G.obj X) :=
  Multiequalizer.ι (enrichedHom.multicospanIndex F G) (ULift.up X)

end

noncomputable def id (F : C ⥤ D) [HasEnrichedHom F F] : 𝟙_ D ⟶ enrichedHom F F :=
    Multiequalizer.lift _ _ (fun ⟨X⟩ ↦ ihom.id _)
      (fun _ ↦ by dsimp; rw [ihom.id_pre_app])

noncomputable def comp (F G H : C ⥤ D)
    [HasEnrichedHom F G] [HasEnrichedHom G H] [HasEnrichedHom F H] :
    F.enrichedHom G ⊗ G.enrichedHom H ⟶ F.enrichedHom H :=
  Multiequalizer.lift _ _ (fun ⟨X⟩ ↦ (app F G X ⊗ app G H X) ≫ ihom.comp _ _ _)
    (fun a ↦ by
      dsimp
      simp only [Category.assoc]
      have := ihom.map_tensor_comp_pre_app (F.map a.hom)
        (G.map a.hom) (H.map a.hom)
      dsimp at this
      dsimp [app]
      sorry)

@[reassoc (attr := simp)]
lemma id_comp (F G : C ⥤ D) [HasEnrichedHom F G] [HasEnrichedHom F F] :
    (λ_ _).inv ≫ enrichedHom.id F ▷ _ ≫ enrichedHom.comp F F G = 𝟙 (F.enrichedHom G) := by
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
