import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.GaloisCategories.Basic

universe u v w

open CategoryTheory Limits Functor

lemma colimMapIdentity {J C : Type*} [Category C] [Category J] (F : J ⥤ C) [HasColimit F]
    : colimMap (𝟙 F) = 𝟙 (colimit F) := by
  aesop

namespace Galois

variable {C : Type u} [Category.{u, u} C] {F : C ⥤ FintypeCat.{u}} [PreGaloisCategory C] [FibreFunctor F]

def ConnectedObjects := { A : C | ConnectedObject A }

def Idx : Type (max u u) := (A : @ConnectedObjects C _) × F.obj (A : C)

instance : Category (@Idx C _ F) where
  Hom := by
    intro ⟨A, a⟩ ⟨B, b⟩
    exact { f : (A : C) ⟶ B // F.map f a = b }
  id := by
    intro ⟨A, a⟩
    exact ⟨𝟙 (A : C), by simp⟩
  comp := by
    intro ⟨A, a⟩ ⟨B, b⟩ ⟨C, c⟩ ⟨f, hf⟩ ⟨g, hg⟩
    have h : F.map (f ≫ g) a = c := by
      simp only [map_comp, FintypeCat.comp_apply, hf, hg]
    exact ⟨f ≫ g, h⟩

def diag (X : C) : (@Idx C _ F)ᵒᵖ ⥤ Type u where
  obj := by
    intro ⟨A, _⟩
    exact (A : C) ⟶ X
  map := by
    intro ⟨A, _⟩ ⟨B, _⟩ ⟨f, _⟩ (g : (A : C) ⟶ X)
    exact f ≫ g
  map_id := by
    intro ⟨A, _⟩
    ext (g : (A : C) ⟶ X)
    show 𝟙 (A : C) ≫ g = g
    simp only [Category.id_comp]
  map_comp := by
    intro ⟨A, _⟩ ⟨B, _⟩ ⟨D, _⟩ ⟨f, _⟩ ⟨g, _⟩
    ext (h : (A : C) ⟶ X)
    show (g ≫ f) ≫ h = g ≫ (f ≫ h)
    simp only [Category.assoc]

--instance (X : C) : HasColimit (@diag C _ F X) := inferInstance

def bli (X : C) : Cocone (@diag C _ F X) where
  pt := FintypeCat.incl.obj <| F.obj X
  ι := {
    app := by
      intro ⟨A, a⟩
      show ((A : C) ⟶ X) → F.obj X
      intro f
      exact F.map f a
    naturality := by
      intro ⟨A, a⟩ ⟨B, b⟩ ⟨f, hf⟩
      ext (g : (A : C) ⟶ X)
      show F.map (f ≫ g) b = F.map g a
      simp only [map_comp, FintypeCat.comp_apply, hf]
  }

def diagTrans {X Y : C} (f : X ⟶ Y) : @diag C _ F X ⟶ @diag C _ F Y where
  app := by
    intro ⟨A, a⟩
    intro g
    exact g ≫ f
  naturality := by
    intro ⟨A, a⟩ ⟨B, b⟩ ⟨u, hu⟩
    ext (g : (A : C) ⟶ X)
    show (u ≫ g) ≫ f = u ≫ (g ≫ f)
    simp only [Category.assoc]

noncomputable def blabla : C ⥤ Type u where
  obj X := colimit (@diag C _ F X)
  map {X Y} f := by
    show colimit (@diag C _ F X) → colimit (@diag C _ F Y)
    exact colim.map (diagTrans f)
  map_id := by
    intro X
    simp
    have h1 : diagTrans (𝟙 X) = 𝟙 (@diag C _ F X) := sorry
    rw [h1]
    exact colimMapIdentity (diag X)

noncomputable def bla (X : C) : colimit (@diag C _ F X) ⟶ (FintypeCat.incl.obj <| F.obj X) :=
  colimit.desc (@diag C _ F X) (bli X)
