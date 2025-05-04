/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.Functor.CurryingThree
import Mathlib.Tactic.SuppressCompilation

/-!
# Trifunctors from quotient categories

-/

namespace CategoryTheory.Quotient

variable {C₁ C₂ C₃ C₁₂ C : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₁₂] [Category C]
  (r₁ : HomRel C₁) (r₂ : HomRel C₂) (r₁₂ : HomRel C₁₂) (r₃ : HomRel C₃)
  (r : HomRel C)

-- to be moved
variable {r₁} in
lemma functor_obj_surjective (X : Quotient r₁) :
    ∃ (Y : C₁), (functor r₁).obj Y = X :=
  ⟨X.as, rfl⟩

def natTransLift₃ {F G : Quotient r₁ ⥤ Quotient r₂ ⥤ Quotient r₃ ⥤ C}
    (τ : ((((whiskeringLeft₃ _).obj (functor r₁)).obj (functor r₂)).obj (functor r₃)).obj F ⟶
      ((((whiskeringLeft₃ _).obj (functor r₁)).obj (functor r₂)).obj (functor r₃)).obj G) :
    F ⟶ G where
  app X₁ :=
    { app X₂ :=
        { app X₃ := ((τ.app _).app _).app _
          naturality := by
            rintro _ _ ⟨f₃⟩
            exact ((τ.app X₁.as).app X₂.as).naturality f₃ }
      naturality := by
        rintro _ _ ⟨f₂⟩
        ext ⟨X₃⟩
        exact congr_app ((τ.app X₁.as).naturality f₂) X₃ }
  naturality := by
    rintro _ _ ⟨f₁⟩
    ext ⟨X₂⟩ ⟨X₃⟩
    exact congr_app (congr_app (τ.naturality f₁) X₂) X₃

@[simp]
lemma natTransLift₃_app_app_app
    {F G : Quotient r₁ ⥤ Quotient r₂ ⥤ Quotient r₃ ⥤ C}
    (τ : ((((whiskeringLeft₃ _).obj (functor r₁)).obj (functor r₂)).obj (functor r₃)).obj F ⟶
      ((((whiskeringLeft₃ _).obj (functor r₁)).obj (functor r₂)).obj (functor r₃)).obj G)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((natTransLift₃ r₁ r₂ r₃ τ).app ((functor r₁).obj X₁)).app ((functor r₂).obj X₂)).app
      ((functor r₃).obj X₃) = ((τ.app X₁).app X₂).app X₃ := rfl

def natIsoLift₃ {F G : Quotient r₁ ⥤ Quotient r₂ ⥤ Quotient r₃ ⥤ C}
    (τ : ((((whiskeringLeft₃ _).obj (functor r₁)).obj (functor r₂)).obj (functor r₃)).obj F ≅
      ((((whiskeringLeft₃ _).obj (functor r₁)).obj (functor r₂)).obj (functor r₃)).obj G) :
    F ≅ G where
  hom := natTransLift₃ _ _ _ τ.hom
  inv := natTransLift₃ _ _ _ τ.inv
  hom_inv_id := by
    ext X₁ X₂ X₃
    obtain ⟨X₁, rfl⟩ := X₁.functor_obj_surjective
    obtain ⟨X₂, rfl⟩ := X₂.functor_obj_surjective
    obtain ⟨X₃, rfl⟩ := X₃.functor_obj_surjective
    simp
  inv_hom_id := by
    ext X₁ X₂ X₃
    obtain ⟨X₁, rfl⟩ := X₁.functor_obj_surjective
    obtain ⟨X₂, rfl⟩ := X₂.functor_obj_surjective
    obtain ⟨X₃, rfl⟩ := X₃.functor_obj_surjective
    simp

variable {r₁ r₂ r₁₂ r₃ r} {F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂} {G : C₁₂ ⥤ C₃ ⥤ C}
  {F₁₂' : Quotient r₁ ⥤ Quotient r₂ ⥤ Quotient r₁₂}
  {G' : Quotient r₁₂ ⥤ Quotient r₃ ⥤ Quotient r}
  (eF : (((whiskeringLeft₂ _).obj (functor r₁)).obj (functor r₂)).obj F₁₂' ≅
      F₁₂ ⋙ (whiskeringRight _ _ _).obj (functor r₁₂))
  (eG : (((whiskeringLeft₂ _).obj (functor r₁₂)).obj (functor r₃)).obj G' ≅
      G ⋙ (whiskeringRight _ _ _).obj (functor r))

set_option maxHeartbeats 400000 in
-- this is slow
suppress_compilation in
@[simps!]
def bifunctorComp₁₂Iso :
    ((((whiskeringLeft₃ _).obj (functor r₁)).obj (functor r₂)).obj (functor r₃)).obj
      (bifunctorComp₁₂ F₁₂' G') ≅
        ((Functor.postcompose₃).obj (functor r)).obj (bifunctorComp₁₂ F₁₂ G) :=
  NatIso.ofComponents
    (fun X₁ ↦ NatIso.ofComponents
      (fun X₂ ↦ NatIso.ofComponents
        (fun X₃ ↦ (G'.mapIso ((eF.app X₁).app X₂)).app ((functor r₃).obj X₃) ≪≫
          (eG.app ((F₁₂.obj X₁).obj X₂)).app X₃)
        (fun {X₃ Y₃} f₃ ↦ by
          have := (eG.hom.app ((F₁₂.obj X₁).obj X₂)).naturality f₃
          dsimp at this ⊢
          simp only [NatTrans.naturality_assoc, Category.assoc, this]))
      (fun {X₂ Y₂} f₂ ↦ by
        ext X₃
        have h₁ := congr_app (G'.congr_map ((eF.hom.app X₁).naturality f₂)) ((functor r₃).obj X₃)
        have h₂ := congr_app (eG.hom.naturality ((F₁₂.obj X₁).map f₂)) X₃
        simp only [Functor.map_comp] at h₁
        dsimp at h₁ h₂ ⊢
        simp only [Category.assoc, reassoc_of% h₁, h₂]))
    (fun {X₁ Y₁} f₁ ↦ by
      ext X₂ X₃
      dsimp
      have h₂ := congr_app (G'.congr_map (congr_app (eF.hom.naturality f₁) X₂))
        ((functor r₃).obj X₃)
      have h₁ := congr_app (eG.hom.naturality ((F₁₂.map f₁).app X₂)) X₃
      dsimp at h₁ h₂ ⊢
      simp only [Functor.map_comp, NatTrans.comp_app] at h₂
      simp only [Category.assoc, ← h₁, reassoc_of% h₂])

end CategoryTheory.Quotient
