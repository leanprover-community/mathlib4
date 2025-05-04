/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Quotient

/-!
# Trifunctors from quotient categories

-/

namespace CategoryTheory.Quotient

variable {C₁ C₂ C₃ D : Type*} [Category C₁] [Category C₂] [Category C₃] [Category D]
  (r₁ : HomRel C₁) (r₂ : HomRel C₂) (r₃ : HomRel C₃)

-- to be moved
variable {r₁} in
lemma functor_obj_surjective (X : Quotient r₁) :
    ∃ (Y : C₁), (functor r₁).obj Y = X :=
  ⟨X.as, rfl⟩

def natTransLift₃ {F G : Quotient r₁ ⥤ Quotient r₂ ⥤ Quotient r₃ ⥤ D}
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
    {F G : Quotient r₁ ⥤ Quotient r₂ ⥤ Quotient r₃ ⥤ D}
    (τ : ((((whiskeringLeft₃ _).obj (functor r₁)).obj (functor r₂)).obj (functor r₃)).obj F ⟶
      ((((whiskeringLeft₃ _).obj (functor r₁)).obj (functor r₂)).obj (functor r₃)).obj G)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((natTransLift₃ r₁ r₂ r₃ τ).app ((functor r₁).obj X₁)).app ((functor r₂).obj X₂)).app
      ((functor r₃).obj X₃) = ((τ.app X₁).app X₂).app X₃ := rfl

def natIsoLift₃ {F G : Quotient r₁ ⥤ Quotient r₂ ⥤ Quotient r₃ ⥤ D}
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

end CategoryTheory.Quotient
