/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Quotient

/-!
# Bifunctors from quotient categories

-/

namespace CategoryTheory.Quotient

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  (r₁ : HomRel C₁) (r₂ : HomRel C₂)

def lift₂ (F : C₁ ⥤ C₂ ⥤ D)
    (h₁ : ∀ ⦃X₁ Y₁ : C₁⦄ (f₁ f₁' : X₁ ⟶ Y₁) (_ : r₁ f₁ f₁') (X₂ : C₂),
      (F.map f₁).app X₂ = (F.map f₁').app X₂)
    (h₂ : ∀ (X₁ : C₁) ⦃X₂ Y₂ : C₂⦄ (f₂ f₂' : X₂ ⟶ Y₂) (_ : r₂ f₂ f₂'),
      (F.obj X₁).map f₂ = (F.obj X₁).map f₂') :
    Quotient r₁ ⥤ Quotient r₂ ⥤ D :=
  lift r₁
    { obj X₁ := lift r₂ (F.obj X₁) (by aesop)
      map {X₁ Y₁} f₁ := natTransLift _ (F.map f₁) }
    (by aesop)

end CategoryTheory.Quotient
