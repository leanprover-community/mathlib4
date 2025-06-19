/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Cylinder
import Mathlib.CategoryTheory.Quotient

/-!
# Homotopies in model categories

-/

open CategoryTheory

namespace HomotopicalAlgebra

variable {C : Type*} [Category C] [ModelCategory C]

namespace Cylinder

variable {X : C} (P : Cylinder X) {Y : C}

structure LeftHomotopy (f g : X ⟶ Y) where
  h : P.I ⟶ Y
  h₀ : P.i₀ ≫ h = f := by aesop_cat
  h₁ : P.i₁ ≫ h = g := by aesop_cat

namespace LeftHomotopy

attribute [reassoc (attr := simp)] h₀ h₁

variable {P}

@[simps]
def refl (f : X ⟶ Y) : P.LeftHomotopy f f where
  h := P.σ ≫ f

@[simps]
def postcomp {f g : X ⟶ Y} (h : P.LeftHomotopy f g) {Z : C} (p : Y ⟶ Z) :
    P.LeftHomotopy (f ≫ p) (g ≫ p) where
  h := h.h ≫ p

end LeftHomotopy

end Cylinder

def LeftHomotopyRel : HomRel C :=
  fun X _ f g ↦ ∃ (P : Cylinder X), Nonempty (P.LeftHomotopy f g)

namespace LeftHomotopyRel

variable {X Y : C}

lemma refl (f : X ⟶ Y) : LeftHomotopyRel f f :=
  ⟨Classical.arbitrary _, ⟨.refl _⟩⟩

lemma postcomp {f g : X ⟶ Y} (h : LeftHomotopyRel f g) {Z : C} (p : Y ⟶ Z) :
    LeftHomotopyRel (f ≫ p) (g ≫ p) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact ⟨P, ⟨h.postcomp p⟩⟩

end LeftHomotopyRel

end HomotopicalAlgebra
