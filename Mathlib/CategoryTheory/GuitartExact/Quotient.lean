/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder
public import Mathlib.CategoryTheory.GuitartExact.Opposite

/-!
# Guitart exact squares and quotient categories

-/

@[expose] public section

namespace CategoryTheory.TwoSquare.GuitartExact

open HomotopicalAlgebra Opposite

variable {C₀ C H₀ H : Type*} [Category C₀] [Category C] [Category H₀] [Category H]
  {T : C₀ ⥤ H₀} {L : C₀ ⥤ C} {R : H₀ ⥤ H} {B : C ⥤ H}
  [T.EssSurj] [T.Full] [B.Full]

lemma quotient_of_exists_leftHomotopy (e : T ⋙ R ≅ L ⋙ B)
    (h : ∀ ⦃X₀ : C₀⦄ ⦃Y : C⦄ (f₀ f₁ : L.obj X₀ ⟶ Y) (_ : B.map f₀ = B.map f₁),
      ∃ (P : Precylinder X₀), T.map P.i₀ = T.map P.i₁ ∧
        0 = by
          sorry) :
    GuitartExact e.hom := by
  /- (h : ∀ ⦃X₀ : C₀⦄ ⦃Y : C⦄ (f₀ f₁ : L.obj X₀ ⟶ Y) (_ : B.map f₀ = B.map f₁),
      ∃ (Cyl : C₀) (i₀ i₁ : X₀ ⟶ Cyl) (_ : T.map i₀ = T.map i₁)
          (φ : L.obj Cyl ⟶ Y), L.map i₀ ≫ φ = f₀ ∧
        L.map i₁ ≫ φ = f₁) : GuitartExact e.hom := by-/
  sorry

end CategoryTheory.TwoSquare.GuitartExact
