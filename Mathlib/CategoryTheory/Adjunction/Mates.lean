/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Emily Riehl
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Whiskering

import Mathlib.Tactic.ApplyFun

#align_import category_theory.adjunction.mates from "leanprover-community/mathlib"@"cea27692b3fdeb328a2ddba6aabf181754543184"

/-!
# Mate of natural transformations

This file establishes the bijection between the 2-cells

         L₁                  R₁
      C --→ D             C ←-- D
    G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
      E --→ F             E ←-- F
         L₂                  R₂

where `L₁ ⊣ R₁` and `L₂ ⊣ R₂`. The corresponding natural transformations are called mates.

This bijection includes a number of interesting cases as specializations. For instance, in the
special case where `G,H` are identity functors then the bijection preserves and reflects
isomorphisms (i.e. we have bijections`(L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂)`, and if either side is an iso then the
other side is as well). This demonstrates that adjoints to a given functor are unique up to
isomorphism (since if `L₁ ≅ L₂` then we deduce `R₁ ≅ R₂`).

Another example arises from considering the square representing that a functor `H` preserves
products, in particular the morphism `HA ⨯ H- ⟶ H(A ⨯ -)`. Then provided `(A ⨯ -)` and `HA ⨯ -`
have left adjoints (for instance if the relevant categories are cartesian closed), the transferred
natural transformation is the exponential comparison morphism: `H(A ^ -) ⟶ HA ^ H-`.
Furthermore if `H` has a left adjoint `L`, this morphism is an isomorphism iff its mate
`L(HA ⨯ -) ⟶ A ⨯ L-` is an isomorphism, see
https://ncatlab.org/nlab/show/Frobenius+reciprocity#InCategoryTheory.
This also relates to Grothendieck's yoga of six operations, though this is not spelled out in
mathlib: https://ncatlab.org/nlab/show/six+operations.
-/

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉
namespace CategoryTheory

open Category Functor Adjunction NatTrans

section Mates

variable {C : Type u₁} {D : Type u₂}{E : Type u₃} {F : Type u₄}
variable [Category.{v₁} C] [Category.{v₂} D][Category.{v₃} E] [Category.{v₄} F]
variable {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- Suppose we have a square of functors (where the top and
bottom are adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` respectively).

      C ↔ D
    G ↓   ↓ H
      E ↔ F

Then we have a bijection between natural transformations `G ⋙ L₂ ⟶ L₁ ⋙ H` and
`R₁ ⋙ G ⟶ H ⋙ R₂`. This can be seen as a bijection of the 2-cells:

         L₁                  R₁
      C --→ D             C ←-- D
    G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
      E --→ F             E ←-- F
         L₂                  R₂

Note that if one of the transformations is an iso, it does not imply the other is an iso.
-/

-- ER: The original definition of the mates equivalence.
def transferNatTrans : (G ⋙ L₂ ⟶ L₁ ⋙ H) ≃ (R₁ ⋙ G ⟶ H ⋙ R₂) where
  toFun h :=
    { app := fun X => adj₂.unit.app _ ≫ R₂.map (h.app _ ≫ H.map (adj₁.counit.app _))
      naturality := fun X Y f => by
        dsimp
        rw [assoc, ← R₂.map_comp, assoc, ← H.map_comp, ← adj₁.counit_naturality, H.map_comp, ←
          Functor.comp_map L₁, ← h.naturality_assoc]
        simp }
  invFun h :=
    { app := fun X => L₂.map (G.map (adj₁.unit.app _) ≫ h.app _) ≫ adj₂.counit.app _
      naturality := fun X Y f => by
        dsimp
        rw [← L₂.map_comp_assoc, ← G.map_comp_assoc, ← adj₁.unit_naturality, G.map_comp_assoc, ←
          Functor.comp_map, h.naturality]
        simp }
  left_inv h := by
    ext X
    dsimp
    simp only [L₂.map_comp, assoc, adj₂.counit_naturality, adj₂.left_triangle_components_assoc, ←
      Functor.comp_map G L₂, h.naturality_assoc, Functor.comp_map L₁, ← H.map_comp,
      adj₁.left_triangle_components]
    dsimp
    simp only [id_comp, ← Functor.comp_map, ← Functor.comp_obj, NatTrans.naturality_assoc]
    simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp]
    have : Prefunctor.map L₁.toPrefunctor (NatTrans.app adj₁.unit X) ≫
        NatTrans.app adj₁.counit (Prefunctor.obj L₁.toPrefunctor X) = 𝟙 _ := by simp
    simp [this]
  -- See library note [dsimp, simp].
  right_inv h := by
    ext X
    dsimp
    simp [-Functor.comp_map, ← Functor.comp_map H, Functor.comp_map R₁, -NatTrans.naturality, ←
      h.naturality, -Functor.map_comp, ← Functor.map_comp_assoc G, R₂.map_comp]
#align category_theory.transfer_nat_trans CategoryTheory.transferNatTrans

/-- Corresponding natural transformations under the equivalence below are called mates.-/
@[simps]
def Mates :
    (G ⋙ L₂ ⟶ L₁ ⋙ H) ≃ (R₁ ⋙ G ⟶ H ⋙ R₂) where
      toFun := fun α ↦
        whiskerLeft (R₁ ⋙ G) adj₂.unit ≫
        whiskerRight (whiskerLeft R₁ α) R₂ ≫
        whiskerRight adj₁.counit (H ⋙ R₂)
      invFun := fun β ↦
        whiskerRight adj₁.unit (G ⋙ L₂) ≫
        whiskerRight (whiskerLeft L₁ β) L₂ ≫
        whiskerLeft (L₁ ⋙ H) adj₂.counit
      left_inv := by
        intro α
        ext
        unfold whiskerRight whiskerLeft
        simp only [comp_obj, id_obj, Functor.comp_map, comp_app, map_comp, assoc, counit_naturality,
          counit_naturality_assoc, left_triangle_components_assoc]
        rw [← assoc, ← Functor.comp_map, α.naturality, Functor.comp_map, assoc, ← H.map_comp,
          left_triangle_components, map_id]
        simp only [comp_obj, comp_id]
      right_inv := by
        intro β
        ext
        unfold whiskerLeft whiskerRight
        simp only [comp_obj, id_obj, Functor.comp_map, comp_app, map_comp, assoc,
          unit_naturality_assoc, right_triangle_components_assoc]
        rw [← assoc, ← Functor.comp_map, assoc, ← β.naturality, ← assoc, Functor.comp_map,
          ← G.map_comp, right_triangle_components, map_id, id_comp]
#align category_theory.mates CategoryTheory.Mates

-- ER: Note these definitions agree.
theorem RightMateEqualsTransferNatTrans
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) :
    Mates adj₁ adj₂ α = (transferNatTrans adj₁ adj₂) α := by
  ext; unfold Mates transferNatTrans; simp

-- ER: Note these definitions agree.
theorem LeftMateEqualsTransferNatTrans.symm
    (α : R₁ ⋙ G ⟶ H ⋙ R₂) :
    (Mates adj₁ adj₂).symm α = (transferNatTrans adj₁ adj₂).symm α := by
  ext; unfold Mates transferNatTrans; simp

-- ER: Propose to cut and replace with the version below:
theorem transferNatTrans_counit (f : G ⋙ L₂ ⟶ L₁ ⋙ H) (Y : D) :
    L₂.map ((transferNatTrans adj₁ adj₂ f).app _) ≫ adj₂.counit.app _ =
      f.app _ ≫ H.map (adj₁.counit.app Y) := by
  erw [Functor.map_comp]
  simp

/-- A component of a transposed version of the mates correspondence. -/
theorem Mates_counit (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (d : D) :
    L₂.map ((Mates adj₁ adj₂ α).app _) ≫ adj₂.counit.app _ =
      α.app _ ≫ H.map (adj₁.counit.app d) := by
  erw [Functor.map_comp]; simp

-- ER: Propose to cut and replace with the version below:
theorem unit_transferNatTrans (f : G ⋙ L₂ ⟶ L₁ ⋙ H) (X : C) :
    G.map (adj₁.unit.app X) ≫ (transferNatTrans adj₁ adj₂ f).app _ =
      adj₂.unit.app _ ≫ R₂.map (f.app _) := by
  dsimp [transferNatTrans]
  rw [← adj₂.unit_naturality_assoc, ← R₂.map_comp, ← Functor.comp_map G L₂, f.naturality_assoc,
    Functor.comp_map, ← H.map_comp]
  dsimp; simp
#align category_theory.unit_transfer_nat_trans CategoryTheory.unit_transferNatTrans

-- ER: I don't get why this is harder than the counit case.
/- A component of a transposed version of the mates correspondence. -/
theorem unit_Mates (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (c : C) :
    G.map (adj₁.unit.app c) ≫ (Mates adj₁ adj₂ α).app _ =
      adj₂.unit.app _ ≫ R₂.map (α.app _) := by
  dsimp [Mates]
  rw [← adj₂.unit_naturality_assoc]
  slice_lhs 2 3 =>
    {
      rw [← R₂.map_comp, ← Functor.comp_map G L₂]
      rw [α.naturality]
    }
  rw [R₂.map_comp]
  slice_lhs 3 4 =>
    {
      rw [← R₂.map_comp, Functor.comp_map L₁ H]
      rw [← H.map_comp]
      rw [left_triangle_components]
    }
  simp only [comp_obj, map_id, comp_id]

-- See library note [dsimp, simp]
end Mates

section MatesVComp

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable {D : Type u₄} {E : Type u₅} {F : Type u₆}
variable [Category.{v₁} A] [Category.{v₂} B][Category.{v₃} C]
variable [Category.{v₄} D] [Category.{v₅} E][Category.{v₆} F]
variable {G₁ : A ⥤ C}{G₂ : C ⥤ E}{H₁ : B ⥤ D}{H₂ : D ⥤ F}
variable {L₁ : A ⥤ B}{R₁ : B ⥤ A} {L₂ : C ⥤ D}{R₂ : D ⥤ C}
variable {L₃ : E ⥤ F}{R₃ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)

/-- Squares between left adjoints can be composed "vertically" by pasting. -/
def LeftAdjointSquare.vcomp :
    (G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) → (G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂) → ((G₁ ⋙ G₂) ⋙ L₃ ⟶ L₁ ⋙ (H₁ ⋙ H₂)) :=
  fun α β ↦ (whiskerLeft G₁ β) ≫ (whiskerRight α H₂)
#align category_theory.leftadjointsquare_vcomp CategoryTheory.LeftAdjointSquare.vcomp

/-- Squares between right adjoints can be composed "vertically" by pasting. -/
def RightAdjointSquare.vcomp :
    (R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) → (R₂ ⋙ G₂ ⟶ H₂ ⋙ R₃) → (R₁ ⋙ (G₁ ⋙ G₂) ⟶ (H₁ ⋙ H₂) ⋙ R₃) :=
  fun α β ↦ (whiskerRight α G₂) ≫ (whiskerLeft H₁ β)
#align category_theory.rightadjointsquare_vcomp CategoryTheory.RightAdjointSquare.vcomp

/-- The mates equivalence commutes with vertical composition. -/
theorem Mates_vcomp
    (α : G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) (β : G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂) :
    (Mates (G := G₁ ⋙ G₂) (H := H₁ ⋙ H₂) adj₁ adj₃) (LeftAdjointSquare.vcomp α β) =
      RightAdjointSquare.vcomp (Mates adj₁ adj₂ α) (Mates adj₂ adj₃ β) := by
  unfold LeftAdjointSquare.vcomp RightAdjointSquare.vcomp Mates
  ext b
  simp only [comp_obj, Equiv.coe_fn_mk, whiskerLeft_comp, whiskerLeft_twice, whiskerRight_comp,
    assoc, comp_app, whiskerLeft_app, whiskerRight_app, id_obj, Functor.comp_map,
    whiskerRight_twice]
  slice_rhs 1 4 =>
    {
      rw [← assoc, ← assoc, ← unit_naturality (adj₃)]
    }
  rw [L₃.map_comp, R₃.map_comp]
  slice_rhs 2 4 =>
    {
      rw [← R₃.map_comp, ← R₃.map_comp, ← assoc, ← L₃.map_comp, ← G₂.map_comp, ← G₂.map_comp]
      rw [← Functor.comp_map G₂ L₃, β.naturality]
    }
  rw [(L₂ ⋙ H₂).map_comp, R₃.map_comp, R₃.map_comp]
  slice_rhs 4 5 =>
    {
      rw [← R₃.map_comp, Functor.comp_map L₂ _, ← Functor.comp_map _ L₂, ← H₂.map_comp]
      rw [adj₂.counit.naturality]
    }
  simp only [comp_obj, Functor.comp_map, map_comp, id_obj, Functor.id_map, assoc]
  slice_rhs 4 5 =>
    {
      rw [← R₃.map_comp, ← H₂.map_comp, ← Functor.comp_map _ L₂, adj₂.counit.naturality]
    }
  simp only [comp_obj, id_obj, Functor.id_map, map_comp, assoc]
  slice_rhs 3 4 =>
    {
      rw [← R₃.map_comp, ← H₂.map_comp, left_triangle_components]
    }
  simp only [map_id, id_comp]

end MatesVComp

section MatesHComp

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄} {E : Type u₅} {F : Type u₆}
variable [Category.{v₁} A] [Category.{v₂} B][Category.{v₃} C]
variable [Category.{v₄} D] [Category.{v₅} E][Category.{v₆} F]
variable {G : A ⥤ D}{H : B ⥤ E}{K : C ⥤ F}
variable {L₁ : A ⥤ B}{R₁ : B ⥤ A} {L₂ : D ⥤ E}{R₂ : E ⥤ D}
variable {L₃ : B ⥤ C}{R₃ : C ⥤ B} {L₄ : E ⥤ F}{R₄ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
variable (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)

/-- Squares between left adjoints can be composed "horizontally" by pasting. -/
def LeftAdjointSquare.hcomp :
    (G ⋙ L₂ ⟶ L₁ ⋙ H) → (H ⋙ L₄ ⟶ L₃ ⋙ K) → (G ⋙ (L₂ ⋙ L₄) ⟶ (L₁ ⋙ L₃) ⋙ K) := fun α β ↦
  (whiskerRight α L₄) ≫ (whiskerLeft L₁ β)

/-- Squares between right adjoints can be composed "horizontally" by pasting. -/
def RightAdjointSquare.hcomp :
    (R₁ ⋙ G ⟶ H ⋙ R₂) → (R₃ ⋙ H ⟶ K ⋙ R₄) → ((R₃ ⋙ R₁) ⋙ G ⟶ K ⋙ (R₄ ⋙ R₂)) := fun α β ↦
  (whiskerLeft R₃ α) ≫ (whiskerRight β R₂)

/-- The mates equivalence commutes with horizontal composition of squares. -/
theorem Mates_hcomp
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (β : H ⋙ L₄ ⟶ L₃ ⋙ K) :
    (Mates (adj₁.comp adj₃) (adj₂.comp adj₄)) (LeftAdjointSquare.hcomp α β) =
      RightAdjointSquare.hcomp (Mates adj₁ adj₂ α) (Mates adj₃ adj₄ β) := by
  unfold LeftAdjointSquare.hcomp RightAdjointSquare.hcomp Mates Adjunction.comp
  ext c
  simp only [comp_obj, whiskerLeft_comp, whiskerLeft_twice, whiskerRight_comp, assoc,
    Equiv.coe_fn_mk, comp_app, whiskerLeft_app, whiskerRight_app, id_obj, associator_inv_app,
    Functor.comp_map, associator_hom_app, map_id, id_comp, whiskerRight_twice]
  slice_rhs 2 4 =>
    {
      rw [← R₂.map_comp, ← R₂.map_comp, ← assoc, ← unit_naturality (adj₄)]
    }
  rw [R₂.map_comp, L₄.map_comp, R₄.map_comp, R₂.map_comp]
  slice_rhs 4 5 =>
    {
      rw [← R₂.map_comp, ← R₄.map_comp, ← Functor.comp_map _ L₄ , β.naturality]
    }
  simp only [comp_obj, Functor.comp_map, map_comp, assoc]

end MatesHComp

section MatesSquareComp

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable {D : Type u₄} {E : Type u₅} {F : Type u₆}
variable {X : Type u₇} {Y : Type u₈} {Z : Type u₉}
variable [Category.{v₁} A] [Category.{v₂} B][Category.{v₃} C]
variable [Category.{v₄} D] [Category.{v₅} E][Category.{v₆} F]
variable [Category.{v₇} X] [Category.{v₈} Y][Category.{v₉} Z]
variable {G₁ : A ⥤ D} {H₁ : B ⥤ E} {K₁ : C ⥤ F} {G₂ : D ⥤ X} {H₂ : E ⥤ Y} {K₂ : F ⥤ Z}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B} {L₃ : D ⥤ E} {R₃ : E ⥤ D}
variable {L₄ : E ⥤ F} {R₄ : F ⥤ E} {L₅ : X ⥤ Y} {R₅ : Y ⥤ X} {L₆ : Y ⥤ Z} {R₆ : Z ⥤ Y}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
variable (adj₄ : L₄ ⊣ R₄) (adj₅ : L₅ ⊣ R₅) (adj₆ : L₆ ⊣ R₆)

/-- Squares of squares between left adjoints can be composed by iterating vertical and horizontal composition.-/
def LeftAdjointSquare.comp
    (α : G₁ ⋙ L₃ ⟶ L₁ ⋙ H₁) (β : H₁ ⋙ L₄ ⟶ L₂ ⋙ K₁)
    (γ : G₂ ⋙ L₅ ⟶ L₃ ⋙ H₂) (δ : H₂ ⋙ L₆ ⟶ L₄ ⋙ K₂) :
    ((G₁ ⋙ G₂) ⋙ (L₅ ⋙ L₆)) ⟶ ((L₁ ⋙ L₂) ⋙ (K₁ ⋙ K₂)) :=
  LeftAdjointSquare.vcomp (LeftAdjointSquare.hcomp α β) (LeftAdjointSquare.hcomp γ δ)
#align category_theory.leftadjointsquare_comp CategoryTheory.LeftAdjointSquare.comp

theorem LeftAdjointSquare.comp_vhcomp
    (α : G₁ ⋙ L₃ ⟶ L₁ ⋙ H₁) (β : H₁ ⋙ L₄ ⟶ L₂ ⋙ K₁)
    (γ : G₂ ⋙ L₅ ⟶ L₃ ⋙ H₂) (δ : H₂ ⋙ L₆ ⟶ L₄ ⋙ K₂) :
    LeftAdjointSquare.comp α β γ δ =
      LeftAdjointSquare.vcomp (LeftAdjointSquare.hcomp α β) (LeftAdjointSquare.hcomp γ δ) := rfl

/-- Horizontal and vertical composition of squares commutes.-/
theorem LeftAdjointSquare.comp_hvcomp
    (α : G₁ ⋙ L₃ ⟶ L₁ ⋙ H₁) (β : H₁ ⋙ L₄ ⟶ L₂ ⋙ K₁)
    (γ : G₂ ⋙ L₅ ⟶ L₃ ⋙ H₂) (δ : H₂ ⋙ L₆ ⟶ L₄ ⋙ K₂) :
    LeftAdjointSquare.comp α β γ δ =
      LeftAdjointSquare.hcomp (LeftAdjointSquare.vcomp α γ) (LeftAdjointSquare.vcomp β δ) := by
  unfold LeftAdjointSquare.comp LeftAdjointSquare.hcomp LeftAdjointSquare.vcomp
  unfold whiskerLeft whiskerRight
  ext a
  simp only [comp_obj, comp_app, map_comp, assoc]
  slice_rhs 2 3 =>
    {
      rw [← Functor.comp_map _ L₆, δ.naturality]
    }
  simp only [comp_obj, Functor.comp_map, assoc]

/-- Squares of squares between right adjoints can be composed by iterating vertical and horizontal composition.-/
def RightAdjointSquare.comp
    (α : R₁ ⋙ G₁ ⟶ H₁ ⋙ R₃) (β : R₂ ⋙ H₁ ⟶ K₁ ⋙ R₄)
    (γ : R₃ ⋙ G₂ ⟶ H₂ ⋙ R₅) (δ : R₄ ⋙ H₂ ⟶ K₂ ⋙ R₆) :
    ((R₂ ⋙ R₁) ⋙ (G₁ ⋙ G₂) ⟶ (K₁ ⋙ K₂) ⋙ (R₆ ⋙ R₅)) :=
  RightAdjointSquare.vcomp (RightAdjointSquare.hcomp α β) (RightAdjointSquare.hcomp γ δ)
#align category_theory.rightadjointsquare_comp CategoryTheory.RightAdjointSquare.comp

theorem RightAdjointSquare.comp_vhcomp
    (α : R₁ ⋙ G₁ ⟶ H₁ ⋙ R₃) (β : R₂ ⋙ H₁ ⟶ K₁ ⋙ R₄)
    (γ : R₃ ⋙ G₂ ⟶ H₂ ⋙ R₅) (δ : R₄ ⋙ H₂ ⟶ K₂ ⋙ R₆) :
    RightAdjointSquare.comp α β γ δ =
    RightAdjointSquare.vcomp (RightAdjointSquare.hcomp α β) (RightAdjointSquare.hcomp γ δ) := rfl

/-- Horizontal and vertical composition of squares commutes.-/
theorem RightAdjointSquare.comp_hvcomp
    (α : R₁ ⋙ G₁ ⟶ H₁ ⋙ R₃) (β : R₂ ⋙ H₁ ⟶ K₁ ⋙ R₄)
    (γ : R₃ ⋙ G₂ ⟶ H₂ ⋙ R₅) (δ : R₄ ⋙ H₂ ⟶ K₂ ⋙ R₆) :
    RightAdjointSquare.comp α β γ δ =
    RightAdjointSquare.hcomp (RightAdjointSquare.vcomp α γ) (RightAdjointSquare.vcomp β δ) := by
  unfold RightAdjointSquare.comp RightAdjointSquare.hcomp RightAdjointSquare.vcomp
  unfold whiskerLeft whiskerRight
  ext c
  simp only [comp_obj, comp_app, map_comp, assoc]
  slice_rhs 2 3 =>
    {
      rw [← Functor.comp_map _ R₅, ← γ.naturality]
    }
  simp only [comp_obj, Functor.comp_map, assoc]

/-- The mates equivalence commutes with composition of squares of squares. These results form the basis for an isomorphism of double categories to be proven later.
-/
theorem Mates_square
    (α : G₁ ⋙ L₃ ⟶ L₁ ⋙ H₁) (β : H₁ ⋙ L₄ ⟶ L₂ ⋙ K₁)
    (γ : G₂ ⋙ L₅ ⟶ L₃ ⋙ H₂) (δ : H₂ ⋙ L₆ ⟶ L₄ ⋙ K₂) :
    (Mates (G := G₁ ⋙ G₂) (H := K₁ ⋙ K₂) (adj₁.comp adj₂) (adj₅.comp adj₆))
        (LeftAdjointSquare.comp α β γ δ) =
      RightAdjointSquare.comp
        (Mates adj₁ adj₃ α) (Mates adj₂ adj₄ β) (Mates adj₃ adj₅ γ) (Mates adj₄ adj₆ δ) := by
  have vcomp :=
    Mates_vcomp (adj₁.comp adj₂) (adj₃.comp adj₄) (adj₅.comp adj₆)
      (LeftAdjointSquare.hcomp α β) (LeftAdjointSquare.hcomp γ δ)
  have hcomp1 := Mates_hcomp adj₁ adj₃ adj₂ adj₄ α β
  have hcomp2 := Mates_hcomp adj₃ adj₅ adj₄ adj₆ γ δ
  rw [hcomp1, hcomp2] at vcomp
  exact vcomp

end MatesSquareComp

section Conjugates

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable {L₁ L₂ L₃ : C ⥤ D} {R₁ R₂ R₃ : D ⥤ C}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)

/-- Given two adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` both between categories `C`, `D`, there is a
bijection between natural transformations `L₂ ⟶ L₁` and natural transformations `R₁ ⟶ R₂`. This is defined as a special case of `Mates`, where the two "vertical" functors are identity, modulo composition with the unitors.
TODO: Generalise to when the two vertical functors are equivalences rather than being exactly `𝟭`.

Furthermore, this bijection preserves (and reflects) isomorphisms, i.e. a transformation is an iso
iff its image under the bijection is an iso, see eg `CategoryTheory.transferNatTransSelf_iso`.
This is in contrast to the general case `transferNatTrans` which
 does not in general have this property.-/

/-- Mates between parallel adjunctions are called conjugates. -/
def Conjugates : (L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂) :=
  calc
    (L₂ ⟶ L₁) ≃ _ := (Iso.homCongr L₂.leftUnitor L₁.rightUnitor).symm
    _ ≃ _ := Mates adj₁ adj₂
    _ ≃ (R₁ ⟶ R₂) := R₁.rightUnitor.homCongr R₂.leftUnitor

/-- A component of a transposed form of the conjugation definition. -/
theorem Conjugates_counit (α : L₂ ⟶ L₁) (d : D) :
    L₂.map ((Conjugates adj₁ adj₂ α).app _) ≫ adj₂.counit.app d =
      α.app _ ≫ adj₁.counit.app d := by
  dsimp [Conjugates]
  rw [id_comp, comp_id]
  have := Mates_counit adj₁ adj₂ (L₂.leftUnitor.hom ≫ α ≫ L₁.rightUnitor.inv) d
  dsimp at this
  rw [this]
  simp only [comp_id, id_comp]

/-- A component of a transposed form of the conjugation definition. -/
theorem unit_Conjugates (α : L₂ ⟶ L₁) (c : C) :
    adj₁.unit.app _ ≫ (Conjugates adj₁ adj₂ α).app _ =
      adj₂.unit.app c ≫ R₂.map (α.app _) := by
  dsimp [Conjugates]
  rw [id_comp, comp_id]
  have := unit_Mates adj₁ adj₂ (L₂.leftUnitor.hom ≫ α ≫ L₁.rightUnitor.inv) c
  dsimp at this
  rw [this]
  simp

@[simp]
theorem Conjugates_id : Conjugates adj₁ adj₁ (𝟙 _) = 𝟙 _ := by
  ext
  dsimp [Conjugates, Mates]
  simp only [comp_id, map_id, id_comp, right_triangle_components]

@[simp]
theorem Conjugates_symm_id : (Conjugates adj₁ adj₁).symm (𝟙 _) = 𝟙 _ := by
  rw [Equiv.symm_apply_eq]
  simp only [Conjugates_id]
#align category_theory.conjugates_symm_id CategoryTheory.Conjugates_symm_id

theorem Conjugates_adjunction_id {L R : C ⥤ C} (adj : L ⊣ R) (α : 𝟭 C ⟶ L) (c : C) :
    (Conjugates adj Adjunction.id α).app c = α.app (R.obj c) ≫ adj.counit.app c := by
  dsimp [Conjugates, Mates, Adjunction.id]
  simp only [comp_id, id_comp]

theorem Conjugates_adjunction_id_symm {L R : C ⥤ C} (adj : L ⊣ R) (α : R ⟶ 𝟭 C) (c : C) :
    ((Conjugates adj Adjunction.id).symm α).app c = adj.unit.app c ≫ α.app (L.obj c) := by
  dsimp [Conjugates, Mates, Adjunction.id]
  simp only [comp_id, id_comp]
end Conjugates


section ConjugateComposition
variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable {L₁ L₂ L₃ : C ⥤ D} {R₁ R₂ R₃ : D ⥤ C}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)

theorem Conjugates_comp (α : L₂ ⟶ L₁) (β : L₃ ⟶ L₂) :
    Conjugates adj₁ adj₂ α ≫ Conjugates adj₂ adj₃ β =
      Conjugates adj₁ adj₃ (β ≫ α) := by
  ext d
  dsimp [Conjugates, Mates]
  have vcomp := Mates_vcomp adj₁ adj₂ adj₃
    (L₂.leftUnitor.hom ≫ α ≫ L₁.rightUnitor.inv)
    (L₃.leftUnitor.hom ≫ β ≫ L₂.rightUnitor.inv)
  have vcompd := congr_app vcomp d
  dsimp [Mates, LeftAdjointSquare.vcomp, RightAdjointSquare.vcomp] at vcompd
  simp at vcompd
  simp only [comp_id, id_comp, assoc, map_comp]
  rw [vcompd]

-- ER: Warning: swapped order of the arguments.
theorem Conjugates_symm_comp (α : R₁ ⟶ R₂) (β : R₂ ⟶ R₃) :
    (Conjugates adj₂ adj₃).symm β ≫ (Conjugates adj₁ adj₂).symm α =
      (Conjugates adj₁ adj₃).symm (α ≫ β) := by
  rw [Equiv.eq_symm_apply, ← Conjugates_comp _ adj₂]
  simp only [Equiv.apply_symm_apply]

theorem Conjugates_comm {α : L₂ ⟶ L₁} {β : L₁ ⟶ L₂} (βα : β ≫ α = 𝟙 _) :
    Conjugates adj₁ adj₂ α ≫ Conjugates adj₂ adj₁ β = 𝟙 _ := by
  rw [Conjugates_comp, βα, Conjugates_id]

theorem Conjugates_symm_comm {α : R₁ ⟶ R₂}{β : R₂ ⟶ R₁} (αβ : α ≫ β = 𝟙 _) :
    (Conjugates adj₂ adj₁).symm β ≫ (Conjugates adj₁ adj₂).symm α = 𝟙 _ := by
  rw [Conjugates_symm_comp, αβ, Conjugates_symm_id]

/-- If `α` is an isomorphism between left adjoints, then its conjugate transformation is an isomorphism.
The converse is given in `Conjugates_of_iso`.
-/
instance Conjugates_iso (α : L₂ ⟶ L₁) [IsIso α] :
    IsIso (Conjugates adj₁ adj₂ α) :=
  ⟨⟨Conjugates adj₂ adj₁ (inv α),
      ⟨Conjugates_comm _ _ (by simp), Conjugates_comm _ _ (by simp)⟩⟩⟩

/-- If `α` is an isomorphism between right adjoints, then its conjugate transformation is an isomorphism.
The converse is given in `Conjugates_symm_of_iso`.
-/
instance Conjugates_symm_iso (α : R₁ ⟶ R₂) [IsIso α] :
    IsIso ((Conjugates adj₁ adj₂).symm α) :=
  ⟨⟨(Conjugates adj₂ adj₁).symm (inv α),
      ⟨Conjugates_symm_comm _ _ (by simp), Conjugates_symm_comm _ _ (by simp)⟩⟩⟩

/-- If `α` is a natural transformation between left adjoints whose conjugate natural transformation is an isomorphism,
then `α` is an isomorphism.
The converse is given in `Conjugate_iso`.
-/
theorem Conjugate_of_iso (α : L₂ ⟶ L₁) [IsIso (Conjugates adj₁ adj₂ α)] :
    IsIso α := by
  suffices IsIso ((Conjugates adj₁ adj₂).symm (Conjugates adj₁ adj₂ α))
    by simpa using this
  infer_instance

/--
If `α` is a natural transformation between right adjoints whose conjugate natural transformation is an isomorphism,
then `α` is an isomorphism.
The converse is given in `Conjugates_symm_iso`.
-/
theorem Conjugates_symm_of_iso (α : R₁ ⟶ R₂)
    [IsIso ((Conjugates adj₁ adj₂).symm α)] : IsIso α := by
  suffices IsIso ((Conjugates adj₁ adj₂) ((Conjugates adj₁ adj₂).symm α))
    by simpa using this
  infer_instance
end ConjugateComposition

section Self
variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable {L₁ L₂ L₃ : C ⥤ D} {R₁ R₂ R₃ : D ⥤ C}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)

/-- The old definition to be cut.-/
def transferNatTransSelf : (L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂) :=
  calc
    (L₂ ⟶ L₁) ≃ _ := (Iso.homCongr L₂.leftUnitor L₁.rightUnitor).symm
    _ ≃ _ := transferNatTrans adj₁ adj₂
    _ ≃ (R₁ ⟶ R₂) := R₁.rightUnitor.homCongr R₂.leftUnitor
#align category_theory.transfer_nat_trans_self CategoryTheory.transferNatTransSelf

theorem transferNatTransSelf_counit (f : L₂ ⟶ L₁) (X) :
    L₂.map ((transferNatTransSelf adj₁ adj₂ f).app _) ≫ adj₂.counit.app X =
      f.app _ ≫ adj₁.counit.app X := by
  dsimp [transferNatTransSelf]
  rw [id_comp, comp_id]
  have := transferNatTrans_counit adj₁ adj₂ (L₂.leftUnitor.hom ≫ f ≫ L₁.rightUnitor.inv) X
  dsimp at this
  rw [this]
  simp
#align category_theory.transfer_nat_trans_self_counit CategoryTheory.transferNatTransSelf_counit

theorem unit_transferNatTransSelf (f : L₂ ⟶ L₁) (X) :
    adj₁.unit.app _ ≫ (transferNatTransSelf adj₁ adj₂ f).app _ =
      adj₂.unit.app X ≫ R₂.map (f.app _) := by
  dsimp [transferNatTransSelf]
  rw [id_comp, comp_id]
  have := unit_transferNatTrans adj₁ adj₂ (L₂.leftUnitor.hom ≫ f ≫ L₁.rightUnitor.inv) X
  dsimp at this
  rw [this]
  simp
#align category_theory.unit_transfer_nat_trans_self CategoryTheory.unit_transferNatTransSelf

@[simp]
theorem transferNatTransSelf_id : transferNatTransSelf adj₁ adj₁ (𝟙 _) = 𝟙 _ := by
  ext
  dsimp [transferNatTransSelf, transferNatTrans]
  simp
#align category_theory.transfer_nat_trans_self_id CategoryTheory.transferNatTransSelf_id

-- See library note [dsimp, simp]
@[simp]
theorem transferNatTransSelf_symm_id : (transferNatTransSelf adj₁ adj₁).symm (𝟙 _) = 𝟙 _ := by
  rw [Equiv.symm_apply_eq]
  simp
#align category_theory.transfer_nat_trans_self_symm_id CategoryTheory.transferNatTransSelf_symm_id

theorem transferNatTransSelf_comp (f g) :
    transferNatTransSelf adj₁ adj₂ f ≫ transferNatTransSelf adj₂ adj₃ g =
      transferNatTransSelf adj₁ adj₃ (g ≫ f) := by
  ext
  dsimp [transferNatTransSelf, transferNatTrans]
  simp only [id_comp, comp_id]
  rw [← adj₃.unit_naturality_assoc, ← R₃.map_comp, g.naturality_assoc, L₂.map_comp, assoc,
    adj₂.counit_naturality, adj₂.left_triangle_components_assoc, assoc]
#align category_theory.transfer_nat_trans_self_comp CategoryTheory.transferNatTransSelf_comp

theorem transferNatTransSelf_adjunction_id {L R : C ⥤ C} (adj : L ⊣ R) (f : 𝟭 C ⟶ L) (X : C) :
    (transferNatTransSelf adj Adjunction.id f).app X = f.app (R.obj X) ≫ adj.counit.app X := by
  dsimp [transferNatTransSelf, transferNatTrans, Adjunction.id]
  simp only [comp_id, id_comp]
#align category_theory.transfer_nat_trans_self_adjunction_id CategoryTheory.transferNatTransSelf_adjunction_id

theorem transferNatTransSelf_adjunction_id_symm {L R : C ⥤ C} (adj : L ⊣ R) (g : R ⟶ 𝟭 C) (X : C) :
    ((transferNatTransSelf adj Adjunction.id).symm g).app X = adj.unit.app X ≫ g.app (L.obj X) := by
  dsimp [transferNatTransSelf, transferNatTrans, Adjunction.id]
  simp only [comp_id, id_comp]
#align category_theory.transfer_nat_trans_self_adjunction_id_symm CategoryTheory.transferNatTransSelf_adjunction_id_symm

theorem transferNatTransSelf_symm_comp (f g) :
    (transferNatTransSelf adj₂ adj₁).symm f ≫ (transferNatTransSelf adj₃ adj₂).symm g =
      (transferNatTransSelf adj₃ adj₁).symm (g ≫ f) := by
  rw [Equiv.eq_symm_apply, ← transferNatTransSelf_comp _ adj₂]
  simp
#align category_theory.transfer_nat_trans_self_symm_comp CategoryTheory.transferNatTransSelf_symm_comp

theorem transferNatTransSelf_comm {f g} (gf : g ≫ f = 𝟙 _) :
    transferNatTransSelf adj₁ adj₂ f ≫ transferNatTransSelf adj₂ adj₁ g = 𝟙 _ := by
  rw [transferNatTransSelf_comp, gf, transferNatTransSelf_id]
#align category_theory.transfer_nat_trans_self_comm CategoryTheory.transferNatTransSelf_comm

theorem transferNatTransSelf_symm_comm {f g} (gf : g ≫ f = 𝟙 _) :
    (transferNatTransSelf adj₁ adj₂).symm f ≫ (transferNatTransSelf adj₂ adj₁).symm g = 𝟙 _ := by
  rw [transferNatTransSelf_symm_comp, gf, transferNatTransSelf_symm_id]
#align category_theory.transfer_nat_trans_self_symm_comm CategoryTheory.transferNatTransSelf_symm_comm

/-- If `f` is an isomorphism, then the transferred natural transformation is an isomorphism.
The converse is given in `transferNatTransSelf_of_iso`.
-/
instance transferNatTransSelf_iso (f : L₂ ⟶ L₁) [IsIso f] :
    IsIso (transferNatTransSelf adj₁ adj₂ f) :=
  ⟨⟨transferNatTransSelf adj₂ adj₁ (inv f),
      ⟨transferNatTransSelf_comm _ _ (by simp), transferNatTransSelf_comm _ _ (by simp)⟩⟩⟩
#align category_theory.transfer_nat_trans_self_iso CategoryTheory.transferNatTransSelf_iso

/-- If `f` is an isomorphism, then the un-transferred natural transformation is an isomorphism.
The converse is given in `transferNatTransSelf_symm_of_iso`.
-/
instance transferNatTransSelf_symm_iso (f : R₁ ⟶ R₂) [IsIso f] :
    IsIso ((transferNatTransSelf adj₁ adj₂).symm f) :=
  ⟨⟨(transferNatTransSelf adj₂ adj₁).symm (inv f),
      ⟨transferNatTransSelf_symm_comm _ _ (by simp), transferNatTransSelf_symm_comm _ _ (by simp)⟩⟩⟩
#align category_theory.transfer_nat_trans_self_symm_iso CategoryTheory.transferNatTransSelf_symm_iso

/-- If `f` is a natural transformation whose transferred natural transformation is an isomorphism,
then `f` is an isomorphism.
The converse is given in `transferNatTransSelf_iso`.
-/
theorem transferNatTransSelf_of_iso (f : L₂ ⟶ L₁) [IsIso (transferNatTransSelf adj₁ adj₂ f)] :
    IsIso f := by
  suffices IsIso ((transferNatTransSelf adj₁ adj₂).symm (transferNatTransSelf adj₁ adj₂ f))
    by simpa using this
  infer_instance
#align category_theory.transfer_nat_trans_self_of_iso CategoryTheory.transferNatTransSelf_of_iso

/--
If `f` is a natural transformation whose un-transferred natural transformation is an isomorphism,
then `f` is an isomorphism.
The converse is given in `transferNatTransSelf_symm_iso`.
-/
theorem transferNatTransSelf_symm_of_iso (f : R₁ ⟶ R₂)
    [IsIso ((transferNatTransSelf adj₁ adj₂).symm f)] : IsIso f := by
  suffices IsIso ((transferNatTransSelf adj₁ adj₂) ((transferNatTransSelf adj₁ adj₂).symm f))
    by simpa using this
  infer_instance
#align category_theory.transfer_nat_trans_self_symm_of_iso CategoryTheory.transferNatTransSelf_symm_of_iso

end Self

end CategoryTheory
