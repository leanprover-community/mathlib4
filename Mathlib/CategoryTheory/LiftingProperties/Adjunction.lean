/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

#align_import category_theory.lifting_properties.adjunction from "leanprover-community/mathlib"@"32253a1a1071173b33dc7d6a218cf722c6feb514"

/-!

# Lifting properties and adjunction

In this file, we obtain `Adjunction.HasLiftingProperty_iff`, which states
that when we have an adjunction `adj : G ⊣ F` between two functors `G : C ⥤ D`
and `F : D ⥤ C`, then a morphism of the form `G.map i` has the left lifting
property in `D` with respect to a morphism `p` if and only the morphism `i`
has the left lifting property in `C` with respect to `F.map p`.

-/


namespace CategoryTheory

open Category

variable {C D : Type*} [Category C] [Category D] {G : C ⥤ D} {F : D ⥤ C}

namespace CommSq

section

variable {A B : C} {X Y : D} {i : A ⟶ B} {p : X ⟶ Y} {u : G.obj A ⟶ X} {v : G.obj B ⟶ Y}
  (sq : CommSq u (G.map i) p v) (adj : G ⊣ F)

/-- When we have an adjunction `G ⊣ F`, any commutative square where the left
map is of the form `G.map i` and the right map is `p` has an "adjoint" commutative
square whose left map is `i` and whose right map is `F.map p`. -/
theorem right_adjoint : CommSq (adj.homEquiv _ _ u) i (F.map p) (adj.homEquiv _ _ v) :=
  ⟨by
    simp only [Adjunction.homEquiv_unit, assoc, ← F.map_comp, sq.w]
    -- ⊢ NatTrans.app adj.unit A ≫ F.map (G.map i ≫ v) = i ≫ NatTrans.app adj.unit B  …
    rw [F.map_comp, Adjunction.unit_naturality_assoc]⟩
    -- 🎉 no goals
#align category_theory.comm_sq.right_adjoint CategoryTheory.CommSq.right_adjoint

/-- The liftings of a commutative are in bijection with the liftings of its (right)
adjoint square. -/
def rightAdjointLiftStructEquiv : sq.LiftStruct ≃ (sq.right_adjoint adj).LiftStruct
    where
  toFun l :=
    { l := adj.homEquiv _ _ l.l
      fac_left := by rw [← adj.homEquiv_naturality_left, l.fac_left]
                     -- 🎉 no goals
      fac_right := by rw [← Adjunction.homEquiv_naturality_right, l.fac_right] }
                      -- 🎉 no goals
  invFun l :=
    { l := (adj.homEquiv _ _).symm l.l
      fac_left := by
        rw [← Adjunction.homEquiv_naturality_left_symm, l.fac_left]
        -- ⊢ ↑(Adjunction.homEquiv adj A X).symm (↑(Adjunction.homEquiv adj A X) u) = u
        apply (adj.homEquiv _ _).left_inv
        -- 🎉 no goals
      fac_right := by
        rw [← Adjunction.homEquiv_naturality_right_symm, l.fac_right]
        -- ⊢ ↑(Adjunction.homEquiv adj B Y).symm (↑(Adjunction.homEquiv adj B Y) v) = v
        apply (adj.homEquiv _ _).left_inv }
        -- 🎉 no goals
  left_inv := by aesop_cat
                 -- 🎉 no goals
  right_inv := by aesop_cat
                  -- 🎉 no goals
#align category_theory.comm_sq.right_adjoint_lift_struct_equiv CategoryTheory.CommSq.rightAdjointLiftStructEquiv

/-- A square has a lifting if and only if its (right) adjoint square has a lifting. -/
theorem right_adjoint_hasLift_iff : HasLift (sq.right_adjoint adj) ↔ HasLift sq := by
  simp only [HasLift.iff]
  -- ⊢ Nonempty (LiftStruct (_ : CommSq (↑(Adjunction.homEquiv adj A X) u) i (F.map …
  exact Equiv.nonempty_congr (sq.rightAdjointLiftStructEquiv adj).symm
  -- 🎉 no goals
#align category_theory.comm_sq.right_adjoint_has_lift_iff CategoryTheory.CommSq.right_adjoint_hasLift_iff

instance [HasLift sq] : HasLift (sq.right_adjoint adj) := by
  rw [right_adjoint_hasLift_iff]
  -- ⊢ HasLift ?sq
  infer_instance
  -- 🎉 no goals

end

section

variable {A B : C} {X Y : D} {i : A ⟶ B} {p : X ⟶ Y} {u : A ⟶ F.obj X} {v : B ⟶ F.obj Y}
  (sq : CommSq u i (F.map p) v) (adj : G ⊣ F)

/-- When we have an adjunction `G ⊣ F`, any commutative square where the left
map is of the form `i` and the right map is `F.map p` has an "adjoint" commutative
square whose left map is `G.map i` and whose right map is `p`. -/
theorem left_adjoint : CommSq ((adj.homEquiv _ _).symm u) (G.map i) p ((adj.homEquiv _ _).symm v) :=
  ⟨by
    simp only [Adjunction.homEquiv_counit, assoc, ← G.map_comp_assoc, ← sq.w]
    -- ⊢ G.map u ≫ NatTrans.app adj.counit X ≫ p = G.map (u ≫ F.map p) ≫ NatTrans.app …
    rw [G.map_comp, assoc, Adjunction.counit_naturality]⟩
    -- 🎉 no goals
#align category_theory.comm_sq.left_adjoint CategoryTheory.CommSq.left_adjoint

/-- The liftings of a commutative are in bijection with the liftings of its (left)
adjoint square. -/
def leftAdjointLiftStructEquiv : sq.LiftStruct ≃ (sq.left_adjoint adj).LiftStruct
    where
  toFun l :=
    { l := (adj.homEquiv _ _).symm l.l
      fac_left := by rw [← adj.homEquiv_naturality_left_symm, l.fac_left]
                     -- 🎉 no goals
      fac_right := by rw [← adj.homEquiv_naturality_right_symm, l.fac_right] }
                      -- 🎉 no goals
  invFun l :=
    { l := (adj.homEquiv _ _) l.l
      fac_left := by
        rw [← adj.homEquiv_naturality_left, l.fac_left]
        -- ⊢ ↑(Adjunction.homEquiv adj A X) (↑(Adjunction.homEquiv adj A X).symm u) = u
        apply (adj.homEquiv _ _).right_inv
        -- 🎉 no goals
      fac_right := by
        rw [← adj.homEquiv_naturality_right, l.fac_right]
        -- ⊢ ↑(Adjunction.homEquiv adj B Y) (↑(Adjunction.homEquiv adj B Y).symm v) = v
        apply (adj.homEquiv _ _).right_inv }
        -- 🎉 no goals
  left_inv := by aesop_cat
                 -- 🎉 no goals
  right_inv := by aesop_cat
                  -- 🎉 no goals
#align category_theory.comm_sq.left_adjoint_lift_struct_equiv CategoryTheory.CommSq.leftAdjointLiftStructEquiv

/-- A (left) adjoint square has a lifting if and only if the original square has a lifting. -/
theorem left_adjoint_hasLift_iff : HasLift (sq.left_adjoint adj) ↔ HasLift sq := by
  simp only [HasLift.iff]
  -- ⊢ Nonempty (LiftStruct (_ : CommSq (↑(Adjunction.homEquiv adj A X).symm u) (G. …
  exact Equiv.nonempty_congr (sq.leftAdjointLiftStructEquiv adj).symm
  -- 🎉 no goals
#align category_theory.comm_sq.left_adjoint_has_lift_iff CategoryTheory.CommSq.left_adjoint_hasLift_iff

instance [HasLift sq] : HasLift (sq.left_adjoint adj) := by
  rw [left_adjoint_hasLift_iff]
  -- ⊢ HasLift ?sq
  infer_instance
  -- 🎉 no goals

end

end CommSq

namespace Adjunction

theorem hasLiftingProperty_iff (adj : G ⊣ F) {A B : C} {X Y : D} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty (G.map i) p ↔ HasLiftingProperty i (F.map p) := by
  constructor <;> intro <;> constructor <;> intro f g sq
  -- ⊢ HasLiftingProperty (G.map i) p → HasLiftingProperty i (F.map p)
                  -- ⊢ HasLiftingProperty i (F.map p)
                  -- ⊢ HasLiftingProperty (G.map i) p
                            -- ⊢ ∀ {f : A ⟶ F.obj X} {g : B ⟶ F.obj Y} (sq : CommSq f i (F.map p) g), CommSq. …
                            -- ⊢ ∀ {f : G.obj A ⟶ X} {g : G.obj B ⟶ Y} (sq : CommSq f (G.map i) p g), CommSq. …
                                            -- ⊢ CommSq.HasLift sq
                                            -- ⊢ CommSq.HasLift sq
  · rw [← sq.left_adjoint_hasLift_iff adj]
    -- ⊢ CommSq.HasLift (_ : CommSq (↑(homEquiv adj A X).symm f) (G.map i) p (↑(homEq …
    infer_instance
    -- 🎉 no goals
  · rw [← sq.right_adjoint_hasLift_iff adj]
    -- ⊢ CommSq.HasLift (_ : CommSq (↑(homEquiv adj A X) f) i (F.map p) (↑(homEquiv a …
    infer_instance
    -- 🎉 no goals
#align category_theory.adjunction.has_lifting_property_iff CategoryTheory.Adjunction.hasLiftingProperty_iff

end Adjunction

end CategoryTheory

