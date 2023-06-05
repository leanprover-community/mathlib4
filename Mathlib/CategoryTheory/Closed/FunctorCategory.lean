/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle

! This file was ported from Lean 3 source module category_theory.closed.functor_category
! leanprover-community/mathlib commit 0caf3701139ef2e69c215717665361cda205a90b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Closed.Monoidal
import Mathbin.CategoryTheory.Monoidal.FunctorCategory

/-!
# Functors from a groupoid into a monoidal closed category form a monoidal closed category.

(Using the pointwise monoidal structure on the functor category.)
-/


noncomputable section

open CategoryTheory

open CategoryTheory.MonoidalCategory

open CategoryTheory.MonoidalClosed

namespace CategoryTheory.Functor

variable {C D : Type _} [Groupoid D] [Category C] [MonoidalCategory C] [MonoidalClosed C]

/-- Auxiliary definition for `category_theory.monoidal_closed.functor_closed`.
The internal hom functor `F ⟶[C] -` -/
@[simps]
def closedIhom (F : D ⥤ C) : (D ⥤ C) ⥤ D ⥤ C :=
  ((whiskeringRight₂ D Cᵒᵖ C C).obj internalHom).obj (Groupoid.invFunctor D ⋙ F.op)
#align category_theory.functor.closed_ihom CategoryTheory.Functor.closedIhom

/-- Auxiliary definition for `category_theory.monoidal_closed.functor_closed`.
The unit for the adjunction `(tensor_left F) ⊣ (ihom F)`. -/
@[simps]
def closedUnit (F : D ⥤ C) : 𝟭 (D ⥤ C) ⟶ tensorLeft F ⋙ closedIhom F
    where app G :=
    { app := fun X => (ihom.coev (F.obj X)).app (G.obj X)
      naturality' := by
        intro X Y f
        dsimp
        simp only [ihom.coev_naturality, closed_ihom_obj_map, monoidal.tensor_obj_map]
        dsimp
        rw [coev_app_comp_pre_app_assoc, ← functor.map_comp]
        simp }
#align category_theory.functor.closed_unit CategoryTheory.Functor.closedUnit

/-- Auxiliary definition for `category_theory.monoidal_closed.functor_closed`.
The counit for the adjunction `(tensor_left F) ⊣ (ihom F)`. -/
@[simps]
def closedCounit (F : D ⥤ C) : closedIhom F ⋙ tensorLeft F ⟶ 𝟭 (D ⥤ C)
    where app G :=
    { app := fun X => (ihom.ev (F.obj X)).app (G.obj X)
      naturality' := by
        intro X Y f
        dsimp
        simp only [closed_ihom_obj_map, pre_comm_ihom_map]
        rw [← tensor_id_comp_id_tensor, id_tensor_comp]
        simp }
#align category_theory.functor.closed_counit CategoryTheory.Functor.closedCounit

/-- If `C` is a monoidal closed category and `D` is groupoid, then every functor `F : D ⥤ C` is
closed in the functor category `F : D ⥤ C` with the pointwise monoidal structure. -/
@[simps]
instance closed (F : D ⥤ C) : Closed F
    where isAdj :=
    { right := closedIhom F
      adj :=
        Adjunction.mkOfUnitCounit
          { Unit := closedUnit F
            counit := closedCounit F } }
#align category_theory.functor.closed CategoryTheory.Functor.closed

/-- If `C` is a monoidal closed category and `D` is groupoid, then the functor category `D ⥤ C`,
with the pointwise monoidal structure, is monoidal closed. -/
@[simps]
instance monoidalClosed : MonoidalClosed (D ⥤ C) where closed' := by infer_instance
#align category_theory.functor.monoidal_closed CategoryTheory.Functor.monoidalClosed

theorem ihom_map (F : D ⥤ C) {G H : D ⥤ C} (f : G ⟶ H) : (ihom F).map f = (closedIhom F).map f :=
  rfl
#align category_theory.functor.ihom_map CategoryTheory.Functor.ihom_map

theorem ihom_ev_app (F G : D ⥤ C) : (ihom.ev F).app G = (closedCounit F).app G :=
  rfl
#align category_theory.functor.ihom_ev_app CategoryTheory.Functor.ihom_ev_app

theorem ihom_coev_app (F G : D ⥤ C) : (ihom.coev F).app G = (closedUnit F).app G :=
  rfl
#align category_theory.functor.ihom_coev_app CategoryTheory.Functor.ihom_coev_app

end CategoryTheory.Functor

