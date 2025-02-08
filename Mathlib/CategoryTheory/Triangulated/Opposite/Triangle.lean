/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.CategoryTheory.Triangulated.Opposite.Basic

/-!
# Triangles in the opposite category of a (pre)triangulated category

Let `C` be a (pre)triangulated category.
In `CategoryTheory.Triangulated.Opposite.Basic`, we have constructed
a shift on `Cᵒᵖ` that will be part of a structure of (pre)triangulated
category. In this file, we construct an equivalence of categories
between `(Triangle C)ᵒᵖ` and `Triangle Cᵒᵖ`, called
`CategoryTheory.Pretriangulated.triangleOpEquivalence`. It sends a triangle
`X ⟶ Y ⟶ Z ⟶ X⟦1⟧` in `C` to the triangle `op Z ⟶ op Y ⟶ op X ⟶ (op Z)⟦1⟧` in `Cᵒᵖ`
(without introducing signs).

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

namespace CategoryTheory.Pretriangulated

open Category Limits Preadditive ZeroObject Opposite

variable (C : Type*) [Category C] [HasShift C ℤ]

namespace TriangleOpEquivalence

/-- The functor which sends a triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` in `C` to the triangle
`op Z ⟶ op Y ⟶ op X ⟶ (op Z)⟦1⟧` in `Cᵒᵖ` (without introducing signs). -/
@[simps]
noncomputable def functor : (Triangle C)ᵒᵖ ⥤ Triangle Cᵒᵖ where
  obj T := Triangle.mk T.unop.mor₂.op T.unop.mor₁.op
      ((opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op T.unop.obj₁) ≫
        T.unop.mor₃.op⟦(1 : ℤ)⟧')
  map {T₁ T₂} φ :=
    { hom₁ := φ.unop.hom₃.op
      hom₂ := φ.unop.hom₂.op
      hom₃ := φ.unop.hom₁.op
      comm₁ := Quiver.Hom.unop_inj φ.unop.comm₂.symm
      comm₂ := Quiver.Hom.unop_inj φ.unop.comm₁.symm
      comm₃ := by
        dsimp
        rw [assoc, ← Functor.map_comp, ← op_comp, ← φ.unop.comm₃, op_comp, Functor.map_comp,
          opShiftFunctorEquivalence_counitIso_inv_naturality_assoc]
        rfl }

/-- The functor which sends a triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` in `Cᵒᵖ` to the triangle
`Z.unop ⟶ Y.unop ⟶ X.unop ⟶ Z.unop⟦1⟧` in `C` (without introducing signs). -/
@[simps]
noncomputable def inverse : Triangle Cᵒᵖ ⥤ (Triangle C)ᵒᵖ where
  obj T := Opposite.op (Triangle.mk T.mor₂.unop T.mor₁.unop
      (((opShiftFunctorEquivalence C 1).unitIso.inv.app T.obj₁).unop ≫ T.mor₃.unop⟦(1 : ℤ)⟧'))
  map {T₁ T₂} φ := Quiver.Hom.op
    { hom₁ := φ.hom₃.unop
      hom₂ := φ.hom₂.unop
      hom₃ := φ.hom₁.unop
      comm₁ := Quiver.Hom.op_inj φ.comm₂.symm
      comm₂ := Quiver.Hom.op_inj φ.comm₁.symm
      comm₃ := Quiver.Hom.op_inj (by
        dsimp
        rw [assoc, ← opShiftFunctorEquivalence_unitIso_inv_naturality,
          ← op_comp_assoc, ← Functor.map_comp, ← unop_comp, ← φ.comm₃,
          unop_comp, Functor.map_comp, op_comp, assoc]) }

/-- The unit isomorphism of the
equivalence `triangleOpEquivalence C : (Triangle C)ᵒᵖ ≌ Triangle Cᵒᵖ` . -/
@[simps!]
noncomputable def unitIso : 𝟭 _ ≅ functor C ⋙ inverse C :=
  NatIso.ofComponents (fun T => Iso.op
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (Quiver.Hom.op_inj
        (by simp [shift_unop_opShiftFunctorEquivalence_counitIso_inv_app]))))
    (fun {T₁ T₂} f => Quiver.Hom.unop_inj (by aesop_cat))

/-- The counit isomorphism of the
equivalence `triangleOpEquivalence C : (Triangle C)ᵒᵖ ≌ Triangle Cᵒᵖ` . -/
@[simps!]
noncomputable def counitIso : inverse C ⋙ functor C ≅ 𝟭 _ :=
  NatIso.ofComponents (fun T => by
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · simp
    · simp
    · dsimp
      rw [Functor.map_id, comp_id, id_comp, Functor.map_comp,
        ← opShiftFunctorEquivalence_counitIso_inv_naturality_assoc,
        opShiftFunctorEquivalence_counitIso_inv_app_shift, ← Functor.map_comp,
        Iso.hom_inv_id_app, Functor.map_id]
      simp only [Functor.id_obj, comp_id])
    (by aesop_cat)

end TriangleOpEquivalence

/-- An anti-equivalence between the categories of triangles in `C` and in `Cᵒᵖ`.
A triangle in `Cᵒᵖ` shall be distinguished iff it correspond to a distinguished
triangle in `C` via this equivalence. -/
@[simps]
noncomputable def triangleOpEquivalence :
    (Triangle C)ᵒᵖ ≌ Triangle Cᵒᵖ where
  functor := TriangleOpEquivalence.functor C
  inverse := TriangleOpEquivalence.inverse C
  unitIso := TriangleOpEquivalence.unitIso C
  counitIso := TriangleOpEquivalence.counitIso C

end CategoryTheory.Pretriangulated
