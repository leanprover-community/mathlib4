/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

/-!
# The opposite of a triangulated category is triangulated

The pretriangulated structure on `Cᵒᵖ` was constructed in the file
`CategoryTheory.Triangulated.Opposite.Pretriangulated`. Here, we show
that `Cᵒᵖ` is triangulated if `C` is triangulated.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Preadditive Limits

namespace Pretriangulated

variable (C : Type*) [Category* C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Opposite

scoped instance [IsTriangulated C] : IsTriangulated Cᵒᵖ := by
  have : ∀ ⦃X₁ X₂ X₃ : C⦄ (u₁₂ : X₁ ⟶ X₂) (u₂₃ : X₂ ⟶ X₃),
    ∃ (Z₁₂ Z₂₃ Z₁₃ : C)
      (v₁₂ : Z₁₂ ⟶ X₁) (w₁₂ : X₂ ⟶ Z₁₂⟦(1 : ℤ)⟧) (h₁₂ : Triangle.mk v₁₂ u₁₂ w₁₂ ∈ distTriang C)
      (v₂₃ : Z₂₃ ⟶ X₂) (w₂₃ : X₃ ⟶ Z₂₃⟦(1 : ℤ)⟧) (h₂₃ : Triangle.mk v₂₃ u₂₃ w₂₃ ∈ distTriang C)
      (v₁₃ : Z₁₃ ⟶ X₁) (w₁₃ : X₃ ⟶ Z₁₃⟦(1 : ℤ)⟧)
        (h₁₃ : Triangle.mk v₁₃ (u₁₂ ≫ u₂₃) w₁₃ ∈ distTriang C),
        Nonempty (Triangulated.Octahedron rfl (rot_of_distTriang _ h₁₂)
          (rot_of_distTriang _ h₂₃) (rot_of_distTriang _ h₁₃)) := by
    intro X₁ X₂ X₃ u₁₂ u₂₃
    obtain ⟨Z₁₂, v₁₂, w₁₂, h₁₂⟩ := distinguished_cocone_triangle₁ u₁₂
    obtain ⟨Z₂₃, v₂₃, w₂₃, h₂₃⟩ := distinguished_cocone_triangle₁ u₂₃
    obtain ⟨Z₁₃, v₁₃, w₁₃, h₁₃⟩ := distinguished_cocone_triangle₁ (u₁₂ ≫ u₂₃)
    exact ⟨_, _, _, _, _, h₁₂, _, _, h₂₃, _, _, h₁₃, ⟨Triangulated.someOctahedron _ _ _ _⟩⟩
  refine IsTriangulated.mk' (fun X₁ X₂ X₃ u₁₂ u₂₃ ↦ ?_)
  obtain ⟨Z₁₂, Z₂₃, Z₁₃, v₁₂, w₁₂, h₁₂, v₂₃, w₂₃, h₂₃, v₁₃, w₁₃, h₁₃, ⟨H⟩⟩ :=
    this u₂₃.unop u₁₂.unop
  refine ⟨X₁, X₂, X₃, _, _, _, u₁₂, u₂₃, Iso.refl _, Iso.refl _, Iso.refl _, by simp, by simp,
    v₂₃.op, opShiftFunctorEquivalenceSymmHomEquiv w₂₃.op, ?_,
    v₁₂.op, opShiftFunctorEquivalenceSymmHomEquiv w₁₂.op, ?_,
    v₁₃.op, opShiftFunctorEquivalenceSymmHomEquiv w₁₃.op, ?_, ?_⟩
  · rw [mem_distTriang_op_iff]
    refine Pretriangulated.isomorphic_distinguished _ h₂₃ _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_
    simpa using opShiftFunctorEquivalenceSymmHomEquiv_left_inv w₂₃.op
  · rw [mem_distTriang_op_iff]
    refine Pretriangulated.isomorphic_distinguished _ h₁₂ _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_
    simpa using opShiftFunctorEquivalenceSymmHomEquiv_left_inv w₁₂.op
  · rw [mem_distTriang_op_iff]
    refine Pretriangulated.isomorphic_distinguished _ h₁₃ _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_
    simpa using opShiftFunctorEquivalenceSymmHomEquiv_left_inv w₁₃.op
  · obtain ⟨m₁, hm₁⟩ := (shiftFunctor C (1 : ℤ)).map_surjective H.m₃
    obtain ⟨m₃, hm₃⟩ := (shiftFunctor C (1 : ℤ)).map_surjective H.m₁
    exact ⟨{
      m₁ := m₁.op
      m₃ := m₃.op
      comm₁ := Quiver.Hom.unop_inj ((shiftFunctor C (1 : ℤ)).map_injective (by
        simpa [hm₁] using H.comm₄.symm))
      comm₂ := Quiver.Hom.unop_inj ((shiftFunctor C (1 : ℤ)).map_injective (by
        have := H.comm₃
        dsimp at this ⊢
        rw [← hm₁] at this
        rw [Functor.map_comp, shift_opShiftFunctorEquivalenceSymmHomEquiv_unop_assoc,
          shift_opShiftFunctorEquivalenceSymmHomEquiv_unop,
          Quiver.Hom.unop_op, Quiver.Hom.unop_op, this]))
      comm₃ := Quiver.Hom.unop_inj ((shiftFunctor C (1 : ℤ)).map_injective (by
        simpa [hm₃] using H.comm₂))
      comm₄ := Quiver.Hom.unop_inj ((shiftFunctor C (1 : ℤ)).map_injective (by
        have := H.comm₁
        rw [← hm₃] at this
        dsimp at this ⊢
        rw [Functor.map_comp, Functor.map_comp,
          shift_opShiftFunctorEquivalenceSymmHomEquiv_unop_assoc,
          shift_opShiftFunctorEquivalenceSymmHomEquiv_unop,
          Quiver.Hom.unop_op, Quiver.Hom.unop_op, this,
          ← unop_comp_assoc, opShiftFunctorEquivalence_unitIso_hom_naturality,
          unop_comp_assoc, Quiver.Hom.unop_op]))
      mem := by
        rw [← Triangle.shift_distinguished_iff _ (-1), mem_distTriang_op_iff']
        refine ⟨_, H.mem, ⟨Triangle.isoMk _ _
          ((shiftFunctorOpIso C _ _ (neg_add_cancel 1)).app _)
          (-((shiftFunctorOpIso C _ _ (neg_add_cancel 1)).app _))
          ((shiftFunctorOpIso C _ _ (neg_add_cancel 1)).app _)
          (by simp [← hm₁]) (by simp [← hm₃]) ?_⟩⟩
        have h₁ := (shiftFunctorComm Cᵒᵖ 1 (-1)).hom.naturality v₂₃.op
        have h₂ := (shiftFunctorComm Cᵒᵖ 1 (-1)).hom.naturality w₁₂.op
        dsimp at h₁ h₂ ⊢
        simp only [Int.negOnePow_neg, Int.negOnePow_one, Functor.map_comp, Category.assoc,
          Units.neg_smul, one_smul, neg_comp, Functor.map_neg, comp_neg, neg_inj]
        rw [reassoc_of% h₁, shiftFunctor_op_map v₂₃.op (-1) 1,
          ← Functor.map_comp, Category.assoc, Category.assoc, Iso.inv_hom_id_app,
          Functor.map_comp, opShiftFunctorEquivalenceSymmHomEquiv_apply,
          Functor.map_comp_assoc, reassoc_of% h₂,
          shift_opShiftFunctorEquivalence_counitIso_inv_app _ _ _ (neg_add_cancel 1)]
        simp [← Functor.map_comp]}⟩

end Opposite

end Pretriangulated

end CategoryTheory
