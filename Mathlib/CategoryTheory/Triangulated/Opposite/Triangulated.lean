/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

/-!
# The opposite of a triangulated category is triangulated

-/

namespace CategoryTheory

namespace Pretriangulated

variable (C : Type*) [Category C] [HasShift C ℤ]
  [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C]

namespace Opposite

set_option maxHeartbeats 600000 in
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
  apply IsTriangulated.mk'
  intros X₁ X₂ X₃ u₁₂ u₂₃
  obtain ⟨Z₁₂, Z₂₃, Z₁₃, v₁₂, w₁₂, h₁₂, v₂₃, w₂₃, h₂₃, v₁₃, w₁₃, h₁₃, ⟨H⟩⟩ :=
    this u₂₃.unop u₁₂.unop
  refine ⟨X₁, X₂, X₃, _, _, _, u₁₂, u₂₃, Iso.refl _, Iso.refl _, Iso.refl _, by simp, by simp,
    v₂₃.op, opShiftFunctorEquivalence_symm_homEquiv 1 _ _ w₂₃.op, ?_,
    v₁₂.op, opShiftFunctorEquivalence_symm_homEquiv 1 _ _ w₁₂.op, ?_,
    v₁₃.op, opShiftFunctorEquivalence_symm_homEquiv 1 _ _ w₁₃.op, ?_, ?_⟩
  · rw [mem_distTriang_op_iff]
    refine Pretriangulated.isomorphic_distinguished _ h₂₃ _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_
    simpa using opShiftFunctorEquivalence_symm_homEquiv_left_inv w₂₃.op
  · rw [mem_distTriang_op_iff]
    refine Pretriangulated.isomorphic_distinguished _ h₁₂ _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_
    simpa using opShiftFunctorEquivalence_symm_homEquiv_left_inv w₁₂.op
  · rw [mem_distTriang_op_iff]
    refine Pretriangulated.isomorphic_distinguished _ h₁₃ _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_
    simpa using opShiftFunctorEquivalence_symm_homEquiv_left_inv w₁₃.op
  · obtain ⟨m₁, hm₁⟩ := (shiftFunctor C (1 : ℤ)).map_surjective H.m₃
    obtain ⟨m₃, hm₃⟩ := (shiftFunctor C (1 : ℤ)).map_surjective H.m₁
    exact
     ⟨{ m₁ := m₁.op
        m₃ := m₃.op
        comm₁ := by
          apply Quiver.Hom.unop_inj
          apply (shiftFunctor C (1 : ℤ)).map_injective
          simpa [← hm₁] using H.comm₄.symm
        comm₂ := by
          have eq := H.comm₃
          dsimp at eq
          rw [← eq, ← hm₁, op_comp, opShiftFunctorEquivalence_symm_homEquiv_apply,
            opShiftFunctorEquivalence_symm_homEquiv_apply]
          simp only [Functor.id_obj, opShiftFunctorEquivalence_inverse,
            opShiftFunctorEquivalence_functor,
            Functor.comp_obj, Functor.op_obj, Functor.map_comp]
          erw [← NatTrans.naturality_assoc]
          rfl
        comm₃ := by
          apply Quiver.Hom.unop_inj
          apply (shiftFunctor C (1 : ℤ)).map_injective
          simpa [← hm₃] using H.comm₂
        comm₄ := by
          have eq := congr_arg Quiver.Hom.op H.comm₁
          dsimp at eq
          simp only [Opposite.op_unop, Triangle.mk_obj₁]
          rw [opShiftFunctorEquivalence_symm_homEquiv_apply,
            opShiftFunctorEquivalence_symm_homEquiv_apply, assoc, ← Functor.map_comp,
            ← eq, ← hm₃, Functor.map_comp]
          erw [← NatTrans.naturality_assoc]
          rfl
        mem := by
          rw [← Triangle.shift_distinguished_iff _ (-1), mem_distTriang_op_iff']
          refine ⟨_, H.mem, ⟨?_⟩⟩
          refine Triangle.isoMk _ _
            ((shiftFunctorOpIso C _ _ (neg_add_cancel 1)).app _)
            (-((shiftFunctorOpIso C _ _ (neg_add_cancel 1)).app _))
            ((shiftFunctorOpIso C _ _ (neg_add_cancel 1)).app _) ?_ ?_ ?_
          · dsimp
            simp [← hm₁]
          · dsimp
            simp [← hm₃]
          · dsimp
            simp only [Int.negOnePow_neg, Int.negOnePow_one, Functor.map_comp, assoc,
              one_smul, neg_comp, comp_neg, Functor.map_neg, neg_inj, Units.neg_smul]
            erw [(shiftFunctorComm Cᵒᵖ 1 (-1)).hom.naturality_assoc v₂₃.op]
            dsimp
            rw [shiftFunctor_op_map _ _ (neg_add_cancel 1) v₂₃.op]
            erw [opShiftFunctorEquivalence_symm_homEquiv_apply]
            simp
            nth_rewrite 1 [← Functor.map_comp]
            rw [Iso.inv_hom_id_app]
            simp
            have eq := (shiftFunctorComm Cᵒᵖ 1 (-1)).hom.naturality w₁₂.op
            dsimp at eq
            rw [reassoc_of% eq]
            rw [shiftFunctor_op_map _ _ (neg_add_cancel 1) w₁₂.op]
            simp only [← Functor.map_comp_assoc, ← Functor.map_comp, assoc]
            erw [Iso.inv_hom_id_app_assoc]
            simp only [Functor.op_obj, Opposite.unop_op, Opposite.op_unop,
              Quiver.Hom.unop_op, Functor.map_comp, ← assoc]
            congr 2
            simp only [assoc]
            rw [shiftFunctorComm_hom_app_of_add_eq_zero _ _ (add_neg_cancel 1)]
            simp only [Functor.comp_obj, Functor.id_obj, assoc]
            rw [shiftFunctorCompIsoId_op_hom_app]
            rw [shiftFunctorCompIsoId_op_inv_app]
            simp only [shiftFunctor_op_map _ _ (neg_add_cancel 1)]
            simp only [shiftFunctor_op_map _ _ (add_neg_cancel 1)]
            simp
            rw [opShiftFunctorEquivalence_counitIso_inv_app _ _ _ (add_neg_cancel 1)]
            rw [opShiftFunctorEquivalence_counitIso_inv_app _ _ _ (add_neg_cancel 1)]
            simp only [Functor.id_obj, Functor.comp_obj, unop_comp, Opposite.unop_op,
              Quiver.Hom.unop_op, Functor.map_comp, op_comp, assoc]
            simp only [← op_comp, ← op_comp_assoc, assoc, ← Functor.map_comp,
              ← Functor.map_comp_assoc, ← unop_comp, ← unop_comp_assoc]
            rw [Iso.inv_hom_id_app]
            rw [Iso.inv_hom_id_app]
            simp only [Functor.op_obj, Opposite.unop_op, unop_id, Functor.map_id, id_comp,
              op_comp, assoc]
            simp only [← assoc];congr 1; simp only [assoc]
            rw [shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app]
            simp only [← op_comp_assoc, ← op_comp, assoc, Iso.inv_hom_id_app,
              Functor.id_obj, comp_id]
            simp
            rw [← op_comp]
            erw [(shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)).hom.naturality]
            rfl }⟩


end Opposite

end Pretriangulated

end CategoryTheory
