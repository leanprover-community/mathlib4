/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Presentable.StrongGenerator
import Mathlib.CategoryTheory.Generator.Presheaf
import Mathlib.CategoryTheory.Generator.Type
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# Categories of presheaves are locally presentable

-/

universe w v v' u u'

namespace CategoryTheory

open Opposite Limits

instance (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalPresentable PUnit.{w + 1} κ where
  preservesColimitOfShape J _ _ := by
    let e : coyoneda.obj (op (PUnit.{w + 1})) ≅ 𝟭 _ :=
      NatIso.ofComponents (fun X ↦ Equiv.toIso
        { toFun f := f .unit
          invFun x _ := x })
    exact preservesColimitsOfShape_of_natIso e.symm

namespace Presheaf

attribute [local simp] freeYonedaHomEquiv_comp in
instance {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
    [HasColimitsOfSize.{w, w} A] [HasCoproducts.{v} A]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] (X : C) (M : A)
    [IsCardinalPresentable M κ] :
    IsCardinalPresentable (freeYoneda X M) κ := by
  let e : coyoneda.obj (op (freeYoneda X M)) ≅
      (evaluation Cᵒᵖ A).obj (op X) ⋙ coyoneda.obj (op M) ⋙ uliftFunctor.{u} :=
    NatIso.ofComponents (fun P ↦ Equiv.toIso (freeYonedaHomEquiv.trans Equiv.ulift.symm))
  constructor
  intro J _ _
  have := preservesColimitsOfShape_of_isCardinalPresentable M κ J
  exact preservesColimitsOfShape_of_natIso e.symm

variable (C : Type w) [SmallCategory C]

instance (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalLocallyPresentable (Cᵒᵖ ⥤ Type w) κ := by
  rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
  have := isSeparating (C := C) (S := fun (_ : Unit) ↦ PUnit.{w + 1}) (by
    rw [Set.range_const]
    exact Types.isSeparator_punit)
  refine ⟨_, inferInstance, isStrongGenerator_iff.2 ⟨this, ?_⟩, ?_⟩
  · rintro P₁ P₂ i _ h
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨X⟩
    rw [isIso_iff_bijective]
    constructor
    · rw [← mono_iff_injective]
      infer_instance
    · intro y
      obtain ⟨φ, hφ⟩ := h (⟨freeYoneda X PUnit, ⟨X, .unit⟩, by simp⟩)
        (freeYonedaHomEquiv.2 (fun _ ↦ y))
      obtain ⟨φ, rfl⟩ := freeYonedaHomEquiv.symm.surjective φ
      dsimp at hφ
      rw [freeYonedaHomEquiv_symm_comp, EmbeddingLike.apply_eq_iff_eq] at hφ
      exact ⟨φ .unit, congr_fun hφ .unit⟩
  · rintro ⟨P, hP⟩
    simp only [Set.mem_range, Prod.exists, exists_const] at hP
    obtain ⟨X, rfl⟩ := hP
    infer_instance

instance : IsLocallyPresentable.{w} (Cᵒᵖ ⥤ Type w) where
  exists_cardinal :=
    ⟨_, Cardinal.fact_isRegular_aleph0, inferInstance⟩

end Presheaf

end CategoryTheory
