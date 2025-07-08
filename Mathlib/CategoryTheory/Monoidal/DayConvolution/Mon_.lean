/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# Monoid objects internal to Day convolution

Let `C` and `V` be monoidal categories such that we
have a Day convolution monoidal structure on `C ⊛⥤ V` (the
type alias `CategoryTheory.MonoidalCategory.DayFunctor` for
functors endowed with the Day convolution monoidal structure).

In this file, we show that given a lax monoidal functor `F : C ⥤ V`,
there is a canonical monoid object structure on `F` when the
latter is interpreted as an object of `C ⊛⥤ V`. Conversely, we
show that any such object admits a lax monoidal structure on their
underlying functor.
-/

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.MonoidalCategory.DayFunctor
open scoped ExternalProduct DayFunctor
variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]

variable
    [∀ (F G : C ⥤ V),
      (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
        (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d)
        (tensorRight v)]
    [∀ (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

section asMon_

variable (F : C ⥤ V) [F.LaxMonoidal]

open LawfulDayConvolutionMonoidalCategoryStruct in
def mulOfLaxMonoidal :
    (DayFunctor.mk F) ⊗ (DayFunctor.mk F) ⟶ (DayFunctor.mk F) :=
  tensorDesc <|
    { app x := Functor.LaxMonoidal.μ F _ _
      naturality {x y} f := by
        simp [tensorHom_def] }

@[reassoc (attr := simp)]
lemma η_comp_mulOfLaxMonoidal (x y : C) :
    (η (.mk F) (.mk F)).app (x, y) ≫
      (mulOfLaxMonoidal F).natTrans.app (x ⊗ y) =
    (Functor.LaxMonoidal.μ F x y) := by
  simp [mulOfLaxMonoidal]

def unitOfLaxMonoidal : (𝟙_ (C ⊛⥤ V)) ⟶ (DayFunctor.mk F) :=
  unitDesc <| Functor.LaxMonoidal.ε F

@[reassoc (attr := simp)]
lemma ν_comp_unitOfLaxMonoidal :
    (ν C V) ≫ (unitOfLaxMonoidal F).natTrans.app (𝟙_ C) =
    Functor.LaxMonoidal.ε F := by
  simp [unitOfLaxMonoidal]

instance : Mon_Class (DayFunctor.mk F) where
  one := unitOfLaxMonoidal F
  mul := mulOfLaxMonoidal F
  one_mul := by
    rw [← cancel_epi (λ_ (DayFunctor.mk F)).inv, Iso.inv_hom_id]

    
    -- apply tensor_hom_ext
    -- intro x y
    -- dsimp
    -- simp
  mul_one := by 
    sorry
  mul_assoc := by 
    sorry

end asMon_

section toLaxMonoidal

end toLaxMonoidal

end CategoryTheory.MonoidalCategory.DayFunctor

end
