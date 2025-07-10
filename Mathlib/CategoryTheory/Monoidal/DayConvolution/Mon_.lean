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
In such a situation, we show that given a lax monoidal functor `F : C ⥤ V`,
there is a canonical monoid object structure on `F` when the
latter is interpreted as an object of `C ⊛⥤ V`. Conversely, we
show that any such object admits a lax monoidal structure on their
underlying functor. We show that this defines an equivalence
(for `F : C ⊛⥤ V`) between lax monoidal structures on `F.functor` and internal
monoid structures on `F`.
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
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d)
        (tensorRight v)]
    [∀ (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

section asMon_

variable (F : C ⥤ V) [F.LaxMonoidal]

instance mon_ClassOfLaxMonoidal : Mon_Class (mk F) where
  one := unitDesc <| Functor.LaxMonoidal.ε F
  mul :=
    tensorDesc <|
      { app x := Functor.LaxMonoidal.μ F _ _
        naturality {x y} f := by
          simp [tensorHom_def] }
  one_mul := by
    ext1
    apply Functor.hom_ext_of_isLeftKanExtension
      (𝟙_ (C ⊛⥤ V) ⊗ .mk F).functor (unitLeft (DayFunctor.mk F))
    ext
    dsimp
    simp only [Category.assoc, η_app_comp_whiskerRight_natTrans_app_tensor_assoc,
      externalProductBifunctor_obj_obj, η_comp_tensorDesc_app,
      ← comp_whiskerRight_assoc, ν_comp_unitDesc]
    rw [DayFunctor.ν_η_leftUnitor]
    simp
  mul_one := by
    ext1
    apply Functor.hom_ext_of_isLeftKanExtension
      (DayFunctor.mk F ⊗ 𝟙_ (C ⊛⥤ V)).functor (unitRight <| DayFunctor.mk F)
    ext
    dsimp
    simp only [Category.assoc, η_app_comp_whiskerLeft_natTrans_app_tensor_assoc,
      externalProductBifunctor_obj_obj, η_comp_tensorDesc_app,
      ← whiskerLeft_comp_assoc, ν_comp_unitDesc]
    rw [DayFunctor.ν_η_rightUnitor]
    simp
  mul_assoc := by
    ext1
    apply Functor.hom_ext_of_isLeftKanExtension
      ((mk F ⊗ mk F) ⊗ mk F).functor
        (η (_ ⊗ _) _)
    letI :
      ((mk F ⊗ mk F).functor ⊠ (mk F).functor).IsLeftKanExtension
        (ExternalProduct.extensionUnitLeft _ (η _ _) _) :=
      isLeftKanExtensionExtensionUnitLeft (mk F) (mk F) (mk F).functor
    apply Functor.hom_ext_of_isLeftKanExtension
      ((DayFunctor.mk F ⊗ DayFunctor.mk F).functor ⊠ (DayFunctor.mk F).functor)
        (ExternalProduct.extensionUnitLeft (mk F ⊗ mk F).functor (η _ _) _)
    ext ⟨⟨x, y⟩, z⟩
    dsimp
    simp only [whiskerLeft_id, Category.comp_id,
      η_app_comp_whiskerRight_natTrans_app_tensor_assoc,
      externalProductBifunctor_obj_obj, η_comp_tensorDesc_app,
      ← comp_whiskerRight_assoc]
    rw [η_η_associator_hom_assoc]
    simp [← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]
lemma η_comp_mul (x y : C) :
    (η (mk F) (mk F)).app (x, y) ≫
      (Mon_Class.mul (X := mk F)).natTrans.app (x ⊗ y) =
    Functor.LaxMonoidal.μ F x y := by
  simp [Mon_Class.mul]

@[reassoc (attr := simp)]
lemma ν_comp_one :
    ν C V ≫ (Mon_Class.one (X := mk F)).natTrans.app (𝟙_ C) =
    Functor.LaxMonoidal.ε F := by
  simp [Mon_Class.one]

end asMon_

section toLaxMonoidal

open scoped Prod

variable (F : C ⊛⥤ V) [Mon_Class F]

@[simps]
instance laxMonoidalOfMon_Class : F.functor.LaxMonoidal where
  μ x y := (η F F).app (x, y) ≫ (Mon_Class.mul (X := F)).natTrans.app (x ⊗ y)
  ε := ν C V ≫ (Mon_Class.one (X := F)).natTrans.app _
  associativity x y z := by
    haveI :=
      ((η F F).app (x, y) ▷ F.functor.obj z ≫
        (η (F ⊗ F) F).app (x ⊗ y, z)) ≫=
        congrArg (·.natTrans.app _) (Mon_Class.mul_assoc F)
    dsimp at this
    simpa using this =≫ F.functor.map (α_ x y z).hom
  left_unitality x := by
    haveI := ((unitLeft F).app x) ≫=
      congrArg (·.natTrans.app _) (Mon_Class.one_mul F)
    dsimp at this
    simpa using this.symm =≫ (F.functor.map (λ_ x).hom)
  right_unitality x := by
    haveI := ((unitRight F).app x) ≫=
      congrArg (·.natTrans.app _) (Mon_Class.mul_one F)
    dsimp at this
    simpa using this.symm =≫ F.functor.map (ρ_ x).hom

end toLaxMonoidal

/-- Lax monoidal structures on `F.functor` correspond bijectively with
`Mon_Class` structures on `F`, realizing the slogan that "monoids for Day
convolutions correspond to lax monoidal functors". -/
def mon_ClassLaxMonoidalEquiv (F : C ⊛⥤ V) :
    Mon_Class F ≃ F.functor.LaxMonoidal where
  toFun _ := by infer_instance
  invFun _ := inferInstanceAs <| Mon_Class (mk F.functor)
  left_inv x := by
    ext1
    dsimp [Mon_Class.mul]
    apply tensor_hom_ext
    intro x y
    simp [externalProductBifunctor_obj_obj, Functor.comp_obj, tensor_obj,
      η_comp_tensorDesc_app]
  right_inv x := by
    ext1
    · simp
    · ext x x'
      simp [Mon_Class.mul]

end CategoryTheory.MonoidalCategory.DayFunctor

end
