/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-!
# Day functors to type

In this file, we study day functors `Cᵒᵖ ⊛⥤ Type u₁`, i.e presheaves
with the Day convolution monoidal structure when `C` is an `u₁`-small category.
Such restriction on size is necessary in order to obtain existence of
relevant Kan extensions in `Type u₁`.


## Implementation

The way we state and prove monoidality of the Yoneda embedding is by registering
a `LawfulDayConvolutionMonoidalCategoryStruct Cᵒᵖ (Type v₁) C`. An actual
`Functor.Monoidal` instance on `yoneda ⋙ (DayFunctor.equiv Cᵒᵖ (Type v₁))` will
then follow from the general fact that whenever there is a
`LawfulDayConvolutionMonoidalCategoryStruct C V D`, the induced functor
`D ⥤ (C ⊛⥤ V)` is monoidal.

## TODOs
- Construct an explicit model of the internal hom in terms of the
Yoneda embedding.
- Show that left Kan extension along Yoneda of a monoidal functor
remains monoidal.
-/

universe v₁ u₁

namespace CategoryTheory.MonoidalCategory.DayFunctor
open scoped ExternalProduct

section

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

open Opposite

@[simps! ι convolutionExtensionUnit unitUnit]
instance : LawfulDayConvolutionMonoidalCategoryStruct Cᵒᵖ (Type v₁) C where
  ι := yoneda
  convolutionExtensionUnit c c' := { app X := fun Y ↦ Y.1 ⊗ₘ Y.2 }
  unitUnit := fun _ ↦ 𝟙 _
  isPointwiseLeftKanExtensionConvolutionExtensionUnit c c' c'' :=
    { desc s v := s.ι.app
        (CostructuredArrow.mk (Y := (op c, op c')) v.op)
        (𝟙 _, 𝟙 _)
      fac s j := by
        ext ⟨t, t'⟩
        let u :
            (CostructuredArrow.mk (Y := (op c, op c'))
              ((t.op ⊗ₘ t'.op) ≫ j.hom)) ⟶ j :=
          CostructuredArrow.homMk (t.op, t'.op)
        haveI := congr_arg (fun t ↦ t (𝟙 c, 𝟙 c')) (s.w u)
        dsimp at this
        simpa using this.symm
      uniq s m hm := by
        ext x
        simpa using congr_arg (fun t ↦ t (𝟙 c, 𝟙 c')) <|
          hm (CostructuredArrow.mk (Y := (op c, op c')) x.op) }
  isPointwiseLeftKanExtensionUnitUnit c :=
    { desc s v := s.ι.app (CostructuredArrow.mk (Y := default) v.op) PUnit.unit
      fac s j := by
        dsimp
        let u : CostructuredArrow.mk (Y := default) (𝟙 (𝟙_ Cᵒᵖ) ≫ j.hom) ⟶ j :=
          CostructuredArrow.homMk (Discrete.eqToHom rfl)
        simpa using (s.w u).symm
      uniq s m hm := by
        ext x
        simpa using congr_fun
          (hm (CostructuredArrow.mk (Y := default) x.op)) PUnit.unit }
  convolutionExtensionUnit_comp_ι_map_tensorHom_app := by aesop_cat
  convolutionExtensionUnit_comp_ι_map_whiskerLeft_app _ _ _ _ _ _ := by
    ext ⟨t, t'⟩
    simp [tensorHom_def]
  convolutionExtensionUnit_comp_ι_map_whiskerRight_app _ _ _ _ := by
    ext ⟨t, t'⟩
    simp [tensorHom_def']
  associator_hom_unit_unit _ _ _ _ _ _ := by
    ext ⟨⟨t, t'⟩, t''⟩
    simp
  leftUnitor_hom_unit_app _ _ := by
    ext ⟨_, _⟩
    simp
  rightUnitor_hom_unit_app _ _ := by
    ext ⟨_, _⟩
    simp

/-- An abbreviation for the "monoidal" version of Yoneda, taking
values in Day functors rather than presheaves. -/
@[simps!]
def dayYoneda : C ⥤ (Cᵒᵖ ⊛⥤ Type v₁) := yoneda ⋙ (equiv Cᵒᵖ _).inverse

end

section SmallCategory

variable (C : Type u₁) [SmallCategory C] [MonoidalCategory C]

-- We need to help type class resolution here.
local instance : ∀ (v : Type u₁),
    Limits.PreservesColimitsOfSize.{u₁, u₁} (tensorRight v) := fun _ ↦
  ⟨⟨Limits.preservesColimit_of_braided_and_preservesColimit_tensor_left _ _⟩⟩

local instance : ∀ (v : Type u₁),
    Limits.PreservesColimitsOfSize.{0, u₁} (tensorRight v) := fun _ ↦
  ⟨⟨Limits.preservesColimit_of_braided_and_preservesColimit_tensor_left _ _⟩⟩

open LawfulDayConvolutionMonoidalCategoryStruct DayFunctor in
noncomputable instance : (dayYoneda C).Monoidal :=
  inferInstanceAs <| (ι Cᵒᵖ (Type u₁) C ⋙ (equiv _ _).inverse).Monoidal

section lemmas

open Opposite Functor LawfulDayConvolutionMonoidalCategoryStruct
open scoped Prod

variable {C}

@[reassoc]
lemma η_dayYoneda_μ (c c' : C) (x y : Cᵒᵖ) :
    (η (dayYoneda C|>.obj c) (dayYoneda C|>.obj c')).app (x, y) ≫
    (LaxMonoidal.μ (dayYoneda C) c c').natTrans.app (x ⊗ y) =
    (convolutionExtensionUnit Cᵒᵖ (Type u₁) c c').app (x, y) :=
  η_ι_equivInverse_μ Cᵒᵖ (Type u₁) c c' _ _

@[simp]
lemma η_dayYoneda_μ_apply (c c' : C) (x y : Cᵒᵖ)
    (f₁ : unop x ⟶ c) (f₂ : unop y ⟶ c') :
    (LaxMonoidal.μ (dayYoneda C) c c').natTrans.app (x ⊗ y)
      ((η (dayYoneda C|>.obj c) (dayYoneda C|>.obj c')).app (x, y)
        (f₁ ×ₘ f₂)) =
    f₁ ⊗ₘ f₂ :=
  congr_fun (η_ι_equivInverse_μ Cᵒᵖ (Type u₁) c c' _ _) (f₁ ×ₘ f₂)

@[reassoc]
lemma convolutionExtensionUnit_dayYoneda_δ (c c' : C) (x y : Cᵒᵖ) :
    (convolutionExtensionUnit Cᵒᵖ (Type u₁) c c').app (x, y) ≫
    (OplaxMonoidal.δ (dayYoneda C) c c').natTrans.app (x ⊗ y) =
  (η (dayYoneda C|>.obj c) (dayYoneda C|>.obj c')).app (x, y) :=
  convolutionExtensionUnit_ι_equivInverse_δ Cᵒᵖ (Type u₁) c c' _ _

@[simp]
lemma convolutionExtensionUnit_dayYoneda_δ_apply (c c' : C) (x y : Cᵒᵖ)
    (f₁ : unop x ⟶ c) (f₂ : unop y ⟶ c') :
    (OplaxMonoidal.δ (dayYoneda C) c c').natTrans.app (x ⊗ y) (f₁ ⊗ₘ f₂) =
    (η (dayYoneda C|>.obj c) (dayYoneda C|>.obj c')).app (x, y) (f₁ ×ₘ f₂) :=
  congr_fun (convolutionExtensionUnit_ι_equivInverse_δ Cᵒᵖ (Type u₁) c c' _ _)
    (f₁ ×ₘ f₂)

variable (C)

@[reassoc]
lemma ν_dayYoneda_ε :
    ν Cᵒᵖ (Type u₁) ≫ (LaxMonoidal.ε (dayYoneda C)).natTrans.app (𝟙_ Cᵒᵖ) =
    unitUnit Cᵒᵖ (Type u₁) C :=
  ν_ι_equivInverse_ε Cᵒᵖ (Type u₁) _

@[simp]
lemma ν_dayYoneda_ε_punit :
  (LaxMonoidal.ε (dayYoneda C)).natTrans.app (𝟙_ Cᵒᵖ)
    (ν Cᵒᵖ (Type u₁) PUnit.unit) = 𝟙 _ :=
  congr_fun (ν_ι_equivInverse_ε Cᵒᵖ (Type u₁) _) PUnit.unit

@[reassoc]
lemma ν_dayYoneda_η :
    unitUnit Cᵒᵖ (Type u₁) C ≫
      (OplaxMonoidal.η (dayYoneda C)).natTrans.app (𝟙_ Cᵒᵖ) =
    ν Cᵒᵖ (Type u₁) :=
  ν_ι_equivInverse_η Cᵒᵖ (Type u₁) _

@[simp]
lemma ν_dayYoneda_η_punit :
    (OplaxMonoidal.η (dayYoneda C)).natTrans.app (𝟙_ Cᵒᵖ) (𝟙 (𝟙_ C)) =
    ν Cᵒᵖ (Type u₁) PUnit.unit :=
  congr_fun (ν_ι_equivInverse_η Cᵒᵖ (Type u₁) _) PUnit.unit

end lemmas

end SmallCategory

end CategoryTheory.MonoidalCategory.DayFunctor
