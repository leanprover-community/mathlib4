/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

#align_import category_theory.limits.mono_coprod from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!

# Categories where inclusions into coproducts are monomorphisms

If `C` is a category, the class `MonoCoprod C` expresses that left
inclusions `A ⟶ A ⨿ B` are monomorphisms when `HasCoproduct A B`
is satisfied. If it is so, it is shown that right inclusions are
also monomorphisms.

TODO @joelriou: show that if `X : I → C` and `ι : J → I` is an injective map,
then the canonical morphism `∐ (X ∘ ι) ⟶ ∐ X` is a monomorphism.

TODO: define distributive categories, and show that they satisfy `MonoCoprod`, see
<https://ncatlab.org/toddtrimble/published/distributivity+implies+monicity+of+coproduct+inclusions>

-/


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

universe u

namespace CategoryTheory

namespace Limits

variable (C : Type*) [Category C]

/-- This condition expresses that inclusion morphisms into coproducts are monomorphisms. -/
class MonoCoprod : Prop where
  /-- the left inclusion of a colimit binary cofan is mono -/
  binaryCofan_inl : ∀ ⦃A B : C⦄ (c : BinaryCofan A B) (_ : IsColimit c), Mono c.inl
#align category_theory.limits.mono_coprod CategoryTheory.Limits.MonoCoprod

variable {C}

instance (priority := 100) monoCoprodOfHasZeroMorphisms [HasZeroMorphisms C] : MonoCoprod C :=
  ⟨fun A B c hc => by
    haveI : IsSplitMono c.inl :=
      IsSplitMono.mk' (SplitMono.mk (hc.desc (BinaryCofan.mk (𝟙 A) 0)) (IsColimit.fac _ _ _))
    infer_instance⟩
#align category_theory.limits.mono_coprod_of_has_zero_morphisms CategoryTheory.Limits.monoCoprodOfHasZeroMorphisms

namespace MonoCoprod

theorem binaryCofan_inr {A B : C} [MonoCoprod C] (c : BinaryCofan A B) (hc : IsColimit c) :
    Mono c.inr := by
  haveI hc' : IsColimit (BinaryCofan.mk c.inr c.inl) :=
    BinaryCofan.IsColimit.mk _ (fun f₁ f₂ => hc.desc (BinaryCofan.mk f₂ f₁))
      (by aesop_cat) (by aesop_cat)
      (fun f₁ f₂ m h₁ h₂ => BinaryCofan.IsColimit.hom_ext hc (by aesop_cat) (by aesop_cat))
  exact binaryCofan_inl _ hc'
#align category_theory.limits.mono_coprod.binary_cofan_inr CategoryTheory.Limits.MonoCoprod.binaryCofan_inr

instance {A B : C} [MonoCoprod C] [HasBinaryCoproduct A B] : Mono (coprod.inl : A ⟶ A ⨿ B) :=
  binaryCofan_inl _ (colimit.isColimit _)

instance {A B : C} [MonoCoprod C] [HasBinaryCoproduct A B] : Mono (coprod.inr : B ⟶ A ⨿ B) :=
  binaryCofan_inr _ (colimit.isColimit _)

theorem mono_inl_iff {A B : C} {c₁ c₂ : BinaryCofan A B} (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    Mono c₁.inl ↔ Mono c₂.inl := by
  suffices
    ∀ (c₁ c₂ : BinaryCofan A B) (_ : IsColimit c₁) (_ : IsColimit c₂) (_ : Mono c₁.inl),
      Mono c₂.inl
    by exact ⟨fun h₁ => this _ _ hc₁ hc₂ h₁, fun h₂ => this _ _ hc₂ hc₁ h₂⟩
  intro c₁ c₂ hc₁ hc₂
  intro
  simpa only [IsColimit.comp_coconePointUniqueUpToIso_hom] using
    mono_comp c₁.inl (hc₁.coconePointUniqueUpToIso hc₂).hom
#align category_theory.limits.mono_coprod.mono_inl_iff CategoryTheory.Limits.MonoCoprod.mono_inl_iff

theorem mk' (h : ∀ A B : C, ∃ (c : BinaryCofan A B) (_ : IsColimit c), Mono c.inl) : MonoCoprod C :=
  ⟨fun A B c' hc' => by
    obtain ⟨c, hc₁, hc₂⟩ := h A B
    simpa only [mono_inl_iff hc' hc₁] using hc₂⟩
#align category_theory.limits.mono_coprod.mk' CategoryTheory.Limits.MonoCoprod.mk'

instance monoCoprodType : MonoCoprod (Type u) :=
  MonoCoprod.mk' fun A B => by
    refine' ⟨BinaryCofan.mk (Sum.inl : A ⟶ Sum A B) Sum.inr, _, _⟩
    · exact BinaryCofan.IsColimit.mk _
        (fun f₁ f₂ x => by
          rcases x with x | x
          exacts [f₁ x, f₂ x])
        (fun f₁ f₂ => by rfl)
        (fun f₁ f₂ => by rfl)
        (fun f₁ f₂ m h₁ h₂ => by
          funext x
          rcases x with x | x
          · exact congr_fun h₁ x
          · exact congr_fun h₂ x)
    · rw [mono_iff_injective]
      intro a₁ a₂ h
      simpa using h
#align category_theory.limits.mono_coprod.mono_coprod_type CategoryTheory.Limits.MonoCoprod.monoCoprodType

end MonoCoprod

end Limits

end CategoryTheory
