/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.Limits.Indization.FilteredColimits

/-!
# Ind-objects are closed under products (sometimes)
-/

universe v u

namespace CategoryTheory.Limits

variable {C : Type v} [SmallCategory C] {α : Type v}

theorem isIndObject_pi (h : ∀ (g : α → C), IsIndObject (∏ᶜ yoneda.obj ∘ g))
    (f : α → Cᵒᵖ ⥤ Type v) (hf : ∀ a, IsIndObject (f a)) : IsIndObject (∏ᶜ f) := by
  let F := fun a => (hf a).presentation.F ⋙ yoneda
  suffices (∏ᶜ f ≅ colimit (pointwiseProduct F)) from
    (isIndObject_colimit _ _ (fun i => h _)).map this.inv
  have := isIso_colimitPointwiseProductToProductColimit F
  refine Pi.mapIso (fun s => ?_) ≪≫ (asIso (colimitPointwiseProductToProductColimit F)).symm
  exact IsColimit.coconePointUniqueUpToIso (hf s).presentation.isColimit (colimit.isColimit _)

theorem isIndObject_pi_of_hasLimitsOfShape [HasLimitsOfShape (Discrete α) C]
    (f : α → Cᵒᵖ ⥤ Type v) (hf : ∀ a, IsIndObject (f a)) : IsIndObject (∏ᶜ f) :=
  isIndObject_pi (fun g => (isIndObject_limit_of_hasLimit (Discrete.functor g)).map
      (HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete g yoneda)).hom) f hf

end CategoryTheory.Limits
