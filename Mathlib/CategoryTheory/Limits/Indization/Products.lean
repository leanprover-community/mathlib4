/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.Limits.Indization.FilteredColimits

/-!
# Ind-objects are closed under products

We show that if `C` admits products indexed by `α`, then `IsIndObject` is closed under taking
products in `Cᵒᵖ ⥤ Type v` indexed by `α`. This will imply that the functor `Ind C ⥤ Cᵒᵖ ⥤ Type v`
creates products indexed by `α` and that the functor `C ⥤ Ind C` preserves them.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Prop. 6.1.16(ii)
-/

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {α : Type v}

theorem isIndObject_pi (h : ∀ (g : α → C), IsIndObject (∏ᶜ yoneda.obj ∘ g))
    (f : α → Cᵒᵖ ⥤ Type v) (hf : ∀ a, IsIndObject (f a)) : IsIndObject (∏ᶜ f) := by
  let F := fun a => (hf a).presentation.F ⋙ yoneda
  suffices (∏ᶜ f ≅ colimit (pointwiseProduct F)) from
    (isIndObject_colimit _ _ (fun i => h _)).map this.inv
  refine Pi.mapIso (fun s => ?_) ≪≫ (asIso (colimitPointwiseProductToProductColimit F)).symm
  exact IsColimit.coconePointUniqueUpToIso (hf s).presentation.isColimit (colimit.isColimit _)

theorem isIndObject_limit_of_discrete (h : ∀ (g : α → C), IsIndObject (∏ᶜ yoneda.obj ∘ g))
    (F : Discrete α ⥤ Cᵒᵖ ⥤ Type v) (hF : ∀ a, IsIndObject (F.obj a)) : IsIndObject (limit F) :=
  IsIndObject.map (Pi.isoLimit _).hom (isIndObject_pi h _ (fun a => hF ⟨a⟩))

theorem isIndObject_limit_of_discrete_of_hasLimitsOfShape [HasLimitsOfShape (Discrete α) C]
    (F : Discrete α ⥤ Cᵒᵖ ⥤ Type v) (hF : ∀ a, IsIndObject (F.obj a)) : IsIndObject (limit F) :=
  isIndObject_limit_of_discrete (fun g => (isIndObject_limit_comp_yoneda (Discrete.functor g)).map
      (HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete g yoneda)).hom) F hF

end CategoryTheory.Limits
