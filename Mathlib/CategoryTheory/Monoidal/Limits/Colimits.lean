/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Sifted

/-!
# Tensor product of colimits

In this file, we apply the `PreservesColimit₂` API to the bifunctor
`curriedTensor C` on a monoidal category `C`.

Given cocones `c₁` and `c₂` for functors `F₁ : J₁ ⥤ C` and `F₂ : J₂ ⥤ C`,
we define a cocone `c₁.tensor₂ c₂` for the functor `J₁ × J₂ ⥤ C` obtained
using the tensor product on `C`, and we obtain that it is a colimit cocone
if both `c₁` and `c₂` are, and `PreservesColimit₂ F₁ F₂ (curriedTensor C)` holds.

We also introduce a definition `Cocone.tensor` which takes as an input two
cocones `c₁` and `c₂` for two functors `F₁ : J ⥤ C` and `F₂ : J ⥤ C` and
produces a cocone for `F₁ ⊗ F₂ : J ⥤ C` with point `c₁.pt ⊗ c₂.pt` and we show
that it is a colimit cocone when `PreservesColimit₂ F₁ F₂ (curriedTensor C)`
holds and `J` is sifted.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory.Limits

open MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {J J₁ J₂ : Type*} [Category* J] [Category* J₁] [Category* J₂]

section

variable {F₁ : J₁ ⥤ C} {F₂ : J₂ ⥤ C} {c₁ : Cocone F₁} {c₂ : Cocone F₂}

variable (c₁ c₂) in
/-- The external tensor product of two cocones. -/
abbrev Cocone.tensor₂ :
    Cocone (externalProduct F₁ F₂) :=
  (curriedTensor C).mapCocone₂ c₁ c₂

/-- The external tensor product of colimit cocones for functors `F₁ : J₁ ⥤ C`
and `F₂ : J₂ ⥤ C` is a colimit cocone when `PreservesColimit₂ F₁ F₂ (curriedTensor C)`
holds. -/
noncomputable def IsColimit.tensor₂ [PreservesColimit₂ F₁ F₂ (curriedTensor C)]
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    IsColimit (c₁.tensor₂ c₂) :=
  isColimitOfPreserves₂ (curriedTensor C) hc₁ hc₂

end

section

variable {F₁ F₂ : J ⥤ C} {c₁ : Cocone F₁} {c₂ : Cocone F₂}

variable (c₁ c₂) in
/-- The tensor product of two cocones. -/
@[simps!]
def Cocone.tensor : Cocone (F₁ ⊗ F₂) where
  pt := c₁.pt ⊗ c₂.pt
  ι.app j := c₁.ι.app j ⊗ₘ c₂.ι.app j

attribute [local simp] tensorHom_def in
/-- The tensor product of colimit cocones for functors `F₁ : J ⥤ C`
and `F₂ : J ⥤ C` is a colimit cocone when `PreservesColimit₂ F₁ F₂ (curriedTensor C)`
holds and `J` is sifted. -/
noncomputable def IsColimit.tensor [PreservesColimit₂ F₁ F₂ (curriedTensor C)] [IsSifted J]
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    IsColimit (c₁.tensor c₂) := by
  refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).1
    ((Functor.Final.isColimitWhiskerEquiv (Functor.diag J) _).2 (hc₁.tensor₂ hc₂))
  · exact NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp)
  · exact Cocone.ext (Iso.refl _)

end

end CategoryTheory.Limits
