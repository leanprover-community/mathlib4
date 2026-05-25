/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.BifunctorCokernel
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Tensor products of cokernels

Let `c₁` and `c₂` be cokernel coforks for morphisms `f₁ : X₁ ⟶ Y₁` and
`f₂ : X₂ ⟶ Y₂` in a monoidal preadditive category. We define a cokernel
cofork for `(X₁ ⊗ Y₂) ⨿ (Y₁ ⊗ X₂) ⟶ Y₁ ⊗ Y₂` with point `c₁.pt ⊗ c₂.pt`,
and show that it is colimit if `c₁` and `c₂` are colimit, and the
cokernels of `f₁` and `f₂` are preserved by suitable tensor products.

-/

@[expose] public section

namespace CategoryTheory.Limits.CokernelCofork

open MonoidalCategory MonoidalPreadditive

variable {C : Type*} [Category* C]
  [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {X₁ Y₁ : C} {f₁ : X₁ ⟶ Y₁} {c₁ : CokernelCofork f₁} (hc₁ : IsColimit c₁)
  {X₂ Y₂ : C} {f₂ : X₂ ⟶ Y₂} {c₂ : CokernelCofork f₂} (hc₂ : IsColimit c₂)
  [HasBinaryCoproduct (X₁ ⊗ Y₂) (Y₁ ⊗ X₂)]

variable (c₁ c₂) in
/-- Given two cokernel coforks `c₁` and `c₂` for `f₁ : X₁ ⟶ Y₁` and `f₂ : X₂ ⟶ Y₂`,
this is the cokernel cofork for `(X₁ ⊗ Y₂) ⨿ (Y₁ ⊗ X₂) ⟶ Y₁ ⊗ Y₂` with
point `c₁.pt ⊗ c₂.pt`. -/
noncomputable abbrev tensor : CokernelCofork (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)) :=
  CokernelCofork.ofπ (c₁.π ⊗ₘ c₂.π) (by
    ext
    · simp [tensorHom_def, ← comp_whiskerRight_assoc, coprod.inl_desc]
    · simp [tensorHom_def', ← whiskerLeft_comp_assoc, coprod.inr_desc])

/-- Given two colimit cokernel coforks `c₁` and `c₂` for `f₁ : X₁ ⟶ Y₁` and
`f₂ : X₂ ⟶ Y₂`, if the cokernels of `f₁` and `f₂` are preserves by suitable
tensor products, then `c₁.pt ⊗ c₂.pt` is the cokernel of the
morphism `(X₁ ⊗ Y₂) ⨿ (Y₁ ⊗ X₂) ⟶ Y₁ ⊗ Y₂`. -/
noncomputable def isColimitTensor
    [PreservesColimit (parallelPair f₂ 0) (tensorLeft c₁.pt)]
    [PreservesColimit (parallelPair f₁ 0) (tensorRight Y₂)]
    [PreservesColimit (parallelPair f₁ 0) (tensorRight X₂)] :
    IsColimit (c₁.tensor c₂) :=
  haveI : HasBinaryCoproduct (((curriedTensor C).obj X₁).obj Y₂)
    (((curriedTensor C).obj Y₁).obj X₂) := by assumption
  IsColimit.ofIsoColimit (isColimitMapBifunctor hc₁ hc₂ (curriedTensor C))
    (Cofork.ext (Iso.refl _) (by dsimp only [Cofork.π]; simp [tensorHom_def]))

end CategoryTheory.Limits.CokernelCofork
