/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
#

-/

@[expose] public section

universe w v u

open CategoryTheory Limits GrothendieckTopology MonoidalCategory

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  [IsCofiltered C] [InitiallySmall.{w} C]
  {R : Cᵒᵖ ⥤ RingCat.{w}} {cR : Cocone R} (hcR : IsColimit cR)
  {M : PresheafOfModules.{w} R}
  {cM : Cocone M.presheaf} (hcM : IsColimit cM)

namespace moduleColimit

variable (cR cM) in
@[simps]
noncomputable def coconeTensorForget :
    Cocone (R ⋙ forget _ ⊗ M.presheaf ⋙ forget _) where
  pt := cR.pt ⊗ cM.pt
  ι.app X := (forget _).map (cR.ι.app X) ⊗ₘ (forget _).map (cM.ι.app X)
  ι.naturality _ _ f := by
    dsimp
    ext
    · exact ConcreteCategory.congr_hom (cR.w f) _
    · exact ConcreteCategory.congr_hom (cM.w f) _

def isColimitCoconeTensorForget :
    IsColimit (coconeTensorForget cR cM) := by
  have := hcR
  have := hcM
  have : LocallySmall.{w} C := inferInstance
  have : InitiallySmall.{w} C := inferInstance
  have : IsCofiltered C := inferInstance
  sorry

variable (cM) in
@[simps]
noncomputable def coconeSMul :
    Cocone (R ⋙ forget _ ⊗ M.presheaf ⋙ forget _) where
  pt := cM.pt
  ι.app U := fun ⟨(r : R.obj U), (m : M.obj U)⟩ ↦ by exact cM.ι.app U (r • m)
  ι.naturality V U f := by
    ext ⟨r, m⟩
    exact (ConcreteCategory.congr_arg (cM.ι.app U)
      (M.map_smul f r m).symm).trans (ConcreteCategory.congr_hom (cM.w f) _)

noncomputable def smul : cR.pt → cM.pt → cM.pt :=
  Function.curry
    ((isColimitCoconeTensorForget hcR hcM).desc (coconeSMul cM))

lemma smul_eq {U : Cᵒᵖ} (r : R.obj U) (m : M.obj U) :
    smul hcR hcM (cR.ι.app U r) (cM.ι.app U m) =
      cM.ι.app U (r • m) :=
  congr_fun ((isColimitCoconeTensorForget hcR hcM).fac (coconeSMul cM) U) ⟨r, m⟩

end moduleColimit

open moduleColimit in

noncomputable def moduleColimit : Module cR.pt cM.pt := by
  letI : SMul cR.pt cM.pt := ⟨smul hcR hcM⟩
  let ιR {U : Cᵒᵖ} (r : R.obj U) : cR.pt := cR.ι.app U r
  have ιR_zero (U : Cᵒᵖ) : ιR (0 : R.obj U) = 0 :=
    (cR.ι.app U).hom.map_zero
  have ιR_one (U : Cᵒᵖ) : ιR (1 : R.obj U) = 1 :=
    (cR.ι.app U).hom.map_one
  have ιR_add {U : Cᵒᵖ} (r₁ r₂ : R.obj U) :
      ιR (r₁ + r₂) = ιR r₁ + ιR r₂ :=
    (cR.ι.app U).hom.map_add _ _
  have ιR_mul {U : Cᵒᵖ} (r₁ r₂ : R.obj U) :
      ιR (r₁ * r₂) = ιR r₁ * ιR r₂ :=
    (cR.ι.app U).hom.map_mul _ _
  let ιM {U : Cᵒᵖ} (m : M.obj U) : cM.pt := cM.ι.app U m
  have ιM_zero (U : Cᵒᵖ) : ιM (0 : M.obj U) = 0 :=
    (cM.ι.app U).hom.map_zero
  have ιM_add {U : Cᵒᵖ} (m₁ m₂ : M.obj U) :
      ιM (m₁ + m₂) = ιM m₁ + ιM m₂ :=
    (cM.ι.app U).hom.map_add _ _
  have H {U : Cᵒᵖ} (r : R.obj U) (m : M.obj U) :
      ιR r • ιM m = ιM (r • m) := smul_eq _ _ _ _
  have jointly_surjective_ring (r : cR.pt) :
      ∃ (U : Cᵒᵖ) (a : R.obj U), ιR a = r := sorry
  have jointly_surjective_module (m : cM.pt) :
      ∃ (U : Cᵒᵖ) (x : M.obj U), ιM x = m := sorry
  have jointly_surjective₃ (r : cR.pt) (m₁ m₂ : cM.pt) :
      ∃ (U : Cᵒᵖ) (a : R.obj U) (x₁ x₂ : M.obj U),
        ιR a = r ∧ ιM x₁ = m₁ ∧ ιM x₂ = m₂ := sorry
  have jointly_surjective₃' (r₁ r₂ : cR.pt) (m : cM.pt) :
      ∃ (U : Cᵒᵖ) (a₁ a₂ : R.obj U) (x : M.obj U),
        ιR a₁ = r₁ ∧ ιR a₂ = r₂ ∧ ιM x = m := sorry
  exact {
    mul_smul r₁ r₂ m := by
      obtain ⟨U, r₁, r₂, m, rfl, rfl, rfl⟩ := jointly_surjective₃' r₁ r₂ m
      simp only [← ιR_mul, H, ← mul_smul]
    one_smul m := by
      obtain ⟨U, m, rfl⟩ := jointly_surjective_module m
      simpa [ιR_one] using H 1 m
    zero_smul m := by
      obtain ⟨U, m, rfl⟩ := jointly_surjective_module m
      simpa [ιR_zero, ιM_zero] using H 0 m
    smul_zero r := by
      obtain ⟨U, r, rfl⟩ := jointly_surjective_ring r
      simpa [ιM_zero] using H r 0
    smul_add r m₁ m₂ := by
      obtain ⟨U, r, m₁, m₂, rfl, rfl, rfl⟩ := jointly_surjective₃ r m₁ m₂
      simp only [← ιM_add, H, smul_add]
    add_smul r₁ r₂ m := by
      obtain ⟨U, r₁, r₂, m, rfl, rfl, rfl⟩ := jointly_surjective₃' r₁ r₂ m
      simp only [← ιR_add, H, add_smul, ← ιM_add] }

end PresheafOfModules
