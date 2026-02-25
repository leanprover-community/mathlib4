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

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Limits.Cocone

variable {D : Type*} [Category D]
  [CartesianMonoidalCategory D] {F₁ F₂ : C ⥤ D}
  (c₁ : Cocone F₁) (c₂ : Cocone F₂)

@[simps]
noncomputable def tensor (c₁ : Cocone F₁) (c₂ : Cocone F₂) : Cocone (F₁ ⊗ F₂) where
  pt := c₁.pt ⊗ c₂.pt
  ι.app X := c₁.ι.app X ⊗ₘ c₂.ι.app X

end Limits.Cocone

namespace Limits.Types

variable {F₁ F₂ : C ⥤ Type w} {c₁ : Cocone F₁} {c₂ : Cocone F₂}
  (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)

-- this could be provable more generally in suitable monoidal categories `D`
-- where tensorLeft and tensorRight commute with colimits of shape `C`
-- and `C` is sifted?
open IsFiltered in
noncomputable def isColimitCoconeTensor [IsFiltered C] :
    IsColimit (c₁.tensor c₂) := by
  refine Nonempty.some ((isColimit_iff_coconeTypesIsColimit ..).2 ⟨?_, ?_⟩)
  · intro x y h
    obtain ⟨i, x, rfl⟩ := Functor.ιColimitType_jointly_surjective _ x
    obtain ⟨j, y, rfl⟩ := Functor.ιColimitType_jointly_surjective _ y
    wlog hij : i = j generalizing i j
    · rw [Prod.ext_iff] at h
      dsimp at h
      have := this _ ((F₁ ⊗ F₂).map (leftToMax i j) x) _ ((F₁ ⊗ F₂).map (rightToMax i j) y)
        (by cat_disch) rfl
      simpa only [Functor.ιColimitType_map] using this
    subst hij
    rw [Prod.ext_iff] at h
    dsimp at h
    obtain ⟨k, f, h₁, h₂⟩ :
        ∃ (k : C) (f : i ⟶ k), F₁.map f x.1 = F₁.map f y.1 ∧
          F₂.map f x.2 = F₂.map f y.2 := by
      obtain ⟨j₁, f₁, h₁⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc₁ _ _).1 h.1
      obtain ⟨j₂, f₂, h₂⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc₂ _ _).1 h.2
      obtain ⟨k, g₁, g₂, fac⟩  := IsFiltered.span f₁ f₂
      exact ⟨k, f₁ ≫ g₁, by simp [h₁], by simp [fac, h₂]⟩
    simp [← Functor.ιColimitType_map _ f, h₁, h₂]
  · intro ⟨x₁, x₂⟩
    obtain ⟨j₁, x₁, rfl⟩  := Types.jointly_surjective_of_isColimit hc₁ x₁
    obtain ⟨j₂, x₂, rfl⟩  := Types.jointly_surjective_of_isColimit hc₂ x₂
    exact ⟨(F₁ ⊗ F₂).ιColimitType (max j₁ j₂) ⟨F₁.map (leftToMax _ _) x₁,
      F₂.map (rightToMax _ _) x₂⟩, by cat_disch⟩

end Limits.Types

end CategoryTheory

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  [IsCofiltered C] [InitiallySmall.{w} C]
  {R : Cᵒᵖ ⥤ RingCat.{w}} {cR : Cocone R} (hcR : IsColimit cR)
  {M : PresheafOfModules.{w} R}
  {cM : Cocone M.presheaf} (hcM : IsColimit cM)

local instance : PreservesColimitsOfShape Cᵒᵖ (forget RingCat.{w}) :=
  Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{w} Cᵒᵖ) _

local instance : PreservesColimitsOfShape Cᵒᵖ (forget AddCommGrpCat.{w}) :=
  Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{w} Cᵒᵖ) _

def ModuleColimit (_ : IsColimit cR) (_ : IsColimit cM) : Type w := cM.pt

instance : AddCommGroup (ModuleColimit hcR hcM) :=
    inferInstanceAs (AddCommGroup cM.pt)

namespace ModuleColimit

variable (cR cM) in
noncomputable def coconeTensorForget :
    Cocone (R ⋙ forget _ ⊗ M.presheaf ⋙ forget _) :=
  Cocone.tensor ((forget _).mapCocone  cR) ((forget _).mapCocone cM)

noncomputable def isColimitCoconeTensorForget :
    IsColimit (coconeTensorForget cR cM) :=
  Types.isColimitCoconeTensor (isColimitOfPreserves (forget _) hcR)
    (isColimitOfPreserves (forget _) hcM)

@[simps]
noncomputable def coconeSMul :
    Cocone (R ⋙ forget _ ⊗ M.presheaf ⋙ forget _) where
  pt := ModuleColimit hcR hcM
  ι.app U := fun ⟨(r : R.obj U), (m : M.obj U)⟩ ↦ by exact cM.ι.app U (r • m)
  ι.naturality V U f := by
    ext ⟨r, m⟩
    exact (ConcreteCategory.congr_arg (cM.ι.app U)
      (M.map_smul f r m).symm).trans (ConcreteCategory.congr_hom (cM.w f) _)

noncomputable def smul : cR.pt → cM.pt → cM.pt :=
  Function.curry
    ((isColimitCoconeTensorForget hcR hcM).desc (coconeSMul hcR hcM))

noncomputable instance : SMul cR.pt (ModuleColimit hcR hcM) where
  smul := ((isColimitCoconeTensorForget hcR hcM).desc (coconeSMul hcR hcM)).curry

variable (cR) in
abbrev ιR {U : Cᵒᵖ} : R.obj U →+* cR.pt := (cR.ι.app U).hom

variable {hcR hcM} in
noncomputable abbrev ιM {U : Cᵒᵖ} : M.obj U →+ ModuleColimit hcR hcM :=
  (cM.ι.app U).hom

@[simp]
lemma smul_eq {U : Cᵒᵖ} (r : R.obj U) (m : M.obj U) :
    ιR cR r • ιM (hcR := hcR) (hcM := hcM) m = ιM (r • m) :=
  congr_fun ((isColimitCoconeTensorForget hcR hcM).fac (coconeSMul hcR hcM) U) ⟨r, m⟩

variable {hcR hcM} in
lemma ιM_jointly_surjective (m : ModuleColimit hcR hcM) :
    ∃ (U : Cᵒᵖ) (x : M.obj U), ιM x = m :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget AddCommGrpCat) hcM) m

include hcR in
lemma ιR_jointly_surjective (r : cR.pt) :
    ∃ (U : Cᵒᵖ) (a : R.obj U), ιR cR a = r :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget RingCat) hcR) r

variable {hcR hcM} in
lemma jointly_surjective₃ (r₁ r₂ : cR.pt) (m : ModuleColimit hcR hcM) :
    ∃ (U : Cᵒᵖ) (a₁ a₂ : R.obj U) (x : M.obj U),
      ιR cR a₁ = r₁ ∧ ιR cR a₂ = r₂ ∧ ιM x = m := by
  obtain ⟨U, ⟨a₁, a₂, x⟩, h⟩ := Types.jointly_surjective_of_isColimit
    (Types.isColimitCoconeTensor (isColimitOfPreserves (forget RingCat) hcR)
      (Types.isColimitCoconeTensor
        (isColimitOfPreserves (forget RingCat) hcR)
        (isColimitOfPreserves (forget AddCommGrpCat) hcM))) ⟨r₁, r₂, m⟩
  rw [Prod.ext_iff, Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, a₁, a₂, x, rfl, rfl, rfl⟩

variable {hcR hcM} in
lemma jointly_surjective₃' (r : cR.pt) (m₁ m₂ : ModuleColimit hcR hcM) :
    ∃ (U : Cᵒᵖ) (a : R.obj U) (x₁ x₂ : M.obj U),
      ιR cR a = r ∧ ιM x₁ = m₁ ∧ ιM x₂ = m₂ := by
  obtain ⟨U, ⟨a, x₁, x₂⟩, h⟩ := Types.jointly_surjective_of_isColimit
    (Types.isColimitCoconeTensor (isColimitOfPreserves (forget RingCat) hcR)
      (Types.isColimitCoconeTensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM)
        (isColimitOfPreserves (forget AddCommGrpCat) hcM))) ⟨r, m₁, m₂⟩
  rw [Prod.ext_iff, Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, a, x₁, x₂, rfl, rfl, rfl⟩

noncomputable instance : Module cR.pt (ModuleColimit hcR hcM) where
  mul_smul r₁ r₂ m := by
    obtain ⟨U, r₁, r₂, m, rfl, rfl, rfl⟩ := jointly_surjective₃ r₁ r₂ m
    simp only [smul_eq, ← mul_smul, ← map_mul]
  one_smul m := by
    obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
    simpa using smul_eq hcR hcM 1 m
  zero_smul m := by
    obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
    simpa using smul_eq hcR hcM 0 m
  smul_zero r := by
    obtain ⟨U, r, rfl⟩ := ιR_jointly_surjective hcR r
    simpa using smul_eq hcR hcM r 0
  smul_add r m₁ m₂ := by
    obtain ⟨U, r, m₁, m₂, rfl, rfl, rfl⟩ := jointly_surjective₃' r m₁ m₂
    simp only [smul_eq, smul_add, ← map_add]
  add_smul r₁ r₂ m := by
    obtain ⟨U, r₁, r₂, m, rfl, rfl, rfl⟩ := jointly_surjective₃ r₁ r₂ m
    simp only [smul_eq, ← map_add, add_smul]

end ModuleColimit

end PresheafOfModules
