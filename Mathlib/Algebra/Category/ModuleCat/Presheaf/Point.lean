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
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits

/-!
#

-/

@[expose] public section

universe w v u

open CategoryTheory Limits GrothendieckTopology MonoidalCategory

attribute [local instance] hasColimitsOfShape_of_finallySmall

attribute [local instance] IsFiltered.isSifted

-- this should be moved
local instance {J C D : Type*} [Category* J] [Category* C] [Category* D]
    (F : C ⥤ D) [PreservesFilteredColimitsOfSize.{w, w} F]
    [FinallySmall.{w} J] [LocallySmall.{w} J] [IsFiltered J] :
    PreservesColimitsOfShape J F :=
  Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{w} J) _

namespace PresheafOfModules
-- this part should go in a separate file
-- `Algebra/Category/ModuleCat/Presheaf/ColimitModule`

section

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  [IsCofiltered C] [InitiallySmall.{w} C]
  {R : Cᵒᵖ ⥤ RingCat.{w}} {cR : Cocone R} (hcR : IsColimit cR)

section

variable {M : PresheafOfModules.{w} R} {cM : Cocone M.presheaf} (hcM : IsColimit cM)

def ModuleColimit (_ : IsColimit cR) (_ : IsColimit cM) : Type w := cM.pt
  deriving AddCommGroup

namespace ModuleColimit

variable (cR cM) in
noncomputable def coconeTensorForget :
    Cocone (R ⋙ forget _ ⊗ M.presheaf ⋙ forget _) :=
  ((forget _).mapCocone  cR).tensor ((forget _).mapCocone cM)

noncomputable def isColimitCoconeTensorForget :
    IsColimit (coconeTensorForget cR cM) :=
  (isColimitOfPreserves (forget _) hcR).tensor (isColimitOfPreserves (forget _) hcM)

@[simps]
noncomputable def coconeSMul :
    Cocone (R ⋙ forget _ ⊗ M.presheaf ⋙ forget _) where
  pt := ModuleColimit hcR hcM
  ι.app U := fun ⟨(r : R.obj U), (m : M.obj U)⟩ ↦ by exact cM.ι.app U (r • m)
  ι.naturality V U f := by
    ext ⟨r, m⟩
    exact (ConcreteCategory.congr_arg (cM.ι.app U)
      (M.map_smul f r m).symm).trans (ConcreteCategory.congr_hom (cM.w f) _)

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

set_option backward.isDefEq.respectTransparency false in
variable {hcR hcM} in
lemma jointly_surjective₂ (r : cR.pt) (m : ModuleColimit hcR hcM) :
    ∃ (U : Cᵒᵖ) (a : R.obj U) (x : M.obj U),
      ιR cR a = r ∧ ιM x = m := by
  obtain ⟨U, ⟨a, x⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      (isColimitOfPreserves (forget AddCommGrpCat) hcM)) ⟨r, m⟩
  rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨U, a, x, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable {hcR hcM} in
lemma jointly_surjective₃ (r₁ r₂ : cR.pt) (m : ModuleColimit hcR hcM) :
    ∃ (U : Cᵒᵖ) (a₁ a₂ : R.obj U) (x : M.obj U),
      ιR cR a₁ = r₁ ∧ ιR cR a₂ = r₂ ∧ ιM x = m := by
  obtain ⟨U, ⟨a₁, a₂, x⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      ((isColimitOfPreserves (forget RingCat) hcR).tensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM))) ⟨r₁, r₂, m⟩
  rw [Prod.ext_iff, Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, a₁, a₂, x, rfl, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable {hcR hcM} in
lemma jointly_surjective₃' (r : cR.pt) (m₁ m₂ : ModuleColimit hcR hcM) :
    ∃ (U : Cᵒᵖ) (a : R.obj U) (x₁ x₂ : M.obj U),
      ιR cR a = r ∧ ιM x₁ = m₁ ∧ ιM x₂ = m₂ := by
  obtain ⟨U, ⟨a, x₁, x₂⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
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

end

set_option backward.isDefEq.respectTransparency false in
noncomputable def colimitFunctor : PresheafOfModules.{w} R ⥤ ModuleCat cR.pt where
  obj M := ModuleCat.of _ (ModuleColimit hcR (colimit.isColimit M.presheaf))
  map {M₁ M₂} f := ModuleCat.ofHom
    { toFun := colimMap ((toPresheaf _).map f)
      map_add' := by simp
      map_smul' m x := by
        obtain ⟨U, m, x, rfl, rfl⟩ := ModuleColimit.jointly_surjective₂ m x
        have h₁ := ConcreteCategory.congr_hom
          (ι_colimMap ((toPresheaf _).map f) U) (m • x)
        have h₂ := ConcreteCategory.congr_hom
          (ι_colimMap ((toPresheaf _).map f) U) x
        dsimp at h₁ h₂ ⊢
        rw [ModuleColimit.smul_eq]
        erw [h₁, h₂, ModuleColimit.smul_eq]
        erw [(f.app U).hom.map_smul]
        rfl }
  map_id M :=
    (forget₂ _ AddCommGrpCat).map_injective (by
      change colimMap ((toPresheaf _).map (𝟙 M)) = 𝟙 _
      exact colimit.hom_ext (by simp))
  map_comp f g :=
    (forget₂ _ AddCommGrpCat).map_injective (by
      change colimMap ((toPresheaf _).map (f ≫ g)) =
        colimMap ((toPresheaf _).map f) ≫ colimMap ((toPresheaf _).map g)
      exact colimit.hom_ext (by simp))

end

end PresheafOfModules

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} (Φ : Point.{w} J)

section

variable {R : Cᵒᵖ ⥤ RingCat.{w}} {c : Cocone ((CategoryOfElements.π Φ.fiber).op ⋙ R)}
  (hc : IsColimit c)

noncomputable def fiberOfIsColimit : PresheafOfModules.{w} R ⥤ ModuleCat c.pt :=
  PresheafOfModules.pushforward₀ _ _ ⋙ PresheafOfModules.colimitFunctor hc

noncomputable def fiberOfIsColimitCompForget₂Iso :
    Φ.fiberOfIsColimit hc ⋙ forget₂ _ AddCommGrpCat ≅
      PresheafOfModules.toPresheaf _ ⋙ Φ.presheafFiber :=
  Iso.refl _

end

noncomputable def presheafOfModulesFiberOfRing {R : Cᵒᵖ ⥤ RingCat.{w}} :
    PresheafOfModules.{w} R ⥤ ModuleCat.{w} (Φ.presheafFiber.obj R :) :=
  Φ.fiberOfIsColimit (colimit.isColimit _)

noncomputable def presheafOfModulesFiber {R : Cᵒᵖ ⥤ CommRingCat.{w}} :
    PresheafOfModules.{w} (R ⋙ forget₂ _ _) ⥤
      ModuleCat.{w} (Φ.presheafFiber.obj R :) :=
  Φ.fiberOfIsColimit (R := R ⋙ forget₂ _ _ )
    (isColimitOfPreserves (forget₂ _ RingCat)
    (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ R)))

end CategoryTheory.GrothendieckTopology.Point
