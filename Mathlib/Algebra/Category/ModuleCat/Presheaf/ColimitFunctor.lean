/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits

/-!
# The colimit module of a presheaf of modules on a cofiltered category

Given a colimit cocone `cR` for a presheaf of rings `R` on a cofiltered category `C`,
`M` a presheaf of modules over `R`, and a colimit cocone `cM` for the underlying
functor `Cᵒᵖ ⥤ AddCommGrpCat` of `M`, we define a structure of module over `cR.pt`
on a type-synonym `PresheafOfModules.ModuleColimit` for `cM.pt`. This extends to
a functor `PresheafOfModules.colimitFunctor : PresheafOfModules R ⥤ ModuleCat cR.pt`.

## TODO (@joelriou)
* Define fiber functors on categories of (pre)sheaves of modules
* Refactor `Mathlib/Algebra/Category/ModuleCat/Stalk.lean` so that it uses
this slightly more general construction.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

attribute [local instance] hasColimitsOfShape_of_finallySmall
  IsFiltered.isSifted FinallySmall.preservesColimitsOfShape_of_isFiltered

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  [IsCofiltered C] [InitiallySmall.{w} C]
  {R : Cᵒᵖ ⥤ RingCat.{w}} {cR : Cocone R} (hcR : IsColimit cR)

section

variable {M : PresheafOfModules.{w} R} {cM : Cocone M.presheaf} (hcM : IsColimit cM)
  {M' : PresheafOfModules.{w} R} {cM' : Cocone M'.presheaf} (hcM' : IsColimit cM')
  {M'' : PresheafOfModules.{w} R} {cM'' : Cocone M''.presheaf} (hcM'' : IsColimit cM'')

/-- Given a colimit cocone for a presheaf of rings `R` on a cofiltered category `C`,
`M` a presheaf of modules over `R`, and a colimit cocone `cM` for the underlying
functor `Cᵒᵖ ⥤ AddCommGrpCat` of `M`, this is the type `cM.pt` on which we define
a module structure below. -/
@[nolint unusedArguments]
def ModuleColimit (_ : IsColimit cR) (_ : IsColimit cM) : Type w := cM.pt

instance : AddCommGroup (ModuleColimit hcR hcM) :=
  inferInstanceAs (AddCommGroup cM.pt)

namespace ModuleColimit

/-- The cocone for `R ⋙ forget _ ⊗ M.presheaf ⋙ forget _` with point
`ModuleColimit hcR hcM` which allows to define the scalar multiplication
by `cR.pt` on `ModuleColimit hcR hcM`. -/
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
  smul :=
    (((isColimitOfPreserves (forget _) hcR).tensor
      (isColimitOfPreserves (forget _) hcM)).desc (coconeSMul hcR hcM)).curry

variable (cR) in
/-- The "inclusion" maps to the colimit ring. -/
abbrev ιR {U : Cᵒᵖ} : R.obj U →+* cR.pt := (cR.ι.app U).hom

variable {hcR hcM} in
/-- The "inclusion" maps to the colimit module, as an additive map. -/
noncomputable abbrev ιM {U : Cᵒᵖ} : M.obj U →+ ModuleColimit hcR hcM :=
  (cM.ι.app U).hom

@[simp]
lemma smul_eq {U : Cᵒᵖ} (r : R.obj U) (m : M.obj U) :
    ιR cR r • ιM (hcR := hcR) (hcM := hcM) m = ιM (r • m) :=
  congr_fun (((isColimitOfPreserves (forget _) hcR).tensor
    (isColimitOfPreserves (forget _) hcM)).fac (coconeSMul hcR hcM) U) ⟨r, m⟩

variable {hcR hcM} in
lemma ιM_jointly_surjective (m : ModuleColimit hcR hcM) :
    ∃ (U : Cᵒᵖ) (x : M.obj U), ιM x = m :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget AddCommGrpCat) hcM) m

set_option backward.isDefEq.respectTransparency false in
variable {hcR hcM hcM'} in
lemma ιM_jointly_surjective₂ (m : ModuleColimit hcR hcM) (m' : ModuleColimit hcR hcM') :
    ∃ (U : Cᵒᵖ) (x : M.obj U) (x' : M'.obj U), ιM x = m ∧ ιM x' = m' := by
  obtain ⟨U, ⟨x, x'⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
      (isColimitOfPreserves (forget AddCommGrpCat) hcM')) ⟨m, m'⟩
  rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨U, x, x', rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable {hcR hcM hcM' hcM''} in
lemma ιM_jointly_surjective₃ (m : ModuleColimit hcR hcM) (m' : ModuleColimit hcR hcM')
    (m'' : ModuleColimit hcR hcM'') :
    ∃ (U : Cᵒᵖ) (x : M.obj U) (x' : M'.obj U) (x'' : M''.obj U),
      ιM x = m ∧ ιM x' = m' ∧ ιM x'' = m'' := by
  obtain ⟨U, ⟨x, x', x''⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
      ((isColimitOfPreserves (forget AddCommGrpCat) hcM').tensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM''))) ⟨m, m', m''⟩
  rw [Prod.ext_iff, Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, x, x', x'', rfl, rfl, rfl⟩

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
variable {hcR hcM hcM'} in
lemma jointly_surjective₃' (r : cR.pt) (m₁ : ModuleColimit hcR hcM) (m₂ : ModuleColimit hcR hcM') :
    ∃ (U : Cᵒᵖ) (a : R.obj U) (x₁ : M.obj U) (x₂ : M'.obj U),
      ιR cR a = r ∧ ιM x₁ = m₁ ∧ ιM x₂ = m₂ := by
  obtain ⟨U, ⟨a, x₁, x₂⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM'))) ⟨r, m₁, m₂⟩
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

section

variable {M' : PresheafOfModules.{w} R} {cM' : Cocone M'.presheaf}
  (hcM' : IsColimit cM')

/-- The linear map between the colimit modules induced by a morphism of modules. -/
noncomputable def map (f : M ⟶ M') :
    ModuleColimit hcR hcM →ₗ[cR.pt] ModuleColimit hcR hcM' where
  toFun := hcM.desc ((Cocone.precompose ((toPresheaf _).map f)).obj cM')
  map_add' _ _ := map_add _ _ _
  map_smul' r m := by
    obtain ⟨U, r, m, rfl, rfl⟩ := ModuleColimit.jointly_surjective₂ r m
    let c := (Cocone.precompose ((toPresheaf _).map f)).obj cM'
    have h₁ := ConcreteCategory.congr_hom (hcM.fac c U) (r • m)
    have h₂ := ConcreteCategory.congr_hom (hcM.fac c U) m
    dsimp [c] at h₁ h₂ ⊢
    rw [ModuleColimit.smul_eq]
    erw [h₁, h₂, ModuleColimit.smul_eq, ← (f.app U).hom.map_smul]
    rfl

@[simp]
lemma map_apply (f : M ⟶ M') {U : Cᵒᵖ} (m : M.obj U) :
    dsimp% map hcR hcM hcM' f (ιM m) = ιM (f.app _ m) :=
  ConcreteCategory.congr_hom (hcM.fac ((Cocone.precompose ((toPresheaf _).map f)).obj cM') U) m

@[simp]
lemma map_id : map hcR hcM hcM (𝟙 M) = .id := by
  ext m
  obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
  simp

lemma comp_map
    (f : M ⟶ M')
    {M'' : PresheafOfModules.{w} R} {cM'' : Cocone M''.presheaf}
    (hcM'' : IsColimit cM'') (g : M' ⟶ M'') :
    (map hcR hcM' hcM'' g).comp (map hcR hcM hcM' f) = map hcR hcM hcM'' (f ≫ g) := by
  ext m
  obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
  simp

end

end ModuleColimit

end

/-- The colimit module functor from the category of presheaves of modules
over a presheaf of rings `R` on a cofiltered category to the category
of modules over a colimit of `R`. -/
noncomputable def colimitFunctor : PresheafOfModules.{w} R ⥤ ModuleCat.{w} cR.pt where
  obj M := ModuleCat.of _ (ModuleColimit hcR (colimit.isColimit M.presheaf))
  map f := ModuleCat.ofHom (ModuleColimit.map _ _ _ f)
  map_comp f g := by ext : 1; exact (ModuleColimit.comp_map ..).symm

end PresheafOfModules
