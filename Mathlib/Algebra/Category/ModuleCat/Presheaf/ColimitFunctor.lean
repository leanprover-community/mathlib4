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

variable (cR) in
/-- Given a cocone `cR` for a functor `R : Cᵒᵖ ⥤ RingCat`, this is the
functor `ModuleCat cR.pt ⥤ PresheafOfModules R` which sends a module `M`
over `cR.pt` to a presheaf of modules whose underlying presheaf of
abelian groups is the constant functor `Cᵒᵖ ⥤ AddCommGrpCat` with value `M`. -/
noncomputable def constFunctor : ModuleCat cR.pt ⥤ PresheafOfModules.{w} R where
  obj M :=
    { obj X := (ModuleCat.restrictScalars (cR.ι.app X).hom).obj M
      map {X Y} f :=
        (ModuleCat.restrictScalarsComp' _ _ _
          (by ext; dsimp; rw [← Cocone.w cR f]; dsimp; rfl)).hom.app _ }
  map φ := { app X := (ModuleCat.restrictScalars (cR.ι.app X).hom).map φ }

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
  ι.app U := TypeCat.ofHom fun ⟨(r : R.obj U), (m : M.obj U)⟩ ↦ by exact cM.ι.app U (r • m)
  ι.naturality V U f := by
    ext ⟨r, m⟩
    exact (ConcreteCategory.congr_arg (cM.ι.app U)
      (M.map_smul f r m).symm).trans (ConcreteCategory.congr_hom (cM.w f) _)

noncomputable instance : SMul cR.pt (ModuleColimit hcR hcM) where
  smul :=
    (((isColimitOfPreserves (forget _) hcR).tensor
      (isColimitOfPreserves (forget _) hcM)).desc (coconeSMul hcR hcM) : _ → _).curry

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
  ConcreteCategory.congr_hom (((isColimitOfPreserves (forget _) hcR).tensor
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

/-- Auxiliary definition for `homEquiv`. This is the universal property
of `PresheafOfModules.ModuleColimit`, as an abelian group. -/
noncomputable def homEquiv' {N : Type w} [AddCommGroup N] :
    (ModuleColimit hcR hcM →+ N) ≃+ (M.presheaf ⟶ (Functor.const _).obj (.of N)) where
  toEquiv := (ConcreteCategory.homEquiv (X := AddCommGrpCat.of (ModuleColimit hcR hcM))
    (Y := AddCommGrpCat.of N)).symm.trans hcM.homEquiv
  map_add' _ _ := rfl

omit [LocallySmall.{w, v, u} C] [IsCofiltered C] [InitiallySmall C] in
lemma homEquiv'_app_apply {N : ModuleCat.{w} cR.pt}
    (α : ModuleColimit hcR hcM →+ N) {X : Cᵒᵖ} (x : M.obj X) :
    dsimp% (homEquiv' hcR hcM α).app X x = α (cM.ι.app X x) :=
  rfl

omit [LocallySmall.{w, v, u} C] [IsCofiltered C] [InitiallySmall C] in
lemma homEquiv'_symm_apply {N : ModuleCat.{w} cR.pt}
    (β : M.presheaf ⟶ (Functor.const _).obj (.of N)) {X : Cᵒᵖ} (x : M.obj X) :
    (homEquiv' hcR hcM).symm β (cM.ι.app X x) = β.app X x :=
  ConcreteCategory.congr_hom (hcM.ι_app_homEquiv_symm β X) x

lemma map_smul_homEquiv'_iff {N : ModuleCat.{w} cR.pt}
    (α : ModuleColimit hcR hcM →+ N) :
    dsimp% (∀ (U : Cᵒᵖ) (r : R.obj U) (m : M.obj U), (homEquiv' hcR hcM α).app U (r • m) =
        letI m' : N := (homEquiv' hcR hcM α).app U m; letI r' : cR.pt := cR.ι.app U r
        r' • m') ↔
    ∀ (r : cR.pt) (m : ModuleColimit hcR hcM), α (r • m) = r • α m := by
  refine ⟨fun h r m ↦ ?_, fun h U r m ↦ ?_⟩
  · obtain ⟨U, r, m, rfl, rfl⟩ := jointly_surjective₂ r m
    refine Eq.trans ?_ ((homEquiv'_app_apply ..).symm.trans (h U r m))
    congr 1
    apply smul_eq
  · rw [homEquiv'_app_apply, homEquiv'_app_apply, ← h]
    congr 1
    exact (smul_eq ..).symm

/-- This is the universal property of `PresheafOfModules.ModuleColimit` as a module.
See also `PresheafOfModules.colimitAdjunction`. -/
noncomputable def homEquiv {N : ModuleCat.{w} cR.pt} :
    (ModuleCat.of cR.pt (ModuleColimit hcR hcM) ⟶ N) ≃+ (M ⟶ (constFunctor cR).obj N) where
  toFun φ := PresheafOfModules.homMk
    (homEquiv' hcR hcM ((forget₂ _ AddCommGrpCat).map φ).hom)
      ((map_smul_homEquiv'_iff hcR hcM ((forget₂ _ AddCommGrpCat).map φ).hom).2 (by simp))
  invFun ψ := ModuleCat.ofHom
    { toFun := (homEquiv' hcR hcM).symm ((toPresheaf _).map ψ)
      map_add' := by simp
      map_smul' := by
        obtain ⟨φ, hφ⟩ := (homEquiv' hcR hcM).surjective ((toPresheaf _).map ψ)
        simp only [← hφ, AddEquiv.symm_apply_apply, RingHom.id_apply]
        refine (map_smul_homEquiv'_iff hcR hcM φ).1 (fun U r m ↦ ?_)
        rw [hφ]
        erw [toPresheaf_map_app_apply]
        rw [map_smul]
        rfl }
  left_inv φ := (forget₂ _ AddCommGrpCat).map_injective (by
    ext : 1
    exact (homEquiv' hcR hcM).left_inv ((forget₂ _ AddCommGrpCat).map φ).hom)
  right_inv ψ := (toPresheaf _).map_injective ((homEquiv' hcR hcM).right_inv _)
  map_add' φ₁ φ₂ := (toPresheaf _).map_injective
    ((homEquiv' hcR hcM).map_add ((forget₂ _ AddCommGrpCat).map φ₁).hom
      ((forget₂ _ AddCommGrpCat).map φ₂).hom)

@[simp]
lemma homEquiv_app_apply {N : ModuleCat.{w} cR.pt}
    (α : ModuleCat.of cR.pt (ModuleColimit hcR hcM) ⟶ N) {X : Cᵒᵖ} (x : M.obj X) :
    dsimp% (homEquiv hcR hcM α).app X x = α (cM.ι.app X x) :=
  rfl

lemma homEquiv_naturality_right {N N' : ModuleCat.{w} cR.pt}
    (φ : ModuleCat.of cR.pt (ModuleColimit hcR hcM) ⟶ N) (g : N ⟶ N') :
    homEquiv hcR hcM (φ ≫ g) = homEquiv hcR hcM φ ≫ (constFunctor cR).map g := rfl

@[simp]
lemma homEquiv_symm_apply {N : ModuleCat.{w} cR.pt} (β : M ⟶ (constFunctor cR).obj N)
    {X : Cᵒᵖ} (x : M.obj X) :
    dsimp% (homEquiv hcR hcM).symm β (cM.ι.app X x) = β.app X x := by
  exact homEquiv'_symm_apply ..

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

lemma homEquiv_naturality_left {M' : PresheafOfModules.{w} R} {cM' : Cocone M'.presheaf}
    (hcM' : IsColimit cM') {N : ModuleCat.{w} cR.pt}
    (φ' : ModuleCat.of cR.pt (ModuleColimit hcR hcM') ⟶ N)
    (f : M ⟶ M') :
    homEquiv hcR hcM (ModuleCat.ofHom (map hcR hcM hcM' f) ≫ φ') =
      f ≫ homEquiv hcR hcM' φ' := by
  ext U m
  simp only [homEquiv_app_apply, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply, comp_app]
  apply congr_arg
  exact map_apply hcR hcM hcM' f m

lemma homEquiv_naturality_left_symm {M' : PresheafOfModules.{w} R} {cM' : Cocone M'.presheaf}
    (hcM' : IsColimit cM') {N : ModuleCat.{w} cR.pt}
    (f : M ⟶ M') (g : M' ⟶ (constFunctor cR).obj N) :
    (homEquiv hcR hcM).symm (f ≫ g) =
      ModuleCat.ofHom (map hcR hcM hcM' f) ≫ (homEquiv hcR hcM').symm g :=
  (homEquiv hcR hcM).injective (by
    obtain ⟨g, rfl⟩ := (homEquiv hcR hcM').surjective g
    simp [homEquiv_naturality_left])

end ModuleColimit

end

/-- The colimit module functor from the category of presheaves of modules
over a presheaf of rings `R` on a cofiltered category to the category
of modules over a colimit of `R`. -/
noncomputable def colimitFunctor : PresheafOfModules.{w} R ⥤ ModuleCat.{w} cR.pt where
  obj M := ModuleCat.of _ (ModuleColimit hcR (colimit.isColimit M.presheaf))
  map f := ModuleCat.ofHom (ModuleColimit.map _ _ _ f)
  map_comp f g := by ext : 1; exact (ModuleColimit.comp_map ..).symm

/-- Given a presheaf of rings `R` on a cofiltered category, this is the
adjunction between `colimitFunctor : PresheafOfModules R ⥤ ModuleCat cR.pt`
and the constant functor. -/
noncomputable def colimitAdjunction :
    colimitFunctor.{w} hcR ⊣ constFunctor.{w} cR :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := (ModuleColimit.homEquiv _ _).toEquiv
      homEquiv_naturality_left_symm _ _ := ModuleColimit.homEquiv_naturality_left_symm _ _ _ _ _
      homEquiv_naturality_right _ _ := ModuleColimit.homEquiv_naturality_right _ _ _ _ }

lemma colimitAdjunction_homEquiv
    (F : PresheafOfModules R) (G : ModuleCat cR.pt) :
    dsimp% (colimitAdjunction.{w} hcR).homEquiv F G =
      (ModuleColimit.homEquiv hcR
        (colimit.isColimit F.presheaf)).toEquiv := by
  simp [colimitAdjunction]

open ModuleColimit in
lemma colimitAdjunction_homEquiv_symm_apply
    {F : PresheafOfModules R} {G : ModuleCat cR.pt}
    (β : F ⟶ (constFunctor cR).obj G) {X : Cᵒᵖ} (m : F.obj X) :
    ((colimitAdjunction.{w} hcR).homEquiv F G).symm β
      (ModuleColimit.ιM (hcR := hcR) (hcM := colimit.isColimit F.presheaf) m) =
        β.app X m := by
  rw [colimitAdjunction_homEquiv]
  apply homEquiv_symm_apply

end PresheafOfModules
