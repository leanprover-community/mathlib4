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
# The colimit module of a presheaf of module on a cofiltered category

Given a colimit cocone `cR` for a presheaf of rings `R` on a cofiltered category `C`,
`M` a presheaf of modules over `R`, and a colimit cocone `cM` for the underlying
functor `Cᵒᵖ ⥤ AddCommGrpCat` of `M`, we define a structure of module over `cR.pt`
on a type-synonym for `cM.pt`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

attribute [local instance] hasColimitsOfShape_of_finallySmall
  IsFiltered.isSifted FinallySmall.preservesColimitsOfShape_of_isFiltered

namespace PresheafOfModules

section

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  [IsCofiltered C] [InitiallySmall.{w} C]
  {R : Cᵒᵖ ⥤ RingCat.{w}} {cR : Cocone R} (hcR : IsColimit cR)

set_option backward.isDefEq.respectTransparency false in
variable (cR) in
noncomputable def constFunctor : ModuleCat cR.pt ⥤ PresheafOfModules.{w} R where
  obj M :=
    { obj X := (ModuleCat.restrictScalars (cR.ι.app X).hom).obj M
      map {X Y} f :=
        (ModuleCat.restrictScalarsComp' _ _ _
          (by ext; dsimp; rw [← Cocone.w cR f]; dsimp)).hom.app _ }
  map φ := { app X := (ModuleCat.restrictScalars (cR.ι.app X).hom).map φ }

section

variable {M : PresheafOfModules.{w} R} {cM : Cocone M.presheaf} (hcM : IsColimit cM)

/-- Given a colimit cocone for a presheaf of rings `R` on a cofiltered category `C`,
`M` a presheaf of modules over `R`, and a colimit cocone `cM` for the underlying
functor `Cᵒᵖ ⥤ AddCommGrpCat` of `M`, this is the type `cM.pt` on which we define
a module structure below. -/
@[nolint unusedArguments]
def ModuleColimit (_ : IsColimit cR) (_ : IsColimit cM) : Type w := cM.pt
  deriving AddCommGroup

namespace ModuleColimit

/-- The cocone `R ⋙ forget _ ⊗ M.presheaf ⋙ forget _` with point
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

noncomputable def homEquiv' {N : Type w} [AddCommGroup N] :
    (ModuleColimit hcR hcM →+ N) ≃+ (M.presheaf ⟶ (Functor.const _).obj (.of N)) :=
  AddEquiv.trans
    { toFun f := AddCommGrpCat.ofHom f
      invFun f := f.hom
      map_add' _ _:= rfl }
    { toEquiv := hcM.homEquiv
      map_add' _ _ := rfl }

omit [LocallySmall.{w, v, u} C] [IsCofiltered C] [InitiallySmall C] in
lemma homEquiv'_app_apply {N : ModuleCat.{w} cR.pt}
    (α : ModuleColimit hcR hcM →+ N) {X : Cᵒᵖ} (x : M.obj X) :
    dsimp% (homEquiv' hcR hcM α).app X x = α (cM.ι.app X x) :=
  rfl

lemma map_smul_homEquiv'_iff {N : ModuleCat.{w} cR.pt}
    (α : ModuleColimit hcR hcM →+ N) :
    (∀ (U : Cᵒᵖ) (r : R.obj U) (m : M.obj U), (homEquiv' hcR hcM α).app U (r • m) =
        letI m' : N := (homEquiv' hcR hcM α).app U m; letI r' : cR.pt := cR.ι.app U r
        r' • m') ↔
    ∀ (r : cR.pt) (m : ModuleColimit hcR hcM), α (r • m) = r • α m := by
  refine ⟨fun h r m ↦ ?_, fun h U r m ↦ ?_⟩
  · obtain ⟨U, r, m, rfl, rfl⟩ := jointly_surjective₂ r m
    refine Eq.trans ?_ ((homEquiv'_app_apply ..).symm.trans (h U r m))
    congr 1
    apply smul_eq
  · dsimp
    rw [homEquiv'_app_apply, homEquiv'_app_apply, ← h]
    congr 1
    exact (smul_eq ..).symm

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
        change ψ.app U (r • m) = _
        rw [map_smul]
        rfl}
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

section

variable {M' : PresheafOfModules.{w} R} {cM' : Cocone M'.presheaf}
  (hcM' : IsColimit cM')

variable (cM') in
@[simps]
noncomputable def mapCocone (f : M ⟶ M') : Cocone M.presheaf where
  pt := cM'.pt
  ι.app U := (forget₂ _ _).map (f.app U) ≫ cM'.ι.app U
  ι.naturality U V g := by
    ext m
    have h₁ := ConcreteCategory.congr_arg (cM'.ι.app V)
      (ConcreteCategory.congr_hom (f.naturality g) m)
    have h₂ := ConcreteCategory.congr_hom (cM'.w g)  (f.app _ m)
    exact h₁.trans h₂

noncomputable def map (f : M ⟶ M') :
    ModuleColimit hcR hcM →ₗ[cR.pt] ModuleColimit hcR hcM' where
  toFun := hcM.desc (mapCocone cM' f)
  map_add' _ _ := map_add _ _ _
  map_smul' r m := by
    obtain ⟨U, r, m, rfl, rfl⟩ := ModuleColimit.jointly_surjective₂ r m
    have h₁ := ConcreteCategory.congr_hom (hcM.fac (mapCocone cM' f) U) (r • m)
    have h₂ := ConcreteCategory.congr_hom (hcM.fac (mapCocone cM' f) U) m
    dsimp at h₁ h₂ ⊢
    rw [ModuleColimit.smul_eq]
    erw [h₁, h₂, ModuleColimit.smul_eq, ← (f.app U).hom.map_smul]
    rfl

@[simp]
lemma map_apply (f : M ⟶ M') {U : Cᵒᵖ} (m : M.obj U) :
    dsimp% map hcR hcM hcM' f (ιM m) = ιM (f.app _ m) :=
  ConcreteCategory.congr_hom (hcM.fac (mapCocone cM' f) U) m

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

/-- The colimit module of a presheaf of modules over a cofiltered category. -/
@[simps! obj]
noncomputable def colimitFunctor : PresheafOfModules.{w} R ⥤ ModuleCat cR.pt where
  obj M := ModuleCat.of _ (ModuleColimit hcR (colimit.isColimit M.presheaf))
  map f := ModuleCat.ofHom (ModuleColimit.map _ _ _ f)
  map_comp f g := by ext : 1; exact (ModuleColimit.comp_map ..).symm

noncomputable def colimitAdjunction :
    colimitFunctor.{w} hcR ⊣ constFunctor.{w} cR :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := (ModuleColimit.homEquiv _ _).toEquiv
      homEquiv_naturality_left_symm _ _ := ModuleColimit.homEquiv_naturality_left_symm _ _ _ _ _
      homEquiv_naturality_right _ _ := ModuleColimit.homEquiv_naturality_right _ _ _ _ }

end

end PresheafOfModules
