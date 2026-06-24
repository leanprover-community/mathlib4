/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel, Jujian Zhang, Weihong Xu,
  Andrew Yang, Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Data.Fintype.Order

/-!

# Construction of M^~

Given any commutative ring `R` and `R`-module `M`, we construct the sheaf `M^~` of `𝒪_SpecR`-modules
such that `M^~(U)` is the set of dependent functions that are locally fractions.

## Main definitions
* `AlgebraicGeometry.tilde` : `M^~` as a sheaf of `𝒪_{Spec R}`-modules.
* `AlgebraicGeometry.tilde.adjunction` : `~` is left adjoint to taking global sections.

-/

@[expose] public noncomputable section

universe u

open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

namespace AlgebraicGeometry

open _root_.PrimeSpectrum

/-- The forgetful functor from `𝒪_{Spec R}` modules to sheaves of `R`-modules. -/
def modulesSpecToSheaf :
    (Spec R).Modules ⥤ TopCat.Sheaf (ModuleCat R) (Spec R) :=
  SheafOfModules.forgetToSheafModuleCat (Spec R).ringCatSheaf (.op ⊤)
    (Limits.initialOpOfTerminal Limits.isTerminalTop) ⋙
  sheafCompose _ (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom)

/-- The global section functor for `𝒪_{Spec R}` modules -/
noncomputable
def moduleSpecΓFunctor : (Spec (.of R)).Modules ⥤ ModuleCat R :=
  modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤)

set_option backward.isDefEq.respectTransparency false in
open PrimeSpectrum in
/-- The forgetful functor from `𝒪_{Spec R}` modules to sheaves of `R`-modules is fully faithful. -/
def SpecModulesToSheafFullyFaithful : (modulesSpecToSheaf (R := R)).FullyFaithful where
  preimage {M N} f := ⟨fun U ↦ ModuleCat.ofHom ⟨(f.1.app U).hom.toAddHom, by
    intro t m
    apply TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj N).2
    intro x hxU
    obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : basicOpen _ ≤ _⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.unop.2
    refine ⟨_, hrU, hxr, ?_⟩
    refine Eq.trans ?_ (N.val.map_smul (homOfLE hrU).op t _).symm
    change N.1.map (homOfLE hrU).op (f.1.app _ _) = _ • N.1.map (homOfLE hrU).op (f.1.app _ _)
    have (x : _) :
        f.1.app _ (M.1.map (homOfLE hrU).op _) = N.1.map (homOfLE hrU).op (f.1.app _ x) :=
      congr($(f.1.naturality (homOfLE hrU).op).hom x)
    rw [← this, ← this, M.val.map_smul]
    generalize (Spec R).ringCatSheaf.obj.map (homOfLE hrU).op t = t
    letI := Module.compHom (R := Γ(Spec R, basicOpen r)) Γ(M, basicOpen r)
      (algebraMap R Γ(Spec R, basicOpen r))
    haveI : IsScalarTower R Γ(Spec R, basicOpen r) Γ(M, basicOpen r) :=
      .of_algebraMap_smul fun _ _ ↦ rfl
    letI := Module.compHom Γ(N, basicOpen r) (algebraMap R Γ(Spec R, basicOpen r))
    haveI : IsScalarTower R Γ(Spec R, basicOpen r) Γ(N, basicOpen r) :=
      .of_algebraMap_smul fun _ _ ↦ rfl
    exact (IsLocalization.linearMap_compatibleSMul (.powers (M := R) r)
      Γ(Spec R, basicOpen r) Γ(M, basicOpen r) Γ(N, basicOpen r)).map_smul
      (f.hom.app _).hom _ _⟩, fun i ↦ by ext x; exact congr($(f.1.naturality i).hom x)⟩
  map_preimage f := rfl
  preimage_map f := rfl

instance : (modulesSpecToSheaf (R := R)).Faithful := SpecModulesToSheafFullyFaithful.faithful

instance : (modulesSpecToSheaf (R := R)).Full := SpecModulesToSheafFullyFaithful.full

namespace Scheme.Modules

variable {M : (Spec R).Modules} {U V : (Spec R).Opens}

instance : Module R Γ(M, U) :=
  inferInstanceAs <| Module R ((modulesSpecToSheaf.obj M).obj.obj (.op U))

instance : IsScalarTower R Γ(Spec R, U) Γ(M, U) :=
  IsScalarTower.of_compHom R Γ(Spec R, U) Γ(M, U)

lemma smul_Spec_def (r : R) (x : Γ(M, U)) :
    r • x = ((Spec R).presheaf.map U.leTop.op) ((Scheme.ΓSpecIso R).inv r) • x :=
  rfl

@[simp]
lemma map_smul_Spec (hUV : .op V ⟶ .op U) (f : R) (x : Γ(M, V)) :
    dsimp% M.presheaf.map hUV (f • x) = f • M.presheaf.map hUV x :=
  ((modulesSpecToSheaf.obj M).obj.map hUV).hom.map_smul f x

lemma isUnit_algebraMap_end_of_le_basicOpen (f : R) (hf : U ≤ PrimeSpectrum.basicOpen f) :
    IsUnit (algebraMap R (Module.End R Γ(M, U)) f) := by
  rw [Module.End.isUnit_iff]
  have : ⇑((algebraMap R (Module.End ↑R ↑Γ(M, U))) f) =
      algebraMap (Γ(Spec R, U)) (Module.End Γ(Spec R, U) Γ(M, U))
        (((Spec R).presheaf.map (homOfLE hf).op) <| algebraMap R _ f) :=
    rfl
  rw [this, ← Module.End.isUnit_iff]
  exact ((IsLocalization.Away.algebraMap_isUnit _).map _).map _

lemma isSMulRegular_of_le_basicOpen {f : R} (hle : U ≤ PrimeSpectrum.basicOpen f) :
    IsSMulRegular Γ(M, U) f := by
  intro x y hxy
  have := M.isUnit_algebraMap_end_of_le_basicOpen _ hle
  rw [Module.End.isUnit_iff] at this
  exact this.injective hxy

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma restrictAppIso_smul_Spec {S : CommRingCat.{u}} (f : R ⟶ S)
    [IsOpenImmersion (Spec.map f)] {U : (Spec S).Opens} (r : R)
    (x : Γ(M.restrict (Spec.map f), U)) :
    dsimp% (M.restrictAppIso (Spec.map f) U).hom (f r • x) =
      r • (M.restrictAppIso (Spec.map f) U).hom x := by
  rw [smul_Spec_def, smul_Spec_def]
  simp_rw [smul_restrictAppIso_hom_apply, ← ConcreteCategory.comp_apply, Category.assoc]
  have :
      f ≫ (ΓSpecIso S).inv ≫ (Spec S).presheaf.map U.leTop.op ≫ (Hom.appIso (Spec.map f) U).inv =
        (ΓSpecIso R).inv ≫ (Spec R).presheaf.map (Spec.map f ''ᵁ U).leTop.op := by
    simp [Iso.cancel_iso_inv_left, Hom.app_eq_appLE]
    rfl
  rw [this]

set_option linter.dupNamespace false in
@[deprecated (since := "2026-06-04")]
alias Scheme.Modules.restrictAppIso_smul_Spec := restrictAppIso_smul_Spec

end Scheme.Modules

/--
`M^~` as a sheaf of `𝒪_{Spec R}`-modules
-/
def tilde : (Spec R).Modules where
  val := moduleStructurePresheaf R M
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (structureSheafInType R M).2

namespace tilde

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation). The image of `tilde` under `modulesSpecToSheaf` is isomorphic to
`structurePresheafInModuleCat`. They are defeq as types but the `Smul` instance are not defeq. -/
noncomputable
def modulesSpecToSheafIso :
    (modulesSpecToSheaf.obj (tilde M)).1 ≅ structurePresheafInModuleCat R M :=
  NatIso.ofComponents (fun U ↦ LinearEquiv.toModuleIso
    (X₁ := (modulesSpecToSheaf.obj (tilde M)).presheaf.obj _)
    { __ := AddEquiv.refl _,
      map_smul' r m := IsScalarTower.algebraMap_smul (M := ((structureSheafInType R M).obj.obj U))
        ((structureSheafInType R R).obj.obj U) r m }) fun _ ↦ rfl

/-- The map from `M` to `Γ(M, U)`. This is a localization map when `U = D(f)`. -/
def toOpen (U : (Spec R).Opens) : M ⟶ (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op U) :=
  ModuleCat.ofHom (StructureSheaf.toOpenₗ R M U) ≫ ((modulesSpecToSheafIso M).app _).inv

@[reassoc (attr := simp)]
theorem toOpen_res (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U) :
    toOpen M U ≫ (modulesSpecToSheaf.obj (tilde M)).presheaf.map i.op = toOpen M V :=
  rfl

instance (f : R) : IsLocalizedModule.Away f (toOpen M (basicOpen f)).hom :=
  .of_linearEquiv (.powers f) (StructureSheaf.toOpenₗ R M (basicOpen f))
    ((modulesSpecToSheafIso M).app _).toLinearEquiv.symm

noncomputable
instance (x : PrimeSpectrum.Top R) : Module R ((tilde M).presheaf.stalk x) :=
  inferInstanceAs (Module R ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x))

/--
If `x` is a point of `Spec R`, this is the morphism of `R`-modules from `M` to the stalk of
`M^~` at `x`.
-/
noncomputable def toStalk (x : PrimeSpectrum.Top R) :
    ModuleCat.of R M ⟶ ModuleCat.of R ((tilde M).presheaf.stalk x) :=
  ModuleCat.ofHom (StructureSheaf.toStalkₗ ..)

instance (x : PrimeSpectrum.Top R) :
    IsLocalizedModule x.asIdeal.primeCompl (toStalk M x).hom :=
  inferInstanceAs (IsLocalizedModule x.asIdeal.primeCompl (StructureSheaf.toStalkₗ ..))

/-- The tilde construction is functorial. -/
protected noncomputable def map {M N : ModuleCat R} (f : M ⟶ N) : tilde M ⟶ tilde N :=
  SpecModulesToSheafFullyFaithful.preimage ⟨(modulesSpecToSheafIso M).hom ≫
    { app U := ModuleCat.ofHom (StructureSheaf.comapₗ f.hom _ _ .rfl) } ≫
    (modulesSpecToSheafIso N).inv⟩

@[simp, reassoc]
protected lemma map_id {M : ModuleCat R} : tilde.map (𝟙 M) = 𝟙 _ := by
  ext p x
  exact Subtype.ext (funext fun y ↦ DFunLike.congr_fun (LocalizedModule.map_id _) _)

@[simp, reassoc]
protected lemma map_comp {M N P : ModuleCat R} (f : M ⟶ N) (g : N ⟶ P) :
    tilde.map (f ≫ g) = tilde.map f ≫ tilde.map g := by
  ext p x
  exact Subtype.ext (funext
    fun y ↦ DFunLike.congr_fun (IsLocalizedModule.map_comp' y.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl N)
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl P) _ _) _)

@[reassoc (attr := simp)]
lemma toOpen_map_app {M N : ModuleCat R} (f : M ⟶ N)
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    toOpen M U ≫ (modulesSpecToSheaf.map (tilde.map f)).1.app _ =
    f ≫ toOpen N U := by
  ext x; exact Subtype.ext (funext fun y ↦ IsLocalizedModule.map_apply y.1.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
     (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl N) _ x)

variable (R) in
/-- Tilde as a functor -/
@[simps] protected noncomputable def functor : ModuleCat R ⥤ (Spec (.of R)).Modules where
  obj := tilde
  map := tilde.map

instance isIso_toOpen_top {M : ModuleCat R} : IsIso (toOpen M ⊤) := by
  rw [toOpen, isIso_comp_right_iff, ConcreteCategory.isIso_iff_bijective]
  exact StructureSheaf.toOpenₗ_top_bijective

/-- The isomorphism between the global sections of `M^~` and `M`. -/
@[simps! hom]
noncomputable def isoTop (M : ModuleCat R) :
    M ≅ (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op ⊤) :=
  asIso (toOpen M ⊤)

@[deprecated (since := "2026-05-30")]
alias isUnit_algebraMap_end_basicOpen := Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen

end tilde

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- This is the counit of the tilde-Gamma adjunction. -/
noncomputable def Scheme.Modules.fromTildeΓ (M : (Spec (.of R)).Modules) :
    tilde ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) ⟶ M :=
  SpecModulesToSheafFullyFaithful.preimage
    ⟨TopCat.Sheaf.restrictHomEquivHom _ _ isBasis_basic_opens
    { app (f : Rᵒᵖ) := by
        refine (ModuleCat.ofHom (IsLocalizedModule.lift (.powers (M := R) f.unop)
          (tilde.toOpen _ (PrimeSpectrum.basicOpen f.unop)).hom
          ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op).hom ?_):)
        rw [Subtype.forall]
        change Submonoid.powers _ ≤ (IsUnit.submonoid _).comap _
        simp only [inducedFunctor_obj, Submonoid.powers_le, Submonoid.mem_comap]
        exact M.isUnit_algebraMap_end_of_le_basicOpen f.unop le_rfl
      naturality {f g : Rᵒᵖ} i := by
        letI N := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)
        ext1
        apply IsLocalizedModule.ext (.powers (M := R) f.unop)
          (tilde.toOpen _ (PrimeSpectrum.basicOpen (R := R) f.unop)).hom
        · rw [Subtype.forall]
          change Submonoid.powers _ ≤ (IsUnit.submonoid _).comap _
          simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
          obtain ⟨n, a, e⟩ : ∃ n, f.unop ∣ g.unop ^ n := by
            simpa only [Ideal.mem_radical_iff, Ideal.mem_span_singleton] using
              (basicOpen_le_basicOpen_iff _ _).mp (i.1.hom.le)
          refine ((Commute.isUnit_mul_iff (b := algebraMap R _ a) (.map (.all _ _) _)).mp ?_).1
          rw [← map_mul, ← e, map_pow]
          exact (M.isUnit_algebraMap_end_of_le_basicOpen g.unop le_rfl).pow n
        · dsimp [← ModuleCat.hom_comp]
          rw [tilde.toOpen_res_assoc]
          ext x
          dsimp
          simp only [IsLocalizedModule.lift_apply, ← ModuleCat.comp_apply, ← Functor.map_comp]
          rfl }⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma Scheme.Modules.toOpen_fromTildeΓ_app (M : (Spec (.of R)).Modules) (U) :
    tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) U ≫
      (modulesSpecToSheaf.map M.fromTildeΓ).1.app (.op U) =
    (modulesSpecToSheaf.obj M).1.map (homOfLE le_top).op := by
  wlog hU : U = PrimeSpectrum.basicOpen 1 generalizing U
  · rw [← tilde.toOpen_res _ (PrimeSpectrum.basicOpen 1) _ (homOfLE (by simp)), Category.assoc,
      NatTrans.naturality, ← Category.assoc, this, ← Functor.map_comp, ← op_comp, homOfLE_comp]
    simp
  subst hU
  simp only [fromTildeΓ,
    homOfLE_leOfHom, Functor.FullyFaithful.map_preimage, TopCat.Sheaf.extend_hom_app]
  ext x
  refine (IsLocalizedModule.lift_apply (.powers (M := R) 1)
    (tilde.toOpen _ (PrimeSpectrum.basicOpen (R := R) 1)).hom
    ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op).hom (by simp) x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- This is the counit of the tilde-Gamma adjunction. -/
noncomputable def Scheme.Modules.fromTildeΓNatTrans :
    moduleSpecΓFunctor (R := R) ⋙ tilde.functor (R := R) ⟶ 𝟭 _ where
  app := fromTildeΓ
  naturality {M N} f := by
    apply SpecModulesToSheafFullyFaithful.map_injective
    apply CategoryTheory.Sheaf.hom_ext
    apply (TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens).symm.injective
    ext r : 3
    apply IsLocalizedModule.ext (.powers (M := R) r.unop)
      (tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤))
        (PrimeSpectrum.basicOpen (R := R) r.unop)).hom
    · rw [Subtype.forall]
      change Submonoid.powers _ ≤ (IsUnit.submonoid _).comap _
      simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      exact N.isUnit_algebraMap_end_of_le_basicOpen r.unop le_rfl
    dsimp [TopCat.Sheaf.restrictHomEquivHom, Functor.IsCoverDense.restrictHomEquivHom,
      moduleSpecΓFunctor, Sheaf.forget]
    simp only [← ModuleCat.hom_comp, Functor.map_comp]
    congr 1
    erw [tilde.toOpen_map_app_assoc, toOpen_fromTildeΓ_app N (PrimeSpectrum.basicOpen r.unop),
      toOpen_fromTildeΓ_app_assoc M (PrimeSpectrum.basicOpen r.unop),
      ← (modulesSpecToSheaf.map f).hom.naturality]

/-- `tilde.isoTop` bundled as a natural isomorphism.
This is the unit of the tilde-Gamma adjunction. -/
def tilde.toTildeΓNatIso : 𝟭 _ ≅ tilde.functor R ⋙ moduleSpecΓFunctor :=
  NatIso.ofComponents tilde.isoTop fun f ↦ (tilde.toOpen_map_app f _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open Scheme.Modules in
/-- The tilde-Gamma adjunction. -/
def tilde.adjunction : tilde.functor R ⊣ moduleSpecΓFunctor where
  unit := toTildeΓNatIso.hom
  counit := fromTildeΓNatTrans
  left_triangle_components M := by
    apply SpecModulesToSheafFullyFaithful.map_injective
    apply CategoryTheory.Sheaf.hom_ext
    apply (TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens).symm.injective
    ext r : 3
    apply IsLocalizedModule.ext (.powers (M := R) r.unop)
      (toOpen _ (PrimeSpectrum.basicOpen (R := R) r.unop)).hom
    · rw [Subtype.forall]
      change Submonoid.powers _ ≤ (IsUnit.submonoid _).comap _
      simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen r.unop le_rfl
    dsimp [toTildeΓNatIso, isoTop,
      TopCat.Sheaf.restrictHomEquivHom, Functor.IsCoverDense.restrictHomEquivHom,
      fromTildeΓNatTrans, moduleSpecΓFunctor, Sheaf.forget, sheafToPresheaf]
    simp only [← ModuleCat.hom_comp, Functor.map_comp]
    congr 1
    rw [ObjectProperty.FullSubcategory.comp_hom]
    dsimp
    rw [toOpen_map_app_assoc, toOpen_fromTildeΓ_app]
    rfl
  right_triangle_components M := by
    dsimp [toTildeΓNatIso, fromTildeΓNatTrans, tilde.isoTop, moduleSpecΓFunctor, Sheaf.forget]
    rw [toOpen_fromTildeΓ_app]
    exact (modulesSpecToSheaf.obj M).obj.map_id _

instance : IsIso (tilde.adjunction (R := R)).unit := by
  dsimp [tilde.adjunction]; infer_instance

/-- The tilde functor is fully faithful. We will later show that the essential image is
exactly quasi-coherent modules. -/
def tilde.fullyFaithfulFunctor : (tilde.functor R).FullyFaithful :=
  tilde.adjunction.fullyFaithfulLOfIsIsoUnit

instance : (tilde.functor R).Full := tilde.fullyFaithfulFunctor.full
instance : (tilde.functor R).Faithful := tilde.fullyFaithfulFunctor.faithful
instance : (tilde.functor R).IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
instance : (tilde.functor R).Additive :=
  have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts (tilde.functor R)
  Functor.additive_of_preservesBinaryBiproducts _

section

variable {M N : ModuleCat R} (f g : M ⟶ N)

@[simp] lemma tilde.map_zero : tilde.map (0 : M ⟶ N) = 0 :=
  (tilde.functor R).map_zero _ _

@[simp] lemma tilde.map_add : tilde.map (f + g) = tilde.map f + tilde.map g :=
  (tilde.functor R).map_add

@[simp] lemma tilde.map_sub : tilde.map (f - g) = tilde.map f - tilde.map g :=
  (tilde.functor R).map_sub

@[simp] lemma tilde.map_neg : tilde.map (-f) = - tilde.map f :=
  (tilde.functor R).map_neg

end

lemma isIso_fromTildeΓ_iff {M : (Spec R).Modules} :
    IsIso M.fromTildeΓ ↔ (tilde.functor R).essImage M :=
  tilde.adjunction.isIso_counit_app_iff_mem_essImage

section IsQuasicoherent

open Limits

/-- Tilde of `R` as an `R`-module is isomorphic to the structure sheaf `𝒪_{Spec R}`. -/
noncomputable
def tildeSelf : tilde (ModuleCat.of R R) ≅ SheafOfModules.unit.{u} _ := .refl _

instance : IsIso (Scheme.Modules.fromTildeΓ (SheafOfModules.unit.{u} (Spec R).ringCatSheaf)) :=
  isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩

/-- Tilde of direct sums of `R` as an `R`-module is isomorphic to the free sheaf. -/
noncomputable
def tildeFinsupp (ι : Type u) : tilde (ModuleCat.of R (ι →₀ R)) ≅ SheafOfModules.free.{u} ι :=
  letI H : IsColimit <| (tilde.functor R).mapCocone (ModuleCat.finsuppCocone R R ι) :=
    isColimitOfPreserves (tilde.functor R) (ModuleCat.finsuppCoconeIsColimit R R ι)
  letI iso : (Discrete.functor fun (_ : ι) ↦ ModuleCat.of R R) ⋙ tilde.functor R ≅
         Discrete.functor fun _ ↦ SheafOfModules.unit.{u} _ :=
      Discrete.natIso (fun _ ↦ tildeSelf)
  IsColimit.coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv iso.symm _).symm H) (coproductIsCoproduct _)

instance (ι : Type u) :
    IsIso (Scheme.Modules.fromTildeΓ (R := R) (SheafOfModules.free.{u} ι)) :=
  isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeFinsupp _⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Given a presentation of a module `M`, we may construct an associated presentation of `M^~`. -/
noncomputable
def presentationTilde (s : Set M) (hs : Submodule.span R s = ⊤)
    (t : Set (s →₀ R))
    (ht : Submodule.span R t = LinearMap.ker (Finsupp.linearCombination R ((↑) : s → M))) :
    (tilde M).Presentation := by
  haveI H₁ : Function.Exact
      (ModuleCat.ofHom (Finsupp.linearCombination (α := t) R (↑)))
      (ModuleCat.ofHom (Finsupp.linearCombination (α := s) (M := M) R (↑))) :=
    (LinearMap.exact_iff.mpr (by simp [Finsupp.range_linearCombination, ht]))
  refine SheafOfModules.presentationOfIsCokernelFree.{u}
      ((tildeFinsupp t).inv ≫ tilde.map (ModuleCat.ofHom (Finsupp.linearCombination R (↑))) ≫
        (tildeFinsupp s).hom) ((tildeFinsupp s).inv ≫
          tilde.map (ModuleCat.ofHom (Finsupp.linearCombination R (↑)))) (by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Preadditive.IsIso.comp_left_eq_zero]
    rw [← tilde.map_comp, ← ModuleCat.ofHom_comp]
    convert! tilde.map_zero
    exact congr(ModuleCat.ofHom $(H₁.linearMap_comp_eq_zero))) ?_
  letI h₁ := ModuleCat.isColimitCokernelCofork _ _ H₁
    (by simp [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hs])
  refine IsCokernel.ofIso _ (CokernelCofork.mapIsColimit _ h₁ (tilde.functor R)) _ (tildeFinsupp t)
    (tildeFinsupp s) (.refl _) (by simp) (by simp)

instance : (tilde M).IsQuasicoherent :=
  (presentationTilde.{u} _ .univ (by simp) _ (Submodule.span_eq _)).isQuasicoherent

set_option backward.isDefEq.respectTransparency false in
lemma isIso_fromTildeΓ_of_presentation (M : (Spec R).Modules) (P : M.Presentation) :
    IsIso M.fromTildeΓ := by
  rw [isIso_fromTildeΓ_iff]
  let g := (tilde.functor _).preimage <| (tildeFinsupp _).hom ≫ P.relations.π ≫ kernel.ι _ ≫
    (tildeFinsupp _).inv
  let iso : cokernel ((tilde.functor R).map g) ≅ cokernel (P.relations.π ≫ kernel.ι _) := by
    refine cokernel.mapIso _ _ (tildeFinsupp _) (tildeFinsupp _) ?_
    simp only [g, (tilde.functor R).map_preimage]
    simp
  exact ⟨cokernel g, ⟨PreservesCokernel.iso (tilde.functor R) g ≪≫ iso ≪≫
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) P.isColimit⟩⟩

section IsLocalizing

variable (M : (Spec R).Modules) (f : R) {S : CommRingCat.{u}} (φ : R ⟶ S)

open TopologicalSpace

/-- A sheaf `M` of `R-modules` is localizing if for all `f` in `R`, the restriction map
from `M(⊤)` to `M(D(f))` is localization with respect to `f`. -/
abbrev IsLocalizing (M : TopCat.Sheaf (ModuleCat R) (Spec R)) : Prop :=
  ∀ f : R, IsLocalizedModule (.powers f) (M.obj.map (basicOpen f).leTop.op).hom

theorem isLocalizing_of_iso {M N : TopCat.Sheaf (ModuleCat R) (Spec R)} (φ : M ≅ N)
    (hM : IsLocalizing M) :
    IsLocalizing N := by
  intro f
  rw [← IsLocalizedModule.comp_iff_of_bijective_left _ _ <|
    ConcreteCategory.bijective_of_isIso (φ.inv.hom.app (op (basicOpen f))), ← ModuleCat.hom_comp,
    φ.inv.hom.naturality (basicOpen f).leTop.op, ModuleCat.hom_comp,
    IsLocalizedModule.comp_iff_of_bijective_right _ _ <| ConcreteCategory.bijective_of_isIso _]
  exact hM f

theorem isLocalizing_iff_of_iso {M N : TopCat.Sheaf (ModuleCat R) (Spec R)} (φ : M ≅ N) :
    IsLocalizing M ↔ IsLocalizing N :=
  ⟨fun h => isLocalizing_of_iso φ h, fun h => isLocalizing_of_iso φ.symm h⟩

theorem isLocalizing_of_isIso_app_top {M N : TopCat.Sheaf (ModuleCat.{u} R) (Spec R)} {φ : M ⟶ N}
    (h : IsIso (φ.hom.app (op ⊤))) (hM : IsLocalizing M) (hN : IsLocalizing N) :
    IsIso φ := by
  refine TopCat.Sheaf.isIso_iff_isIso_basis (φ := φ) isBasis_basic_opens (fun f => ?_)
  refine ModuleCat.isIso_of_isLocalizedModule_comp (hM f) ?_
  rw [φ.hom.naturality]
  exact IsLocalizedModule.of_linearEquiv_right _ _ (asIso (φ.hom.app (op ⊤))).toLinearEquiv

theorem isLocalizing_tilde (M : ModuleCat R) :
    IsLocalizing (modulesSpecToSheaf.obj (tilde M)) := by
  intro f
  -- We can't rewrite with `tilde.toOpen_res` below, because of def-eq abuse between
  -- `Spec R` and `PrimeSpectrum R`.
  have heq : tilde.toOpen M ⊤ ≫ (modulesSpecToSheaf.obj (tilde M)).obj.map (basicOpen f).leTop.op =
      tilde.toOpen M (basicOpen f) :=
    tilde.toOpen_res _ _ _ _
  rw [← IsLocalizedModule.comp_iff_of_bijective_right _ _ <|
    ConcreteCategory.bijective_of_isIso (tilde.toOpen M ⊤), ← ModuleCat.hom_comp, heq]
  infer_instance

/-- An `𝓞_Spec R` module `M` is isomorphic to `Γ(M)^~` if and only if it is localizing
as a sheaf of `R` modules -/
theorem isIso_fromTildeΓ_iff_isLocalizing (M : (Spec R).Modules) :
    IsIso M.fromTildeΓ ↔ IsLocalizing (modulesSpecToSheaf.obj M) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← isLocalizing_iff_of_iso (modulesSpecToSheaf.mapIso (asIso M.fromTildeΓ))]
    exact isLocalizing_tilde _
  · rw [← isIso_iff_of_reflects_iso _ modulesSpecToSheaf]
    refine isLocalizing_of_isIso_app_top ?_ (isLocalizing_tilde _) h
    rw [← isIso_comp_left_iff (tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) ⊤),
      Scheme.Modules.toOpen_fromTildeΓ_app]
    simpa using IsIso.id _

/-- `Scheme.Modules.pushforward` and `modulesSpecToSheaf` commute -/
def pushforwardCompModulesSpecToSheafIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ modulesSpecToSheaf ≅
      modulesSpecToSheaf ⋙ TopCat.Sheaf.pushforward (ModuleCat S) (Spec.map φ).base ⋙
      sheafCompose _ (ModuleCat.restrictScalars φ.hom) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (SheafOfModules.pushforwardCompForgetToSheafModuleCat _ _ _
    (initialOpOfTerminal isTerminalTop)) _ ≪≫ Functor.associator _ _ _ ≪≫
    (Functor.isoWhiskerLeft _ (Functor.associator _ _ _)) ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.sheafComposePushforwardComp φ) ≪≫
    (Functor.associator _ _ _).symm

open scoped ModuleCat.Algebra in
theorem isLocalizing_pushforward_of_isLocalizing {M : (Spec S).Modules}
    (h : IsLocalizing (modulesSpecToSheaf.obj M)) :
    IsLocalizing (modulesSpecToSheaf.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj M)) := by
  rw [← Functor.comp_obj,
  isLocalizing_iff_of_iso ((pushforwardCompModulesSpecToSheafIso φ).app M)]
  have : CommRing ((Spec S).ringCatSheaf.obj.obj ((Opens.map (Spec.map φ).base).op.obj (op ⊤))) :=
    inferInstanceAs (CommRing Γ(Spec S, ⊤))
  algebraize [φ.hom]
  exact fun f => IsLocalizedModule.restrictScalars_powers f _ (h := h (φ f))

/- TODO: Once `IsIso M.fromTildeΓ` is shown to be equivalent to `M` being quasicoherent, use
this to show that quasicoherent sheaves pushforward to quasicoherent sheaves for affine morphisms -/
theorem isIso_fromTildeΓ_pushforward (M : (Spec S).Modules) [h : IsIso M.fromTildeΓ] :
    IsIso ((Scheme.Modules.pushforward (Spec.map φ)).obj M).fromTildeΓ := by
  simp_all only [isIso_fromTildeΓ_iff_isLocalizing]
  exact isLocalizing_pushforward_of_isLocalizing φ h

end IsLocalizing

set_option backward.isDefEq.respectTransparency false in
def Scheme.Modules.presentationRestrict {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] {M : X.Modules} (pres : M.Presentation) :
    (M.restrict f).Presentation :=
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor f) :=
    inferInstance
  pres.map (Scheme.Modules.restrictFunctor.{u} f) (Scheme.Modules.restrictUnitIso _).symm

set_option backward.isDefEq.respectTransparency false in
lemma Scheme.Modules.exists_isOpenCover_presentation {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] :
    ∃ (ι : Type u) (U : ι → X.Opens) (_ : ∀ i, (M.restrict (U i).ι).Presentation),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) := by
  obtain ⟨⟨I, W, cov, pres⟩⟩ := SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := M)
  choose κ hsub heq using fun i ↦ Opens.isBasis_iff_cover.mp X.isBasis_affineOpens (W i)
  refine ⟨Σ (i : I), κ i, fun j ↦ j.2, fun i ↦ ?_, ?_, ?_⟩
  · let u := X.homOfLE (U := i.2) (V := W i.1) (by simp [heq, le_sSup])
    have : PreservesColimitsOfSize.{u, u} (restrictFunctor u) := inferInstance
    let F := (overEquiv (W i.1)).functor ⋙ restrictFunctor u
    let iso : SheafOfModules.overFunctor X.ringCatSheaf _ ⋙ F ≅ restrictFunctor
      (Scheme.Opens.ι i.2.1) := (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv _) _ ≪≫
        (restrictFunctorComp _ _).symm ≪≫ (restrictFunctorCongr (by simp [u]))
    exact SheafOfModules.Presentation.ofIsIso.{u, u, u} (iso.app M).hom <|
      (pres i.1).map F (Scheme.Modules.restrictUnitIso _).symm
  · rw [Opens.coversTop_iff, IsOpenCover] at cov
    rw [IsOpenCover, iSup_sigma, ← cov]
    refine iSup_congr fun i ↦ ?_
    rw [heq i, sSup_eq_iSup']
  · intro j
    exact hsub _ j.2.2

lemma Scheme.Modules.exists_affineOpenCover_presentation {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] :
    ∃ (𝒰 : Scheme.AffineOpenCover.{u} X),
      ∀ i, Nonempty (M.restrict (𝒰.f i)).Presentation := by
  obtain ⟨ι, U, pres, hU, hU'⟩ := M.exists_isOpenCover_presentation
  refine ⟨Scheme.AffineOpenCover.ofIsOpenCover _ hU hU', fun i ↦ ⟨?_⟩⟩
  exact SheafOfModules.Presentation.ofIsIso.{u, u, u} ((restrictFunctorComp _ _).app M).inv <|
    (presentationRestrict (hU' i).isoSpec.inv (pres i))

namespace QuasicoherentTilde

variable (M : (Spec R).Modules)

/-- Auxiliary structure used in the proof of `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`.
These are conditions d1) and d2) from [Theoreme 1.4.1, grothendieck-1971]. -/
private structure Aux (V : (Spec R).Opens) where
  existence (f : R) (hf : basicOpen f ≤ V) (s : Γ(M, basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, V)), M.presheaf.map (homOfLE hf).op t = f ^ n • s
  uniqueness (f : R) (hf : basicOpen f ≤ V) (t : Γ(M, V)) :
    M.presheaf.map (.op <| homOfLE hf) t = (0 : Γ(M, basicOpen f)) →
    ∃ (n : ℕ), f ^ n • t = 0

set_option backward.isDefEq.respectTransparency false in
private lemma Aux.of_le {M : (Spec R).Modules} {V : (Spec R).Opens} (g : R) (hg : basicOpen g ≤ V)
    (hV : Aux M V) :
    Aux M (basicOpen g) where
  existence f hfg s := by
    obtain ⟨n, t, ht⟩ := hV.existence f (le_trans hfg hg) s
    use n, M.presheaf.map (homOfLE hg).op t
    simp [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, ht]
  uniqueness f hfg t ht := by
    obtain ⟨n, t', ht'⟩ := hV.existence g hg t
    obtain ⟨m, hm⟩ := hV.uniqueness _ (le_trans hfg hg) t' <| by
      rw [← homOfLE_comp hfg hg, op_comp, M.presheaf.map_comp_apply, ht', M.map_smul_Spec, ht]
      simp
    refine ⟨m, ((M.isSMulRegular_of_le_basicOpen le_rfl).pow n).right_eq_zero_of_smul ?_⟩
    simp [smul_comm, ← ht', ← M.map_smul_Spec, hm]

set_option backward.isDefEq.respectTransparency false in
/-- [Lemme 1.4.1.1][grothendieck-1971] -/
private lemma Aux.of_eq_iSup_basicOpen {M : (Spec R).Modules} (V : (Spec R).Opens)
    {ι : Type*} [Finite ι] (g : ι → R) (hg : V = ⨆ i, basicOpen (g i))
    (h₁ : ∀ (i : ι), Aux M (basicOpen (g i))) :
    Aux M V := by
  have h₂ (i j : ι) : Aux M (basicOpen (g i * g j)) :=
    .of_le _ (basicOpen_mul_le_left _ _) (h₁ i)
  have hgle (i : ι) : basicOpen (g i) ≤ V := by rw [hg]; exact le_iSup_iff.mpr fun b a ↦ a i
  have h (f : R) (hf : basicOpen f ≤ V) (t : Γ(M, V)) (hs : M.presheaf.map (homOfLE hf).op t = 0) :
      ∃ (n : ℕ), f ^ n • t = 0 := by
    have (i : ι) : ∃ (n : ℕ), M.presheaf.map (homOfLE (hgle i)).op (f ^ n • t) = 0 := by
      have := (h₁ i).uniqueness (f * g i) (basicOpen_mul_le_right f (g i))
        (M.presheaf.map (homOfLE (hgle i)).op t) ?_
      · obtain ⟨n, hn⟩ := this
        use n
        rw [mul_pow, mul_comm, mul_smul, ← Scheme.Modules.map_smul_Spec] at hn
        exact ((M.isSMulRegular_of_le_basicOpen le_rfl).pow n).right_eq_zero_of_smul hn
      · rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp ((basicOpen_mul_le_left f (g i))) hf, op_comp, M.presheaf.map_comp_apply]
        simp [hs]
    choose n hn using this
    use ⨆ i, n i
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i ↦ basicOpen (g i)) _
      (fun i ↦ homOfLE (by rw [hg]; exact le_iSup_iff.mpr fun b a ↦ a i))
    · simp [hg]
    · intro i
      simp only [homOfLE_leOfHom, map_zero]
      have : n i ≤ ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by lia
      rw [this, pow_add, mul_smul, Scheme.Modules.map_smul_Spec, hn i]
      simp
  refine ⟨fun f hf s ↦ ?_, h⟩
  have hug (i : ι) (m : ℕ) :
      IsUnit (algebraMap R (Module.End R Γ(M, basicOpen (g i))) (g i ^ m)) := by
    rw [map_pow]
    exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (g i) le_rfl).pow m
  let s' (i : ι) : Γ(M, basicOpen (f * g i)) :=
    M.presheaf.map (homOfLE <| basicOpen_mul_le_left f (g i)).op s
  have (i : ι) : ∃ (n : ℕ) (t : Γ(M, basicOpen (g i))),
      f ^ n • s' i =
        M.presheaf.map (homOfLE (basicOpen_mul_le_right f (g i))).op t := by
    obtain ⟨n, t', ht'⟩ := (h₁ i).existence (f * g i) (basicOpen_mul_le_right f (g i)) (s' i)
    rw [mul_pow, mul_smul, smul_comm] at ht'
    obtain ⟨ψ, hψ⟩ := IsUnit.exists_right_inv (hug i n)
    use n, ψ t'
    apply ((M.isSMulRegular_of_le_basicOpen (basicOpen_mul_le_right f (g i))).pow n)
    dsimp
    rw [← ht', ← Scheme.Modules.map_smul_Spec]
    congr 1
    have := congr($hψ t')
    rw [Module.End.mul_apply, Module.End.one_apply] at this
    exact this.symm
  choose n t' ht' using this
  let N : ℕ := ⨆ i, n i
  have (i : ι) : n i ≤ N := le_ciSup (Finite.bddAbove_range _) _
  have hN (i : ι) : N = (N - n i) + n i := by grind
  let t (i : ι) : Γ(M, basicOpen (g i)) := f ^ (N - n i) • t' i
  have ht (i : ι) :
      f ^ N • s' i = M.presheaf.map (homOfLE (basicOpen_mul_le_right f (g i))).op (t i) := by
    rw [hN i, pow_add, mul_smul, ht', M.map_smul_Spec]
  obtain ⟨K, hK⟩ : ∃ (K : ℕ), ∀ (i j : ι),
      M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (f ^ K • t i) =
        M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (f ^ K • t j) := by
    have (i j : ι) : ∃ (m : ℕ),
        M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (f ^ m • t i) =
          M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (f ^ m • t j) := by
      have := (h₂ i j).uniqueness (f * (g i * g j)) (basicOpen_mul_le_right _ _)
        (M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (t i) -
          M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (t j)) ?_
      · obtain ⟨m, hm⟩ := this
        use m
        apply (M.isSMulRegular_of_le_basicOpen le_rfl).pow m
        rw [smul_sub, sub_eq_zero] at hm
        rw [M.map_smul_Spec _ (f ^ m), M.map_smul_Spec _ (f ^ m)]
        dsimp
        rwa [← mul_smul, ← mul_smul, ← mul_pow, ← mul_comm f]
      · have hfgigi : basicOpen (f * (g i * g j)) ≤ basicOpen (f * g i) := by
          rw [← mul_assoc]
          exact basicOpen_mul_le_left _ _
        have hfgigj : basicOpen (f * (g i * g j)) ≤ basicOpen (f * g j) := by
          rw [mul_comm (g i) (g j), ← mul_assoc]
          exact basicOpen_mul_le_left _ _
        rw [map_sub,
          ← M.presheaf.map_comp_apply, ← op_comp,
          ← M.presheaf.map_comp_apply, ← op_comp,
          homOfLE_comp, homOfLE_comp,
          ← homOfLE_comp hfgigi (basicOpen_mul_le_right f (g i)),
          ← homOfLE_comp hfgigj (basicOpen_mul_le_right f (g j))]
        rw [op_comp, M.presheaf.map_comp_apply, ← ht i, M.map_smul_Spec,
          ← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp]
        rw [op_comp, M.presheaf.map_comp_apply, ← ht j, M.map_smul_Spec,
          ← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, ← smul_sub, ← map_sub]
        simp
    choose m hm using this
    let K := ⨆ i, ⨆ j, m i j
    refine ⟨K, fun i j ↦ ?_⟩
    have : m i j ≤ K := by
      dsimp [K]
      apply le_ciSup_of_le (Finite.bddAbove_range _) i
      exact le_ciSup (Finite.bddAbove_range _) _
    have : K = (K - m i j) + m i j := by lia
    rw [this, pow_add, mul_smul, mul_smul, M.map_smul_Spec, M.map_smul_Spec _ (f ^ (K - m i j)),
      hm i j]
  refine ⟨N + K, ?_⟩
  have := TopCat.Sheaf.existsUnique_gluing' ⟨_, M.isSheaf⟩ (fun i ↦ basicOpen (g i)) V
    (fun i ↦ homOfLE (by rw [hg]; exact le_iSup_iff.mpr fun b a ↦ a i)) (by simp [hg])
    (fun i ↦ f ^ K • t i) ?_
  · obtain ⟨a, ha, -⟩ := this
    use a
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i ↦ basicOpen (f * g i)) _ ?_ ?_
        _ _ ?_
    · intro i
      exact homOfLE (basicOpen_mul_le_left f (g i))
    · rw [left_eq_inf.mpr hf, hg, inf_iSup_eq]
      simp_rw [basicOpen_mul]
      exact le_rfl
    · intro i
      change M.presheaf.map _ _ = M.presheaf.map _ _
      rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
        ← homOfLE_comp (basicOpen_mul_le_right _ _) (hgle i), op_comp, M.presheaf.map_comp_apply,
        M.map_smul_Spec, ha]
      rw [M.map_smul_Spec]
      rw [pow_add]
      simp_rw [mul_comm]
      rw [mul_smul, ht i]
  · intro i j
    change M.presheaf.map _ _ = M.presheaf.map _ _
    let iso : Γ(M, basicOpen (g i * g j)) ≅ Γ(M, basicOpen (g i) ⊓ basicOpen (g j)) :=
      M.presheaf.mapIso (eqToIso <| (basicOpen_mul (g i) (g j))).op |>.symm
    have : Function.Injective (M.presheaf.map (eqToHom <| (basicOpen_mul (g i) (g j))).op) :=
      ConcreteCategory.injective_of_mono_of_preservesPullback _
    apply this
    dsimp [Opens.infLELeft, Opens.infLERight]
    rw [← M.presheaf.map_comp_apply, ← op_comp, eqToHom_comp_homOfLE]
    rw [← M.presheaf.map_comp_apply, ← op_comp, eqToHom_comp_homOfLE]
    exact hK i j

set_option backward.isDefEq.respectTransparency false in
private lemma isLocalizing_iff_aux (M : (Spec R).Modules) :
    IsLocalizing (modulesSpecToSheaf.obj M) ↔ Aux M ⊤ := by
  let φ (f : R) := ModuleCat.Hom.hom ((modulesSpecToSheaf.obj M).obj.map (basicOpen f).leTop.op)
  refine ⟨fun h ↦ ?_, fun h f ↦ IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_⟩
  · have hf (f : R) : IsLocalizedModule.Away f (φ f) := h f
    refine ⟨fun f hle s ↦ ?_, fun f hle s hs ↦ ?_⟩
    · obtain ⟨n, y, hy⟩ := (hf f).surj _ _ s
      use n, y, hy.symm
    · obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers f) (φ f)).mp hs
      use n, hn
  · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
  · intro x
    obtain ⟨n, t, ht⟩ := h.existence _ _ x
    use n, t, ht.symm
  · intro x hx
    obtain ⟨n, hn⟩ := h.uniqueness _ _ _ hx
    use n, hn

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma _root_.TopCat.Presheaf.map_eqToHom_map_homOfLE {X : TopCat.{u}} (F : X.Presheaf Ab)
    {U V W : TopologicalSpace.Opens X} (hUV : Opposite.op U = .op V)
    (hVW : W ≤ V) :
    F.map (eqToHom hUV) ≫ F.map (homOfLE hVW).op = F.map (homOfLE <| by grind).op := by
  rw [← F.map_comp, eqToHom_comp_homOfLE_op]

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma _root_.TopCat.Presheaf.map_homOfLE_map_eqToHom {X : TopCat.{u}} (F : X.Presheaf Ab)
    {U V W : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (hUW : Opposite.op U = Opposite.op W) :
    F.map (homOfLE hUV).op ≫ F.map (eqToHom hUW) = F.map (homOfLE <| by grind).op := by
  rw [← F.map_comp, homOfLE_op_comp_eqToHom]

end

set_option backward.isDefEq.respectTransparency false in
private lemma aux_basicOpen_of_aux_restrict (M : (Spec R).Modules) (g : R)
    (h : Aux (M.restrict <|
        Spec.map <| CommRingCat.ofHom <| algebraMap R <| Localization.Away g) ⊤) :
      Aux M (basicOpen g) := by
  let a : R ⟶ CommRingCat.of (Localization.Away g) :=
    CommRingCat.ofHom <| algebraMap R _
  set ψ : Spec (.of <| Localization.Away g) ⟶ Spec (.of R) := Spec.map a
  set M' : (Spec (.of <| Localization.Away g)).Modules := M.restrict ψ
  have heq (f : R) (hf : basicOpen f ≤ basicOpen g) :
      basicOpen f = ψ ''ᵁ basicOpen ((ConcreteCategory.hom a) f) := by
    rw [← SpecMap_preimage_basicOpen, Scheme.Hom.image_preimage_eq_opensRange_inf]
    simp [a, ψ, hf]
  let iso : Γ(M', ⊤) ≅ Γ(M, basicOpen g) :=
    M.restrictAppIso _ _ ≪≫ M.presheaf.mapIso (eqToIso <| by simp [ψ, a]).op
  let e (f : R) (hf : basicOpen f ≤ basicOpen g) :
      Γ(M', basicOpen (a f)) ≅ Γ(M, basicOpen f) :=
    M.restrictAppIso ψ (basicOpen (a f)) ≪≫ M.presheaf.mapIso (eqToIso <| heq f hf).op
  refine ⟨?_, ?_⟩
  · intro f hf s
    obtain ⟨n, t, ht⟩ := h.existence (a f) le_top ((e _ hf).inv s)
    use n, iso.hom t
    have := congr((e _ hf).hom $ht)
    simp only [homOfLE_leOfHom, M'] at this
    rw [← ConcreteCategory.comp_apply] at this
    simp only [homOfLE_leOfHom, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
      eqToHom_op, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv, e] at this
    simp only [homOfLE_leOfHom, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
      eqToHom_op, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, iso]
    simp only [homOfLE_leOfHom, Scheme.Modules.map_restrictAppIso_hom_assoc, AddCommGrpCat.hom_comp,
      AddMonoidHom.coe_comp, Function.comp_apply, ← map_pow, ψ] at this
    rw [Scheme.Modules.restrictAppIso_smul_Spec] at this
    simp only [homOfLE_leOfHom, Iso.inv_hom_id_apply, Scheme.Modules.map_smul_Spec,
      eqToHom_map_comp_apply, eqToHom_refl, CategoryTheory.Functor.map_id, AddCommGrpCat.hom_id,
      AddMonoidHom.id_apply] at this
    rw [TopCat.Presheaf.map_eqToHom_map_homOfLE_apply]
    rw [TopCat.Presheaf.map_homOfLE_map_eqToHom_apply] at this
    exact this
  · intro f hf t ht
    obtain ⟨n, hn⟩ := h.uniqueness (a f) le_top (iso.inv t) <| by
      have := congr((e _ hf).inv $ht)
      simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv, eqToHom_op,
        AddCommGrpCat.hom_comp, homOfLE_leOfHom, AddMonoidHom.coe_comp, Function.comp_apply,
        map_zero, e] at this
      simp only [homOfLE_leOfHom, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv,
        eqToHom_op, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
        Scheme.Modules.restrictAppIso_inv_map_apply, M', iso]
      rw [← M.presheaf.map_comp_apply, eqToHom_comp_homOfLE_op]
      rw [← M.presheaf.map_comp_apply, homOfLE_op_comp_eqToHom] at this
      exact this
    use n
    have := congr(iso.hom $hn)
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, eqToHom_op,
      AddCommGrpCat.hom_comp, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv,
      AddMonoidHom.coe_comp, Function.comp_apply, map_zero, iso] at this
    rw [← map_pow, Scheme.Modules.restrictAppIso_smul_Spec] at this
    simp only [ψ] at this
    rw [M.map_smul_Spec] at this
    rw [Iso.inv_hom_id_apply] at this
    simp only [eqToHom_map_comp_apply, eqToHom_refl, CategoryTheory.Functor.map_id,
      AddCommGrpCat.hom_id, AddMonoidHom.id_apply] at this
    exact this

end QuasicoherentTilde

open QuasicoherentTilde in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `M` is a quasi-coherent `𝒪_{Spec R}` module, it is isomorphic to `Γ(M)^~`. -/
instance Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (M : (Spec R).Modules)
    [M.IsQuasicoherent] : IsIso M.fromTildeΓ := by
  rw [isIso_fromTildeΓ_iff_isLocalizing, isLocalizing_iff_aux]
  obtain ⟨ι, U, pres, hU, hU'⟩ := M.exists_isOpenCover_presentation
  obtain ⟨s, hs⟩ := hU.exists_finite_of_compactSpace
  choose κ hκ a ha using fun i : s ↦
    PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact (U i) (hU' i).isCompact
  refine Aux.of_eq_iSup_basicOpen _ (fun i : Sigma κ ↦ a _ i.2) ?_ ?_
  · rw [IsOpenCover] at hs
    rw [eq_comm, iSup_sigma, ← hs]
    exact iSup_congr fun i ↦ (ha i).symm
  · intro i
    let t := (Spec R).homOfLE (U := PrimeSpectrum.basicOpen (a _ i.2)) (V := U i.1)
      (by rw [ha]; exact le_iSup_of_le _ le_rfl)
    let iso : restrictFunctor (U i.1).ι ⋙ restrictFunctor ((basicOpenIsoSpecAway _).inv ≫ t) ≅
        restrictFunctor (Spec.map (CommRingCat.ofHom <| algebraMap _ _)) :=
      (restrictFunctorComp _ _).symm ≪≫
        restrictFunctorCongr (by simp [t, basicOpenIsoSpecAway])
    let pres := SheafOfModules.Presentation.ofIsIso.{u, u, u} (iso.app M).hom <|
      presentationRestrict ((basicOpenIsoSpecAway _).inv ≫ t) (pres i.1)
    have : IsIso _ := isIso_fromTildeΓ_of_presentation (M.restrict _) pres
    rw [isIso_fromTildeΓ_iff_isLocalizing, isLocalizing_iff_aux] at this
    exact aux_basicOpen_of_aux_restrict _ _ this

set_option backward.isDefEq.respectTransparency false in
/-- An `𝒪_{Spec R}` module `M` is quasicoherent if and only if it is isomorphic to `Γ(M)^~`. -/
theorem isQuasicoherent_iff_isIso_fromTildeΓ (M : (Spec R).Modules) :
    M.IsQuasicoherent ↔ IsIso M.fromTildeΓ := by
  refine ⟨fun h ↦ inferInstance, fun h ↦ ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (asIso <| M.fromTildeΓ) inferInstance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma essImage_tilde : (tilde.functor R).essImage =
    SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf := by
  refine le_antisymm ?_ ?_
  · intro M ⟨N, ⟨e⟩⟩
    exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e
      (by dsimp; infer_instance)
  · intro M (h : M.IsQuasicoherent)
    exact ⟨((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)), ⟨asIso <| M.fromTildeΓ⟩⟩

end IsQuasicoherent

end AlgebraicGeometry

namespace ModuleCat

@[deprecated (since := "2026-02-11")] noncomputable alias tilde := AlgebraicGeometry.tilde
@[deprecated (since := "2026-02-11")] noncomputable alias Tilde.toOpen := tilde.toOpen
@[deprecated (since := "2026-02-11")] alias Tilde.toOpen_res := tilde.toOpen_res
@[deprecated (since := "2026-02-11")] noncomputable alias Tilde.toStalk := tilde.toStalk

end ModuleCat
