/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel, Jujian Zhang, Weihong Xu,
  Andrew Yang, Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Limits.Preorder

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
lemma Scheme.Modules.restrictAppIso_smul_Spec {S : CommRingCat.{u}} (f : R ⟶ S)
    [IsOpenImmersion (Spec.map f)] {U : (Spec S).Opens} (r : R)
    (x : Γ(M.restrict (Spec.map f), U)) :
    dsimp% (M.restrictAppIso (Spec.map f) U).hom (f r • x) =
      r • (M.restrictAppIso (Spec.map f) U).hom x := by
  rw [Scheme.Modules.smul_Spec_def, Scheme.Modules.smul_Spec_def]
  simp_rw [smul_restrictAppIso_hom_apply, ← ConcreteCategory.comp_apply, Category.assoc]
  have :
      f ≫ (ΓSpecIso S).inv ≫ (Spec S).presheaf.map U.leTop.op ≫ (Hom.appIso (Spec.map f) U).inv =
        (ΓSpecIso R).inv ≫ (Spec R).presheaf.map (Spec.map f ''ᵁ U).leTop.op := by
    simp [Iso.cancel_iso_inv_left, Hom.app_eq_appLE]
    rfl
  rw [this]

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

end IsQuasicoherent

open CategoryTheory TopologicalSpace

variable {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]

open Limits
set_option backward.defeqAttrib.useBackward true in
lemma _root_.CategoryTheory.Limits.preservesLimit_walkingParallelPair_of_eq
    {C D : Type*} [Category* C] [Category* D] {K : WalkingParallelPair ⥤ C}
    (heq : K.map .left = K.map .right) (F : C ⥤ D) :
    PreservesLimit K F := by
  suffices h : ∀ {X Y : C} {f g : X ⟶ Y} (hfg : f = g), PreservesLimit (parallelPair f g) F by
    have := h heq
    exact preservesLimit_of_iso_diagram _ (diagramIsoParallelPair _).symm
  rintro X Y f g rfl
  refine preservesLimit_of_preserves_limit_cone (isLimitIdFork rfl) ?_
  exact (isLimitMapConeForkEquiv F _).symm (by simpa using! isLimitIdFork rfl)

instance {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f f) F :=
  Limits.preservesLimit_walkingParallelPair_of_eq rfl _

instance (priority := low) {C D : Type*} [Category* C] [Category* D] [Quiver.IsThin C] (F : C ⥤ D) :
    Limits.PreservesLimitsOfShape Limits.WalkingParallelPair F := by
  constructor
  intro K
  exact Limits.preservesLimit_walkingParallelPair_of_eq (Subsingleton.elim _ _) _

def _root_.CategoryTheory.Limits.isLimitEquivFanOfIsThin {C : Type*} [Category* C]
    [Quiver.IsThin C] {J : Type*} [Category* J] {K : J ⥤ C} (c : Cone K) :
    IsLimit c ≃ IsLimit (Fan.mk c.pt c.π.app) where
  toFun hc := Fan.IsLimit.mk _ (fun s ↦ hc.lift { pt := s.pt, π.app j := s.proj j })
    (by subsingleton) (by subsingleton)
  invFun h := { lift s := Fan.IsLimit.lift h s.π.app }

def _root_.CategoryTheory.isPullback_iff_isLimit_binaryFan_of_isThin {C : Type*} [Category* C]
    [Quiver.IsThin C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} :
    IsPullback fst snd f g ↔ Nonempty (IsLimit (BinaryFan.mk fst snd)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨BinaryFan.IsLimit.mk _ (fun u v ↦ h.lift u v (by subsingleton))
      (by subsingleton) (by subsingleton) (by subsingleton)⟩
  · exact ⟨⟨by subsingleton⟩,
      ⟨PullbackCone.IsLimit.mk _ (fun s ↦ BinaryFan.IsLimit.lift h.some s.fst s.snd)
      (by subsingleton) (by subsingleton) (by subsingleton)⟩⟩

instance (priority := low) {C D : Type*} [Category* C] [Category* D] [Quiver.IsThin C]
    [Quiver.IsThin D] (F : C ⥤ D)
    [PreservesLimitsOfShape (Discrete WalkingPair) F] :
    PreservesLimitsOfShape WalkingCospan F := by
  apply preservesLimitsOfShape_walkingCospan_of_forall_isPullback
  intro X Y Z f g hfg
  use pullback f g, pullback.fst f g, pullback.snd f g, .of_hasPullback f g
  rw [isPullback_iff_isLimit_binaryFan_of_isThin]
  constructor
  refine (BinaryFan.mk (pullback.fst f g) (pullback.snd f g)).isLimitMapConeEquiv ?_
  apply isLimitOfPreserves
  apply Nonempty.some
  rw [← CategoryTheory.isPullback_iff_isLimit_binaryFan_of_isThin (f := f) (g := g)]
  exact .of_hasPullback f g

lemma TopologicalSpace.Opens.coe_iInf {X : Type*} [TopologicalSpace X] {ι : Type*} [Finite ι]
    (U : ι → TopologicalSpace.Opens X) :
    (((⨅ i, U i) : Opens X) : Set X) = ⋂ i, U i := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih => rw [← e.iInf_comp, ← e.surjective.iInter_comp, ih]
  | h_empty => simp
  | h_option ih => rw [iInf_option, Set.iInter_option, Opens.coe_inf, ih]

instance {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f) {ι : Type*} [Nonempty ι]
    [Finite ι] :
    PreservesLimitsOfShape (Discrete ι) hf.functor := by
  apply +allowSynthFailures Limits.preservesLimitsOfShape_of_discrete
  intro g
  refine preservesLimit_of_preserves_limit_cone (Preorder.isLimitIInf g) ?_
  refine (Limits.Fan.isLimitMapConeEquiv _ _ _).symm (Preorder.isLimitOfIsGLB _ _ ?_)
  simp only [Discrete.range_functor, homOfLE_leOfHom, Fan.mk_pt]
  have : hf.functor.obj (⨅ i, g i) = ⨅ i, hf.functor.obj (g i) := by
    ext : 1
    simp only [IsOpenMap.coe_functor_obj, TopologicalSpace.Opens.coe_iInf]
    rw [Set.InjOn.image_iInter_eq]
    exact hf.injective.injOn
  rw [this]
  apply isGLB_iInf

instance {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f) :
    PreservesLimitsOfShape WalkingCospan hf.functor := by
  infer_instance

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesLimitsOfShape WalkingCospan (Scheme.Hom.opensFunctor f) := by
  dsimp [Scheme.Hom.opensFunctor]
  infer_instance

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Functor.PreservesOneHypercovers f.opensFunctor (Opens.grothendieckTopology _)
      (Opens.grothendieckTopology _) := by
  refine Functor.PreservesOneHypercovers.of_coverPreserving ?_
  exact Scheme.Hom.coverPreserving_opensFunctor f

set_option backward.isDefEq.respectTransparency false in
lemma Scheme.Modules.isQuasicoherent_restrictFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.restrictFunctor f).obj M).IsQuasicoherent := by
  letI α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf := { app U := (f.appIso U.unop).inv }
  have hα : IsIso α := NatIso.isIso_of_isIso_app _
  dsimp [restrictFunctor]
  convert SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u}
    (J := Opens.grothendieckTopology _) (J' := Opens.grothendieckTopology _) f.opensFunctor _ _
  · convert isIso_of_reflects_iso _ (ObjectProperty.ι _)
    · dsimp
      infer_instance
    · infer_instance
  · refine (SheafOfModules.fullyFaithfulForget _).preimageIso ?_
    refine PresheafOfModules.isoMk ?_ ?_
    · intro U
      dsimp [SheafOfModules.pushforward, PresheafOfModules.unit]
      exact ModuleCat.restrictScalarsIsoOfEquiv (f.appIso U.unop).symm.commRingCatIsoToRingEquiv
    · intro U V g
      ext x
      exact congr($(f.appIso_hom_naturality _).hom x)
  · infer_instance

end AlgebraicGeometry

namespace ModuleCat

@[deprecated (since := "2026-02-11")] noncomputable alias tilde := AlgebraicGeometry.tilde
@[deprecated (since := "2026-02-11")] noncomputable alias Tilde.toOpen := tilde.toOpen
@[deprecated (since := "2026-02-11")] alias Tilde.toOpen_res := tilde.toOpen_res
@[deprecated (since := "2026-02-11")] noncomputable alias Tilde.toStalk := tilde.toStalk

end ModuleCat
