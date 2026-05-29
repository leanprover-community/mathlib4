/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel, Jujian Zhang, Weihong Xu,
  Andrew Yang
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
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
  sheafCompose _ (ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso R).hom.hom)

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

open PrimeSpectrum in
lemma isUnit_algebraMap_end_basicOpen (M : (Spec (.of R)).Modules) (f : R) :
    IsUnit (algebraMap R (Module.End R
      ((modulesSpecToSheaf.obj M).presheaf.obj (.op (basicOpen f)))) f) := by
  rw [Module.End.isUnit_iff]
  change Function.Bijective (algebraMap Γ(Spec R, basicOpen f)
      (Module.End Γ(Spec R, basicOpen f) Γ(M, basicOpen f)) (algebraMap R _ f))
  rw [← Module.End.isUnit_iff]
  exact (IsLocalization.Away.algebraMap_isUnit _).map _

end tilde

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
        exact tilde.isUnit_algebraMap_end_basicOpen M f.unop
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
          exact (tilde.isUnit_algebraMap_end_basicOpen M g.unop).pow n
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
  simp only [fromTildeΓ, inducedFunctor_obj,
    homOfLE_leOfHom, Functor.FullyFaithful.map_preimage, TopCat.Sheaf.extend_hom_app]
  ext x
  refine (IsLocalizedModule.lift_apply (.powers (M := R) 1)
    (tilde.toOpen _ (PrimeSpectrum.basicOpen (R := R) 1)).hom
    ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op).hom (by simp) x)

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
      exact tilde.isUnit_algebraMap_end_basicOpen ..
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
      exact isUnit_algebraMap_end_basicOpen ..
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

section

variable (M : (Spec R).Modules) [M.IsQuasicoherent]

/-- A sheaf `M` of `R-modules` is localizing if for all `f` in `R`, the restriction map
from `M(⊤)` to `M(D(f))` is localization with respect to `f`. -/
abbrev IsLocalizing (M : TopCat.Sheaf (ModuleCat R) (Spec R)) : Prop :=
  ∀ f : R, IsLocalizedModule (.powers f) (M.obj.map (basicOpen f).leTop.op).hom

-- in 37189
lemma isIso_fromTildeΓ_iff_isLocalizing :
    IsIso M.fromTildeΓ ↔ IsLocalizing (modulesSpecToSheaf.obj M) := by
  sorry

lemma _root_.IsLocalizedModule.Away.mk {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {f : M →ₗ[R] N} {r : R}
    (h₁ : IsUnit (algebraMap R (Module.End R N) r))
    (h₂ : ∀ (x : N), ∃ (n : ℕ) (y : M), r ^ n • x = f y)
    (h₃ : ∀ (x y : M), f x = f y → ∃ (n : ℕ), r ^ n • x = r ^ n • y) :
    IsLocalizedModule.Away r f where
  map_units := fun ⟨_, ⟨n, rfl⟩⟩ ↦ by simp [h₁.pow]
  surj x := by
    obtain ⟨n, y, hy⟩ := h₂ x
    use ⟨y, ⟨_, n, rfl⟩⟩
    exact hy
  exists_of_eq {x y} hxy := by
    obtain ⟨n, hn⟩ := h₃ _ _ hxy
    use ⟨_, n, rfl⟩
    exact hn

lemma _root_.IsLocalizedModule.Away.mk_of_addCommGroup {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {f : M →ₗ[R] N} {r : R}
    (h₁ : IsUnit (algebraMap R (Module.End R N) r))
    (h₂ : ∀ (x : N), ∃ (n : ℕ) (y : M), r ^ n • x = f y)
    (h₃ : ∀ (x : M), f x = 0 → ∃ (n : ℕ), r ^ n • x = 0) :
    IsLocalizedModule.Away r f := by
  refine IsLocalizedModule.Away.mk h₁ h₂ fun x y hxy ↦ ?_
  have : f (x - y) = 0 := by simp [hxy]
  obtain ⟨n, hn⟩ := h₃ _ this
  use n
  simpa [smul_sub, sub_eq_zero] using hn

set_option backward.isDefEq.respectTransparency false in
instance (U : (Spec R).Opens) : Module R Γ(M, U) :=
  inferInstanceAs <| Module R ((modulesSpecToSheaf.obj M).obj.obj (.op U))

lemma Scheme.Modules.map_smul' {M : (Spec R).Modules} {U V : (Spec R).Opens} (hUV : U ≤ V) (f : R)
    (x : Γ(M, V)) :
    M.presheaf.map (homOfLE hUV).op (f • x) = f • M.presheaf.map (homOfLE hUV).op x :=
  ((modulesSpecToSheaf.obj M).obj.map (homOfLE hUV).op).hom.map_smul f x

lemma Scheme.Modules.isSMulRegular_of_le_basicOpen {M : (Spec R).Modules} {U : (Spec R).Opens}
    {f : R} (hle : U ≤ PrimeSpectrum.basicOpen f) :
    IsSMulRegular Γ(M, U) f :=
  sorry

/-- d1) and d2) from EGAI. -/
structure Aux (V : (Spec R).Opens) where
  existence (f : R) (hf : basicOpen f ≤ V) (s : Γ(M, basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, V)), M.presheaf.map (homOfLE hf).op t = f ^ n • s
  uniqueness (f : R) (hf : basicOpen f ≤ V) (t : Γ(M, V)) :
    M.presheaf.map (.op <| homOfLE hf) t = (0 : Γ(M, basicOpen f)) →
    ∃ (n : ℕ), f ^ n • t = 0

set_option backward.isDefEq.respectTransparency false in
/-- [Lemme 1.4.1.1][ega1] -/
lemma Aux.of_span_eq_top (M : (Spec R).Modules) (V : (Spec R).Opens)
    {ι : Type*} [Finite ι] (g : ι → R)
    (hg : V = ⨆ i, basicOpen (g i))
    (h₁ : ∀ (i : ι), Aux M (basicOpen (g i)))
    (h₂ : ∀ (i j : ι), Aux M (basicOpen (g i * g j))) :
    Aux M V := by
  have hgle (i : ι) : basicOpen (g i) ≤ V := by rw [hg]; exact le_iSup_iff.mpr fun b a ↦ a i
  have h (f : R) (hf : basicOpen f ≤ V) (t : Γ(M, V)) (hs : M.presheaf.map (homOfLE hf).op t = 0) :
      ∃ (n : ℕ), f ^ n • t = 0 := by
    have (i : ι) : ∃ (n : ℕ), M.presheaf.map (homOfLE (hgle i)).op (f ^ n • t) = 0 := by
      have := (h₁ i).uniqueness (f * g i) (basicOpen_mul_le_right f (g i))
        (M.presheaf.map (homOfLE (hgle i)).op t) ?_
      · obtain ⟨n, hn⟩ := this
        use n
        rw [mul_pow, mul_comm, mul_smul, ← Scheme.Modules.map_smul'] at hn
        apply ((M.isSMulRegular_of_le_basicOpen le_rfl).pow n).right_eq_zero_of_smul
        exact hn
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
      rw [this, pow_add, mul_smul, Scheme.Modules.map_smul', hn i]
      simp
  refine ⟨fun f hf s ↦ ?_, h⟩
  have hug (i : ι) (m : ℕ) :
      IsUnit (algebraMap R (Module.End R Γ(M, basicOpen (g i))) (g i ^ m)) := by
    rw [map_pow]
    exact (tilde.isUnit_algebraMap_end_basicOpen M (g i)).pow m
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
    rw [← ht', ← Scheme.Modules.map_smul']
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
    rw [hN i, pow_add, mul_smul, ht', M.map_smul']
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
        rw [M.map_smul' _ (f ^ m), M.map_smul' _ (f ^ m)]
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
        rw [op_comp, M.presheaf.map_comp_apply, ← ht i, M.map_smul',
          ← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp]
        rw [op_comp, M.presheaf.map_comp_apply, ← ht j, M.map_smul',
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
    rw [this, pow_add, mul_smul, mul_smul, M.map_smul', M.map_smul' _ (f ^ (K - m i j)), hm i j]
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
        M.map_smul', ha, M.map_smul', pow_add, mul_comm, mul_smul, ht i]
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
lemma isLocalizing_iff_aux (M : (Spec R).Modules) :
    IsLocalizing (modulesSpecToSheaf.obj M) ↔ Aux M ⊤ := by
  let φ (f : R) := ModuleCat.Hom.hom ((modulesSpecToSheaf.obj M).obj.map (basicOpen f).leTop.op)
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hf (f : R) : IsLocalizedModule.Away f (φ f) := h f
    refine ⟨?_, ?_⟩
    · intro f hle s
      obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, hy⟩ := (hf f).surj s
      dsimp at hy
      use n, y
      exact hy.symm
    · intro f hle s hs
      obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers f) (φ f)).mp hs
      use n
      exact hn
  · intro h f
    refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
    · exact tilde.isUnit_algebraMap_end_basicOpen M _
    · intro x
      obtain ⟨n, t, ht⟩ := h.existence _ _ x
      use n, t, ht.symm
    · intro x hx
      obtain ⟨n, hn⟩ := h.uniqueness _ _ _ hx
      use n, hn

lemma isIso_fromTildeΓ_of_isQuasicoherent : IsIso M.fromTildeΓ := by
  rw [isIso_fromTildeΓ_iff_isLocalizing, isLocalizing_iff_aux]
  sorry

end

end IsQuasicoherent

end AlgebraicGeometry

namespace ModuleCat

@[deprecated (since := "2026-02-11")] noncomputable alias tilde := AlgebraicGeometry.tilde
@[deprecated (since := "2026-02-11")] noncomputable alias Tilde.toOpen := tilde.toOpen
@[deprecated (since := "2026-02-11")] alias Tilde.toOpen_res := tilde.toOpen_res
@[deprecated (since := "2026-02-11")] noncomputable alias Tilde.toStalk := tilde.toStalk

end ModuleCat
