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
public import Mathlib.Topology.Sheaves.LocallySurjective

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

instance (f : R) : IsLocalizedModule (.powers f) (toOpen M (basicOpen f)).hom :=
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
    convert tilde.map_zero
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

/-- A sheaf `𝓕` of `R-modules` is localizing if for all `f` in `R`, the restriction map
from `𝓕(⊤)` to `𝓕(D(f))` is localization with respect to `f`. -/
abbrev IsLocalizing (M : TopCat.Sheaf (ModuleCat R) (Spec R)) : Prop :=
  ∀ f : R, IsLocalizedModule (.powers f) (M.obj.map (basicOpen f).leTop.op).hom

theorem isLocalizing_of_iso {M N : TopCat.Sheaf (ModuleCat R) (Spec R)} (φ : M ≅ N)
    (_ : IsLocalizing M) :
    IsLocalizing N := by
  intro f
  haveI (U : (Spec R).Opens) : IsIso (φ.hom.hom.app (op U)) :=
    inferInstanceAs (IsIso (((sheafToPresheaf _ _).mapIso φ).hom.app (op U)))
  haveI : IsLocalizedModule (.powers f) (M.obj.map (basicOpen f).leTop.op ≫
      φ.hom.hom.app (op (basicOpen f))).hom :=
    IsLocalizedModule.of_linearEquiv _ _ (asIso (φ.hom.hom.app (op (basicOpen f)))).toLinearEquiv
  rw [φ.hom.hom.naturality (basicOpen f).leTop.op] at this
  have : IsLocalizedModule (Submonoid.powers f) ((inv (φ.hom.hom.app (op ⊤))) ≫
      φ.hom.hom.app (op ⊤) ≫ N.obj.map (basicOpen f).leTop.op).hom :=
    IsLocalizedModule.of_linearEquiv_right _ _ (asIso (inv (φ.hom.hom.app (op ⊤)))).toLinearEquiv
  simpa

theorem isLocalizing_iso_iff {M N : TopCat.Sheaf (ModuleCat R) (Spec R)} (φ : M ≅ N) :
    IsLocalizing M ↔ IsLocalizing N :=
  ⟨fun h => isLocalizing_of_iso φ h, fun h => isLocalizing_of_iso φ.symm h⟩

theorem isLocalizing_of_isIso_app_top {M N : TopCat.Sheaf (ModuleCat.{u} R) (Spec R)} {φ : M ⟶ N}
    (h : IsIso (φ.hom.app (op ⊤))) (hM : IsLocalizing M) (hN : IsLocalizing N) :
    IsIso φ := by
  apply TopCat.Sheaf.isIso_iff_isIso_basis (φ := φ) isBasis_basic_opens
  rintro f
  refine ModuleCat.isIso_of_isLocalizedModule_comp (hM f) ?_
  rw [φ.hom.naturality]
  exact IsLocalizedModule.of_linearEquiv_right _ _ (asIso (φ.hom.app (op ⊤))).toLinearEquiv

theorem isLocalizing_tilde (M : ModuleCat R) :
    IsLocalizing (modulesSpecToSheaf.obj (tilde M)) := by
  intro f
  have : IsLocalizedModule _ (inv (tilde.toOpen M ⊤) ≫ tilde.toOpen M (basicOpen f)).hom :=
    IsLocalizedModule.of_linearEquiv_right (.powers f) (tilde.toOpen M (basicOpen f)).hom
      (asIso (inv (tilde.toOpen M ⊤))).toLinearEquiv
  simpa [show tilde.toOpen M (basicOpen f) = tilde.toOpen M ⊤ ≫
    ((modulesSpecToSheaf.obj (tilde M)).obj.map (basicOpen f).leTop.op) by rfl] using this

/-- An `𝓞_Spec R` module `M` is isomorphic to `Γ(M)^~` if and only if it is localizing
as a sheaf of `R` modules -/
theorem isIso_fromTildeΓ_iff_isLocalizing (M : (Spec R).Modules) :
    IsIso M.fromTildeΓ ↔ IsLocalizing (modulesSpecToSheaf.obj M) := by
  constructor
  · intro _
    rw [← isLocalizing_iso_iff (modulesSpecToSheaf.mapIso (asIso M.fromTildeΓ))]
    exact isLocalizing_tilde _
  intro h
  rw [← isIso_iff_of_reflects_iso _ modulesSpecToSheaf]
  refine isLocalizing_of_isIso_app_top ?_ (isLocalizing_tilde _) h
  rw [← isIso_comp_left_iff (tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) ⊤),
  Scheme.Modules.toOpen_fromTildeΓ_app]
  simpa using IsIso.id _

set_option backward.isDefEq.respectTransparency false in
/-- Natural isomorphism giving a compatibility between `pushforward` and `modulesSpecToSheaf` -/
def pushforward_modulesSpecToSheaf_iso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ modulesSpecToSheaf ≅
    modulesSpecToSheaf ⋙ TopCat.Sheaf.pushforward (ModuleCat S) (Spec.map φ).base ⋙
    sheafCompose _ (ModuleCat.restrictScalars φ.hom) := eqToIso (by
  conv_lhs =>
    change SheafOfModules.forgetToSheafModuleCat (Spec S).ringCatSheaf (.op ⊤)
      (Limits.initialOpOfTerminal Limits.isTerminalTop) ⋙
      TopCat.Sheaf.pushforward (ModuleCat Γ(Spec S, ⊤)) (Spec.map φ).base ⋙
      sheafCompose _ (ModuleCat.restrictScalars (Spec.map φ).appTop.hom) ⋙
      sheafCompose _ (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom)
    arg 2
    arg 2
    equals sheafCompose (Opens.grothendieckTopology (Spec R))
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso S).inv.hom) ⋙
      sheafCompose _ (ModuleCat.restrictScalars φ.hom) =>
      exact Eq.symm congr(sheafCompose (Opens.grothendieckTopology (Spec R))
        (ModuleCat.restrictScalars $(Scheme.ΓSpecIso_inv_naturality φ).hom))
  rfl)

open scoped ModuleCat.Algebra in
theorem isLocalizing_pushforward_of_isLocalizing {M : (Spec S).Modules}
    (h : IsLocalizing (modulesSpecToSheaf.obj M)) :
  IsLocalizing (modulesSpecToSheaf.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj M)) := by
  rw [← Functor.comp_obj,
  isLocalizing_iso_iff ((pushforward_modulesSpecToSheaf_iso φ).app M)]
  have : CommRing ((Spec S).ringCatSheaf.obj.obj ((Opens.map (Spec.map φ).base).op.obj (op ⊤))) :=
    inferInstanceAs (CommRing Γ(Spec S, ⊤))
  algebraize [φ.hom]
  exact fun f => IsLocalizedModule.restrictScalars_powers f _ (h := h (φ f))

/- TODO: Once `IsIso M.fromTildeΓ` is shown to be equivalent to `M` being quasicoherent, use
this to show that quasicoherent sheaves pushforward to quasicoherent sheaves for affine morphisms -/
theorem pushforward_isIso_fromTildeΓ (M : (Spec S).Modules) [h : IsIso M.fromTildeΓ] :
    IsIso ((Scheme.Modules.pushforward (Spec.map φ)).obj M).fromTildeΓ := by
  simp_all only [isIso_fromTildeΓ_iff_isLocalizing]
  exact isLocalizing_pushforward_of_isLocalizing φ h

end IsLocalizing

end IsQuasicoherent

end AlgebraicGeometry

namespace ModuleCat

@[deprecated (since := "2026-02-11")] noncomputable alias tilde := AlgebraicGeometry.tilde
@[deprecated (since := "2026-02-11")] noncomputable alias Tilde.toOpen := tilde.toOpen
@[deprecated (since := "2026-02-11")] alias Tilde.toOpen_res := tilde.toOpen_res
@[deprecated (since := "2026-02-11")] noncomputable alias Tilde.toStalk := tilde.toStalk

end ModuleCat
