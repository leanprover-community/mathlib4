/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.Topology.Sheaves.CommRingCat

/-!
# Affine schemes

We define the category of `AffineScheme`s as the essential image of `Spec`.
We also define predicates about affine schemes and affine open sets.

## Main definitions

* `AlgebraicGeometry.AffineScheme`: The category of affine schemes.
* `AlgebraicGeometry.IsAffine`: A scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an
  isomorphism.
* `AlgebraicGeometry.Scheme.isoSpec`: The canonical isomorphism `X ≅ Spec Γ(X)` for an affine
  scheme.
* `AlgebraicGeometry.AffineScheme.equivCommRingCat`: The equivalence of categories
  `AffineScheme ≌ CommRingᵒᵖ` given by `AffineScheme.Spec : CommRingᵒᵖ ⥤ AffineScheme` and
  `AffineScheme.Γ : AffineSchemeᵒᵖ ⥤ CommRingCat`.
* `AlgebraicGeometry.IsAffineOpen`: An open subset of a scheme is affine if the open subscheme is
  affine.
* `AlgebraicGeometry.IsAffineOpen.fromSpec`: The immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`.

-/

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

open Spec (structureSheaf)

/-- The category of affine schemes -/
def AffineScheme :=
  Scheme.Spec.EssImageSubcategory
deriving Category

/-- A Scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an isomorphism. -/
class IsAffine (X : Scheme) : Prop where
  affine : IsIso X.toSpecΓ

attribute [instance] IsAffine.affine

instance (X : Scheme.{u}) [IsAffine X] : IsIso (ΓSpec.adjunction.unit.app X) := @IsAffine.affine X _

/-- The canonical isomorphism `X ≅ Spec Γ(X)` for an affine scheme. -/
@[simps! -isSimp hom]
def Scheme.isoSpec (X : Scheme) [IsAffine X] : X ≅ Spec Γ(X, ⊤) :=
  asIso X.toSpecΓ

@[reassoc]
theorem Scheme.isoSpec_hom_naturality {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    X.isoSpec.hom ≫ Spec.map (f.appTop) = f ≫ Y.isoSpec.hom := by
  simp only [isoSpec, asIso_hom, Scheme.toSpecΓ_naturality]

@[reassoc]
theorem Scheme.isoSpec_inv_naturality {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Spec.map (f.appTop) ≫ Y.isoSpec.inv = X.isoSpec.inv ≫ f := by
  rw [Iso.eq_inv_comp, isoSpec, asIso_hom, ← Scheme.toSpecΓ_naturality_assoc, isoSpec,
    asIso_inv, IsIso.hom_inv_id, Category.comp_id]

@[reassoc (attr := simp)]
lemma Scheme.toSpecΓ_isoSpec_inv (X : Scheme.{u}) [IsAffine X] :
    X.toSpecΓ ≫ X.isoSpec.inv  = 𝟙 _ :=
  X.isoSpec.hom_inv_id

@[reassoc (attr := simp)]
lemma Scheme.isoSpec_inv_toSpecΓ (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv ≫ X.toSpecΓ = 𝟙 _ :=
  X.isoSpec.inv_hom_id

/-- Construct an affine scheme from a scheme and the information that it is affine.
Also see `AffineScheme.of` for a typeclass version. -/
@[simps]
def AffineScheme.mk (X : Scheme) (_ : IsAffine X) : AffineScheme :=
  ⟨X, ΓSpec.adjunction.mem_essImage_of_unit_isIso _⟩

/-- Construct an affine scheme from a scheme. Also see `AffineScheme.mk` for a non-typeclass
version. -/
def AffineScheme.of (X : Scheme) [h : IsAffine X] : AffineScheme :=
  AffineScheme.mk X h

/-- Type check a morphism of schemes as a morphism in `AffineScheme`. -/
def AffineScheme.ofHom {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    AffineScheme.of X ⟶ AffineScheme.of Y :=
  f

@[simp]
theorem essImage_Spec {X : Scheme} : Scheme.Spec.essImage X ↔ IsAffine X :=
  ⟨fun h => ⟨Functor.essImage.unit_isIso h⟩,
    fun _ => ΓSpec.adjunction.mem_essImage_of_unit_isIso _⟩

@[deprecated (since := "2025-04-08")] alias mem_Spec_essImage := essImage_Spec

instance isAffine_affineScheme (X : AffineScheme.{u}) : IsAffine X.obj :=
  ⟨Functor.essImage.unit_isIso X.property⟩

instance (R : CommRingCatᵒᵖ) : IsAffine (Scheme.Spec.obj R) :=
  AlgebraicGeometry.isAffine_affineScheme ⟨_, Scheme.Spec.obj_mem_essImage R⟩

instance isAffine_Spec (R : CommRingCat) : IsAffine (Spec R) :=
  AlgebraicGeometry.isAffine_affineScheme ⟨_, Scheme.Spec.obj_mem_essImage (op R)⟩

theorem IsAffine.of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] [h : IsAffine Y] : IsAffine X := by
  rw [← essImage_Spec] at h ⊢; exact Functor.essImage.ofIso (asIso f).symm h

@[deprecated (since := "2025-03-31")] alias isAffine_of_isIso := IsAffine.of_isIso

/-- If `f : X ⟶ Y` is a morphism between affine schemes, the corresponding arrow is isomorphic
to the arrow of the morphism on prime spectra induced by the map on global sections. -/
noncomputable
def arrowIsoSpecΓOfIsAffine {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Arrow.mk f ≅ Arrow.mk (Spec.map f.appTop) :=
  Arrow.isoMk X.isoSpec Y.isoSpec (ΓSpec.adjunction.unit_naturality _)

/-- If `f : A ⟶ B` is a ring homomorphism, the corresponding arrow is isomorphic
to the arrow of the morphism induced on global sections by the map on prime spectra. -/
def arrowIsoΓSpecOfIsAffine {A B : CommRingCat} (f : A ⟶ B) :
    Arrow.mk f ≅ Arrow.mk ((Spec.map f).appTop) :=
  Arrow.isoMk (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm
    (Scheme.ΓSpecIso_inv_naturality f).symm

theorem Scheme.isoSpec_Spec (R : CommRingCat.{u}) :
    (Spec R).isoSpec = Scheme.Spec.mapIso (Scheme.ΓSpecIso R).op :=
  Iso.ext (SpecMap_ΓSpecIso_hom R).symm

@[simp] theorem Scheme.isoSpec_Spec_hom (R : CommRingCat.{u}) :
    (Spec R).isoSpec.hom = Spec.map (Scheme.ΓSpecIso R).hom :=
  (SpecMap_ΓSpecIso_hom R).symm

@[simp] theorem Scheme.isoSpec_Spec_inv (R : CommRingCat.{u}) :
    (Spec R).isoSpec.inv = Spec.map (Scheme.ΓSpecIso R).inv :=
  congr($(isoSpec_Spec R).inv)

lemma ext_of_isAffine {X Y : Scheme} [IsAffine Y] {f g : X ⟶ Y} (e : f.appTop = g.appTop) :
    f = g := by
  rw [← cancel_mono Y.toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, e]

namespace AffineScheme

/-- The `Spec` functor into the category of affine schemes. -/
def Spec : CommRingCatᵒᵖ ⥤ AffineScheme :=
  Scheme.Spec.toEssImage

/-! We copy over instances from `Scheme.Spec.toEssImage`. -/

instance Spec_full : Spec.Full := Functor.Full.toEssImage _

instance Spec_faithful : Spec.Faithful := Functor.Faithful.toEssImage _

instance Spec_essSurj : Spec.EssSurj := Functor.EssSurj.toEssImage (F := _)

/-- The forgetful functor `AffineScheme ⥤ Scheme`. -/
@[simps!]
def forgetToScheme : AffineScheme ⥤ Scheme :=
  Scheme.Spec.essImage.ι

/-! We copy over instances from `Scheme.Spec.essImageInclusion`. -/

instance forgetToScheme_full : forgetToScheme.Full :=
  inferInstanceAs Scheme.Spec.essImage.ι.Full

instance forgetToScheme_faithful : forgetToScheme.Faithful :=
  inferInstanceAs Scheme.Spec.essImage.ι.Faithful

/-- The global section functor of an affine scheme. -/
def Γ : AffineSchemeᵒᵖ ⥤ CommRingCat :=
  forgetToScheme.op ⋙ Scheme.Γ

/-- The category of affine schemes is equivalent to the category of commutative rings. -/
def equivCommRingCat : AffineScheme ≌ CommRingCatᵒᵖ :=
  equivEssImageOfReflective.symm

instance : Γ.{u}.rightOp.IsEquivalence := equivCommRingCat.isEquivalence_functor

instance : Γ.{u}.rightOp.op.IsEquivalence := equivCommRingCat.op.isEquivalence_functor

instance ΓIsEquiv : Γ.{u}.IsEquivalence :=
  inferInstanceAs (Γ.{u}.rightOp.op ⋙ (opOpEquivalence _).functor).IsEquivalence

instance hasColimits : HasColimits AffineScheme.{u} :=
  haveI := Adjunction.has_limits_of_equivalence.{u} Γ.{u}
  Adjunction.has_colimits_of_equivalence.{u} (opOpEquivalence AffineScheme.{u}).inverse

instance hasLimits : HasLimits AffineScheme.{u} := by
  haveI := Adjunction.has_colimits_of_equivalence Γ.{u}
  haveI : HasLimits AffineScheme.{u}ᵒᵖᵒᵖ := Limits.hasLimits_op_of_hasColimits
  exact Adjunction.has_limits_of_equivalence (opOpEquivalence AffineScheme.{u}).inverse

noncomputable instance Γ_preservesLimits : PreservesLimits Γ.{u}.rightOp := inferInstance

noncomputable instance forgetToScheme_preservesLimits : PreservesLimits forgetToScheme := by
  apply (config := { allowSynthFailures := true })
    @preservesLimits_of_natIso _ _ _ _ _ _
      (Functor.isoWhiskerRight equivCommRingCat.unitIso forgetToScheme).symm
  change PreservesLimits (equivCommRingCat.functor ⋙ Scheme.Spec)
  infer_instance

end AffineScheme

/-- An open subset of a scheme is affine if the open subscheme is affine. -/
def IsAffineOpen {X : Scheme} (U : X.Opens) : Prop :=
  IsAffine U

/-- The set of affine opens as a subset of `opens X`. -/
def Scheme.affineOpens (X : Scheme) : Set X.Opens :=
  {U : X.Opens | IsAffineOpen U}

instance {Y : Scheme.{u}} (U : Y.affineOpens) : IsAffine U :=
  U.property

theorem isAffineOpen_opensRange {X Y : Scheme} [IsAffine X] (f : X ⟶ Y)
    [H : IsOpenImmersion f] : IsAffineOpen (Scheme.Hom.opensRange f) := by
  refine .of_isIso (IsOpenImmersion.isoOfRangeEq f (Y.ofRestrict _) ?_).inv
  exact Subtype.range_val.symm

theorem isAffineOpen_top (X : Scheme) [IsAffine X] : IsAffineOpen (⊤ : X.Opens) := by
  convert isAffineOpen_opensRange (𝟙 X)
  ext1
  exact Set.range_id.symm

theorem exists_isAffineOpen_mem_and_subset {X : Scheme.{u}} {x : X}
    {U : X.Opens} (hxU : x ∈ U) : ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W.1 ⊆ U := by
  obtain ⟨R, f, hf⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset hxU
  exact ⟨Scheme.Hom.opensRange f (H := hf.1),
    ⟨AlgebraicGeometry.isAffineOpen_opensRange f (H := hf.1), hf.2.1, hf.2.2⟩⟩

instance Scheme.isAffine_affineCover (X : Scheme) (i : X.affineCover.I₀) :
    IsAffine (X.affineCover.X i) :=
  isAffine_Spec _

instance Scheme.isAffine_affineBasisCover (X : Scheme) (i : X.affineBasisCover.I₀) :
    IsAffine (X.affineBasisCover.X i) :=
  isAffine_Spec _

instance Scheme.isAffine_affineOpenCover (X : Scheme) (𝒰 : X.AffineOpenCover) (i : 𝒰.I₀) :
    IsAffine (𝒰.openCover.X i) :=
  inferInstanceAs (IsAffine (Spec (𝒰.X i)))

instance (X : Scheme) [CompactSpace X] (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)] (i) :
    IsAffine (𝒰.finiteSubcover.X i) :=
  inferInstanceAs (IsAffine (𝒰.X _))

instance {X} [IsAffine X] (i) :
    IsAffine ((Scheme.coverOfIsIso (P := @IsOpenImmersion) (𝟙 X)).X i) := by
  dsimp; infer_instance

theorem isBasis_affine_open (X : Scheme) : Opens.IsBasis X.affineOpens := by
  rw [Opens.isBasis_iff_nbhd]
  rintro U x (hU : x ∈ (U : Set X))
  obtain ⟨S, hS, hxS, hSU⟩ := X.affineBasisCover_is_basis.exists_subset_of_mem_open hU U.isOpen
  refine ⟨⟨S, X.affineBasisCover_is_basis.isOpen hS⟩, ?_, hxS, hSU⟩
  rcases hS with ⟨i, rfl⟩
  exact isAffineOpen_opensRange _

theorem iSup_affineOpens_eq_top (X : Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤ := by
  apply Opens.ext
  rw [Opens.coe_iSup]
  apply IsTopologicalBasis.sUnion_eq
  rw [← Set.image_eq_range]
  exact isBasis_affine_open X

theorem Scheme.map_PrimeSpectrum_basicOpen_of_affine
    (X : Scheme) [IsAffine X] (f : Γ(X, ⊤)) :
    X.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f :=
  Scheme.toSpecΓ_preimage_basicOpen _ _

theorem isBasis_basicOpen (X : Scheme) [IsAffine X] :
    Opens.IsBasis (Set.range (X.basicOpen : Γ(X, ⊤) → X.Opens)) := by
  convert PrimeSpectrum.isBasis_basic_opens.of_isInducing
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso X.isoSpec)).isInducing using 1
  ext V
  simp only [Set.mem_range, exists_exists_eq_and, Set.mem_setOf,
    ← Opens.coe_inj (V := V), ← Scheme.toSpecΓ_preimage_basicOpen]
  rfl

/-- The canonical map `U ⟶ Spec Γ(X, U)` for an open `U ⊆ X`. -/
noncomputable
def Scheme.Opens.toSpecΓ {X : Scheme.{u}} (U : X.Opens) :
    U.toScheme ⟶ Spec Γ(X, U) :=
  U.toScheme.toSpecΓ ≫ Spec.map U.topIso.inv

@[reassoc (attr := simp)]
lemma Scheme.Opens.toSpecΓ_SpecMap_map {X : Scheme} (U V : X.Opens) (h : U ≤ V) :
    U.toSpecΓ ≫ Spec.map (X.presheaf.map (homOfLE h).op) = X.homOfLE h ≫ V.toSpecΓ := by
  delta Scheme.Opens.toSpecΓ
  simp [← Spec.map_comp, ← X.presheaf.map_comp, toSpecΓ_naturality_assoc]

@[simp]
lemma Scheme.Opens.toSpecΓ_top {X : Scheme} :
    (⊤ : X.Opens).toSpecΓ = (⊤ : X.Opens).ι ≫ X.toSpecΓ := by
  simp [Scheme.Opens.toSpecΓ, toSpecΓ_naturality]; rfl

@[reassoc]
lemma Scheme.Opens.toSpecΓ_appTop {X : Scheme.{u}} (U : X.Opens) :
    U.toSpecΓ.appTop = (Scheme.ΓSpecIso Γ(X, U)).hom ≫ U.topIso.inv := by
  simp [Scheme.Opens.toSpecΓ]

namespace IsAffineOpen

variable {X Y : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))

attribute [-simp] eqToHom_op in
/-- The isomorphism `U ≅ Spec Γ(X, U)` for an affine `U`. -/
@[simps! -isSimp inv]
def isoSpec :
    ↑U ≅ Spec Γ(X, U) :=
  haveI : IsAffine U := hU
  U.toScheme.isoSpec ≪≫ Scheme.Spec.mapIso U.topIso.symm.op

lemma isoSpec_hom : hU.isoSpec.hom = U.toSpecΓ := rfl

@[reassoc (attr := simp)]
lemma toSpecΓ_isoSpec_inv : U.toSpecΓ ≫ hU.isoSpec.inv = 𝟙 _ := hU.isoSpec.hom_inv_id

@[reassoc (attr := simp)]
lemma isoSpec_inv_toSpecΓ : hU.isoSpec.inv ≫ U.toSpecΓ = 𝟙 _ := hU.isoSpec.inv_hom_id

open IsLocalRing in
lemma isoSpec_hom_base_apply (x : U) :
    hU.isoSpec.hom.base x = (Spec.map (X.presheaf.germ U x x.2)).base (closedPoint _) := by
  dsimp [IsAffineOpen.isoSpec_hom, Scheme.isoSpec_hom, Scheme.toSpecΓ_base, Scheme.Opens.toSpecΓ]
  rw [← Scheme.comp_base_apply, ← Spec.map_comp,
    (Iso.eq_comp_inv _).mpr (Scheme.Opens.germ_stalkIso_hom U (V := ⊤) x trivial),
    X.presheaf.germ_res_assoc, Spec.map_comp, Scheme.comp_base_apply]
  congr 1
  exact IsLocalRing.comap_closedPoint (U.stalkIso x).inv.hom

lemma isoSpec_inv_appTop :
    hU.isoSpec.inv.appTop = U.topIso.hom ≫ (Scheme.ΓSpecIso Γ(X, U)).inv := by
  simp_rw [Scheme.Opens.toScheme_presheaf_obj, isoSpec_inv, Scheme.isoSpec, asIso_inv,
    Scheme.comp_app, Scheme.Opens.topIso_hom, Scheme.ΓSpecIso_inv_naturality,
    Scheme.inv_appTop, -- `check_compositions` reports defeq problems starting after this step.
    IsIso.inv_comp_eq]
  rw [Scheme.toSpecΓ_appTop]
  -- We need `erw` here because the goal has
  -- `Scheme.ΓSpecIso Γ(↑U, ⊤)).hom ≫ Scheme.ΓSpecIso Γ(X, U.ι ''ᵁ ⊤)).inv`
  -- and `Γ(X, U.ι ''ᵁ ⊤)` is non-reducibly defeq to `Γ(↑U, ⊤)`.
  erw [Iso.hom_inv_id_assoc]
  simp only [Opens.map_top]

lemma isoSpec_hom_appTop :
    hU.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(X, U)).hom ≫ U.topIso.inv := by
  have := congr(inv $hU.isoSpec_inv_appTop)
  rw [IsIso.inv_comp, IsIso.Iso.inv_inv, IsIso.Iso.inv_hom] at this
  have := (Scheme.Γ.map_inv hU.isoSpec.inv.op).trans this
  rwa [← op_inv, IsIso.Iso.inv_inv] at this

/-- The open immersion `Spec Γ(X, U) ⟶ X` for an affine `U`. -/
def fromSpec :
    Spec Γ(X, U) ⟶ X :=
  haveI : IsAffine U := hU
  hU.isoSpec.inv ≫ U.ι

instance isOpenImmersion_fromSpec :
    IsOpenImmersion hU.fromSpec := by
  delta fromSpec
  infer_instance

@[reassoc (attr := simp)]
lemma isoSpec_inv_ι : hU.isoSpec.inv ≫ U.ι = hU.fromSpec := rfl

@[reassoc (attr := simp)]
lemma toSpecΓ_fromSpec : U.toSpecΓ ≫ hU.fromSpec = U.ι := toSpecΓ_isoSpec_inv_assoc _ _

@[simp]
theorem range_fromSpec :
    Set.range hU.fromSpec.base = (U : Set X) := by
  delta IsAffineOpen.fromSpec; dsimp [IsAffineOpen.isoSpec_inv]
  rw [Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ]
  · exact Subtype.range_coe
  rw [← TopCat.coe_comp, ← TopCat.epi_iff_surjective]
  infer_instance

@[simp]
theorem opensRange_fromSpec : hU.fromSpec.opensRange = U := Opens.ext (range_fromSpec hU)

@[reassoc (attr := simp)]
theorem map_fromSpec {V : X.Opens} (hV : IsAffineOpen V) (f : op U ⟶ op V) :
    Spec.map (X.presheaf.map f) ≫ hU.fromSpec = hV.fromSpec := by
  have : IsAffine U := hU
  haveI : IsAffine _ := hV
  conv_rhs =>
    rw [fromSpec, ← X.homOfLE_ι (V := U) f.unop.le, isoSpec_inv, Category.assoc,
      ← Scheme.isoSpec_inv_naturality_assoc,
      ← Spec.map_comp_assoc, Scheme.homOfLE_appTop, ← Functor.map_comp]
  rw [fromSpec, isoSpec_inv, Category.assoc, ← Spec.map_comp_assoc, ← Functor.map_comp]
  rfl

@[reassoc]
lemma Spec_map_appLE_fromSpec (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : V ≤ f ⁻¹ᵁ U) :
    Spec.map (f.appLE U V i) ≫ hU.fromSpec = hV.fromSpec ≫ f := by
  have : IsAffine U := hU
  simp only [IsAffineOpen.fromSpec, Category.assoc, isoSpec_inv]
  simp_rw [← Scheme.homOfLE_ι _ i]
  rw [Category.assoc, ← morphismRestrict_ι,
    ← Category.assoc _ (f ∣_ U) U.ι, ← @Scheme.isoSpec_inv_naturality_assoc,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, Scheme.comp_appTop, morphismRestrict_appTop,
    Scheme.homOfLE_appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map,
    Scheme.Hom.appLE_map, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

lemma fromSpec_top [IsAffine X] : (isAffineOpen_top X).fromSpec = X.isoSpec.inv := by
  rw [fromSpec, isoSpec_inv, Category.assoc, ← @Scheme.isoSpec_inv_naturality,
    ← Spec.map_comp_assoc, Scheme.Opens.ι_appTop, ← X.presheaf.map_comp, ← op_comp,
    eqToHom_comp_homOfLE, ← eqToHom_eq_homOfLE rfl, eqToHom_refl, op_id, X.presheaf.map_id,
    Spec.map_id, Category.id_comp]

lemma fromSpec_app_of_le (V : X.Opens) (h : U ≤ V) :
    hU.fromSpec.app V = X.presheaf.map (homOfLE h).op ≫
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec _).presheaf.map (homOfLE le_top).op := by
  have : U.ι ⁻¹ᵁ V = ⊤ := eq_top_iff.mpr fun x _ ↦ h x.2
  rw [IsAffineOpen.fromSpec, Scheme.comp_app, Scheme.Opens.ι_app, Scheme.app_eq _ this,
    ← Scheme.Hom.appTop, IsAffineOpen.isoSpec_inv_appTop]
  simp only [Scheme.Opens.toScheme_presheaf_map, Scheme.Opens.topIso_hom,
    Category.assoc, ← X.presheaf.map_comp_assoc]
  rfl

include hU in
protected theorem isCompact :
    IsCompact (U : Set X) := by
  convert @IsCompact.image _ _ _ _ Set.univ hU.fromSpec.base PrimeSpectrum.compactSpace.1
    (by fun_prop)
  convert hU.range_fromSpec.symm
  exact Set.image_univ

include hU in
theorem image_of_isOpenImmersion (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsAffineOpen (f ''ᵁ U) := by
  have : IsAffine _ := hU
  convert isAffineOpen_opensRange (U.ι ≫ f)
  ext1
  exact Set.image_eq_range _ _

theorem preimage_of_isIso {U : Y.Opens} (hU : IsAffineOpen U) (f : X ⟶ Y) [IsIso f] :
    IsAffineOpen (f ⁻¹ᵁ U) :=
  haveI : IsAffine _ := hU
  .of_isIso (f ∣_ U)

theorem _root_.AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion
    (f : AlgebraicGeometry.Scheme.Hom X Y) [H : IsOpenImmersion f] {U : X.Opens} :
    IsAffineOpen (f ''ᵁ U) ↔ IsAffineOpen U where
  mp hU := by
    refine .of_isIso (IsOpenImmersion.isoOfRangeEq (X.ofRestrict U.isOpenEmbedding ≫ f)
      (Y.ofRestrict _) ?_).hom (h := hU)
    rw [Scheme.comp_base, TopCat.coe_comp, Set.range_comp]
    dsimp [Opens.coe_inclusion', Scheme.restrict]
    rw [Subtype.range_coe, Subtype.range_coe]
    rfl
  mpr hU := hU.image_of_isOpenImmersion f

/-- The affine open sets of an open subscheme corresponds to
the affine open sets containing in the image. -/
@[simps]
def _root_.AlgebraicGeometry.IsOpenImmersion.affineOpensEquiv (f : X ⟶ Y) [H : IsOpenImmersion f] :
    X.affineOpens ≃ { U : Y.affineOpens // U ≤ f.opensRange } where
  toFun U := ⟨⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩, Set.image_subset_range _ _⟩
  invFun U := ⟨f ⁻¹ᵁ U, f.isAffineOpen_iff_of_isOpenImmersion.mp (by
    rw [show f ''ᵁ f ⁻¹ᵁ U = U from Opens.ext (Set.image_preimage_eq_of_subset U.2)]; exact U.1.2)⟩
  left_inv _ := Subtype.ext (Opens.ext (Set.preimage_image_eq _ H.base_open.injective))
  right_inv U := Subtype.ext (Subtype.ext (Opens.ext (Set.image_preimage_eq_of_subset U.2)))

/-- The affine open sets of an open subscheme
corresponds to the affine open sets containing in the subset. -/
@[simps! apply_coe_coe]
def _root_.AlgebraicGeometry.affineOpensRestrict {X : Scheme.{u}} (U : X.Opens) :
    U.toScheme.affineOpens ≃ { V : X.affineOpens // V ≤ U } :=
  (IsOpenImmersion.affineOpensEquiv U.ι).trans (Equiv.subtypeEquivProp (by simp))

@[simp]
lemma _root_.AlgebraicGeometry.affineOpensRestrict_symm_apply_coe
    {X : Scheme.{u}} (U : X.Opens) (V) :
    ((affineOpensRestrict U).symm V).1 = U.ι ⁻¹ᵁ V := rfl

instance (priority := 100) _root_.AlgebraicGeometry.Scheme.compactSpace_of_isAffine
    (X : Scheme) [IsAffine X] :
    CompactSpace X :=
  ⟨(isAffineOpen_top X).isCompact⟩

@[simp]
theorem fromSpec_preimage_self :
    hU.fromSpec ⁻¹ᵁ U = ⊤ := by
  ext1
  rw [Opens.map_coe, Opens.coe_top, ← hU.range_fromSpec, ← Set.image_univ]
  exact Set.preimage_image_eq _ PresheafedSpace.IsOpenImmersion.base_open.injective

theorem ΓSpecIso_hom_fromSpec_app :
    (Scheme.ΓSpecIso Γ(X, U)).hom ≫ hU.fromSpec.app U =
      (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op := by
  simp only [fromSpec, Scheme.comp_coeBase, Opens.map_comp_obj, Scheme.comp_app,
    Scheme.Opens.ι_app_self, eqToHom_op, Scheme.app_eq _ U.ι_preimage_self,
    Scheme.Opens.toScheme_presheaf_map, eqToHom_unop, eqToHom_map U.ι.opensFunctor, Opens.map_top,
    isoSpec_inv_appTop, Scheme.Opens.topIso_hom, Category.assoc, ← Functor.map_comp_assoc,
    eqToHom_trans, eqToHom_refl, X.presheaf.map_id, Category.id_comp, Iso.hom_inv_id_assoc]

@[elementwise]
theorem fromSpec_app_self :
    hU.fromSpec.app U = (Scheme.ΓSpecIso Γ(X, U)).inv ≫
      (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op := by
  rw [← hU.ΓSpecIso_hom_fromSpec_app, Iso.inv_hom_id_assoc]

theorem fromSpec_preimage_basicOpen' :
    hU.fromSpec ⁻¹ᵁ X.basicOpen f = (Spec Γ(X, U)).basicOpen ((Scheme.ΓSpecIso Γ(X, U)).inv f) := by
  rw [Scheme.preimage_basicOpen, hU.fromSpec_app_self]
  exact Scheme.basicOpen_res_eq _ _ (eqToHom hU.fromSpec_preimage_self).op

theorem fromSpec_preimage_basicOpen :
    hU.fromSpec ⁻¹ᵁ X.basicOpen f = PrimeSpectrum.basicOpen f := by
  rw [fromSpec_preimage_basicOpen', ← basicOpen_eq_of_affine]

theorem fromSpec_image_basicOpen :
    hU.fromSpec ''ᵁ (PrimeSpectrum.basicOpen f) = X.basicOpen f := by
  rw [← hU.fromSpec_preimage_basicOpen]
  ext1
  change hU.fromSpec.base '' (hU.fromSpec.base ⁻¹' (X.basicOpen f : Set X)) = _
  rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left, hU.range_fromSpec]
  exact Scheme.basicOpen_le _ _

@[simp]
theorem basicOpen_fromSpec_app :
    (Spec Γ(X, U)).basicOpen (hU.fromSpec.app U f) = PrimeSpectrum.basicOpen f := by
  rw [← hU.fromSpec_preimage_basicOpen, Scheme.preimage_basicOpen]

include hU in
theorem basicOpen :
    IsAffineOpen (X.basicOpen f) := by
  rw [← hU.fromSpec_image_basicOpen, Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion]
  convert isAffineOpen_opensRange
    (Spec.map (CommRingCat.ofHom <| algebraMap Γ(X, U) (Localization.Away f)))
  exact Opens.ext (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm

lemma Spec_basicOpen {R : CommRingCat} (f : R) :
    IsAffineOpen (X := Spec R) (PrimeSpectrum.basicOpen f) :=
  basicOpen_eq_of_affine f ▸ (isAffineOpen_top Spec(R)).basicOpen _

instance [IsAffine X] (r : Γ(X, ⊤)) : IsAffine (X.basicOpen r) :=
  (isAffineOpen_top X).basicOpen _

include hU in
theorem ι_basicOpen_preimage (r : Γ(X, ⊤)) :
    IsAffineOpen ((X.basicOpen r).ι ⁻¹ᵁ U) := by
  apply (X.basicOpen r).ι.isAffineOpen_iff_of_isOpenImmersion.mp
  dsimp [Scheme.Hom.opensFunctor, LocallyRingedSpace.IsOpenImmersion.opensFunctor]
  rw [Opens.functor_obj_map_obj, Opens.isOpenEmbedding_obj_top, inf_comm,
    ← Scheme.basicOpen_res _ _ (homOfLE le_top).op]
  exact hU.basicOpen _

include hU in
theorem exists_basicOpen_le {V : X.Opens} (x : V) (h : ↑x ∈ U) :
    ∃ f : Γ(X, U), X.basicOpen f ≤ V ∧ ↑x ∈ X.basicOpen f := by
  have : IsAffine _ := hU
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, h₁, h₂⟩ :=
    (isBasis_basicOpen U).exists_subset_of_mem_open (x.2 : (⟨x, h⟩ : U) ∈ _)
      ((Opens.map U.inclusion').obj V).isOpen
  have :
    U.ι ''ᵁ (U.toScheme.basicOpen r) =
      X.basicOpen (X.presheaf.map (eqToHom U.isOpenEmbedding_obj_top.symm).op r) := by
    refine (Scheme.image_basicOpen U.ι r).trans ?_
    rw [Scheme.basicOpen_res_eq]
    simp only [Scheme.Opens.toScheme_presheaf_obj, Scheme.Opens.ι_appIso, Iso.refl_inv,
      CommRingCat.id_apply]
  use X.presheaf.map (eqToHom U.isOpenEmbedding_obj_top.symm).op r
  rw [← this]
  exact ⟨Set.image_subset_iff.mpr h₂, ⟨_, h⟩, h₁, rfl⟩

noncomputable
instance {R : CommRingCat} {U} : Algebra R Γ(Spec R, U) :=
  ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op).hom.toAlgebra

@[simp]
lemma algebraMap_Spec_obj {R : CommRingCat} {U} : algebraMap R Γ(Spec R, U) =
    ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op).hom := rfl

instance {R : CommRingCat} {f : R} :
    IsLocalization.Away f Γ(Spec R, PrimeSpectrum.basicOpen f) :=
  inferInstanceAs (IsLocalization.Away f
    ((Spec.structureSheaf R).val.obj (op <| PrimeSpectrum.basicOpen f)))

/-- Given an affine open U and some `f : U`,
this is the canonical map `Γ(𝒪ₓ, D(f)) ⟶ Γ(Spec 𝒪ₓ(U), D(f))`
This is an isomorphism, as witnessed by an `IsIso` instance. -/
def basicOpenSectionsToAffine :
    Γ(X, X.basicOpen f) ⟶ Γ(Spec Γ(X, U), PrimeSpectrum.basicOpen f) :=
  hU.fromSpec.c.app (op <| X.basicOpen f) ≫
    (Spec Γ(X, U)).presheaf.map (eqToHom <| (hU.fromSpec_preimage_basicOpen f).symm).op

instance basicOpenSectionsToAffine_isIso :
    IsIso (basicOpenSectionsToAffine hU f) := by
  delta basicOpenSectionsToAffine
  refine IsIso.comp_isIso' ?_ inferInstance
  apply PresheafedSpace.IsOpenImmersion.isIso_of_subset
  rw [hU.range_fromSpec]
  exact RingedSpace.basicOpen_le _ _

include hU in
theorem isLocalization_basicOpen :
    IsLocalization.Away f Γ(X, X.basicOpen f) := by
  apply
    (IsLocalization.isLocalization_iff_of_ringEquiv (Submonoid.powers f)
      (asIso <| basicOpenSectionsToAffine hU f).commRingCatIsoToRingEquiv).mpr
  convert StructureSheaf.IsLocalization.to_basicOpen _ f using 1
  -- Porting note: more hand holding is required here, the next 3 lines were not necessary
  congr 1
  dsimp [CommRingCat.ofHom, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
    basicOpenSectionsToAffine]
  rw [hU.fromSpec.naturality_assoc, hU.fromSpec_app_self]
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
  exact CommRingCat.hom_ext_iff.mp (StructureSheaf.toOpen_res _ _ _ _)

instance _root_.AlgebraicGeometry.isLocalization_away_of_isAffine
    [IsAffine X] (r : Γ(X, ⊤)) :
    IsLocalization.Away r Γ(X, X.basicOpen r) :=
  isLocalization_basicOpen (isAffineOpen_top X) r

lemma appLE_eq_away_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e) (r : Γ(Y, U)) :
    letI := hU.isLocalization_basicOpen r
    letI := hV.isLocalization_basicOpen (f.appLE U V e r)
    f.appLE (Y.basicOpen r) (X.basicOpen (f.appLE U V e r)) (by simp [Scheme.Hom.appLE]) =
        CommRingCat.ofHom (IsLocalization.Away.map _ _ (f.appLE U V e).hom r) := by
  letI := hU.isLocalization_basicOpen r
  letI := hV.isLocalization_basicOpen (f.appLE U V e r)
  ext : 1
  apply IsLocalization.ringHom_ext (.powers r)
  rw [IsLocalization.Away.map, CommRingCat.hom_ofHom, IsLocalization.map_comp,
    RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

lemma app_basicOpen_eq_away_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (h : IsAffineOpen (f ⁻¹ᵁ U)) (r : Γ(Y, U)) :
    haveI := hU.isLocalization_basicOpen r
    haveI := h.isLocalization_basicOpen (f.app U r)
    f.app (Y.basicOpen r) =
      (CommRingCat.ofHom
        (IsLocalization.Away.map Γ(Y, Y.basicOpen r) Γ(X, X.basicOpen (f.app U r)) (f.app U).hom r)
        ≫ X.presheaf.map (eqToHom (by simp)).op) := by
  haveI := hU.isLocalization_basicOpen r
  haveI := h.isLocalization_basicOpen (f.app U r)
  ext : 1
  apply IsLocalization.ringHom_ext (.powers r)
  rw [IsLocalization.Away.map, CommRingCat.hom_comp, RingHom.comp_assoc, CommRingCat.hom_ofHom,
    IsLocalization.map_comp, RingHom.algebraMap_toAlgebra,
    RingHom.algebraMap_toAlgebra, ← RingHom.comp_assoc, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, ← X.presheaf.map_comp]
  simp

/-- `f.app (Y.basicOpen r)` is isomorphic to map induced on localizations
`Γ(Y, Y.basicOpen r) ⟶ Γ(X, X.basicOpen (f.app U r))` -/
def appBasicOpenIsoAwayMap {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (h : IsAffineOpen (f ⁻¹ᵁ U)) (r : Γ(Y, U)) :
    haveI := hU.isLocalization_basicOpen r
    haveI := h.isLocalization_basicOpen (f.app U r)
    Arrow.mk (f.app (Y.basicOpen r)) ≅
      Arrow.mk (CommRingCat.ofHom (IsLocalization.Away.map Γ(Y, Y.basicOpen r)
        Γ(X, X.basicOpen (f.app U r)) (f.app U).hom r)) :=
  Arrow.isoMk (Iso.refl _) (X.presheaf.mapIso (eqToIso (by simp)).op) <| by
    simp [hU.app_basicOpen_eq_away_map f h]

include hU in
theorem isLocalization_of_eq_basicOpen {V : X.Opens} (i : V ⟶ U) (e : V = X.basicOpen f) :
    @IsLocalization.Away _ _ f Γ(X, V) _ (X.presheaf.map i.op).hom.toAlgebra := by
  subst e; convert isLocalization_basicOpen hU f using 3

instance _root_.AlgebraicGeometry.Γ_restrict_isLocalization
    (X : Scheme.{u}) [IsAffine X] (r : Γ(X, ⊤)) :
    IsLocalization.Away r Γ(X.basicOpen r, ⊤) :=
  (isAffineOpen_top X).isLocalization_of_eq_basicOpen r _ (Opens.isOpenEmbedding_obj_top _)

include hU in
theorem basicOpen_basicOpen_is_basicOpen (g : Γ(X, X.basicOpen f)) :
    ∃ f' : Γ(X, U), X.basicOpen f' = X.basicOpen g := by
  have := isLocalization_basicOpen hU f
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.surj'' (Submonoid.powers f) g
  use f * x
  rw [Algebra.smul_def, Scheme.basicOpen_mul, Scheme.basicOpen_mul, RingHom.algebraMap_toAlgebra,
    Scheme.basicOpen_res]
  refine (inf_eq_left.mpr (inf_le_left.trans_eq (Scheme.basicOpen_of_isUnit _ ?_).symm)).symm
  exact
    Submonoid.leftInv_le_isUnit _
      (IsLocalization.toInvSubmonoid (Submonoid.powers f) (Γ(X, X.basicOpen f))
        _).prop

include hU in
theorem _root_.AlgebraicGeometry.exists_basicOpen_le_affine_inter
    {V : X.Opens} (hV : IsAffineOpen V) (x : X) (hx : x ∈ U ⊓ V) :
    ∃ (f : Γ(X, U)) (g : Γ(X, V)), X.basicOpen f = X.basicOpen g ∧ x ∈ X.basicOpen f := by
  obtain ⟨f, hf₁, hf₂⟩ := hU.exists_basicOpen_le ⟨x, hx.2⟩ hx.1
  obtain ⟨g, hg₁, hg₂⟩ := hV.exists_basicOpen_le ⟨x, hf₂⟩ hx.2
  obtain ⟨f', hf'⟩ :=
    basicOpen_basicOpen_is_basicOpen hU f (X.presheaf.map (homOfLE hf₁ : _ ⟶ V).op g)
  replace hf' := (hf'.trans (RingedSpace.basicOpen_res _ _ _)).trans (inf_eq_right.mpr hg₁)
  exact ⟨f', g, hf', hf'.symm ▸ hg₂⟩

/-- The prime ideal of `𝒪ₓ(U)` corresponding to a point `x : U`. -/
noncomputable def primeIdealOf (x : U) :
    PrimeSpectrum Γ(X, U) :=
  hU.isoSpec.hom.base x

theorem fromSpec_primeIdealOf (x : U) :
    hU.fromSpec.base (hU.primeIdealOf x) = x.1 := by
  dsimp only [IsAffineOpen.fromSpec, Subtype.coe_mk, IsAffineOpen.primeIdealOf]
  rw [← Scheme.comp_base_apply, Iso.hom_inv_id_assoc]
  rfl

open IsLocalRing in
theorem primeIdealOf_eq_map_closedPoint (x : U) :
    hU.primeIdealOf x = (Spec.map (X.presheaf.germ _ x x.2)).base (closedPoint _) :=
  hU.isoSpec_hom_base_apply _

/-- If a point `x : U` is a closed point, then its corresponding prime ideal is maximal. -/
theorem primeIdealOf_isMaximal_of_isClosed (x : U) (hx : IsClosed {(x : X)}) :
    (hU.primeIdealOf x).asIdeal.IsMaximal := by
  have hx₀ : IsClosed {x} := by
    simpa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective]
      using hx.preimage U.isOpenEmbedding'.continuous
  apply (hU.primeIdealOf x).isClosed_singleton_iff_isMaximal.mp
  rw [primeIdealOf, ← Set.image_singleton]
  refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed <|
    IsHomeomorph.isClosedEmbedding ?_).mp hx₀
  apply (TopCat.isIso_iff_isHomeomorph _).mp
  infer_instance

theorem isLocalization_stalk' (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec.base y ∈ U) :
    @IsLocalization.AtPrime
      (R := Γ(X, U))
      (S := X.presheaf.stalk <| hU.fromSpec.base y) _ _
      ((TopCat.Presheaf.algebra_section_stalk X.presheaf _)) y.asIdeal _ := by
  apply
    (@IsLocalization.isLocalization_iff_of_ringEquiv (R := Γ(X, U))
      (S := X.presheaf.stalk (hU.fromSpec.base y)) _ y.asIdeal.primeCompl _
      (TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec.base y, hy⟩) _ _
      (asIso <| hU.fromSpec.stalkMap y).commRingCatIsoToRingEquiv).mpr
  convert StructureSheaf.IsLocalization.to_stalk Γ(X, U) y using 1
  delta IsLocalization.AtPrime StructureSheaf.stalkAlgebra
  rw [RingHom.algebraMap_toAlgebra, RingEquiv.toRingHom_eq_coe,
    CategoryTheory.Iso.commRingCatIsoToRingEquiv_toRingHom, asIso_hom, ← CommRingCat.hom_comp,
    Scheme.stalkMap_germ, IsAffineOpen.fromSpec_app_self, Category.assoc, TopCat.Presheaf.germ_res]
  rfl

theorem isLocalization_stalk (x : U) :
    IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asIdeal := by
  rcases x with ⟨x, hx⟩
  set y := hU.primeIdealOf ⟨x, hx⟩ with hy
  have : hU.fromSpec.base y = x := hy ▸ hU.fromSpec_primeIdealOf ⟨x, hx⟩
  clear_value y
  subst this
  exact hU.isLocalization_stalk' y hx

lemma stalkMap_injective (f : X ⟶ Y) {U : Opens Y} (hU : IsAffineOpen U) (x : X)
    (hx : f.base x ∈ U)
    (h : ∀ g, f.stalkMap x (Y.presheaf.germ U (f.base x) hx g) = 0 →
      Y.presheaf.germ U (f.base x) hx g = 0) :
    Function.Injective (f.stalkMap x) := by
  letI := Y.presheaf.algebra_section_stalk ⟨f.base x, hx⟩
  apply (hU.isLocalization_stalk ⟨f.base x, hx⟩).injective_of_map_algebraMap_zero
  exact h

include hU in
lemma mem_ideal_iff {s : Γ(X, U)} {I : Ideal Γ(X, U)} :
    s ∈ I ↔ ∀ (x : X) (h : x ∈ U), X.presheaf.germ U x h s ∈ I.map (X.presheaf.germ U x h).hom := by
  refine ⟨fun hs x hxU ↦ Ideal.mem_map_of_mem _ hs, fun H ↦ ?_⟩
  letI (x : _) : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec.base x)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf _
  have (P : Ideal Γ(X, U)) [hP : P.IsPrime] : IsLocalization.AtPrime _ P :=
      hU.isLocalization_stalk' ⟨P, hP⟩ (hU.isoSpec.inv.base _).2
  refine Submodule.mem_of_localization_maximal
      (fun P hP ↦ X.presheaf.stalk (hU.fromSpec.base ⟨P, hP.isPrime⟩))
      (fun P hP ↦ Algebra.linearMap _ _) _ _ ?_
  intro P hP
  rw [Ideal.localized₀_eq_restrictScalars_map]
  exact H _ _

include hU in
lemma ideal_le_iff {I J : Ideal Γ(X, U)} :
    I ≤ J ↔ ∀ (x : X) (h : x ∈ U),
      I.map (X.presheaf.germ U x h).hom ≤ J.map (X.presheaf.germ U x h).hom :=
  ⟨fun h _ _ ↦ Ideal.map_mono h,
    fun H _ hs ↦ hU.mem_ideal_iff.mpr fun x hx ↦ H x hx (Ideal.mem_map_of_mem _ hs)⟩

include hU in
lemma ideal_ext_iff {I J : Ideal Γ(X, U)} :
    I = J ↔ ∀ (x : X) (h : x ∈ U),
      I.map (X.presheaf.germ U x h).hom = J.map (X.presheaf.germ U x h).hom := by
  simp_rw [le_antisymm_iff, hU.ideal_le_iff, forall_and]

/-- The basic open set of a section `f` on an affine open as an `X.affineOpens`. -/
@[simps]
def _root_.AlgebraicGeometry.Scheme.affineBasicOpen
    (X : Scheme) {U : X.affineOpens} (f : Γ(X, U)) : X.affineOpens :=
  ⟨X.basicOpen f, U.prop.basicOpen f⟩

lemma _root_.AlgebraicGeometry.Scheme.affineBasicOpen_le
    (X : Scheme) {V : X.affineOpens} (f : Γ(X, V.1)) : X.affineBasicOpen f ≤ V :=
  X.basicOpen_le f

include hU in
/--
In an affine open set `U`, a family of basic open covers `U` iff the sections span `Γ(X, U)`.
See `iSup_basicOpen_of_span_eq_top` for the inverse direction without the affine-ness assumption.
-/
theorem basicOpen_union_eq_self_iff (s : Set Γ(X, U)) :
    ⨆ f : s, X.basicOpen (f : Γ(X, U)) = U ↔ Ideal.span s = ⊤ := by
  trans ⋃ i : s, (PrimeSpectrum.basicOpen i.1).1 = Set.univ
  · trans
      hU.fromSpec.base ⁻¹' (⨆ f : s, X.basicOpen (f : Γ(X, U))).1 =
        hU.fromSpec.base ⁻¹' U.1
    · refine ⟨fun h => by rw [h], ?_⟩
      intro h
      apply_fun Set.image hU.fromSpec.base at h
      rw [Set.image_preimage_eq_inter_range, Set.image_preimage_eq_inter_range, hU.range_fromSpec]
        at h
      simp only [Set.inter_self, Opens.carrier_eq_coe, Set.inter_eq_right] at h
      ext1
      refine Set.Subset.antisymm ?_ h
      simp only [Set.iUnion_subset_iff, SetCoe.forall, Opens.coe_iSup]
      intro x _
      exact X.basicOpen_le x
    · simp only [Opens.iSup_def, Set.preimage_iUnion]
      congr! 1
      · refine congr_arg (Set.iUnion ·) ?_
        ext1 x
        exact congr_arg Opens.carrier (hU.fromSpec_preimage_basicOpen _)
      · exact congr_arg Opens.carrier hU.fromSpec_preimage_self
  · simp only [Opens.carrier_eq_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
    rw [← Set.compl_iInter, Set.compl_univ_iff, ← PrimeSpectrum.zeroLocus_iUnion, ←
      PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_span]
    simp only [Set.iUnion_singleton_eq_range, Subtype.range_val_subtype, Set.setOf_mem_eq]

include hU in
theorem self_le_basicOpen_union_iff (s : Set Γ(X, U)) :
    (U ≤ ⨆ f : s, X.basicOpen f.1) ↔ Ideal.span s = ⊤ := by
  rw [← hU.basicOpen_union_eq_self_iff, @comm _ Eq]
  refine ⟨fun h => le_antisymm h ?_, le_of_eq⟩
  simp only [iSup_le_iff, SetCoe.forall]
  intro x _
  exact X.basicOpen_le x

end IsAffineOpen

open _root_.PrimeSpectrum in
/-- The restriction of `Spec.map f` to a basic open `D(r)` is isomorphic to `Spec.map` of the
localization of `f` away from `r`. -/
noncomputable
def SpecMapRestrictBasicOpenIso {R S : CommRingCat} (f : R ⟶ S) (r : R) :
    Arrow.mk (Spec.map f ∣_ (PrimeSpectrum.basicOpen r)) ≅
      Arrow.mk (Spec.map <| CommRingCat.ofHom (Localization.awayMap f.hom r)) := by
  letI e₁ : Localization.Away r ≃ₐ[R] Γ(Spec R, basicOpen r) :=
    IsLocalization.algEquiv (Submonoid.powers r) _ _
  letI e₂ : Localization.Away (f.hom r) ≃ₐ[S] Γ(Spec S, basicOpen (f.hom r)) :=
    IsLocalization.algEquiv (Submonoid.powers (f.hom r)) _ _
  refine Arrow.isoMk ?_ ?_ ?_
  · exact Spec(S).isoOfEq (comap_basicOpen _ _) ≪≫
      (IsAffineOpen.Spec_basicOpen (f.hom r)).isoSpec ≪≫ Scheme.Spec.mapIso e₂.toCommRingCatIso.op
  · exact (IsAffineOpen.Spec_basicOpen r).isoSpec ≪≫ Scheme.Spec.mapIso e₁.toCommRingCatIso.op
  · have := AlgebraicGeometry.IsOpenImmersion.of_isLocalization
      (S := (Localization.Away r)) r
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))]
    simp only [Arrow.mk_left, Arrow.mk_right, Functor.id_obj, Scheme.isoOfEq_rfl, Iso.refl_trans,
      Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op,
      Arrow.mk_hom, Category.assoc, ← Spec.map_comp]
    conv =>
      congr
      · enter [2, 1]; tactic =>
        change _ =
          (f ≫ (Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.map (homOfLE le_top).op)
        ext
        simp only [Localization.awayMap, IsLocalization.Away.map, AlgEquiv.toRingEquiv_eq_coe,
          RingEquiv.toCommRingCatIso_hom, AlgEquiv.toRingEquiv_toRingHom, CommRingCat.hom_comp,
          CommRingCat.hom_ofHom, RingHom.comp_apply, IsLocalization.map_eq, RingHom.coe_coe,
          AlgEquiv.commutes, IsAffineOpen.algebraMap_Spec_obj]
      · enter [2, 2, 1]; tactic =>
        change _ = (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op
        ext
        simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toCommRingCatIso_hom,
          AlgEquiv.toRingEquiv_toRingHom, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
          RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgEquiv.commutes,
          IsAffineOpen.algebraMap_Spec_obj, homOfLE_leOfHom]
    simp only [IsAffineOpen.isoSpec_hom, homOfLE_leOfHom, Spec.map_comp, Category.assoc,
      Scheme.Opens.toSpecΓ_SpecMap_map_assoc, Scheme.Opens.toSpecΓ_top, Scheme.homOfLE_ι_assoc,
      morphismRestrict_ι_assoc]
    simp only [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]
    rfl

lemma stalkMap_injective_of_isAffine {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] (x : X)
    (h : ∀ g, f.stalkMap x (Y.presheaf.Γgerm (f.base x) g) = 0 →
      Y.presheaf.Γgerm (f.base x) g = 0) :
    Function.Injective (f.stalkMap x) :=
  (isAffineOpen_top Y).stalkMap_injective f x trivial h

/--
Given a spanning set of `Γ(X, U)`, the corresponding basic open sets cover `U`.
See `IsAffineOpen.basicOpen_union_eq_self_iff` for the inverse direction for affine open sets.
-/
lemma iSup_basicOpen_of_span_eq_top {X : Scheme} (U) (s : Set Γ(X, U))
    (hs : Ideal.span s = ⊤) : (⨆ i ∈ s, X.basicOpen i) = U := by
  apply le_antisymm
  · rw [iSup₂_le_iff]
    exact fun i _ ↦ X.basicOpen_le i
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := (isBasis_affine_open X).exists_subset_of_mem_open hx U.2
    refine SetLike.mem_of_subset ?_ hxV
    rw [← (hV.basicOpen_union_eq_self_iff (X.presheaf.map (homOfLE hVU).op '' s)).mpr
      (by rw [← Ideal.map_span, hs, Ideal.map_top])]
    simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Set.iUnion_coe_set, Set.mem_image,
      Set.iUnion_exists, Set.biUnion_and', Set.iUnion_iUnion_eq_right, Scheme.basicOpen_res,
      Opens.coe_inf, Opens.coe_mk, Set.iUnion_subset_iff]
    exact fun i hi ↦ (Set.inter_subset_right.trans
      (Set.subset_iUnion₂ (s := fun x _ ↦ (X.basicOpen x : Set X)) i hi))

/-- Let `P` be a predicate on the affine open sets of `X` satisfying
1. If `P` holds on `U`, then `P` holds on the basic open set of every section on `U`.
2. If `P` holds for a family of basic open sets covering `U`, then `P` holds for `U`.
3. There exists an affine open cover of `X` each satisfying `P`.

Then `P` holds for every affine open of `X`.

This is also known as the **Affine communication lemma** in [*The rising sea*][RisingSea]. -/
@[elab_as_elim]
theorem of_affine_open_cover {X : Scheme} {P : X.affineOpens → Prop}
    {ι} (U : ι → X.affineOpens) (iSup_U : (⨆ i, U i : X.Opens) = ⊤)
    (V : X.affineOpens)
    (basicOpen : ∀ (U : X.affineOpens) (f : Γ(X, U)), P U → P (X.affineBasicOpen f))
    (openCover :
      ∀ (U : X.affineOpens) (s : Finset (Γ(X, U)))
        (_ : Ideal.span (s : Set (Γ(X, U))) = ⊤),
        (∀ f : s, P (X.affineBasicOpen f.1)) → P U)
    (hU : ∀ i, P (U i)) : P V := by
  classical
  have : ∀ (x : V.1), ∃ f : Γ(X, V), ↑x ∈ X.basicOpen f ∧ P (X.affineBasicOpen f) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x.1 ∈ (⨆ i, U i : X.Opens) from iSup_U ▸ trivial)
    obtain ⟨f, g, e, hf⟩ := exists_basicOpen_le_affine_inter V.prop (U i).prop x ⟨x.prop, hi⟩
    refine ⟨f, hf, ?_⟩
    convert basicOpen _ g (hU i) using 1
    ext1
    exact e
  choose f hf₁ hf₂ using this
  suffices Ideal.span (Set.range f) = ⊤ by
    obtain ⟨t, ht₁, ht₂⟩ := (Ideal.span_eq_top_iff_finite _).mp this
    apply openCover V t ht₂
    rintro ⟨i, hi⟩
    obtain ⟨x, rfl⟩ := ht₁ hi
    exact hf₂ x
  rw [← V.prop.self_le_basicOpen_union_iff]
  intro x hx
  rw [iSup_range', SetLike.mem_coe, Opens.mem_iSup]
  exact ⟨_, hf₁ ⟨x, hx⟩⟩

section ZeroLocus

namespace Scheme

open ConcreteCategory

variable (X : Scheme.{u})

/-- On a scheme `X`, the preimage of the zero locus of the prime spectrum
of `Γ(X, ⊤)` under `X.toSpecΓ : X ⟶ Spec Γ(X, ⊤)` agrees with the associated zero locus on `X`. -/
lemma toSpecΓ_preimage_zeroLocus (s : Set Γ(X, ⊤)) :
    X.toSpecΓ.base ⁻¹' PrimeSpectrum.zeroLocus s = X.zeroLocus s :=
  LocallyRingedSpace.toΓSpec_preimage_zeroLocus_eq s

/-- If `X` is affine, the image of the zero locus of global sections of `X` under `X.isoSpec`
is the zero locus in terms of the prime spectrum of `Γ(X, ⊤)`. -/
lemma isoSpec_image_zeroLocus [IsAffine X]
    (s : Set Γ(X, ⊤)) :
    X.isoSpec.hom.base '' X.zeroLocus s = PrimeSpectrum.zeroLocus s := by
  rw [← X.toSpecΓ_preimage_zeroLocus]
  erw [Set.image_preimage_eq]
  exact (bijective_of_isIso X.isoSpec.hom.base).surjective

lemma toSpecΓ_image_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) :
    X.toSpecΓ.base '' X.zeroLocus s = PrimeSpectrum.zeroLocus s :=
  X.isoSpec_image_zeroLocus _

lemma isoSpec_inv_preimage_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) :
    X.isoSpec.inv.base ⁻¹' X.zeroLocus s = PrimeSpectrum.zeroLocus s := by
  rw [← toSpecΓ_preimage_zeroLocus, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.comp_base,
    X.isoSpec_inv_toSpecΓ]
  rfl

lemma isoSpec_inv_image_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) :
    X.isoSpec.inv.base '' PrimeSpectrum.zeroLocus s = X.zeroLocus s := by
  rw [← isoSpec_inv_preimage_zeroLocus, Set.image_preimage_eq]
  exact (bijective_of_isIso X.isoSpec.inv.base).surjective

/-- If `X` is an affine scheme, every closed set of `X` is the zero locus
of a set of global sections. -/
lemma eq_zeroLocus_of_isClosed_of_isAffine [IsAffine X] (s : Set X) :
    IsClosed s ↔ ∃ I : Ideal (Γ(X, ⊤)), s = X.zeroLocus (I : Set Γ(X, ⊤)) := by
  refine ⟨fun hs ↦ ?_, ?_⟩
  · let Z : Set (Spec <| Γ(X, ⊤)) := X.toΓSpecFun '' s
    have hZ : IsClosed Z := (X.isoSpec.hom.homeomorph).isClosedMap _ hs
    obtain ⟨I, (hI : Z = _)⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hZ
    use I
    simp only [← Scheme.toSpecΓ_preimage_zeroLocus, ← hI, Z]
    symm
    exact Set.preimage_image_eq _ (bijective_of_isIso X.isoSpec.hom.base).injective
  · rintro ⟨I, rfl⟩
    exact zeroLocus_isClosed X I.carrier

open Set.Notation in
lemma Opens.toSpecΓ_preimage_zeroLocus {X : Scheme.{u}} (U : X.Opens)
    (s : Set Γ(X, U)) :
    U.toSpecΓ.base ⁻¹' PrimeSpectrum.zeroLocus s = U.1 ↓∩ X.zeroLocus s := by
  rw [toSpecΓ, Scheme.comp_base, TopCat.coe_comp, Set.preimage_comp, Spec.map_base, hom_ofHom]
  erw [PrimeSpectrum.preimage_comap_zeroLocus]
  rw [Scheme.toSpecΓ_preimage_zeroLocus]
  change _ = U.ι.base ⁻¹' (X.zeroLocus s)
  rw [Scheme.preimage_zeroLocus, U.ι_app_self, ← zeroLocus_map_of_eq _ U.ι_preimage_self,
    ← Set.image_comp, ← RingHom.coe_comp, ← CommRingCat.hom_comp]
  congr!
  simp [← Functor.map_comp]
  rfl

end Scheme

lemma IsAffineOpen.fromSpec_preimage_zeroLocus {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U)) :
    hU.fromSpec.base ⁻¹' X.zeroLocus s = PrimeSpectrum.zeroLocus s := by
  ext x
  suffices (∀ f ∈ s, ¬f ∉ x.asIdeal) ↔ s ⊆ x.asIdeal by
    simpa [← hU.fromSpec_image_basicOpen, -not_not] using this
  simp_rw [not_not]
  rfl

lemma IsAffineOpen.fromSpec_image_zeroLocus {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U)) :
    hU.fromSpec.base '' PrimeSpectrum.zeroLocus s = X.zeroLocus s ∩ U := by
  rw [← hU.fromSpec_preimage_zeroLocus, Set.image_preimage_eq_inter_range, range_fromSpec]

open Set.Notation in
lemma Scheme.zeroLocus_inf (X : Scheme.{u}) {U : X.Opens} (I J : Ideal Γ(X, U)) :
    X.zeroLocus (U := U) ↑(I ⊓ J) = X.zeroLocus (U := U) I ∪ X.zeroLocus (U := U) J := by
  suffices U.1 ↓∩ (X.zeroLocus (U := U) ↑(I ⊓ J)) =
      U.1 ↓∩ (X.zeroLocus (U := U) I ∪ X.zeroLocus (U := U) J) by
    ext x
    by_cases hxU : x ∈ U
    · simpa [hxU] using congr(⟨x, hxU⟩ ∈ $this)
    · simp only [Submodule.coe_inf, Set.mem_union,
        codisjoint_iff_compl_le_left.mp (X.codisjoint_zeroLocus (U := U) (I ∩ J)) hxU,
        codisjoint_iff_compl_le_left.mp (X.codisjoint_zeroLocus (U := U) I) hxU, true_or]
  simp only [← U.toSpecΓ_preimage_zeroLocus, PrimeSpectrum.zeroLocus_inf I J,
    Set.preimage_union]

lemma Scheme.zeroLocus_biInf
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι → Ideal Γ(X, U)) {t : Set ι} (ht : t.Finite) :
    X.zeroLocus (U := U) ↑(⨅ i ∈ t, I i) = (⋃ i ∈ t, X.zeroLocus (U := U) (I i)) ∪ (↑U)ᶜ := by
  refine ht.induction_on _ (by simp) fun {i t} hit ht IH ↦ ?_
  simp only [Set.mem_insert_iff, Set.iUnion_iUnion_eq_or_left, ← IH, ← zeroLocus_inf,
    Submodule.coe_inf, Set.union_assoc]
  congr!
  simp

lemma Scheme.zeroLocus_biInf_of_nonempty
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι → Ideal Γ(X, U)) {t : Set ι} (ht : t.Finite) (ht' : t.Nonempty) :
    X.zeroLocus (U := U) ↑(⨅ i ∈ t, I i) = ⋃ i ∈ t, X.zeroLocus (U := U) (I i) := by
  rw [zeroLocus_biInf I ht, Set.union_eq_left]
  obtain ⟨i, hi⟩ := ht'
  exact fun x hx ↦ Set.mem_iUnion₂_of_mem hi
    (codisjoint_iff_compl_le_left.mp (X.codisjoint_zeroLocus (U := U) (I i)) hx)

lemma Scheme.zeroLocus_iInf
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι → Ideal Γ(X, U)) [Finite ι] :
    X.zeroLocus (U := U) ↑(⨅ i, I i) = (⋃ i, X.zeroLocus (U := U) (I i)) ∪ (↑U)ᶜ := by
  simpa using zeroLocus_biInf I Set.finite_univ

lemma Scheme.zeroLocus_iInf_of_nonempty
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι → Ideal Γ(X, U)) [Finite ι] [Nonempty ι] :
    X.zeroLocus (U := U) ↑(⨅ i, I i) = ⋃ i, X.zeroLocus (U := U) (I i) := by
  simpa using zeroLocus_biInf_of_nonempty I Set.finite_univ

end ZeroLocus

section Factorization

variable {X : Scheme.{u}} {A : CommRingCat}

/-- Given `f : X ⟶ Spec A` and some ideal `I ≤ ker(A ⟶ Γ(X, ⊤))`,
this is the lift to `X ⟶ Spec (A ⧸ I)`. -/
def Scheme.Hom.liftQuotient (f : X.Hom (Spec A)) (I : Ideal A)
    (hI : I ≤ RingHom.ker ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom) :
    X ⟶ Spec(A ⧸ I) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.lift _ ((Scheme.ΓSpecIso _).inv ≫ f.appTop).hom hI))

@[reassoc]
lemma Scheme.Hom.liftQuotient_comp (f : X.Hom (Spec A)) (I : Ideal A)
    (hI : I ≤ RingHom.ker ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom) :
    f.liftQuotient I hI ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) = f := by
  rw [Scheme.Hom.liftQuotient, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.lift_comp_mk]
  simp only [CommRingCat.hom_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, ←
    Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom]
  simp only [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- If `X ⟶ Spec A` is a morphism of schemes, then `Spec` of `A ⧸ specTargetImage f`
is the scheme-theoretic image of `f`. For this quotient as an object of `CommRingCat` see
`specTargetImage` below. -/
def specTargetImageIdeal (f : X ⟶ Spec A) : Ideal A :=
  (RingHom.ker <| (((ΓSpec.adjunction).homEquiv X (op A)).symm f).unop.hom)

/-- If `X ⟶ Spec A` is a morphism of schemes, then `Spec` of `specTargetImage f` is the
scheme-theoretic image of `f` and `f` factors as
`specTargetImageFactorization f ≫ Spec.map (specTargetImageRingHom f)`
(see `specTargetImageFactorization_comp`). -/
def specTargetImage (f : X ⟶ Spec A) : CommRingCat :=
  CommRingCat.of (A ⧸ specTargetImageIdeal f)

/-- If `f : X ⟶ Spec A` is a morphism of schemes, then `f` factors via
the inclusion of `Spec (specTargetImage f)` into `X`. -/
def specTargetImageFactorization (f : X ⟶ Spec A) : X ⟶ Spec (specTargetImage f) :=
  f.liftQuotient _ le_rfl

/-- If `f : X ⟶ Spec A` is a morphism of schemes, the induced morphism on spectra of
`specTargetImageRingHom f` is the inclusion of the scheme-theoretic image of `f` into `Spec A`. -/
def specTargetImageRingHom (f : X ⟶ Spec A) : A ⟶ specTargetImage f :=
  CommRingCat.ofHom (Ideal.Quotient.mk (specTargetImageIdeal f))

variable (f : X ⟶ Spec A)

lemma specTargetImageRingHom_surjective : Function.Surjective (specTargetImageRingHom f) :=
  Ideal.Quotient.mk_surjective

lemma specTargetImageFactorization_app_injective :
    Function.Injective <| (specTargetImageFactorization f).appTop := by
  let φ : A ⟶ Γ(X, ⊤) := (((ΓSpec.adjunction).homEquiv X (op A)).symm f).unop
  let φ' : specTargetImage f ⟶ Scheme.Γ.obj (op X) := CommRingCat.ofHom (RingHom.kerLift φ.hom)
  change Function.Injective <| ((ΓSpec.adjunction.homEquiv X _) φ'.op).appTop
  rw [ΓSpec_adjunction_homEquiv_eq]
  apply (RingHom.kerLift_injective φ.hom).comp
  exact ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso _).hom).mp inferInstance).injective

@[reassoc (attr := simp)]
lemma specTargetImageFactorization_comp :
    specTargetImageFactorization f ≫ Spec.map (specTargetImageRingHom f) = f :=
  f.liftQuotient_comp _ _

open RingHom

end Factorization

section Stalks

/-- Variant of `AlgebraicGeometry.localRingHom_comp_stalkIso` for `Spec.map`. -/
@[elementwise]
lemma Scheme.localRingHom_comp_stalkIso {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    (StructureSheaf.stalkIso R (PrimeSpectrum.comap f.hom p)).hom ≫
      (CommRingCat.ofHom <| Localization.localRingHom
        (PrimeSpectrum.comap f.hom p).asIdeal p.asIdeal f.hom rfl) ≫
      (StructureSheaf.stalkIso S p).inv = (Spec.map f).stalkMap p :=
  AlgebraicGeometry.localRingHom_comp_stalkIso f p

/-- Given a morphism of rings `f : R ⟶ S`, the stalk map of `Spec S ⟶ Spec R` at
a prime of `S` is isomorphic to the localized ring homomorphism. -/
def Scheme.arrowStalkMapSpecIso {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    Arrow.mk ((Spec.map f).stalkMap p) ≅ Arrow.mk (CommRingCat.ofHom <| Localization.localRingHom
      (PrimeSpectrum.comap f.hom p).asIdeal p.asIdeal f.hom rfl) := Arrow.isoMk
  (StructureSheaf.stalkIso R (PrimeSpectrum.comap f.hom p))
  (StructureSheaf.stalkIso S p) <| by
    rw [← Scheme.localRingHom_comp_stalkIso]
    simp

end Stalks
end AlgebraicGeometry
