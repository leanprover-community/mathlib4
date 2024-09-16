/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.RingTheory.Localization.InvSubmonoid

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

-- Explicit universe annotations were used in this file to improve performance #12737

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

open Spec (structureSheaf)

/-- The category of affine schemes -/
-- Porting note(#5171): linter not ported yet
-- @[nolint has_nonempty_instance]
def AffineScheme :=
  Scheme.Spec.EssImageSubcategory
deriving Category

/-- A Scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an isomorphism. -/
class IsAffine (X : Scheme) : Prop where
  affine : IsIso (ΓSpec.adjunction.unit.app X)

attribute [instance] IsAffine.affine

/-- The canonical isomorphism `X ≅ Spec Γ(X)` for an affine scheme. -/
@[simps! (config := .lemmasOnly) hom]
def Scheme.isoSpec (X : Scheme) [IsAffine X] : X ≅ Spec Γ(X, ⊤) :=
  asIso (ΓSpec.adjunction.unit.app X)

@[reassoc]
theorem Scheme.isoSpec_hom_naturality {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    X.isoSpec.hom ≫ Spec.map (f.app ⊤) = f ≫ Y.isoSpec.hom := by
  simp only [isoSpec, asIso_hom, ΓSpec.adjunction_unit_naturality]

@[reassoc]
theorem Scheme.isoSpec_inv_naturality {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Spec.map (f.app ⊤) ≫ Y.isoSpec.inv = X.isoSpec.inv ≫ f := by
  rw [Iso.eq_inv_comp, isoSpec, asIso_hom, ← ΓSpec.adjunction_unit_naturality_assoc, isoSpec,
    asIso_inv, IsIso.hom_inv_id, Category.comp_id]

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

theorem mem_Spec_essImage (X : Scheme) : X ∈ Scheme.Spec.essImage ↔ IsAffine X :=
  ⟨fun h => ⟨Functor.essImage.unit_isIso h⟩,
    fun _ => ΓSpec.adjunction.mem_essImage_of_unit_isIso _⟩

instance isAffine_affineScheme (X : AffineScheme.{u}) : IsAffine X.obj :=
  ⟨Functor.essImage.unit_isIso X.property⟩

instance (R : CommRingCatᵒᵖ) : IsAffine (Scheme.Spec.obj R) :=
  AlgebraicGeometry.isAffine_affineScheme ⟨_, Scheme.Spec.obj_mem_essImage R⟩

instance isAffine_Spec (R : CommRingCat) : IsAffine (Spec R) :=
  AlgebraicGeometry.isAffine_affineScheme ⟨_, Scheme.Spec.obj_mem_essImage (op R)⟩

theorem isAffine_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] [h : IsAffine Y] : IsAffine X := by
  rw [← mem_Spec_essImage] at h ⊢; exact Functor.essImage.ofIso (asIso f).symm h

/-- If `f : X ⟶ Y` is a morphism between affine schemes, the corresponding arrow is isomorphic
to the arrow of the morphism on prime spectra induced by the map on global sections. -/
noncomputable
def arrowIsoSpecΓOfIsAffine {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Arrow.mk f ≅ Arrow.mk (Spec.map (Scheme.Γ.map f.op)) :=
  Arrow.isoMk X.isoSpec Y.isoSpec (ΓSpec.adjunction.unit_naturality _)

namespace AffineScheme

/-- The `Spec` functor into the category of affine schemes. -/
def Spec : CommRingCatᵒᵖ ⥤ AffineScheme :=
  Scheme.Spec.toEssImage

-- Porting note (#11081): cannot automatically derive
instance Spec_full : Spec.Full := Functor.Full.toEssImage _

-- Porting note (#11081): cannot automatically derive
instance Spec_faithful : Spec.Faithful := Functor.Faithful.toEssImage _

-- Porting note (#11081): cannot automatically derive
instance Spec_essSurj : Spec.EssSurj := Functor.EssSurj.toEssImage (F := _)

/-- The forgetful functor `AffineScheme ⥤ Scheme`. -/
@[simps!]
def forgetToScheme : AffineScheme ⥤ Scheme :=
  Scheme.Spec.essImageInclusion

-- Porting note (#11081): cannot automatically derive
instance forgetToScheme_full : forgetToScheme.Full :=
show (Scheme.Spec.essImageInclusion).Full from inferInstance

-- Porting note (#11081): cannot automatically derive
instance forgetToScheme_faithful : forgetToScheme.Faithful :=
show (Scheme.Spec.essImageInclusion).Faithful from inferInstance

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
    @preservesLimitsOfNatIso _ _ _ _ _ _
      (isoWhiskerRight equivCommRingCat.unitIso forgetToScheme).symm
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
  refine isAffine_of_isIso (IsOpenImmersion.isoOfRangeEq f (Y.ofRestrict _) ?_).inv
  exact Subtype.range_val.symm

theorem isAffineOpen_top (X : Scheme) [IsAffine X] : IsAffineOpen (⊤ : X.Opens) := by
  convert isAffineOpen_opensRange (𝟙 X)
  ext1
  exact Set.range_id.symm

instance Scheme.isAffine_affineCover (X : Scheme) (i : X.affineCover.J) :
    IsAffine (X.affineCover.obj i) :=
  isAffine_Spec _

instance Scheme.isAffine_affineBasisCover (X : Scheme) (i : X.affineBasisCover.J) :
    IsAffine (X.affineBasisCover.obj i) :=
  isAffine_Spec _

instance Scheme.isAffine_affineOpenCover (X : Scheme) (𝒰 : X.AffineOpenCover) (i : 𝒰.J) :
    IsAffine (𝒰.openCover.obj i) :=
  inferInstanceAs (IsAffine (Spec (𝒰.obj i)))

instance {X} [IsAffine X] (i) : IsAffine ((Scheme.openCoverOfIsIso (𝟙 X)).obj i) := by
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
    (X : Scheme) [IsAffine X] (f : Scheme.Γ.obj (op X)) :
    X.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f :=
  ΓSpec.adjunction_unit_map_basicOpen _ _

theorem isBasis_basicOpen (X : Scheme) [IsAffine X] :
    Opens.IsBasis (Set.range (X.basicOpen : Γ(X, ⊤) → X.Opens)) := by
  delta Opens.IsBasis
  convert PrimeSpectrum.isBasis_basic_opens.inducing
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso X.isoSpec)).inducing using 1
  ext
  simp only [Set.mem_image, exists_exists_eq_and]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, ?_⟩
    exact congr_arg Opens.carrier (ΓSpec.adjunction_unit_map_basicOpen _ _)
  · rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩
    refine ⟨_, ⟨x, rfl⟩, ?_⟩
    exact congr_arg Opens.carrier (ΓSpec.adjunction_unit_map_basicOpen _ _).symm

namespace IsAffineOpen

variable {X Y : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))

/-- The open immersion `Spec Γ(X, U) ⟶ X` for an affine `U`. -/
def fromSpec :
    Spec Γ(X, U) ⟶ X :=
  haveI : IsAffine U := hU
  Spec.map (X.presheaf.map (eqToHom U.openEmbedding_obj_top.symm).op) ≫
    U.toScheme.isoSpec.inv ≫ U.ι

instance isOpenImmersion_fromSpec :
    IsOpenImmersion hU.fromSpec := by
  delta fromSpec
  infer_instance

@[simp]
theorem range_fromSpec :
    Set.range hU.fromSpec.1.base = (U : Set X) := by
  delta IsAffineOpen.fromSpec; dsimp
  rw [Function.comp.assoc, Set.range_comp, Set.range_iff_surjective.mpr, Set.image_univ]
  · exact Subtype.range_coe
  erw [← coe_comp, ← TopCat.epi_iff_surjective] -- now `erw` after #13170
  infer_instance

@[simp]
theorem opensRange_fromSpec : Scheme.Hom.opensRange hU.fromSpec = U := Opens.ext (range_fromSpec hU)

@[reassoc (attr := simp)]
theorem map_fromSpec {V : X.Opens} (hV : IsAffineOpen V) (f : op U ⟶ op V) :
    Spec.map (X.presheaf.map f) ≫ hU.fromSpec = hV.fromSpec := by
  have : IsAffine (X.restrictFunctor.obj U).left := hU
  haveI : IsAffine _ := hV
  conv_rhs =>
    rw [fromSpec, ← X.restrictFunctor_map_ofRestrict f.unop, ← Scheme.isoSpec_inv_naturality_assoc,
      ← Spec.map_comp_assoc, Scheme.restrictFunctor_map_app, ← Functor.map_comp]
  rw [fromSpec, ← Spec.map_comp_assoc, ← Functor.map_comp]
  rfl

include hU in
protected theorem isCompact :
    IsCompact (U : Set X) := by
  convert @IsCompact.image _ _ _ _ Set.univ hU.fromSpec.1.base PrimeSpectrum.compactSpace.1
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
  isAffine_of_isIso (f ∣_ U)

theorem _root_.AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion
    (f : AlgebraicGeometry.Scheme.Hom X Y) [H : IsOpenImmersion f] {U : X.Opens} :
    IsAffineOpen (f ''ᵁ U) ↔ IsAffineOpen U := by
  refine ⟨fun hU => @isAffine_of_isIso _ _
    (IsOpenImmersion.isoOfRangeEq (X.ofRestrict U.openEmbedding ≫ f) (Y.ofRestrict _) ?_).hom ?_ hU,
    fun hU => hU.image_of_isOpenImmersion f⟩
  · erw [Scheme.comp_val_base, coe_comp, Set.range_comp] -- now `erw` after #13170
    dsimp [Opens.coe_inclusion, Scheme.restrict]
    erw [Subtype.range_coe, Subtype.range_coe] -- now `erw` after #13170
    rfl
  · infer_instance

/-- The affine open sets of an open subscheme corresponds to
the affine open sets containing in the image. -/
@[simps]
def _root_.AlgebraicGeometry.IsOpenImmersion.affineOpensEquiv (f : X ⟶ Y) [H : IsOpenImmersion f] :
    X.affineOpens ≃ { U : Y.affineOpens // U ≤ f.opensRange } where
  toFun U := ⟨⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩, Set.image_subset_range _ _⟩
  invFun U := ⟨f ⁻¹ᵁ U, f.isAffineOpen_iff_of_isOpenImmersion.mp (by
    rw [show f ''ᵁ f ⁻¹ᵁ U = U from Opens.ext (Set.image_preimage_eq_of_subset U.2)]; exact U.1.2)⟩
  left_inv _ := Subtype.ext (Opens.ext (Set.preimage_image_eq _ H.base_open.inj))
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
  exact Set.preimage_image_eq _ PresheafedSpace.IsOpenImmersion.base_open.inj

theorem SpecΓIdentity_hom_app_fromSpec :
    (Scheme.ΓSpecIso Γ(X, U)).hom ≫ hU.fromSpec.app U =
      (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op := by
  simp only [fromSpec, Scheme.isoSpec, asIso_inv, Scheme.comp_coeBase, Opens.map_comp_obj,
    ΓSpecIso_obj_hom, Scheme.Opens.topIso_inv, Opens.map_top, Functor.id_obj, Functor.comp_obj,
    Functor.rightOp_obj, Scheme.Γ_obj, unop_op, Scheme.Spec_obj, Scheme.Opens.topIso_hom,
    Scheme.comp_app, Scheme.Opens.ι_app_self, Category.assoc, ← Functor.map_comp_assoc, ← op_comp,
    eqToHom_trans, Scheme.Opens.eq_presheaf_map_eqToHom, Scheme.Hom.naturality_assoc,
    Scheme.inv_app_top, IsIso.hom_inv_id_assoc]
  simp only [eqToHom_op, eqToHom_map, Spec.map_eqToHom, eqToHom_unop,
    Scheme.Spec_map_presheaf_map_eqToHom, eqToHom_trans]

@[elementwise]
theorem fromSpec_app_self :
    hU.fromSpec.app U = (Scheme.ΓSpecIso Γ(X, U)).inv ≫
      (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op := by
  rw [← hU.SpecΓIdentity_hom_app_fromSpec, Iso.inv_hom_id_assoc]

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
  change hU.fromSpec.val.base '' (hU.fromSpec.val.base ⁻¹' (X.basicOpen f : Set X)) = _
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

instance [IsAffine X] (r : Γ(X, ⊤)) : IsAffine (X.basicOpen r) :=
  (isAffineOpen_top X).basicOpen _

include hU in
theorem ι_basicOpen_preimage (r : Γ(X, ⊤)) :
    IsAffineOpen ((X.basicOpen r).ι ⁻¹ᵁ U) := by
  apply (X.basicOpen r).ι.isAffineOpen_iff_of_isOpenImmersion.mp
  dsimp [Scheme.Hom.opensFunctor, LocallyRingedSpace.IsOpenImmersion.opensFunctor]
  rw [Opens.functor_obj_map_obj, Opens.openEmbedding_obj_top, inf_comm,
    ← Scheme.basicOpen_res _ _ (homOfLE le_top).op]
  exact hU.basicOpen _

include hU in
theorem exists_basicOpen_le {V : X.Opens} (x : V) (h : ↑x ∈ U) :
    ∃ f : Γ(X, U), X.basicOpen f ≤ V ∧ ↑x ∈ X.basicOpen f := by
  have : IsAffine _ := hU
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, h₁, h₂⟩ :=
    (isBasis_basicOpen U).exists_subset_of_mem_open (x.2 : ⟨x, h⟩ ∈ _)
      ((Opens.map U.inclusion).obj V).isOpen
  have :
    U.ι ''ᵁ (U.toScheme.basicOpen r) =
      X.basicOpen (X.presheaf.map (eqToHom U.openEmbedding_obj_top.symm).op r) := by
    refine (Scheme.image_basicOpen U.ι r).trans ?_
    rw [Scheme.basicOpen_res_eq]
    simp only [Scheme.Opens.toScheme_presheaf_obj, Scheme.Opens.ι_appIso, Iso.refl_inv,
      CommRingCat.id_apply]
  use X.presheaf.map (eqToHom U.openEmbedding_obj_top.symm).op r
  rw [← this]
  exact ⟨Set.image_subset_iff.mpr h₂, ⟨_, h⟩, h₁, rfl⟩

/-- Given an affine open U and some `f : U`,
this is the canonical map `Γ(𝒪ₓ, D(f)) ⟶ Γ(Spec 𝒪ₓ(U), D(f))`
This is an isomorphism, as witnessed by an `IsIso` instance. -/
def basicOpenSectionsToAffine :
    Γ(X, X.basicOpen f) ⟶ Γ(Spec Γ(X, U), PrimeSpectrum.basicOpen f) :=
  hU.fromSpec.1.c.app (op <| X.basicOpen f) ≫
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
  -- Porting note: more hand holding is required here, the next 4 lines were not necessary
  delta StructureSheaf.openAlgebra
  congr 1
  rw [CommRingCat.ringHom_comp_eq_comp, Iso.commRingIsoToRingEquiv_toRingHom, asIso_hom]
  dsimp [CommRingCat.ofHom, RingHom.algebraMap_toAlgebra]
  change X.presheaf.map _ ≫ basicOpenSectionsToAffine hU f = _
  delta basicOpenSectionsToAffine
  rw [hU.fromSpec.naturality_assoc, hU.fromSpec_app_self]
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
  apply StructureSheaf.toOpen_res

instance _root_.AlgebraicGeometry.isLocalization_away_of_isAffine
    [IsAffine X] (r : Γ(X, ⊤)) :
    IsLocalization.Away r Γ(X, X.basicOpen r) :=
  isLocalization_basicOpen (isAffineOpen_top X) r

lemma appLE_eq_away_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e) (r : Γ(Y, U)) :
    letI := hU.isLocalization_basicOpen r
    letI := hV.isLocalization_basicOpen (f.appLE U V e r)
    f.appLE (Y.basicOpen r) (X.basicOpen (f.appLE U V e r)) (by simp [Scheme.Hom.appLE]) =
        IsLocalization.Away.map _ _ (f.appLE U V e) r := by
  letI := hU.isLocalization_basicOpen r
  letI := hV.isLocalization_basicOpen (f.appLE U V e r)
  apply IsLocalization.ringHom_ext (.powers r)
  rw [← CommRingCat.comp_eq_ring_hom_comp, IsLocalization.Away.map, IsLocalization.map_comp,
    RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_eq_ring_hom_comp,
    Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

include hU in
theorem isLocalization_of_eq_basicOpen {V : X.Opens} (i : V ⟶ U) (e : V = X.basicOpen f) :
    @IsLocalization.Away _ _ f Γ(X, V) _ (X.presheaf.map i.op).toAlgebra := by
  subst e; convert isLocalization_basicOpen hU f using 3

instance _root_.AlgebraicGeometry.Γ_restrict_isLocalization
    (X : Scheme.{u}) [IsAffine X] (r : Γ(X, ⊤)) :
    IsLocalization.Away r Γ(X.basicOpen r, ⊤) :=
  (isAffineOpen_top X).isLocalization_of_eq_basicOpen r _ (Opens.openEmbedding_obj_top _)

include hU in
theorem basicOpen_basicOpen_is_basicOpen (g : Γ(X, X.basicOpen f)) :
    ∃ f' : Γ(X, U), X.basicOpen f' = X.basicOpen g := by
  have := isLocalization_basicOpen hU f
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.surj'' (Submonoid.powers f) g
  use f * x
  rw [Algebra.smul_def, Scheme.basicOpen_mul, Scheme.basicOpen_mul, RingHom.algebraMap_toAlgebra]
  rw [Scheme.basicOpen_res]
  refine (inf_eq_left.mpr ?_).symm
  -- Porting note: a little help is needed here
  convert inf_le_left (α := X.Opens) using 1
  apply Scheme.basicOpen_of_isUnit
  apply
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
  ((@Scheme.isoSpec U hU).hom ≫
    Spec.map (X.presheaf.map (eqToHom U.openEmbedding_obj_top).op)).1.base x

theorem fromSpec_primeIdealOf (x : U) :
    hU.fromSpec.val.base (hU.primeIdealOf x) = x.1 := by
  dsimp only [IsAffineOpen.fromSpec, Subtype.coe_mk, IsAffineOpen.primeIdealOf]
  -- Porting note: in the porting note of `Scheme.comp_val_base`, it says that `elementwise` is
  -- unnecessary, indeed, the linter did not like it, so I just use `elementwise_of%` instead of
  -- adding the corresponding lemma in `Scheme.lean` file
  erw [← elementwise_of% Scheme.comp_val_base] -- now `erw` after #13170
  simp only [Scheme.Opens.toScheme_presheaf_obj, Category.assoc, ← Spec.map_comp_assoc,
    ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
    CategoryTheory.Functor.map_id, Spec.map_id, Category.id_comp, Iso.hom_inv_id_assoc]
  rfl -- `rfl` was not needed before #13170

theorem isLocalization_stalk' (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec.1.base y ∈ U) :
    @IsLocalization.AtPrime
      (R := Γ(X, U))
      (S := X.presheaf.stalk <| hU.fromSpec.1.base y) _ _
      ((TopCat.Presheaf.algebra_section_stalk X.presheaf _)) y.asIdeal _ := by
  apply
    (@IsLocalization.isLocalization_iff_of_ringEquiv (R := Γ(X, U))
      (S := X.presheaf.stalk (hU.fromSpec.1.base y)) _ y.asIdeal.primeCompl _
      (TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec.1.base y, hy⟩) _ _
      (asIso <| hU.fromSpec.stalkMap y).commRingCatIsoToRingEquiv).mpr
  -- Porting note: need to know what the ring is and after convert, instead of equality
  -- we get an `iff`.
  convert StructureSheaf.IsLocalization.to_stalk Γ(X, U) y using 1
  delta IsLocalization.AtPrime StructureSheaf.stalkAlgebra
  rw [iff_iff_eq]
  congr 2
  rw [RingHom.algebraMap_toAlgebra]
  refine (PresheafedSpace.stalkMap_germ hU.fromSpec.1 _ ⟨_, hy⟩).trans ?_
  rw [← Scheme.Hom.app, IsAffineOpen.fromSpec_app_self, Category.assoc, TopCat.Presheaf.germ_res]
  rfl

-- Porting note: I have split this into two lemmas
theorem isLocalization_stalk (x : U) :
    IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asIdeal := by
  rcases x with ⟨x, hx⟩
  set y := hU.primeIdealOf ⟨x, hx⟩ with hy
  have : hU.fromSpec.val.base y = x := hy ▸ hU.fromSpec_primeIdealOf ⟨x, hx⟩
  clear_value y
  subst this
  exact hU.isLocalization_stalk' y hx

/-- The basic open set of a section `f` on an affine open as an `X.affineOpens`. -/
@[simps]
def _root_.AlgebraicGeometry.Scheme.affineBasicOpen
    (X : Scheme) {U : X.affineOpens} (f : Γ(X, U)) : X.affineOpens :=
  ⟨X.basicOpen f, U.prop.basicOpen f⟩

include hU in
/--
In an affine open set `U`, a family of basic open covers `U` iff the sections span `Γ(X, U)`.
See `iSup_basicOpen_of_span_eq_top` for the inverse direction without the affine-ness assumption.
-/
theorem basicOpen_union_eq_self_iff (s : Set Γ(X, U)) :
    ⨆ f : s, X.basicOpen (f : Γ(X, U)) = U ↔ Ideal.span s = ⊤ := by
  trans ⋃ i : s, (PrimeSpectrum.basicOpen i.1).1 = Set.univ
  · trans
      hU.fromSpec.1.base ⁻¹' (⨆ f : s, X.basicOpen (f : Γ(X, U))).1 =
        hU.fromSpec.1.base ⁻¹' U.1
    · refine ⟨fun h => by rw [h], ?_⟩
      intro h
      apply_fun Set.image hU.fromSpec.1.base at h
      rw [Set.image_preimage_eq_inter_range, Set.image_preimage_eq_inter_range, hU.range_fromSpec]
        at h
      simp only [Set.inter_self, Opens.carrier_eq_coe, Set.inter_eq_right] at h
      ext1
      refine Set.Subset.antisymm ?_ h
      simp only [Set.iUnion_subset_iff, SetCoe.forall, Opens.coe_iSup]
      intro x _
      exact X.basicOpen_le x
    · simp only [Opens.iSup_def, Subtype.coe_mk, Set.preimage_iUnion]
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

/-- On a locally ringed space `X`, the preimage of the zero locus of the prime spectrum
of `Γ(X, ⊤)` under `toΓSpecFun` agrees with the associated zero locus on `X`. -/
lemma Scheme.toΓSpec_preimage_zeroLocus_eq {X : Scheme.{u}} (s : Set Γ(X, ⊤)) :
    (ΓSpec.adjunction.unit.app X).val.base ⁻¹' PrimeSpectrum.zeroLocus s = X.zeroLocus s :=
  LocallyRingedSpace.toΓSpec_preimage_zeroLocus_eq s

open ConcreteCategory

/-- If `X` is affine, the image of the zero locus of global sections of `X` under `toΓSpecFun`
is the zero locus in terms of the prime spectrum of `Γ(X, ⊤)`. -/
lemma Scheme.toΓSpec_image_zeroLocus_eq_of_isAffine {X : Scheme.{u}} [IsAffine X]
    (s : Set Γ(X, ⊤)) :
    X.isoSpec.hom.val.base '' X.zeroLocus s = PrimeSpectrum.zeroLocus s := by
  erw [← X.toΓSpec_preimage_zeroLocus_eq, Set.image_preimage_eq]
  exact (bijective_of_isIso X.isoSpec.hom.val.base).surjective

/-- If `X` is an affine scheme, every closed set of `X` is the zero locus
of a set of global sections. -/
lemma Scheme.eq_zeroLocus_of_isClosed_of_isAffine (X : Scheme.{u}) [IsAffine X] (s : Set X) :
    IsClosed s ↔ ∃ I : Ideal (Γ(X, ⊤)), s = X.zeroLocus (I : Set Γ(X, ⊤)) := by
  refine ⟨fun hs ↦ ?_, ?_⟩
  · let Z : Set (Spec <| Γ(X, ⊤)) := X.toΓSpecFun '' s
    have hZ : IsClosed Z := (X.isoSpec.hom.homeomorph).isClosedMap _ hs
    obtain ⟨I, (hI : Z = _)⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hZ
    use I
    simp only [← Scheme.toΓSpec_preimage_zeroLocus_eq, ← hI, Z]
    erw [Set.preimage_image_eq _ (bijective_of_isIso X.isoSpec.hom.val.base).injective]
  · rintro ⟨I, rfl⟩
    exact zeroLocus_isClosed X I.carrier

end ZeroLocus

section Stalks

/-- Variant of `AlgebraicGeometry.localRingHom_comp_stalkIso` for `Spec.map`. -/
@[elementwise]
lemma Scheme.localRingHom_comp_stalkIso {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    (StructureSheaf.stalkIso R (PrimeSpectrum.comap f p)).hom ≫
      (CommRingCat.ofHom <| Localization.localRingHom
        (PrimeSpectrum.comap f p).asIdeal p.asIdeal f rfl) ≫
      (StructureSheaf.stalkIso S p).inv = (Spec.map f).stalkMap p :=
  AlgebraicGeometry.localRingHom_comp_stalkIso f p

/-- Given a morphism of rings `f : R ⟶ S`, the stalk map of `Spec S ⟶ Spec R` at
a prime of `S` is isomorphic to the localized ring homomorphism. -/
def Scheme.arrowStalkMapSpecIso {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    Arrow.mk ((Spec.map f).stalkMap p) ≅ Arrow.mk (CommRingCat.ofHom <| Localization.localRingHom
      (PrimeSpectrum.comap f p).asIdeal p.asIdeal f rfl) := Arrow.isoMk
  (StructureSheaf.stalkIso R (PrimeSpectrum.comap f p))
  (StructureSheaf.stalkIso S p) <| by
    rw [← Scheme.localRingHom_comp_stalkIso]
    simp

end Stalks

@[deprecated (since := "2024-06-21"), nolint defLemma]
alias isAffineAffineScheme := isAffine_affineScheme
@[deprecated (since := "2024-06-21"), nolint defLemma]
alias SpecIsAffine := isAffine_Spec
@[deprecated (since := "2024-06-21")]
alias isAffineOfIso := isAffine_of_isIso
@[deprecated (since := "2024-06-21")]
alias rangeIsAffineOpenOfOpenImmersion := isAffineOpen_opensRange
@[deprecated (since := "2024-06-21")]
alias topIsAffineOpen := isAffineOpen_top
@[deprecated (since := "2024-06-21"), nolint defLemma]
alias Scheme.affineCoverIsAffine := Scheme.isAffine_affineCover
@[deprecated (since := "2024-06-21"), nolint defLemma]
alias Scheme.affineBasisCoverIsAffine := Scheme.isAffine_affineBasisCover
@[deprecated (since := "2024-06-21")]
alias IsAffineOpen.fromSpec_range := IsAffineOpen.range_fromSpec
@[deprecated (since := "2024-06-21")]
alias IsAffineOpen.imageIsOpenImmersion := IsAffineOpen.image_of_isOpenImmersion
@[deprecated (since := "2024-06-21"), nolint defLemma]
alias Scheme.quasi_compact_of_affine := Scheme.compactSpace_of_isAffine
@[deprecated (since := "2024-06-21")]
alias IsAffineOpen.fromSpec_base_preimage := IsAffineOpen.fromSpec_preimage_self
@[deprecated (since := "2024-06-21")]
alias IsAffineOpen.fromSpec_map_basicOpen' := IsAffineOpen.fromSpec_preimage_basicOpen'
@[deprecated (since := "2024-06-21")]
alias IsAffineOpen.fromSpec_map_basicOpen := IsAffineOpen.fromSpec_preimage_basicOpen
@[deprecated (since := "2024-06-21")]
alias IsAffineOpen.opensFunctor_map_basicOpen := IsAffineOpen.fromSpec_image_basicOpen
@[deprecated (since := "2024-06-21")]
alias IsAffineOpen.basicOpenIsAffine := IsAffineOpen.basicOpen
@[deprecated (since := "2024-06-21")]
alias IsAffineOpen.mapRestrictBasicOpen := IsAffineOpen.ι_basicOpen_preimage

end AlgebraicGeometry
