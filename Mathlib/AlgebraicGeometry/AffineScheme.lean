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

#align_import algebraic_geometry.AffineScheme from "leanprover-community/mathlib"@"88474d1b5af6d37c2ab728b757771bced7f5194c"

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

-- Explicit universe annotations were used in this file to improve perfomance #12737

set_option linter.uppercaseLean3 false

set_option allowUnsafeReducibility true in
attribute [local reducible] Quiver.Hom

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
#align algebraic_geometry.AffineScheme AlgebraicGeometry.AffineScheme

/-- A Scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an isomorphism. -/
class IsAffine (X : Scheme) : Prop where
  affine : IsIso (ΓSpec.adjunction.unit.app X)
#align algebraic_geometry.is_affine AlgebraicGeometry.IsAffine

attribute [instance] IsAffine.affine

/-- The canonical isomorphism `X ≅ Spec Γ(X)` for an affine scheme. -/
@[simps! (config := .lemmasOnly) hom]
def Scheme.isoSpec (X : Scheme) [IsAffine X] : X ≅ Spec Γ(X, ⊤) :=
  asIso (ΓSpec.adjunction.unit.app X)
#align algebraic_geometry.Scheme.iso_Spec AlgebraicGeometry.Scheme.isoSpec

/-- Construct an affine scheme from a scheme and the information that it is affine.
Also see `AffineScheme.of` for a typeclass version. -/
@[simps]
def AffineScheme.mk (X : Scheme) (_ : IsAffine X) : AffineScheme :=
  ⟨X, ΓSpec.adjunction.mem_essImage_of_unit_isIso _⟩
#align algebraic_geometry.AffineScheme.mk AlgebraicGeometry.AffineScheme.mk

/-- Construct an affine scheme from a scheme. Also see `AffineScheme.mk` for a non-typeclass
version. -/
def AffineScheme.of (X : Scheme) [h : IsAffine X] : AffineScheme :=
  AffineScheme.mk X h
#align algebraic_geometry.AffineScheme.of AlgebraicGeometry.AffineScheme.of

/-- Type check a morphism of schemes as a morphism in `AffineScheme`. -/
def AffineScheme.ofHom {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    AffineScheme.of X ⟶ AffineScheme.of Y :=
  f
#align algebraic_geometry.AffineScheme.of_hom AlgebraicGeometry.AffineScheme.ofHom

theorem mem_Spec_essImage (X : Scheme) : X ∈ Scheme.Spec.essImage ↔ IsAffine X :=
  ⟨fun h => ⟨Functor.essImage.unit_isIso h⟩,
    fun _ => ΓSpec.adjunction.mem_essImage_of_unit_isIso _⟩
#align algebraic_geometry.mem_Spec_ess_image AlgebraicGeometry.mem_Spec_essImage

instance isAffine_affineScheme (X : AffineScheme.{u}) : IsAffine X.obj :=
  ⟨Functor.essImage.unit_isIso X.property⟩
#align algebraic_geometry.is_affine_AffineScheme AlgebraicGeometry.isAffine_affineScheme

instance (R : CommRingCatᵒᵖ) : IsAffine (Scheme.Spec.obj R) :=
  AlgebraicGeometry.isAffine_affineScheme ⟨_, Scheme.Spec.obj_mem_essImage R⟩

instance isAffine_Spec (R : CommRingCat) : IsAffine (Spec R) :=
  AlgebraicGeometry.isAffine_affineScheme ⟨_, Scheme.Spec.obj_mem_essImage (op R)⟩
#align algebraic_geometry.Spec_is_affine AlgebraicGeometry.isAffine_Spec

theorem isAffine_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] [h : IsAffine Y] : IsAffine X := by
  rw [← mem_Spec_essImage] at h ⊢; exact Functor.essImage.ofIso (asIso f).symm h
#align algebraic_geometry.is_affine_of_iso AlgebraicGeometry.isAffine_of_isIso

namespace AffineScheme

/-- The `Spec` functor into the category of affine schemes. -/
def Spec : CommRingCatᵒᵖ ⥤ AffineScheme :=
  Scheme.Spec.toEssImage
#align algebraic_geometry.AffineScheme.Spec AlgebraicGeometry.AffineScheme.Spec

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
#align algebraic_geometry.AffineScheme.forget_to_Scheme AlgebraicGeometry.AffineScheme.forgetToScheme

-- Porting note (#11081): cannot automatically derive
instance forgetToScheme_full : forgetToScheme.Full :=
show (Scheme.Spec.essImageInclusion).Full from inferInstance

-- Porting note (#11081): cannot automatically derive
instance forgetToScheme_faithful : forgetToScheme.Faithful :=
show (Scheme.Spec.essImageInclusion).Faithful from inferInstance

/-- The global section functor of an affine scheme. -/
def Γ : AffineSchemeᵒᵖ ⥤ CommRingCat :=
  forgetToScheme.op ⋙ Scheme.Γ
#align algebraic_geometry.AffineScheme.Γ AlgebraicGeometry.AffineScheme.Γ

/-- The category of affine schemes is equivalent to the category of commutative rings. -/
def equivCommRingCat : AffineScheme ≌ CommRingCatᵒᵖ :=
  equivEssImageOfReflective.symm
#align algebraic_geometry.AffineScheme.equiv_CommRing AlgebraicGeometry.AffineScheme.equivCommRingCat

instance : Γ.{u}.rightOp.IsEquivalence := equivCommRingCat.isEquivalence_functor

instance : Γ.{u}.rightOp.op.IsEquivalence := equivCommRingCat.op.isEquivalence_functor

instance ΓIsEquiv : Γ.{u}.IsEquivalence :=
  inferInstanceAs (Γ.{u}.rightOp.op ⋙ (opOpEquivalence _).functor).IsEquivalence
#align algebraic_geometry.AffineScheme.Γ_is_equiv AlgebraicGeometry.AffineScheme.ΓIsEquiv

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
def IsAffineOpen {X : Scheme} (U : Opens X) : Prop :=
  IsAffine (X ∣_ᵤ U)
#align algebraic_geometry.is_affine_open AlgebraicGeometry.IsAffineOpen

/-- The set of affine opens as a subset of `opens X`. -/
def Scheme.affineOpens (X : Scheme) : Set (Opens X) :=
  {U : Opens X | IsAffineOpen U}
#align algebraic_geometry.Scheme.affine_opens AlgebraicGeometry.Scheme.affineOpens

instance {Y : Scheme.{u}} (U : Y.affineOpens) :
    IsAffine (Scheme.restrict Y <| Opens.openEmbedding U.val) :=
  U.property

theorem isAffineOpen_opensRange {X Y : Scheme} [IsAffine X] (f : X ⟶ Y)
    [H : IsOpenImmersion f] : IsAffineOpen (Scheme.Hom.opensRange f) := by
  refine isAffine_of_isIso (IsOpenImmersion.isoOfRangeEq f (Y.ofRestrict _) ?_).inv
  exact Subtype.range_val.symm
#align algebraic_geometry.range_is_affine_open_of_open_immersion AlgebraicGeometry.isAffineOpen_opensRange

theorem isAffineOpen_top (X : Scheme) [IsAffine X] : IsAffineOpen (⊤ : Opens X) := by
  convert isAffineOpen_opensRange (𝟙 X)
  ext1
  exact Set.range_id.symm
#align algebraic_geometry.top_is_affine_open AlgebraicGeometry.isAffineOpen_top

instance Scheme.isAffine_affineCover (X : Scheme) (i : X.affineCover.J) :
    IsAffine (X.affineCover.obj i) :=
  isAffine_Spec _
#align algebraic_geometry.Scheme.affine_cover_is_affine AlgebraicGeometry.Scheme.isAffine_affineCover

instance Scheme.isAffine_affineBasisCover (X : Scheme) (i : X.affineBasisCover.J) :
    IsAffine (X.affineBasisCover.obj i) :=
  isAffine_Spec _
#align algebraic_geometry.Scheme.affine_basis_cover_is_affine AlgebraicGeometry.Scheme.isAffine_affineBasisCover

theorem isBasis_affine_open (X : Scheme) : Opens.IsBasis X.affineOpens := by
  rw [Opens.isBasis_iff_nbhd]
  rintro U x (hU : x ∈ (U : Set X))
  obtain ⟨S, hS, hxS, hSU⟩ := X.affineBasisCover_is_basis.exists_subset_of_mem_open hU U.isOpen
  refine ⟨⟨S, X.affineBasisCover_is_basis.isOpen hS⟩, ?_, hxS, hSU⟩
  rcases hS with ⟨i, rfl⟩
  exact isAffineOpen_opensRange _
#align algebraic_geometry.is_basis_affine_open AlgebraicGeometry.isBasis_affine_open

theorem Scheme.map_PrimeSpectrum_basicOpen_of_affine
    (X : Scheme) [IsAffine X] (f : Scheme.Γ.obj (op X)) :
    X.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f :=
  ΓSpec.adjunction_unit_map_basicOpen _ _
#align algebraic_geometry.Scheme.map_prime_spectrum_basic_open_of_affine AlgebraicGeometry.Scheme.map_PrimeSpectrum_basicOpen_of_affine

theorem isBasis_basicOpen (X : Scheme) [IsAffine X] :
    Opens.IsBasis (Set.range (X.basicOpen : Γ(X, ⊤) → Opens X)) := by
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
#align algebraic_geometry.is_basis_basic_open AlgebraicGeometry.isBasis_basicOpen

namespace IsAffineOpen

variable {X Y : Scheme.{u}} {U : Opens X} (hU : IsAffineOpen U) (f : Γ(X, U))

/-- The open immersion `Spec Γ(X, U) ⟶ X` for an affine `U`. -/
def fromSpec :
    (Spec Γ(X, U)) ⟶ X :=
  haveI : IsAffine (X ∣_ᵤ U) := hU
  Spec.map (X.presheaf.map (eqToHom U.openEmbedding_obj_top.symm).op) ≫
    (X ∣_ᵤ U).isoSpec.inv ≫ Scheme.ιOpens U
#align algebraic_geometry.is_affine_open.from_Spec AlgebraicGeometry.IsAffineOpen.fromSpec

instance isOpenImmersion_fromSpec :
    IsOpenImmersion hU.fromSpec := by
  delta fromSpec
  infer_instance
#align algebraic_geometry.is_affine_open.is_open_immersion_from_Spec AlgebraicGeometry.IsAffineOpen.isOpenImmersion_fromSpec

@[simp]
theorem range_fromSpec :
    Set.range hU.fromSpec.1.base = (U : Set X) := by
  delta IsAffineOpen.fromSpec; dsimp
  rw [Function.comp.assoc, Set.range_comp, Set.range_iff_surjective.mpr, Set.image_univ]
  · exact Subtype.range_coe
  erw [← coe_comp, ← TopCat.epi_iff_surjective] -- now `erw` after #13170
  infer_instance
#align algebraic_geometry.is_affine_open.from_Spec_range AlgebraicGeometry.IsAffineOpen.range_fromSpec

@[simp]
theorem fromSpec_image_top : hU.fromSpec ''ᵁ ⊤ = U :=
  Opens.ext (Set.image_univ.trans (range_fromSpec hU))
#align algebraic_geometry.is_affine_open.from_Spec_image_top AlgebraicGeometry.IsAffineOpen.fromSpec_image_top

@[simp]
theorem opensRange_fromSpec : Scheme.Hom.opensRange hU.fromSpec = U := Opens.ext (range_fromSpec hU)

protected theorem isCompact :
    IsCompact (U : Set X) := by
  convert @IsCompact.image _ _ _ _ Set.univ hU.fromSpec.1.base PrimeSpectrum.compactSpace.1
    (by fun_prop)
  convert hU.range_fromSpec.symm
  exact Set.image_univ
#align algebraic_geometry.is_affine_open.is_compact AlgebraicGeometry.IsAffineOpen.isCompact

theorem image_of_isOpenImmersion (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsAffineOpen (f ''ᵁ U) := by
  have : IsAffine _ := hU
  convert isAffineOpen_opensRange (X.ofRestrict U.openEmbedding ≫ f)
  ext1
  exact Set.image_eq_range _ _
#align algebraic_geometry.is_affine_open.image_is_open_immersion AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion

theorem _root_.AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion
    (f : AlgebraicGeometry.Scheme.Hom X Y) [H : IsOpenImmersion f] {U : Opens X} :
    IsAffineOpen (f ''ᵁ U) ↔ IsAffineOpen U := by
  refine ⟨fun hU => @isAffine_of_isIso _ _
    (IsOpenImmersion.isoOfRangeEq (X.ofRestrict U.openEmbedding ≫ f) (Y.ofRestrict _) ?_).hom ?_ hU,
    fun hU => hU.image_of_isOpenImmersion f⟩
  · erw [Scheme.comp_val_base, coe_comp, Set.range_comp] -- now `erw` after #13170
    dsimp [Opens.coe_inclusion, Scheme.restrict]
    erw [Subtype.range_coe, Subtype.range_coe] -- now `erw` after #13170
    rfl
  · infer_instance
#align algebraic_geometry.is_affine_open_iff_of_is_open_immersion AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion

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
def _root_.AlgebraicGeometry.affineOpensRestrict {X : Scheme.{u}} (U : Opens X) :
    (X ∣_ᵤ U).affineOpens ≃ { V : X.affineOpens // V ≤ U } :=
  (IsOpenImmersion.affineOpensEquiv (Scheme.ιOpens U)).trans (Equiv.subtypeEquivProp (by simp))

@[simp]
lemma _root_.AlgebraicGeometry.affineOpensRestrict_symm_apply_coe
    {X : Scheme.{u}} (U : Opens X) (V) :
    ((affineOpensRestrict U).symm V).1 = Scheme.ιOpens U ⁻¹ᵁ V := rfl

instance (priority := 100) _root_.AlgebraicGeometry.Scheme.compactSpace_of_isAffine
    (X : Scheme) [IsAffine X] :
    CompactSpace X :=
  ⟨(isAffineOpen_top X).isCompact⟩
#align algebraic_geometry.Scheme.quasi_compact_of_affine AlgebraicGeometry.Scheme.compactSpace_of_isAffine

@[simp]
theorem fromSpec_preimage_self :
    hU.fromSpec ⁻¹ᵁ U = ⊤ := by
  ext1
  rw [Opens.map_coe, Opens.coe_top, ← hU.range_fromSpec, ← Set.image_univ]
  exact Set.preimage_image_eq _ PresheafedSpace.IsOpenImmersion.base_open.inj
#align algebraic_geometry.is_affine_open.from_Spec_base_preimage AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_self

#adaptation_note /-- 2024-04-23
The backwards compatibility flags don't help here. -/
set_option maxHeartbeats 400000 in
-- Doesn't build without the `IsAffine` instance but the linter complains
@[nolint unusedHavesSuffices]
theorem SpecΓIdentity_hom_app_fromSpec :
    (Scheme.ΓSpecIso Γ(X, U)).hom ≫ hU.fromSpec.app U =
      (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op := by
  have : IsAffine _ := hU
  delta IsAffineOpen.fromSpec Scheme.isoSpec
  rw [Scheme.comp_app, Scheme.comp_app, ΓSpecIso_obj_hom,
    Scheme.ofRestrict_app_self]
  simp only [Category.assoc]
  dsimp only [asIso_inv, Functor.op_obj, unop_op]
  rw [← Functor.map_comp_assoc, ← op_comp, eqToHom_trans, Scheme.eq_restrict_presheaf_map_eqToHom,
    Scheme.Hom.naturality_assoc, Scheme.inv_app_top, IsIso.hom_inv_id_assoc]
  simp only [eqToHom_op, eqToHom_map, Spec.map_eqToHom, eqToHom_unop,
    Scheme.Spec_map_presheaf_map_eqToHom, eqToHom_trans]
#align algebraic_geometry.is_affine_open.Spec_Γ_identity_hom_app_from_Spec AlgebraicGeometry.IsAffineOpen.SpecΓIdentity_hom_app_fromSpec

@[elementwise]
theorem fromSpec_app_self :
    hU.fromSpec.app U = (Scheme.ΓSpecIso Γ(X, U)).inv ≫
      (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op := by
  rw [← hU.SpecΓIdentity_hom_app_fromSpec, Iso.inv_hom_id_assoc]
#align algebraic_geometry.is_affine_open.from_Spec_app_eq AlgebraicGeometry.IsAffineOpen.fromSpec_app_self

theorem fromSpec_preimage_basicOpen' :
    hU.fromSpec ⁻¹ᵁ X.basicOpen f = (Spec Γ(X, U)).basicOpen ((Scheme.ΓSpecIso Γ(X, U)).inv f) := by
  rw [Scheme.preimage_basicOpen, hU.fromSpec_app_self]
  exact Scheme.basicOpen_res_eq _ _ (eqToHom hU.fromSpec_preimage_self).op
#align algebraic_geometry.is_affine_open.opens_map_from_Spec_basic_open AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen'

theorem fromSpec_preimage_basicOpen :
    hU.fromSpec ⁻¹ᵁ X.basicOpen f = PrimeSpectrum.basicOpen f := by
  rw [fromSpec_preimage_basicOpen', ← basicOpen_eq_of_affine]
#align algebraic_geometry.is_affine_open.from_Spec_map_basic_open AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen

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
#align algebraic_geometry.is_affine_open.basic_open_from_Spec_app AlgebraicGeometry.IsAffineOpen.basicOpen_fromSpec_app

theorem basicOpen :
    IsAffineOpen (X.basicOpen f) := by
  rw [← hU.fromSpec_image_basicOpen, Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion]
  convert isAffineOpen_opensRange
    (Spec.map (CommRingCat.ofHom <| algebraMap Γ(X, U) (Localization.Away f)))
  exact Opens.ext (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm
#align algebraic_geometry.is_affine_open.basic_open_is_affine AlgebraicGeometry.IsAffineOpen.basicOpen

theorem ιOpens_basicOpen_preimage (r : Γ(X, ⊤)):
    IsAffineOpen (Scheme.ιOpens (X.basicOpen r) ⁻¹ᵁ U) := by
  apply (Scheme.ιOpens (X.basicOpen r)).isAffineOpen_iff_of_isOpenImmersion.mp
  dsimp [Scheme.Hom.opensFunctor, LocallyRingedSpace.IsOpenImmersion.opensFunctor]
  rw [Opens.functor_obj_map_obj, Opens.openEmbedding_obj_top, inf_comm,
    ← Scheme.basicOpen_res _ _ (homOfLE le_top).op]
  exact hU.basicOpen _
#align algebraic_geometry.is_affine_open.map_restrict_basic_open AlgebraicGeometry.IsAffineOpen.ιOpens_basicOpen_preimage

theorem exists_basicOpen_le {V : Opens X} (x : V) (h : ↑x ∈ U) :
    ∃ f : Γ(X, U), X.basicOpen f ≤ V ∧ ↑x ∈ X.basicOpen f := by
  have : IsAffine _ := hU
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, h₁, h₂⟩ :=
    (isBasis_basicOpen (X ∣_ᵤ U)).exists_subset_of_mem_open (x.2 : ⟨x, h⟩ ∈ _)
      ((Opens.map U.inclusion).obj V).isOpen
  have :
    U.openEmbedding.isOpenMap.functor.obj ((X ∣_ᵤ U).basicOpen r) =
      X.basicOpen (X.presheaf.map (eqToHom U.openEmbedding_obj_top.symm).op r) := by
    refine (Scheme.image_basicOpen (X.ofRestrict U.openEmbedding) r).trans ?_
    rw [← Scheme.basicOpen_res_eq _ _ (eqToHom U.openEmbedding_obj_top).op,
      ← comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
      op_id, CategoryTheory.Functor.map_id, Scheme.Hom.invApp]
    erw [LocallyRingedSpace.IsOpenImmersion.ofRestrict_invApp]
    congr
  use X.presheaf.map (eqToHom U.openEmbedding_obj_top.symm).op r
  rw [← this]
  exact ⟨Set.image_subset_iff.mpr h₂, ⟨_, h⟩, h₁, rfl⟩
#align algebraic_geometry.is_affine_open.exists_basic_open_le AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le

/-- Given an affine open U and some `f : U`,
this is the canonical map `Γ(𝒪ₓ, D(f)) ⟶ Γ(Spec 𝒪ₓ(U), D(f))`
This is an isomorphism, as witnessed by an `IsIso` instance. -/
def basicOpenSectionsToAffine :
    Γ(X, X.basicOpen f) ⟶ Γ(Spec Γ(X, U), PrimeSpectrum.basicOpen f) :=
  hU.fromSpec.1.c.app (op <| X.basicOpen f) ≫
    (Spec Γ(X, U)).presheaf.map (eqToHom <| (hU.fromSpec_preimage_basicOpen f).symm).op
#align algebraic_geometry.basic_open_sections_to_affine AlgebraicGeometry.IsAffineOpen.basicOpenSectionsToAffine

instance basicOpenSectionsToAffine_isIso :
    IsIso (basicOpenSectionsToAffine hU f) := by
  delta basicOpenSectionsToAffine
  apply (config := { allowSynthFailures := true }) IsIso.comp_isIso
  apply PresheafedSpace.IsOpenImmersion.isIso_of_subset
  rw [hU.range_fromSpec]
  exact RingedSpace.basicOpen_le _ _

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
#align algebraic_geometry.is_localization_basic_open AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen

instance _root_.AlgebraicGeometry.isLocalization_away_of_isAffine
    [IsAffine X] (r : Γ(X, ⊤)) :
    IsLocalization.Away r Γ(X, X.basicOpen r) :=
  isLocalization_basicOpen (isAffineOpen_top X) r

lemma appLE_eq_away_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Opens Y} (hU : IsAffineOpen U)
    {V : Opens X} (hV : IsAffineOpen V) (e) (r : Γ(Y, U)) :
    letI := hU.isLocalization_basicOpen r
    letI := hV.isLocalization_basicOpen (f.appLE U V e r)
    f.appLE (Y.basicOpen r) (X.basicOpen (f.appLE U V e r))
      (by simpa [Scheme.Hom.appLE] using X.basicOpen_restrict _ _) =
        IsLocalization.Away.map _ _ (f.appLE U V e) r := by
  letI := hU.isLocalization_basicOpen r
  letI := hV.isLocalization_basicOpen (f.appLE U V e r)
  apply IsLocalization.ringHom_ext (.powers r)
  rw [← CommRingCat.comp_eq_ring_hom_comp, IsLocalization.Away.map, IsLocalization.map_comp,
    RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_eq_ring_hom_comp,
    Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem isLocalization_of_eq_basicOpen {V : Opens X} (i : V ⟶ U) (e : V = X.basicOpen f) :
    @IsLocalization.Away _ _ f Γ(X, V) _ (X.presheaf.map i.op).toAlgebra := by
  subst e; convert isLocalization_basicOpen hU f using 3
#align algebraic_geometry.is_localization_of_eq_basic_open AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen

instance _root_.AlgebraicGeometry.Γ_restrict_isLocalization
    (X : Scheme.{u}) [IsAffine X] (r : Scheme.Γ.obj (op X)) :
    IsLocalization.Away r (Scheme.Γ.obj (op (X ∣_ᵤ X.basicOpen r))) :=
  (isAffineOpen_top X).isLocalization_of_eq_basicOpen r _ (Opens.openEmbedding_obj_top _)
#align algebraic_geometry.Γ_restrict_is_localization AlgebraicGeometry.Γ_restrict_isLocalization

theorem basicOpen_basicOpen_is_basicOpen (g : Γ(X, X.basicOpen f)) :
    ∃ f' : Γ(X, U), X.basicOpen f' = X.basicOpen g := by
  have := isLocalization_basicOpen hU f
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.surj'' (Submonoid.powers f) g
  use f * x
  rw [Algebra.smul_def, Scheme.basicOpen_mul, Scheme.basicOpen_mul, RingHom.algebraMap_toAlgebra]
  rw [Scheme.basicOpen_res]
  refine (inf_eq_left.mpr ?_).symm
  -- Porting note: a little help is needed here
  convert inf_le_left (α := Opens X) using 1
  apply Scheme.basicOpen_of_isUnit
  apply
    Submonoid.leftInv_le_isUnit _
      (IsLocalization.toInvSubmonoid (Submonoid.powers f) (Γ(X, X.basicOpen f))
        _).prop
#align algebraic_geometry.basic_open_basic_open_is_basic_open AlgebraicGeometry.IsAffineOpen.basicOpen_basicOpen_is_basicOpen

theorem _root_.AlgebraicGeometry.exists_basicOpen_le_affine_inter
    {V : Opens X} (hV : IsAffineOpen V) (x : X) (hx : x ∈ U ⊓ V) :
    ∃ (f : Γ(X, U)) (g : Γ(X, V)), X.basicOpen f = X.basicOpen g ∧ x ∈ X.basicOpen f := by
  obtain ⟨f, hf₁, hf₂⟩ := hU.exists_basicOpen_le ⟨x, hx.2⟩ hx.1
  obtain ⟨g, hg₁, hg₂⟩ := hV.exists_basicOpen_le ⟨x, hf₂⟩ hx.2
  obtain ⟨f', hf'⟩ :=
    basicOpen_basicOpen_is_basicOpen hU f (X.presheaf.map (homOfLE hf₁ : _ ⟶ V).op g)
  replace hf' := (hf'.trans (RingedSpace.basicOpen_res _ _ _)).trans (inf_eq_right.mpr hg₁)
  exact ⟨f', g, hf', hf'.symm ▸ hg₂⟩
#align algebraic_geometry.exists_basic_open_le_affine_inter AlgebraicGeometry.exists_basicOpen_le_affine_inter

/-- The prime ideal of `𝒪ₓ(U)` corresponding to a point `x : U`. -/
noncomputable def primeIdealOf (x : U) :
    PrimeSpectrum Γ(X, U) :=
  ((@Scheme.isoSpec (X ∣_ᵤ U) hU).hom ≫
    Spec.map (X.presheaf.map (eqToHom U.openEmbedding_obj_top).op)).1.base x
#align algebraic_geometry.is_affine_open.prime_ideal_of AlgebraicGeometry.IsAffineOpen.primeIdealOf

theorem fromSpec_primeIdealOf (x : U) :
    hU.fromSpec.val.base (hU.primeIdealOf x) = x.1 := by
  dsimp only [IsAffineOpen.fromSpec, Subtype.coe_mk, IsAffineOpen.primeIdealOf]
  -- Porting note: in the porting note of `Scheme.comp_val_base`, it says that `elementwise` is
  -- unnecessary, indeed, the linter did not like it, so I just use `elementwise_of%` instead of
  -- adding the corresponding lemma in `Scheme.lean` file
  erw [← elementwise_of% Scheme.comp_val_base] -- now `erw` after #13170
  simp only [Scheme.restrict_carrier, Scheme.restrict_presheaf_obj, unop_op, Category.assoc, ←
    Spec.map_comp_assoc, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
    CategoryTheory.Functor.map_id, Spec.map_id, Category.id_comp, Iso.hom_inv_id_assoc,
    Scheme.ofRestrict_val_base]
  rfl -- `rfl` was not needed before #13170
#align algebraic_geometry.is_affine_open.from_Spec_prime_ideal_of AlgebraicGeometry.IsAffineOpen.fromSpec_primeIdealOf

theorem isLocalization_stalk' (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec.1.base y ∈ U) :
    @IsLocalization.AtPrime
      (R := Γ(X, U))
      (S := X.presheaf.stalk <| hU.fromSpec.1.base y) _ _
      ((TopCat.Presheaf.algebra_section_stalk X.presheaf _)) y.asIdeal _ := by
  apply
    (@IsLocalization.isLocalization_iff_of_ringEquiv (R := Γ(X, U))
      (S := X.presheaf.stalk (hU.fromSpec.1.base y)) _ y.asIdeal.primeCompl _
      (TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec.1.base y, hy⟩) _ _
      (asIso <| PresheafedSpace.stalkMap hU.fromSpec.1 y).commRingCatIsoToRingEquiv).mpr
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
#align algebraic_geometry.is_affine_open.is_localization_stalk AlgebraicGeometry.IsAffineOpen.isLocalization_stalk

/-- The basic open set of a section `f` on an affine open as an `X.affineOpens`. -/
@[simps]
def _root_.AlgebraicGeometry.Scheme.affineBasicOpen
    (X : Scheme) {U : X.affineOpens} (f : Γ(X, U)) : X.affineOpens :=
  ⟨X.basicOpen f, U.prop.basicOpen f⟩
#align algebraic_geometry.Scheme.affine_basic_open AlgebraicGeometry.Scheme.affineBasicOpen

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
#align algebraic_geometry.is_affine_open.basic_open_union_eq_self_iff AlgebraicGeometry.IsAffineOpen.basicOpen_union_eq_self_iff

theorem self_le_basicOpen_union_iff (s : Set Γ(X, U)) :
    (U ≤ ⨆ f : s, X.basicOpen f.1) ↔ Ideal.span s = ⊤ := by
  rw [← hU.basicOpen_union_eq_self_iff, @comm _ Eq]
  refine ⟨fun h => le_antisymm h ?_, le_of_eq⟩
  simp only [iSup_le_iff, SetCoe.forall]
  intro x _
  exact X.basicOpen_le x
#align algebraic_geometry.is_affine_open.self_le_basic_open_union_iff AlgebraicGeometry.IsAffineOpen.self_le_basicOpen_union_iff

end IsAffineOpen

/-- Let `P` be a predicate on the affine open sets of `X` satisfying
1. If `P` holds on `U`, then `P` holds on the basic open set of every section on `U`.
2. If `P` holds for a family of basic open sets covering `U`, then `P` holds for `U`.
3. There exists an affine open cover of `X` each satisfying `P`.

Then `P` holds for every affine open of `X`.

This is also known as the **Affine communication lemma** in [*The rising sea*][RisingSea]. -/
@[elab_as_elim]
theorem of_affine_open_cover {X : Scheme} {P : X.affineOpens → Prop}
    {ι} (U : ι → X.affineOpens) (iSup_U : (⨆ i, U i : Opens X) = ⊤)
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
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x.1 ∈ (⨆ i, U i : Opens X) from iSup_U ▸ trivial)
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
#align algebraic_geometry.of_affine_open_cover AlgebraicGeometry.of_affine_open_cover

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
alias IsAffineOpen.mapRestrictBasicOpen := IsAffineOpen.ιOpens_basicOpen_preimage

end AlgebraicGeometry
