/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.CategoryTheory.Adjunction.Opposites

/-!
# Subscheme associated to an ideal sheaf

We construct the subscheme associated to an ideal sheaf.

## Main definition
* `AlgebraicGeometry.Scheme.IdealSheafData.subscheme`: The subscheme associated to an ideal sheaf.
* `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι`: The inclusion from the subscheme.
* `AlgebraicGeometry.Scheme.Hom.image`: The scheme-theoretic image of a morphism.
* `AlgebraicGeometry.Scheme.kerAdjunction`:
  The adjunction between taking kernels and taking the associated subscheme.

## Note

Some instances are in `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion` and
`Mathlib/AlgebraicGeometry/Morphisms/Separated` because they need more API to prove.

-/

@[expose] public section

open CategoryTheory TopologicalSpace PrimeSpectrum Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open AffineZariskiSite

variable {X : Scheme.{u}}

variable (I : IdealSheafData X)

@[simps]
def quotientFunctorFunctor : X.IdealSheafData ⥤ X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj I :=
  { obj U := .of <| Γ(X, U.unop.1) ⧸ I.ideal U.unop
    map {U V} i := CommRingCat.ofHom (Ideal.quotientMap _ (X.presheaf.map (homOfLE _).op).hom
      (I.ideal_le_comap_ideal (toOpens_mono i.unop.le)))
    map_comp _ _ := by ext; simp [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl }
  map {I J} f := { app U := CommRingCat.ofHom (Ideal.Quotient.factor (f.le U.unop)) }

@[simps]
def quotientFunctorFunctorι :
    (Functor.const _).obj ((toOpensFunctor X).op ⋙ X.presheaf) ⟶ quotientFunctorFunctor where
  app I := { app U := CommRingCat.ofHom (Ideal.Quotient.mk _) }

abbrev quotientFunctor : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat := quotientFunctorFunctor.obj I

abbrev quotientFunctorι : (toOpensFunctor X).op ⋙ X.presheaf ⟶ I.quotientFunctor :=
  quotientFunctorFunctorι.app I

lemma coequifibered_quotientFunctorι : I.quotientFunctorι.Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U f ↦ ?_
  dsimp
  letI : Algebra (Γ(X, U.1) ⧸ I.ideal U) (Γ(X, X.basicOpen f) ⧸ I.ideal (U.basicOpen f)) :=
      (I.quotientFunctor.map (homOfLE (U.basicOpen_le f)).op).hom.toAlgebra
  letI := (X.presheaf.map (homOfLE (X := X.Opens) (X.basicOpen_le f)).op).hom.toAlgebra
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  simp only [IsLocalization.Away, ← Submonoid.map_powers]
  refine IsLocalization.of_surjective _ _ _ Ideal.Quotient.mk_surjective _
    Ideal.Quotient.mk_surjective ?_ ?_
  · simp [RingHom.algebraMap_toAlgebra, Ideal.quotientMap_comp_mk]
  · simp only [Ideal.mk_ker, RingHom.algebraMap_toAlgebra, I.map_ideal_basicOpen]; rfl

noncomputable
abbrev glueData : (directedCover X).RelativeGluingData :=
  relativeGluingData I.coequifibered_quotientFunctorι

instance (U : X.AffineZariskiSite) : IsPreimmersion (I.glueData.natTrans.app U) :=
  have : IsPreimmersion ((Functor.whiskerRight I.quotientFunctorι.rightOp Scheme.Spec).app U) :=
    .mk_SpecMap
      (isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).isEmbedding
      (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
  .comp _ _

lemma range_glueData_natTrans_app (U : X.AffineZariskiSite) :
    Set.range (I.glueData.natTrans.app U) =
      U.2.isoSpec.inv '' PrimeSpectrum.zeroLocus (I.ideal U) := by
  simp only [AffineZariskiSite.relativeGluingData, NatTrans.comp_app,
    Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  erw [range_comap_of_surjective]
  swap; · exact Ideal.Quotient.mk_surjective
  simp [quotientFunctor, quotientFunctorι, Ideal.mk_ker]

lemma range_glueData_natTrans_app_ι (U : X.AffineZariskiSite) :
    Set.range (I.glueData.natTrans.app U ≫ U.1.ι) = X.zeroLocus (U := U.1) (I.ideal U) ∩ U.1 := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_glueData_natTrans_app]
  dsimp
  rw [← Set.image_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, IsAffineOpen.isoSpec_inv_ι,
    IsAffineOpen.fromSpec_image_zeroLocus]

lemma range_glueDataObjι_ι_eq_support_inter (U : X.AffineZariskiSite) :
    Set.range (I.glueData.natTrans.app U ≫ U.1.ι) = ↑I.support ∩ ↑U.1 :=
  (I.range_glueData_natTrans_app_ι U).trans (I.coe_support_inter U).symm

@[reassoc]
lemma glueData_natTrans_app_ι (U : X.AffineZariskiSite) :
    I.glueData.natTrans.app U ≫ U.1.ι = Spec.map (I.quotientFunctorι.app _) ≫ U.2.fromSpec := by
  simp [relativeGluingData]

/-- The underlying space of `Spec (𝒪ₓ(U)/I(U))` is homeomorphic to its image in `X`. -/
noncomputable
def glueDataObjCarrierIso (U : X.affineOpens) :
    (I.glueData.functor.obj U).carrier ≅ TopCat.of ↑(X.zeroLocus (U := U) (I.ideal U) ∩ U) :=
  TopCat.isoOfHomeo ((I.glueData.natTrans.app U ≫ U.1.ι).isEmbedding.toHomeomorph.trans
    (.setCongr (I.range_glueData_natTrans_app_ι U)))

lemma opensRange_glueData_functor_map {V : X.AffineZariskiSite} (f : Γ(X, V.1)) :
      (I.glueData.functor.map (V.basicOpen_le f).hom).opensRange =
        (I.glueData.natTrans.app V) ⁻¹ᵁ (V.1.ι ⁻¹ᵁ X.basicOpen f) := by
  rw [opensRange_relativeGluingData_map, ← Scheme.Hom.comp_preimage, glueData_natTrans_app_ι,
    Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_basicOpen]
  rfl

/-- `Spec (𝒪ₓ(U)/I(U))`, the object to be glued into the closed subscheme. -/
@[deprecated "use `glueData`" (since := "2026-02-07")]
noncomputable abbrev glueDataObj (U : X.affineOpens) : Scheme := I.glueData.functor.obj U

/-- `Spec (𝒪ₓ(U)/I(U)) ⟶ Spec (𝒪ₓ(U)) = U`, the closed immersion into `U`. -/
@[deprecated "use `glueData`" (since := "2026-02-07")]
noncomputable
def glueDataObjι (U : X.affineOpens) : Spec (I.quotientFunctor.obj (.op U)) ⟶ U.1 :=
  I.glueData.natTrans.app U

@[deprecated (since := "2026-02-07")] alias range_glueDataObjι := range_glueData_natTrans_app

set_option linter.deprecated false in
/-- The open immersion `Spec Γ(𝒪ₓ/I, U) ⟶ Spec Γ(𝒪ₓ/I, V)` if `U ≤ V`. -/
@[deprecated "use `glueData`" (since := "2026-02-07")]
noncomputable
def glueDataObjMap {U V : X.AffineZariskiSite} (h : U ≤ V) : I.glueDataObj U ⟶ I.glueDataObj V :=
  I.glueData.functor.map h.hom

@[deprecated (since := "2026-02-07")]
alias opensRange_glueDataObjMap := opensRange_glueData_functor_map

@[deprecated (since := "2026-02-07")] alias range_glueDataObjι_ι := range_glueData_natTrans_app_ι

@[simp] lemma directedCover_trans {i j : (directedCover X).I₀} (f : i ⟶ j) :
    (directedCover X).trans f = X.homOfLE (((toOpensFunctor _).map f).le) := rfl

private lemma glueData_toBase_injective :
    Function.Injective I.glueData.toBase := by
  intro a b e
  obtain ⟨ia, a, rfl⟩ := I.glueData.cover.exists_eq a
  obtain ⟨ib, b, rfl⟩ := I.glueData.cover.exists_eq b
  have : (I.glueData.natTrans.app ia a).1 = (I.glueData.natTrans.app ib b).1 := by
    have : (I.glueData.cover.f ia ≫ I.glueData.toBase) a =
      (I.glueData.cover.f ib ≫ I.glueData.toBase) b := e
    simp only [Cover.RelativeGluingData.cover_X, Cover.RelativeGluingData.cover_f] at this
    rwa [I.glueData.ι_toBase, I.glueData.ι_toBase] at this
  obtain ⟨f, g, hfg, H⟩ := exists_basicOpen_le_affine_inter ia.2 ib.2
    (I.glueData.natTrans.app ia a).1
      ⟨(I.glueData.natTrans.app ia a).2, this ▸ (I.glueData.natTrans.app ib b).2⟩
  have hmem (W) (hW : W = ib.basicOpen g) :
      b ∈ Set.range (I.glueData.functor.map (homOfLE ⟨g, congr($hW.1).symm⟩)) := by
    subst hW
    refine (I.opensRange_glueData_functor_map _).ge ?_
    change (I.glueData.natTrans.app ib b).1 ∈ X.basicOpen g
    rwa [← this, ← hfg]
  obtain ⟨a, rfl⟩ := (I.opensRange_glueData_functor_map f).ge H
  obtain ⟨b, rfl⟩ := hmem (ia.basicOpen f) (Subtype.ext hfg)
  simp only [← Scheme.Hom.comp_apply, NatTrans.naturality, Cover.functorOfLocallyDirected,
    ← Scheme.Opens.ι_apply, Category.assoc, directedCover_trans,
    basicOpen_coe, toOpensFunctor_obj, homOfLE_ι] at this
  obtain rfl := (Scheme.Hom.isEmbedding _).injective this
  simp [← Scheme.Hom.comp_apply]

private lemma range_glueData_toBase :
    Set.range I.glueData.toBase = I.support := by
  refine subset_antisymm (Set.range_subset_iff.mpr fun x ↦ ?_) ?_
  · obtain ⟨ix, x, rfl⟩ := I.glueData.cover.exists_eq x
    rw [← Scheme.Hom.comp_apply, I.glueData.cover_f, I.glueData.ι_toBase]
    exact ((I.range_glueDataObjι_ι_eq_support_inter ix).le ⟨_, rfl⟩).1
  · intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    obtain ⟨y, rfl⟩ := (I.range_glueDataObjι_ι_eq_support_inter ⟨U, hU⟩).ge ⟨hx, hxU⟩
    rw [← I.glueData.ι_toBase]
    exact ⟨_, rfl⟩

private lemma range_glueData_ι (U : X.affineOpens) :
    Set.range (colimit.ι I.glueData.functor U).base =
      (I.glueData.toBase ⁻¹ᵁ U : Set I.glueData.glued) := by
  simp only [TopologicalSpace.Opens.map_coe]
  apply I.glueData_toBase_injective.image_injective
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
    I.glueData.ι_toBase]
  simp [-Scheme.Hom.comp_base, range_glueData_natTrans_app_ι, Set.image_preimage_eq_inter_range,
    range_glueData_toBase, ← coe_support_inter, Set.inter_comm (U.1 : Set X)]

/-- (Implementation) identifying `Spec(Γ(X, U)/I(U))` with its image in `Spec(𝒪ₓ/I)`. -/
private noncomputable
def glueDataObjIso (U : X.affineOpens) :
    I.glueData.functor.obj U ≅ I.glueData.toBase ⁻¹ᵁ U :=
  IsOpenImmersion.isoOfRangeEq (I.glueData.cover.f U) (Scheme.Opens.ι _) (by
    simpa using (I.glueData.preimage_toBase_eq_range_ι _).symm)

@[reassoc (attr := simp)]
private lemma glueDataObjIso_hom_ι (U : X.affineOpens) :
    (I.glueDataObjIso U).hom ≫ (I.glueData.toBase ⁻¹ᵁ U).ι = I.glueData.cover.f U :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private lemma glueDataObjIso_hom_restrict (U : X.affineOpens) :
    (I.glueDataObjIso U).hom ≫ I.glueData.toBase ∣_ ↑U = I.glueData.natTrans.app U := by
  rw [← cancel_mono U.1.ι]; simp [I.glueData.ι_toBase]

private instance : IsPreimmersion I.glueData.toBase := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsPreimmersion)
    _ (iSup_affineOpens_eq_top X)]
  intro U
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsPreimmersion (I.glueDataObjIso U).hom,
    glueDataObjIso_hom_restrict]
  infer_instance

private instance : QuasiCompact I.glueData.toBase :=
  ⟨fun _ _ ↦ (Topology.IsClosedEmbedding.isProperMap
    ⟨I.glueData.toBase.isEmbedding,
      I.range_glueData_toBase ▸ I.support.isClosed⟩).isCompact_preimage⟩

set_option backward.privateInPublic true in
/-- (Implementation) The underlying space of `Spec(𝒪ₓ/I)` is homeomorphic to the support of `I`. -/
private noncomputable
def gluedHomeo : I.glueData.glued ≃ₜ I.support :=
  I.glueData.toBase.isEmbedding.toHomeomorph.trans (.setCongr I.range_glueData_toBase)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The subscheme associated to an ideal sheaf. -/
noncomputable
def subscheme : Scheme :=
  I.glueData.glued.restrict
    (f := TopCat.ofHom (toContinuousMap I.gluedHomeo.symm))
    I.gluedHomeo.symm.isOpenEmbedding

set_option backward.privateInPublic true in
/-- (Implementation) The isomorphism between the subscheme and the glued scheme. -/
private noncomputable
def subschemeIso : I.subscheme ≅ I.glueData.glued :=
  letI F := I.glueData.glued.ofRestrict (f := TopCat.ofHom (toContinuousMap I.gluedHomeo.symm))
    I.gluedHomeo.symm.isOpenEmbedding
  have : Epi F.base := ConcreteCategory.epi_of_surjective _ I.gluedHomeo.symm.surjective
  letI := IsOpenImmersion.isIso F
  asIso F

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The inclusion from the subscheme associated to an ideal sheaf. -/
noncomputable
def subschemeι : I.subscheme ⟶ X :=
  (I.subschemeIso.hom ≫ I.glueData.toBase).copyBase Subtype.val <| by
    ext x
    change (I.gluedHomeo (I.gluedHomeo.symm x)).1 = x.1
    rw [I.gluedHomeo.apply_symm_apply]

lemma subschemeι_apply (x : I.subscheme) : I.subschemeι x = x.1 := rfl

private lemma subschemeι_def : I.subschemeι = I.subschemeIso.hom ≫ I.glueData.toBase :=
  Scheme.Hom.copyBase_eq _ _ _

/-- See `AlgebraicGeometry.Morphisms.ClosedImmersion` for the closed immersion version. -/
instance : IsPreimmersion I.subschemeι := by
  rw [subschemeι_def]
  infer_instance

instance : QuasiCompact I.subschemeι := by
  rw [subschemeι_def]
  infer_instance

@[simp]
lemma range_subschemeι : Set.range I.subschemeι = I.support := by
  simp [← range_glueData_toBase, I.subschemeι_def, Set.range_comp]

private lemma opensRange_glueData_ι_subschemeIso_inv (U : X.affineOpens) :
    (I.glueData.cover.f U ≫ I.subschemeIso.inv).opensRange = I.subschemeι ⁻¹ᵁ U := by
  ext1
  simp [Set.range_comp, I.range_glueData_ι, subschemeι_def, ← coe_homeoOfIso_symm,
    ← homeoOfIso_symm, ← Homeomorph.coe_symm_toEquiv, Equiv.image_symm_eq_preimage]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The subscheme associated to an ideal sheaf `I` is covered by `Spec(Γ(X, U)/I(U))`. -/
noncomputable
def subschemeCover : I.subscheme.AffineOpenCover where
  I₀ := X.affineOpens
  X U := .of <| Γ(X, U) ⧸ I.ideal U
  f U := I.glueData.cover.f U ≫ I.subschemeIso.inv
  idx x := (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).idx x.1
  covers x := by
    let U := (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).idx x.1
    obtain ⟨⟨y, hy : y ∈ U.1⟩, rfl : y = x.1⟩ :=
      (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).covers x.1
    exact (I.opensRange_glueData_ι_subschemeIso_inv U).ge hy

@[simp]
lemma opensRange_subschemeCover_map (U : X.affineOpens) :
    (I.subschemeCover.f U).opensRange = I.subschemeι ⁻¹ᵁ U :=
  I.opensRange_glueData_ι_subschemeIso_inv U

@[simp]
lemma subschemeCover_map_subschemeι (U : X.affineOpens) :
    I.subschemeCover.f U ≫ I.subschemeι = I.glueData.natTrans.app U ≫ U.1.ι := by
  simp [subschemeCover, subschemeι_def, I.glueData.ι_toBase]

/-- `Γ(𝒪ₓ/I, U) ≅ 𝒪ₓ(U)/I(U)`. -/
noncomputable
def subschemeObjIso (U : X.affineOpens) :
    Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) ≅ .of (Γ(X, U) ⧸ I.ideal U) :=
  I.subscheme.presheaf.mapIso (eqToIso (by simp)).op ≪≫
    (I.subschemeCover.f U).appIso _ ≪≫ Scheme.ΓSpecIso (.of (Γ(X, U) ⧸ I.ideal U))

lemma subschemeι_app (U : X.affineOpens) : I.subschemeι.app U =
    CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)) ≫
    (I.subschemeObjIso U).inv := by
  have := I.subschemeCover_map_subschemeι U
  simp only [glueData_natTrans_app_ι] at this
  replace this := Scheme.Hom.congr_app this U
  simp only [Hom.comp_base, TopologicalSpace.Opens.map_comp_obj, Hom.comp_app,
    IsAffineOpen.fromSpec_app_self, eqToHom_op, Category.assoc, Hom.naturality_assoc,
    TopologicalSpace.Opens.map_top, ← ΓSpecIso_inv_naturality_assoc] at this
  simp_rw [← Category.assoc, ← IsIso.comp_inv_eq, quotientFunctorι, quotientFunctorFunctorι] at this
  rw [← this, Iso.eq_comp_inv]
  simp [← Functor.map_inv, Scheme.Hom.app_eq_appLE, subschemeObjIso,
    - Scheme.Hom.comp_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appIso_hom',
    Scheme.Hom.appLE_comp_appLE_assoc]
  rfl

lemma subschemeι_app_surjective (U : X.affineOpens) :
    Function.Surjective (I.subschemeι.app U) := by
  rw [I.subschemeι_app U]
  exact (I.subschemeObjIso U).commRingCatIsoToRingEquiv.symm.surjective.comp
    Ideal.Quotient.mk_surjective

lemma ker_subschemeι_app (U : X.affineOpens) :
    RingHom.ker (I.subschemeι.app U).hom = I.ideal U := by
  rw [subschemeι_app]
  let e : CommRingCat.of (Γ(X, U) ⧸ I.ideal U) ≅ Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) :=
    (Scheme.ΓSpecIso _).symm ≪≫ ((I.subschemeCover.f U).appIso _).symm ≪≫
      I.subscheme.presheaf.mapIso (eqToIso (by simp)).op
  change RingHom.ker (e.commRingCatIsoToRingEquiv.toRingHom.comp
    (Ideal.Quotient.mk (I.ideal U))) = _
  rw [RingHom.ker_equiv_comp, Ideal.mk_ker]

@[simp]
lemma ker_subschemeι : I.subschemeι.ker = I := by
  ext; simp [ker_subschemeι_app]

instance : IsEmpty (⊤ : X.IdealSheafData).subscheme := by
  rw [← (subschemeι _).ker_eq_top_iff_isEmpty, ker_subschemeι]

/-- Given `I ≤ J`, this is the map `Spec(Γ(X, U)/J(U)) ⟶ Spec(Γ(X, U)/I(U))`. -/
@[deprecated quotientFunctorFunctor (since := "2026-02-07")]
noncomputable
def glueDataObjHom {I J : IdealSheafData X} (h : I ≤ J) (U) :
    J.glueData.functor.obj U ⟶ I.glueData.functor.obj U :=
  Spec.map <| (quotientFunctorFunctor.map h.hom).app (.op U)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The inclusion of ideal sheaf induces an inclusion of subschemes -/
noncomputable
def inclusion {I J : IdealSheafData X} (h : I ≤ J) :
    J.subscheme ⟶ I.subscheme := by
  refine J.subschemeIso.hom ≫ colimMap ?_ ≫ I.subschemeIso.inv
  exact Functor.whiskerRight (quotientFunctorFunctor.map h.hom).rightOp Scheme.Spec

@[reassoc (attr := simp)]
lemma subSchemeCover_map_inclusion {I J : IdealSheafData X} (h : I ≤ J) (U) :
    J.subschemeCover.f U ≫ inclusion h =
    Spec.map ((quotientFunctorFunctor.map h.hom).app (.op U)) ≫ I.subschemeCover.f U := by
  simp [subschemeCover, inclusion]

@[reassoc (attr := simp)]
lemma inclusion_subschemeι {I J : IdealSheafData X} (h : I ≤ J) :
    inclusion h ≫ I.subschemeι = J.subschemeι :=
  J.subschemeCover.openCover.hom_ext _ _ fun _ ↦ by
    simp [relativeGluingData, ← Spec.map_comp_assoc, -Spec.map_comp]; rfl

@[simp, reassoc]
lemma inclusion_id (I : IdealSheafData X) :
    inclusion le_rfl = 𝟙 I.subscheme :=
  I.subschemeCover.openCover.hom_ext _ _ fun _ ↦ by simp

@[reassoc (attr := simp)]
lemma inclusion_comp {I J K : IdealSheafData X} (h₁ : I ≤ J) (h₂ : J ≤ K) :
    inclusion h₂ ≫ inclusion h₁ = inclusion (h₁.trans h₂) :=
  K.subschemeCover.openCover.hom_ext _ _ fun _ ↦ by
    simp [← Spec.map_comp_assoc, -Spec.map_comp, quotientFunctorFunctor]; congr; aesop

/-- The functor taking an ideal sheaf to its associated subscheme. -/
@[simps]
noncomputable
def subschemeFunctor (Y : Scheme.{u}) : (IdealSheafData Y)ᵒᵖ ⥤ Over Y where
  obj I := .mk I.unop.subschemeι
  map {I J} h := Over.homMk (IdealSheafData.inclusion h.unop.le)

end IdealSheafData

noncomputable section image

open Limits

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.affineOpens)

/-- The scheme-theoretic image of a morphism. -/
abbrev Hom.image : Scheme.{u} := f.ker.subscheme

/-- The embedding from the scheme-theoretic image to the codomain. -/
abbrev Hom.imageι : f.image ⟶ Y := f.ker.subschemeι

lemma ideal_ker_le_ker_ΓSpecIso_inv_comp :
    f.ker.ideal U ≤ RingHom.ker ((ΓSpecIso Γ(Y, ↑U)).inv ≫
      (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).appTop).hom := by
  let e : Γ(X, f ⁻¹ᵁ ↑U) ≅ Γ(Limits.pullback (C := Scheme) f U.1.ι, ⊤) :=
    X.presheaf.mapIso (eqToIso (by simp [Scheme.Hom.opensRange_pullbackFst])).op
      ≪≫ (Limits.pullback.fst (C := Scheme) f U.1.ι).appIso ⊤
  have he : f.app U ≫ e.hom =
      (ΓSpecIso Γ(Y, ↑U)).inv ≫ (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).appTop := by
    rw [← (Iso.inv_comp_eq _).mpr U.2.isoSpec_inv_appTop, Category.assoc, Iso.eq_inv_comp]
    simp only [Opens.topIso_hom, eqToHom_op, Hom.app_eq_appLE, Iso.trans_hom, Functor.mapIso_hom,
      Iso.op_hom, eqToIso.hom, Hom.appIso_hom, Hom.appLE_map, Hom.map_appLE, Hom.appLE_comp_appLE,
      Opens.map_top, e, pullback.condition, IsAffineOpen.toSpecΓ_isoSpec_inv, Category.assoc]
    rw [Hom.comp_appLE, Opens.ι_app]
    exact Hom.map_appLE _ _ (homOfLE le_top).op
  rw [← he]
  refine (IdealSheafData.ideal_ofIdeals_le _ _).trans_eq
    (RingHom.ker_equiv_comp _ e.commRingCatIsoToRingEquiv).symm

set_option backward.privateInPublic true in
private noncomputable
def Hom.toImageAux : X ⟶ f.image :=
  Cover.glueMorphisms ((Y.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top Y)).pullback₁ f)
    (fun U ↦ (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).liftQuotient _
      (by exact ideal_ker_le_ker_ΓSpecIso_inv_comp f U) ≫ f.ker.subschemeCover.f U) (by
    intro U V
    rw [← cancel_mono f.imageι]
    simp [AffineZariskiSite.relativeGluingData, Scheme.Hom.liftQuotient_comp_assoc,
      ← pullback.condition, ← pullback.condition_assoc])

set_option backward.privateInPublic true in
private lemma Hom.toImageAux_spec :
    f.toImageAux ≫ f.imageι = f := by
  apply Cover.hom_ext ((Y.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top Y)).pullback₁ f)
  intro U
  simp only [Hom.toImageAux, Cover.ι_glueMorphisms_assoc]
  simp [AffineZariskiSite.relativeGluingData, liftQuotient_comp_assoc, pullback.condition]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The morphism from the domain to the scheme-theoretic image. -/
noncomputable
def Hom.toImage : X ⟶ f.image :=
  f.toImageAux.copyBase (fun x ↦ ⟨f x, f.range_subset_ker_support ⟨x, rfl⟩⟩)
    (funext fun x ↦ Subtype.ext congr($f.toImageAux_spec x))

@[reassoc (attr := simp)]
lemma Hom.toImage_imageι :
    f.toImage ≫ f.imageι = f := by
  convert f.toImageAux_spec using 2
  exact Scheme.Hom.copyBase_eq _ _ _

instance [QuasiCompact f] : IsDominant f.toImage where
  denseRange := by
    rw [denseRange_iff_closure_range, f.imageι.isEmbedding.closure_eq_preimage_closure_image,
      ← Set.univ_subset_iff, ← Set.image_subset_iff, Set.image_univ,
      IdealSheafData.range_subschemeι, Hom.support_ker, ← Set.range_comp,
      ← TopCat.coe_comp, ← Scheme.Hom.comp_base, f.toImage_imageι]

instance [QuasiCompact f] : QuasiCompact f.toImage :=
  have : QuasiCompact (f.toImage ≫ f.imageι) := by simpa
  .of_comp _ f.imageι

instance : IsIso (IdealSheafData.subschemeι ⊥ : _ ⟶ X) :=
  ⟨Scheme.Hom.toImage (𝟙 X) ≫ IdealSheafData.inclusion bot_le,
    by simp [← cancel_mono (IdealSheafData.subschemeι _)], by simp⟩

lemma Hom.toImage_app :
    f.toImage.app (f.imageι ⁻¹ᵁ U) =
      (f.ker.subschemeObjIso U).hom ≫ CommRingCat.ofHom
        (Ideal.Quotient.lift _ (f.app U.1).hom (IdealSheafData.ideal_ofIdeals_le _ _)) := by
  have := ConcreteCategory.epi_of_surjective _ (f.ker.subschemeι_app_surjective U)
  rw [← cancel_epi (f.ker.subschemeι.app U), ← Scheme.Hom.comp_app,
    Scheme.Hom.congr_app f.toImage_imageι, f.ker.subschemeι_app,
    ← IsIso.eq_comp_inv, ← Functor.map_inv]
  simp only [Hom.comp_base, Opens.map_comp_obj, Category.assoc,
    Iso.inv_hom_id_assoc, eqToHom_op, inv_eqToHom]
  rw [← reassoc_of% CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk, CommRingCat.ofHom_hom,
    eqToHom_refl, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

lemma Hom.toImage_app_injective [QuasiCompact f] :
    Function.Injective (f.toImage.app (f.imageι ⁻¹ᵁ U)) := by
  simp only [f.toImage_app U, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp]
  exact (RingHom.lift_injective_of_ker_le_ideal _ _ (by simp)).comp
    (f.ker.subschemeObjIso U).commRingCatIsoToRingEquiv.injective

lemma Hom.stalkFunctor_toImage_injective [QuasiCompact f] (x) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor _ x).map f.toImage.c) := by
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis
    (hB := (Y.isBasis_affineOpens.of_isInducing f.imageι.isEmbedding.isInducing))
  rintro _ ⟨U, hU, rfl⟩
  exact f.toImage_app_injective ⟨U, hU⟩

open IdealSheafData in
/-- The adjunction between `Y.IdealSheafData` and `(Over Y)ᵒᵖ` given by taking kernels. -/
@[simps]
noncomputable
def kerAdjunction (Y : Scheme.{u}) : (subschemeFunctor Y).rightOp ⊣ Y.kerFunctor where
  unit.app I := eqToHom (by simp)
  counit.app f := (Over.homMk f.unop.hom.toImage f.unop.hom.toImage_imageι).op
  counit.naturality _ _ _ := Quiver.Hom.unop_inj (by ext1; simp [← cancel_mono (subschemeι _)])
  left_triangle_components I := Quiver.Hom.unop_inj (by ext1; simp [← cancel_mono (subschemeι _)])

instance : (IdealSheafData.subschemeFunctor Y).Full :=
  have : IsIso Y.kerAdjunction.rightOp.counit := by
    simp [NatTrans.isIso_iff_isIso_app, CategoryTheory.instIsIsoEqToHom]
  Y.kerAdjunction.rightOp.fullyFaithfulROfIsIsoCounit.full

end image

end Scheme

end AlgebraicGeometry
