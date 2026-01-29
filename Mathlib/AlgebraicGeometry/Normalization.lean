/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.Tactic.DepRewrite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# Relative Normalization

Given a qcqs morphism `f : X ⟶ Y`, we define the relative normalization `f.normalization`,
along with the maps that `f` factor into:
- `f.toNormalization : X ⟶ f.normalization`: a dominant morphism
- `f.fromNormalization : f.normalization ⟶ Y`: an integral morphism

It satisfies the universal property:
For any factorization `X ⟶ T ⟶ Y` with `T ⟶ Y` integral,
the map `X ⟶ T` factors through `f.normalization` uniquely.
The factorization map is `AlgebraicGeometry.Scheme.Hom.normalizationDesc`, and the uniqueness result
is `AlgebraicGeometry.Scheme.Hom.normalization.hom_ext`.

-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open AffineZariskiSite

/-- Given a morphism `f : X ⟶ Y`, this is the presheaf of integral closure of `Y` in `X`. -/
def normalizationDiagram : Y.Opensᵒᵖ ⥤ CommRingCat where
  obj U :=
    letI := (f.app U.unop).hom.toAlgebra
    .of (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop))
  map {V U} i :=
    CommRingCat.ofHom ((X.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op).hom.restrict
      _ _ fun x hx ↦ by
      obtain ⟨U, rfl⟩ := Opposite.op_surjective U
      obtain ⟨V, rfl⟩ := Opposite.op_surjective V
      algebraize [(f.app U).hom, (f.app V).hom, (Y.presheaf.map i).hom,
        (X.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op).hom,
        (f.appLE V (f ⁻¹ᵁ U) (f.preimage_mono i.unop.le)).hom]
      have : IsScalarTower Γ(Y, V) Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := .of_algebraMap_eq' <| by
        simp [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]; rfl
      have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
      exact (hx.map (IsScalarTower.toAlgHom Γ(Y, V) _ Γ(X, f ⁻¹ᵁ U))).tower_top)
  map_id U := by simp; rfl
  map_comp i j := by
    simp only [← CommRingCat.ofHom_comp]
    rw [← homOfLE_comp (f.preimage_mono j.unop.le) (f.preimage_mono i.unop.le), op_comp]
    simp_rw [X.presheaf.map_comp]
    rfl

/-- The inclusion from the structure presheaf of `Y` to the integral closure of `Y` in `X`. -/
def normalizationDiagramMap : Y.presheaf ⟶ f.normalizationDiagram where
  app U :=
    letI := (f.app U.unop).hom.toAlgebra
    CommRingCat.ofHom (algebraMap Γ(Y, U.unop) (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop)))
  naturality {U V} i := by ext x; exact Subtype.ext congr($(f.naturality i) x)

variable [QuasiCompact f] [QuasiSeparated f]

lemma preservesLocalization_normalizationDiagramMap :
    PreservesLocalization _ ((toOpensFunctor Y).op.whiskerLeft f.normalizationDiagramMap) := by
  intro U r
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  let : Algebra Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (f.app (U.basicOpen r).1).hom.toAlgebra
  let : Algebra (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
      (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) :=
    ((normalizationDiagram f).map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra
  let inst : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have : IsLocalization.Away r Γ(Y, Y.basicOpen r) :=
    U.2.isLocalization_basicOpen _
  have : IsLocalization.Away ((algebraMap ↑Γ(Y, U.1) ↑Γ(X, f ⁻¹ᵁ U.1)) r)
      Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
    let : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, X.basicOpen (f.app _ r)) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
    dsimp [inst]
    rw! (castMode := .all) [f.preimage_basicOpen r]
    exact isLocalization_basicOpen_of_qcqs (f.isCompact_preimage U.2.isCompact)
        (f.isQuasiSeparated_preimage U.2.isQuasiSeparated) (f.app _ r)
  change IsLocalization.Away ((algebraMap Γ(Y, U.1) (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))) r)
    (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r))
  letI : Algebra ↑Γ(Y, U.1) ↑Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (f.appLE _ _ (f.preimage_mono (Y.basicOpen_le _))).hom.toAlgebra
  have : IsScalarTower Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U.1) Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    .of_algebraMap_eq' <| by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.map_appLE, AffineZariskiSite.basicOpen]
  have : IsScalarTower (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
    (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r))
    Γ(X, f ⁻¹ᵁ Y.basicOpen r) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U.1) (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
    (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) := .of_algebraMap_eq' rfl
  exact IsLocalization.Away.integralClosure r

instance : ((((toOpensFunctor Y).op ⋙ f.normalizationDiagram).rightOp ⋙ Scheme.Spec) ⋙
      Scheme.forget).IsLocallyDirected :=
  f.preservesLocalization_normalizationDiagramMap.isLocallyDirected

instance {U V} (i : U ⟶ V) :
    IsOpenImmersion (((((toOpensFunctor Y).op ⋙
      f.normalizationDiagram).rightOp ⋙ Scheme.Spec)).map i) :=
  f.preservesLocalization_normalizationDiagramMap.isOpenImmersion _ _ _

/-- Given `f : X ⟶ Y`, `f.normalization` is the relative normalization of `Y` in `X`. -/
@[stacks 035H]
def normalization : Scheme :=
  colimit (((toOpensFunctor Y).op ⋙ f.normalizationDiagram).rightOp ⋙ Scheme.Spec)

/-- This is the open cover of `f.normalization` by `Spec` of integral closures of `Γ(Y, U)`
in `Γ(X, f ⁻¹ U)` where `U` ranges over all affine opens. -/
def normalizationOpenCover : f.normalization.OpenCover :=
  Scheme.IsLocallyDirected.openCover _

/-- The dominant morphism into the relative normalization. -/
def toNormalization : X ⟶ f.normalization :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover Y).pullback₁ f)
    (fun U ↦ letI := (f.app U.1).hom.toAlgebra
      (pullbackRestrictIsoRestrict f _).hom ≫
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom <| integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)
      |>.val.toRingHom) ≫ f.normalizationOpenCover.f U) fun {U V : Y.AffineZariskiSite} i ↦ by
  have : (pullbackRestrictIsoRestrict f U.1).inv ≫
      Cover.trans ((directedCover Y).pullback₁ f) i ≫
      (pullbackRestrictIsoRestrict f V.1).hom = X.homOfLE
        (f.preimage_mono (toOpens_mono i.1.1)) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp [Cover.trans, Cover.locallyDirectedPullbackCover]
  rw [← Iso.inv_comp_eq, reassoc_of% this, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Spec.map_comp_assoc]
  dsimp [normalizationOpenCover]
  rw [← colimit.w (((toOpensFunctor Y).op ⋙
    normalizationDiagram f).rightOp ⋙ Scheme.Spec) i]
  dsimp
  rw [← Spec.map_comp_assoc]
  rfl

@[reassoc]
lemma ι_toNormalization (U : Y.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    (f ⁻¹ᵁ U.1).ι ≫ f.toNormalization = (f ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom <| integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) |>.val.toRingHom) ≫
        f.normalizationOpenCover.f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom, ← Category.assoc]
  trans ((directedCover Y).pullback₁ f).f U ≫ f.toNormalization
  · congr 1; simp
  delta toNormalization
  generalize_proofs _ _ _ _ H
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected _ _ H _

/-- The morphism from the relative normalization to itself. This map is integral. -/
def fromNormalization : f.normalization ⟶ Y :=
  colimit.desc _
  { pt := _
    ι := Functor.whiskerRight ((toOpensFunctor Y).op.whiskerLeft
      f.normalizationDiagramMap).rightOp Scheme.Spec ≫ (cocone Y).ι }

@[reassoc]
lemma ι_fromNormalization (U : Y.affineOpens) :
    f.normalizationOpenCover.f U ≫ f.fromNormalization =
      Spec.map (f.normalizationDiagramMap.app (.op U.1)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

lemma fromNormalization_preimage (U : Y.affineOpens) :
    f.fromNormalization ⁻¹ᵁ U = (f.normalizationOpenCover.f U).opensRange :=
  f.preservesLocalization_normalizationDiagramMap.colimitDesc_preimage _ _ _

@[reassoc (attr := simp)]
lemma toNormalization_fromNormalization :
    f.toNormalization ≫ f.fromNormalization = f := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.1)) _ _ fun U ↦ ?_
  refine (f.ι_toNormalization_assoc _ _).trans ?_
  rw [f.ι_fromNormalization, ← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app _) ≫ U.2.fromSpec = (f ⁻¹ᵁ U.1).ι ≫ _
  simp

instance : IsIntegralHom f.fromNormalization := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsIntegralHom) _
    (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq (f.fromNormalization ⁻¹ᵁ U).ι (f.normalizationOpenCover.f U)
      (by simpa using congr($(f.fromNormalization_preimage U).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsIntegralHom e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @IsIntegralHom _ U.2.isoSpec.hom]
  have : (f.normalizationDiagramMap.app (.op U)).hom.IsIntegral := by
    letI := (f.app U).hom.toAlgebra
    change (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))).IsIntegral
    exact algebraMap_isIntegral_iff.mpr inferInstance
  convert IsIntegralHom.SpecMap_iff.mpr this
  rw [← cancel_mono U.2.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, ι_fromNormalization]

lemma toNormalization_app_preimage (U : Y.affineOpens) :
    let := (f.app U.1).hom.toAlgebra
    f.toNormalization.app (f.fromNormalization ⁻¹ᵁ ↑U) =
      f.normalization.presheaf.map (eqToHom (by simp [fromNormalization_preimage])).op ≫
      ((f.normalizationOpenCover.f U).appIso _).hom ≫
      (Scheme.ΓSpecIso _).hom ≫
      CommRingCat.ofHom (integralClosure ↑Γ(Y, ↑U) ↑Γ(X, f ⁻¹ᵁ ↑U)).val.toRingHom ≫
      X.presheaf.map (eqToHom (by simp [← Scheme.Hom.comp_preimage])).op := by
  have H : f.toNormalization ⁻¹ᵁ f.fromNormalization ⁻¹ᵁ U =
      (f ⁻¹ᵁ U).ι ''ᵁ (((f ⁻¹ᵁ U).ι ≫ f.toNormalization) ⁻¹ᵁ f.fromNormalization ⁻¹ᵁ U) := by
    simp [← Scheme.Hom.comp_preimage]
  convert congr($(Scheme.Hom.congr_app (f.ι_toNormalization U) (f.fromNormalization ⁻¹ᵁ U)) ≫
    X.presheaf.map (eqToHom H).op) using 1
  · simp [Hom.app_eq_appLE]
  dsimp
  simp only [eqToHom_op, Hom.appIso_hom, Category.assoc, Scheme.Hom.naturality_assoc, eqToHom_unop,
    ← Functor.map_comp_assoc, eqToHom_map (TopologicalSpace.Opens.map _), eqToHom_trans]
  congr 1
  rw [← IsIso.eq_inv_comp, ← Functor.map_inv, inv_eqToHom]
  simp [← Functor.map_comp, Scheme.Opens.toSpecΓ_appTop,
    ΓSpecIso_naturality_assoc (CommRingCat.ofHom _)]
  rfl

@[stacks 03GP]
instance [IsIntegralHom f] : IsIso f.toNormalization := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
    f.normalizationOpenCover).mpr fun U ↦ ?_
  let e := IsOpenImmersion.isoOfRangeEq (pullback.fst f.toNormalization
    (f.normalizationOpenCover.f U)) (f ⁻¹ᵁ U.1).ι (by simp [← Hom.coe_opensRange,
      Hom.opensRange_pullbackFst, ← f.fromNormalization_preimage, ← Scheme.Hom.comp_preimage])
  rw [← MorphismProperty.cancel_left_of_respectsIso (.isomorphisms _)
    (e ≪≫ (U.2.preimage f).isoSpec).inv]
  letI := (f.app U.1).hom.toAlgebra
  convert_to IsIso (Spec.map (CommRingCat.ofHom
      (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)).val.toRingHom))
  · rw [← cancel_mono (f.normalizationOpenCover.f U), ← cancel_epi (U.2.preimage f).isoSpec.hom]
    simp [e, -Iso.cancel_iso_hom_left, IsAffineOpen.isoSpec_hom,
      Hom.ι_toNormalization]
  have : integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) = ⊤ := by
    rw [integralClosure_eq_top_iff, ← algebraMap_isIntegral_iff, RingHom.algebraMap_toAlgebra]
    exact IsIntegralHom.isIntegral_app _ _ U.2
  rw [this]
  exact inferInstanceAs (IsIso (Scheme.Spec.mapIso (Subalgebra.topEquiv
    (R := Γ(Y, U.1)) (A := ↑Γ(X, f ⁻¹ᵁ U.1))).toCommRingCatIso.op).hom)

instance [IsAffineHom f] : IsAffineHom f.toNormalization := by
  apply MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated) _ f.fromNormalization
  · infer_instance
  · rw [Hom.toNormalization_fromNormalization]
    infer_instance

instance : QuasiCompact f.toNormalization := by
  apply MorphismProperty.of_postcomp (W := @QuasiCompact)
      (W' := @QuasiSeparated) _ f.fromNormalization
  · infer_instance
  · rw [Hom.toNormalization_fromNormalization]
    infer_instance

instance : QuasiSeparated f.toNormalization := by
  suffices QuasiSeparated (Hom.toNormalization f ≫ Hom.fromNormalization f) from
    .of_comp _ f.fromNormalization
  rw [Hom.toNormalization_fromNormalization]
  infer_instance

@[simp]
lemma ker_toNormalization : f.toNormalization.ker = ⊥ := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.fromNormalization ⁻¹ᵁ U.1, U.2.preimage _⟩)
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top _) _) fun U ↦ ?_
  simp only [ker_apply, IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [← RingHom.injective_iff_ker_eq_bot,
    ← ConcreteCategory.mono_iff_injective_of_preservesPullback, ← MorphismProperty.monomorphisms]
  simp only [toNormalization_app_preimage, Functor.rightOp_obj, Functor.comp_obj, Functor.op_obj,
    eqToHom_op, AlgHom.toRingHom_eq_coe, MorphismProperty.cancel_left_of_respectsIso,
    MorphismProperty.cancel_right_of_respectsIso]
  rw [MorphismProperty.monomorphisms, @ConcreteCategory.mono_iff_injective_of_preservesPullback]
  exact Subtype.val_injective

instance : IsDominant f.toNormalization := by
  have := congr(($(f.ker_toNormalization).support : Set f.normalization))
  rw [IdealSheafData.support_bot, Scheme.Hom.support_ker, TopologicalSpace.Closeds.coe_top] at this
  exact ⟨dense_iff_closure_eq.mpr this⟩

@[stacks 0AXN]
instance [IsReduced X] : IsReduced f.normalization :=
  have (i : _) : IsReduced ((normalizationOpenCover f).X i) := by
    have : _root_.IsReduced ((normalizationDiagram f).obj (.op i.1)) :=
      let := (f.app i.1).hom.toAlgebra
      isReduced_of_injective (Subalgebra.val _) Subtype.val_injective
    dsimp [normalizationOpenCover]
    infer_instance
  .of_openCover _ f.normalizationOpenCover

instance [IsIntegral X] : IsIntegral f.normalization :=
  have : IrreducibleSpace f.normalization := by
    rw [irreducibleSpace_def]
    convert ((IrreducibleSpace.isIrreducible_univ X).image _
      f.toNormalization.continuous.continuousOn).closure
    simpa using f.toNormalization.denseRange.closure_range.symm
  isIntegral_of_irreducibleSpace_of_isReduced _

section UniversalProperty

variable {T : Scheme.{u}} (f₁ : X ⟶ T) (f₂ : T ⟶ Y) [IsIntegralHom f₂]

/-- Given an qcqs morphism `f : X ⟶ Y`, which factors into `X ⟶ T ⟶ Y` with `T ⟶ Y` integral,
the map `X ⟶ T` factors through `f.normalization` uniquely.
(See `normalization.hom_ext` for the uniqueness result) -/
noncomputable
def normalizationDesc (H : f = f₁ ≫ f₂) : f.normalization ⟶ T := by
  refine colimit.desc _
    { pt := _
      ι.app U := Spec.map (CommRingCat.ofHom ((f₁.appLE _ _ (by simp [H])).hom.codRestrict _
        fun x ↦ ?_)) ≫ (U.2.preimage f₂).fromSpec,
      ι.naturality := ?_ }
  · algebraize [(f.app U.1).hom, (f₂.app U.1).hom,
      (f₁.appLE (f₂ ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) (by simp [H])).hom]
    have : IsScalarTower Γ(Y, U.1) Γ(T, f₂ ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ U.1) := .of_algebraMap_eq' <| by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        Hom.app_eq_appLE, Hom.appLE_comp_appLE, ← H]
    exact .algebraMap (R := Γ(Y, U.1)) (B := Γ(X, f ⁻¹ᵁ U.1)) (f₂.isIntegral_app U.1 U.2 x)
  · intros U V i
    dsimp
    rw [Category.comp_id, ← Spec.map_comp_assoc, ← (V.2.preimage f₂).map_fromSpec (U.2.preimage f₂)
      (homOfLE (f₂.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.le))).op,
      ← Spec.map_comp_assoc]
    congr 2
    ext i
    apply Subtype.ext
    dsimp [normalizationDiagram]
    simp only [← CommRingCat.comp_apply, appLE_map, map_appLE]

@[reassoc (attr := simp)]
lemma toNormalization_normalizationDesc (H : f = f₁ ≫ f₂) :
    f.toNormalization ≫ f.normalizationDesc f₁ f₂ H = f₁ := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.hom)) _ _ fun U ↦ ?_
  letI := (f.app U.1).hom.toAlgebra
  refine (Scheme.Hom.ι_toNormalization_assoc ..).trans ?_
  dsimp [normalizationOpenCover, normalizationDesc]
  simp only [colimit.ι_desc, ← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f₁.appLE (f₂ ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) (by simp [H])) ≫
    (U.2.preimage f₂).fromSpec = (f ⁻¹ᵁ U.1).ι ≫ f₁
  simp

@[reassoc (attr := simp)]
lemma normalizationDesc_comp (H : f = f₁ ≫ f₂) :
    f.normalizationDesc f₁ f₂ H ≫ f₂ = f.fromNormalization := by
  refine colimit.hom_ext fun U ↦ ?_
  dsimp [normalizationDesc, fromNormalization]
  rw [colimit.ι_desc_assoc, colimit.ι_desc, Category.assoc,
    ← IsAffineOpen.SpecMap_appLE_fromSpec _ U.2 _ le_rfl, ← Spec.map_comp_assoc]
  congr 2
  ext i
  dsimp [normalizationDiagram, normalizationDiagramMap, RingHom.algebraMap_toAlgebra]
  rw [← CommRingCat.comp_apply, Hom.appLE_comp_appLE, app_eq_appLE]
  simp_rw [H]

instance (H : f = f₁ ≫ f₂) : IsIntegralHom (f.normalizationDesc f₁ f₂ H) := by
  have : IsIntegralHom (f.normalizationDesc f₁ f₂ H ≫ f₂) := by
    rw [f.normalizationDesc_comp]; infer_instance
  exact .of_comp _ f₂

/-- The uniqueness part of the universal property for relative normalization.
Suppose `f : X ⟶ Y` is qcqs and factors into `X ⟶ T ⟶ Y` with `T ⟶ Y` affine, then
there is at most one map `f.normalization ⟶ T` that commutes with them. -/
lemma normalization.hom_ext (f₁ f₂ : f.normalization ⟶ T) (g : T ⟶ Y) [IsAffineHom g]
    (H₁ : f.toNormalization ≫ f₁ = f.toNormalization ≫ f₂)
    (hf₁ : f₁ ≫ g = f.fromNormalization) (hf₂ : f₂ ≫ g = f.fromNormalization) : f₁ = f₂ := by
  apply f.normalizationOpenCover.hom_ext _ _ fun U ↦ ?_
  let := (f.app U.1).hom.toAlgebra
  have : IsAffineHom f₁ := have : IsAffineHom (f₁ ≫ g) := hf₁ ▸ inferInstance; .of_comp _ g
  have : IsAffineHom f₂ := have : IsAffineHom (f₂ ≫ g) := hf₂ ▸ inferInstance; .of_comp _ g
  let f₀ := toNormalization f ≫ f₁
  have hf₀ : f₀ = toNormalization f ≫ f₂ := H₁
  refine eq_of_SpecMap_comp_eq_of_isAffineOpen
    (CommRingCat.ofHom (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)).val.toRingHom)
    Subtype.val_injective _ (U.2.preimage g) ?_ ?_ ?_
  · simp only [← Scheme.Hom.comp_preimage, Category.assoc, hf₁, ι_fromNormalization]; simp
  · simp only [← Scheme.Hom.comp_preimage, Category.assoc, hf₂, ι_fromNormalization]; simp
  · have h₁ : f ⁻¹ᵁ U.1 ≤ f₀ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, f₀, Category.assoc,
        hf₁, toNormalization_fromNormalization]; rfl
    have h₁' : f ⁻¹ᵁ U.1 = toNormalization f ⁻¹ᵁ f₂ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, hf₂, toNormalization_fromNormalization]
    have h₂ : fromNormalization f ⁻¹ᵁ U.1 = f₁ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, hf₁]
    have h₂' : fromNormalization f ⁻¹ᵁ U.1 = f₂ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, hf₂]
    have h₃ : f ⁻¹ᵁ U.1 = toNormalization f ⁻¹ᵁ fromNormalization f ⁻¹ᵁ U.1 := by
      simp [← Scheme.Hom.comp_preimage]
    trans Spec.map (f₀.appLE _ _ h₁) ≫ (U.2.preimage g).fromSpec
    · simp only [AlgHom.toRingHom_eq_coe, comp_appLE, Spec.map_comp, Category.assoc, f₀,
        app_eq_appLE]
      rw [IsAffineOpen.SpecMap_appLE_fromSpec _ _ ((U.2.preimage _).preimage _)]
      have : (toNormalization f).appLE (f₁ ⁻¹ᵁ g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) h₁ =
        f.normalization.presheaf.map (eqToHom h₂).op ≫
        (toNormalization f).app (f.fromNormalization ⁻¹ᵁ U.1) ≫
          X.presheaf.map (eqToHom h₃).op := by
        simp [app_eq_appLE]
      rw [this, f.toNormalization_app_preimage U]
      simp [appIso_hom', IsAffineOpen.SpecMap_appLE_fromSpec_assoc _ _ (isAffineOpen_top (Spec _)),
        IsAffineOpen.fromSpec_top]
    · simp only [AlgHom.toRingHom_eq_coe, hf₀, comp_appLE, Spec.map_comp, Category.assoc,
        app_eq_appLE]
      rw [IsAffineOpen.SpecMap_appLE_fromSpec _ _ ((U.2.preimage _).preimage _)]
      have : (toNormalization f).appLE (f₂ ⁻¹ᵁ g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) h₁'.le =
        f.normalization.presheaf.map (eqToHom h₂').op ≫
        (toNormalization f).app (f.fromNormalization ⁻¹ᵁ U.1) ≫
          X.presheaf.map (eqToHom h₃).op := by
        simp [app_eq_appLE]
      rw [this, f.toNormalization_app_preimage U]
      simp [appIso_hom', IsAffineOpen.SpecMap_appLE_fromSpec_assoc _ _ (isAffineOpen_top (Spec _)),
        IsAffineOpen.fromSpec_top]

end UniversalProperty

section Coproduct

variable {U V : Scheme} {iU : U ⟶ X} {iV : V ⟶ X} (e : IsColimit (BinaryCofan.mk iU iV))
    [QuasiCompact iU] [QuasiSeparated iU] [QuasiCompact iV] [QuasiSeparated iV]

/-- The normalization of `Y` in a coproduct is isomorphic to the coproduct of the normalizations in
each of the components. -/
noncomputable def normalizationCoprodIso :
    (iU ≫ f).normalization ⨿ (iV ≫ f).normalization ≅ f.normalization where
  hom := coprod.desc
      ((iU ≫ f).normalizationDesc (iU ≫ f.toNormalization) f.fromNormalization (by simp))
      ((iV ≫ f).normalizationDesc (iV ≫ f.toNormalization) f.fromNormalization (by simp))
  inv := f.normalizationDesc ((e.coconePointUniqueUpToIso (colimit.isColimit _)).hom ≫
      coprod.map (iU ≫ f).toNormalization (iV ≫ f).toNormalization)
      (coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormalization) <| by
    simp only [← Iso.inv_comp_eq, Category.assoc]
    apply coprod.hom_ext <;> simp
  hom_inv_id := by
    ext
    · refine Scheme.Hom.normalization.hom_ext _ _ _
        (coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormalization) ?_ (by simp) (by simp)
      have H : iU ≫ (e.coconePointUniqueUpToIso (colimit.isColimit (pair U V))).hom = coprod.inl :=
        e.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (pair U V)) ⟨.left⟩
      simp [reassoc_of% H]
    · refine Scheme.Hom.normalization.hom_ext _ _ _
        (coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormalization) ?_ (by simp) (by simp)
      have H : iV ≫ (e.coconePointUniqueUpToIso (colimit.isColimit (pair U V))).hom = coprod.inr :=
        e.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (pair U V)) ⟨.right⟩
      simp [reassoc_of% H]
  inv_hom_id := by
    refine Scheme.Hom.normalization.hom_ext _ _ _ f.fromNormalization ?_ (by simp) (by simp)
    rw [← cancel_epi (e.coconePointUniqueUpToIso (colimit.isColimit (pair U V))).inv]
    apply coprod.hom_ext <;> simp

@[reassoc (attr := simp)]
lemma toNormalization_inl_normalizationCoprodIso_hom :
    (iU ≫ f).toNormalization ≫ coprod.inl ≫ (f.normalizationCoprodIso e).hom =
      iU ≫ f.toNormalization := by
  simp [Scheme.Hom.normalizationCoprodIso]

@[reassoc (attr := simp)]
lemma toNormalization_inr_normalizationCoprodIso_hom :
    (iV ≫ f).toNormalization ≫ coprod.inr ≫ (f.normalizationCoprodIso e).hom =
      iV ≫ f.toNormalization := by
  simp [Scheme.Hom.normalizationCoprodIso]

@[reassoc (attr := simp)]
lemma inl_toNormalization_normalizationCoprodIso_inv :
    iU ≫ f.toNormalization ≫ (f.normalizationCoprodIso e).inv =
      (iU ≫ f).toNormalization ≫ coprod.inl := by
  simp [← toNormalization_inl_normalizationCoprodIso_hom_assoc f e]

@[reassoc (attr := simp)]
lemma inr_toNormalization_normalizationCoprodIso_inv :
    iV ≫ f.toNormalization ≫ (f.normalizationCoprodIso e).inv =
      (iV ≫ f).toNormalization ≫ coprod.inr := by
  simp [← toNormalization_inr_normalizationCoprodIso_hom_assoc f e]

@[reassoc (attr := simp)]
lemma inl_normalizationCoprodIso_hom_fromNormalization :
    coprod.inl ≫ (f.normalizationCoprodIso e).hom ≫ f.fromNormalization =
      (iU ≫ f).fromNormalization := by
  simp [Scheme.Hom.normalizationCoprodIso]

@[reassoc (attr := simp)]
lemma inr_normalizationCoprodIso_hom_fromNormalization :
    coprod.inr ≫ (f.normalizationCoprodIso e).hom ≫ f.fromNormalization =
      (iV ≫ f).fromNormalization := by
  simp [Scheme.Hom.normalizationCoprodIso]

@[reassoc, simp]
lemma normalizationCoprodIso_inv_coprodDesc_fromNormalization :
    (f.normalizationCoprodIso e).inv ≫
      coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormalization =
    f.fromNormalization := by
  simp [Scheme.Hom.normalizationCoprodIso]

end Coproduct

end AlgebraicGeometry.Scheme.Hom
