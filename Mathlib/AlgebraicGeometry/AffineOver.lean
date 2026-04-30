/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.EquifiberedLimits
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical

/-!
# Schemes affine over a base

We show that the category of affine `X`-schemes is contravariantly equivalent to
`X.CoequifiberedQCohAlgCat`, a model of the category of quasi-coherent `𝒪ₓ`-algebras.
We use this to conclude that the category of affine `X`-schemes is complete, and that
the forgetful functor to `X`-schemes preserves (and reflects) limits.

## Main definitions
- `AlgebraicGeometry.Scheme.CoequifiberedQCohAlgCat`:
  The category of presheaves `F` of commutative rings over the affine opens of `X` together
  with a structure morphism `α : 𝒪ₓ ⟶ F` satisfying `Γ(F, D(f)) = Γ(F, U)[1/α(f)]`
  for each `f : Γ(𝒪ₓ, U)`.
  This is essentially the category of quasi-coherent `𝒪ₓ`-algebras.
- `AlgebraicGeometry.Scheme.AffineCat`:
  The category of schemes affine over a fixed base. This is an abbrev of `MorphismProperty.Over`.
- `AlgebraicGeometry.Scheme.coequifiberedQCohAlgCatEquivOver`:
  The contravariant equivalence between `X.CoequifiberedQCohAlgCat` and `X.AffineCat`.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open AffineZariskiSite

section CoequifiberedQCohAlgCat

/--
The category of presheaves `F` of commutative rings over the affine opens of `X` together
with a structure morphism `α : 𝒪ₓ ⟶ F` satisfying `Γ(F, D(f)) = Γ(F, U)[1/α(f)]`
for each `f : Γ(𝒪ₓ, U)`.

This is essentially the category of quasi-coherent `𝒪ₓ`-algebras.
Also see `Scheme.coequifiberedQCohAlgCatEquivOver` for the (contravariant) equivalence to
affine `X`-schemes. -/
abbrev CoequifiberedQCohAlgCat (X : Scheme.{u}) : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    fun F : Under ((toOpensFunctor X).op ⋙ X.presheaf) ↦ F.hom.Coequifibered

/-- The forgetful functor on `CoequifiberedQCohAlgCatForget`. -/
abbrev CoequifiberedQCohAlgCatForget (X : Scheme.{u}) :
    X.CoequifiberedQCohAlgCat ⥤ Under ((toOpensFunctor X).op ⋙ X.presheaf) :=
  ObjectProperty.ι _

/-- The gluing data for relative spec associated to a quasi-coherent `𝒪ₓ`-algebra. -/
noncomputable abbrev CoequifiberedQCohAlgCat.gluingData {X : Scheme.{u}}
    (F : X.CoequifiberedQCohAlgCat) :
    (directedCover X).RelativeGluingData := relativeGluingData F.property

@[reassoc (attr := simp)]
lemma CoequifiberedQCohAlgCat.ι_gluingData_toBase {X : Scheme.{u}}
    (F : X.CoequifiberedQCohAlgCat) (U : X.AffineZariskiSite) :
    colimit.ι (J := X.AffineZariskiSite) F.gluingData.functor U ≫ F.gluingData.toBase =
    Spec.map (F.obj.hom.app (.op U)) ≫ U.2.fromSpec := by
  rw [F.gluingData.ι_toBase]
  simp [relativeGluingData]

instance {X : Scheme.{u}} (F : X.CoequifiberedQCohAlgCat) (U : X.AffineZariskiSite) :
    IsAffine (F.gluingData.cover.X U) := isAffine_Spec _

instance : HasColimits X.CoequifiberedQCohAlgCat where
  has_colimits_of_shape _ := hasColimitsOfShape_of_closedUnderColimits _ _

noncomputable instance : CreatesColimits X.CoequifiberedQCohAlgCatForget :=
  ⟨fun {_} ↦ createsColimitsOfShapeFullSubcategoryInclusion ..⟩

end CoequifiberedQCohAlgCat

section AffineCat

/-- The category of schemes relatively affine over a fixed base. -/
abbrev AffineCat (X : Scheme) := MorphismProperty.Over @IsAffineHom ⊤ X

/-- Constructor for `S.AffineCat`. -/
abbrev AffineCat.mk {X S : Scheme} (f : X ⟶ S) [IsAffineHom f] : S.AffineCat :=
  MorphismProperty.Over.mk _ f ‹_›

end AffineCat

section Equivalence

instance {f : MorphismProperty.Over @IsAffineHom ⊤ X} : IsAffineHom f.hom := f.prop

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation). The "relative Spec" functor from quasi-coherent `𝒪ₓ`-algebras to
affine `X`-schemes. Use `coequifiberedQCohAlgCatEquivOver` directly. -/
noncomputable def coequifiberedQCohAlgCatToOver (X : Scheme.{u}) :
    X.CoequifiberedQCohAlgCatᵒᵖ ⥤ X.AffineCat where
  obj F := MorphismProperty.Over.mk _ F.unop.gluingData.toBase <| by
    refine ⟨fun U hU ↦ ?_⟩
    rw [toBase_relativeGluingData_preimage _ _ F.unop.property _ hU]
    exact isAffineOpen_opensRange _
  map {F G} α := MorphismProperty.Over.homMk
    (colimMap (Functor.whiskerRight (α.unop.hom.right.rightOp) _)) <| by
    dsimp
    ext U
    simp [← Spec.map_comp_assoc, ← NatTrans.comp_app, Under.w α.unop.hom]

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation). The sections functor from affine `X`-schemes to quasi-coherent `𝒪ₓ`-algebras.
Use `coequifiberedQCohAlgCatEquivOver` directly. -/
noncomputable def coequifiberedQCohAlgCatOfOver (X : Scheme.{u}) :
    X.AffineCatᵒᵖ ⥤ X.CoequifiberedQCohAlgCat where
  obj f := .mk (.mk (Y := ((preimage f.unop.hom).op ⋙ (toOpensFunctor _).op) ⋙ f.unop.left.presheaf)
      (Functor.whiskerLeft _ f.unop.hom.c)) <| coequifibered_iff_forall_isLocalizationAway.mpr
    fun U r ↦
      (U.2.preimage _).isLocalization_of_eq_basicOpen _ _ (f.unop.hom.preimage_basicOpen r)
  map {f g} α :=
    letI β : preimage g.unop.hom ⋙ toOpensFunctor g.unop.left ⟶ preimage f.unop.hom ⋙
        toOpensFunctor f.unop.left ⋙ TopologicalSpace.Opens.map α.unop.hom.left.base :=
      { app U := eqToHom congr($(Over.w α.unop.hom) ⁻¹ᵁ U.1).symm }
    ⟨Under.homMk (Functor.whiskerLeft _ α.unop.hom.left.c ≫
      Functor.whiskerRight (NatTrans.op β) g.unop.left.presheaf) (by
    ext U : 2
    exact ((Hom.congr_app (Over.w α.unop.hom).symm U.unop.1).trans (Category.assoc _ _ _)).symm)⟩
  map_id f := by
    ext U : 4
    simpa [-CategoryTheory.Functor.map_id] using f.unop.left.presheaf.map_id _
  map_comp {f g h} α β := by
    ext U : 4
    simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, -Scheme.Hom.comp_appLE]

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence between quasi-coherent `𝒪ₓ`-algebras and affine `X`-schemes.
The forwards direction is the relative Spec functor, taking `F` to `colim (F ⋙ Spec)`.
The inverse direction takes `f : Y ⟶ X` to `f_* 𝒪_Y`. -/
@[simps! functor_obj_left functor_obj_hom functor_map_hom_left counitIso_hom_app_hom_left]
noncomputable def coequifiberedQCohAlgCatEquivOver (X : Scheme.{u}) :
    X.CoequifiberedQCohAlgCatᵒᵖ ≌ X.AffineCat where
  functor := X.coequifiberedQCohAlgCatToOver
  inverse := X.coequifiberedQCohAlgCatOfOver.rightOp
  unitIso := by
    refine NatIso.ofComponents (fun F ↦ .op (ObjectProperty.isoMk _ (Under.isoMk
      (NatIso.ofComponents (fun U ↦ F.unop.gluingData.glued.presheaf.mapIso
        (eqToIso ((F.unop.gluingData.cover.f U.unop).image_top_eq_opensRange
        |>.trans (toBase_relativeGluingData_preimage _ _ F.unop.2 _ U.unop.2).symm)).op ≪≫
        ((relativeGluingData F.unop.2).cover.f U.unop).appIso _ ≪≫ Scheme.ΓSpecIso _) ?_) ?_))) ?_
    · intros U V i
      dsimp [coequifiberedQCohAlgCatToOver, coequifiberedQCohAlgCatOfOver, toOpens]
      rw [← cancel_mono (ΓSpecIso _).inv]
      simp only [Hom.appIso_hom', Hom.map_appLE_assoc, Category.assoc, ← Scheme.ΓSpecIso_naturality,
        Iso.hom_inv_id, Category.comp_id, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      congr 1
      exact (colimit.w F.unop.gluingData.functor i.unop).symm
    · ext U : 2
      dsimp [coequifiberedQCohAlgCatToOver, coequifiberedQCohAlgCatOfOver]
      simp [Hom.appIso_hom', Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE_assoc,
        -Hom.comp_appLE]
      simp [Hom.comp_appLE, IsAffineOpen.fromSpec_app_of_le _ _ le_rfl,
        Iso.inv_comp_eq, ← Scheme.ΓSpecIso_naturality, Scheme.Hom.app_eq_appLE]
    · intros F G α
      apply Quiver.Hom.unop_inj
      dsimp
      ext U : 4
      dsimp [coequifiberedQCohAlgCatToOver, coequifiberedQCohAlgCatOfOver, toOpens]
      simp only [Hom.appIso_hom', Hom.map_appLE_assoc, Scheme.Hom.app_eq_appLE, Category.assoc,
        Scheme.Hom.appLE_comp_appLE_assoc, ← Scheme.ΓSpecIso_naturality, ι_colimMap]
      simp
  counitIso := by
    refine NatIso.ofComponents (fun f ↦ ?_) ?_
    · letI H := (X.coequifiberedQCohAlgCatOfOver.rightOp.obj f).unop.property
      letI c : Cocone (relativeGluingData H).functor := ⟨_, fun U ↦ (U.2.preimage f.hom).fromSpec,
        fun U V i ↦ by simpa [coequifiberedQCohAlgCatOfOver] using IsAffineOpen.map_fromSpec _ _ _⟩
      haveI hc₁ : colimit.desc (relativeGluingData H).functor c ≫ f.hom =
          (relativeGluingData H).toBase := by
        ext U
        rw [(relativeGluingData H).ι_toBase]
        simp [← U.2.SpecMap_appLE_fromSpec f.hom (U.2.preimage f.hom) le_rfl,
          coequifiberedQCohAlgCatOfOver, Scheme.Hom.app_eq_appLE, relativeGluingData, c]
      haveI hc₂ : IsIso (colimit.desc _ c) := by
        refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
          (f.left.openCoverOfIsOpenCover _ (.comap (iSup_affineOpens_eq_top X)
          f.hom.base.hom))).mpr fun U ↦ ?_
        convert (IsOpenImmersion.isoOfRangeEq (pullback.fst _ (f.hom ⁻¹ᵁ U.1).ι)
          ((U.2.preimage f.hom).isoSpec.hom ≫ (relativeGluingData H).cover.f U) ?eq).isIso_hom
        case eq =>
          rw [← Hom.coe_opensRange, ← Hom.coe_opensRange]
          congr 1
          rw [Hom.opensRange_comp_of_isIso, Hom.opensRange_pullbackFst, Opens.opensRange_ι]
          exact congr($hc₁ ⁻¹ᵁ U.1).trans (toBase_relativeGluingData_preimage _ _ _ U.1 U.2)
        rw [← cancel_mono (f.hom ⁻¹ᵁ U.1).ι]
        refine (pullback.condition ..).symm.trans ((Iso.inv_comp_eq _).mp ?_)
        refine (IsOpenImmersion.isoOfRangeEq_inv_fac_assoc ..).trans ?_
        simp [IsAffineOpen.isoSpec_hom, c]
      exact MorphismProperty.Over.isoMk (asIso (colimit.desc _ c)) (by simpa)
    · intros g h α
      ext
      dsimp [coequifiberedQCohAlgCatToOver]
      ext
      simpa [coequifiberedQCohAlgCatOfOver, ← Spec.map_comp_assoc, -Spec.map_comp,
        Scheme.Hom.app_eq_appLE] using IsAffineOpen.SpecMap_appLE_fromSpec _ _ _ _
  functor_unitIso_comp F := by
    ext
    dsimp [coequifiberedQCohAlgCatToOver]
    ext
    dsimp [coequifiberedQCohAlgCatOfOver]
    simp only [ι_colimMap_assoc, colimit.ι_desc]
    dsimp
    simp only [eqToHom_op, Hom.appIso_hom', Hom.map_appLE_assoc, Spec.map_comp,
      SpecMap_ΓSpecIso_hom, Category.assoc, Category.comp_id]
    rw [IsAffineOpen.SpecMap_appLE_fromSpec (hV := isAffineOpen_top (Spec _)),
      IsAffineOpen.fromSpec_top, isoSpec_Spec_inv]
    exact toSpecΓ_SpecMap_ΓSpecIso_inv_assoc ..

@[simp]
lemma coequifiberedQCohAlgCatEquivOver_inverse_obj_unop_obj_right_obj
    (Y : MorphismProperty.Over @IsAffineHom ⊤ X) (U : X.AffineZariskiSiteᵒᵖ) :
    (X.coequifiberedQCohAlgCatEquivOver.inverse.obj Y).unop.obj.right.obj U =
      Γ(Y.left, Y.hom ⁻¹ᵁ U.unop.toOpens) := rfl

@[simp]
lemma coequifiberedQCohAlgCatEquivOver_inverse_obj_unop_obj_right_map
    (Y : MorphismProperty.Over @IsAffineHom ⊤ X) {U V : X.AffineZariskiSiteᵒᵖ} (i : U ⟶ V) :
    (X.coequifiberedQCohAlgCatEquivOver.inverse.obj Y).unop.obj.right.map i =
      Y.left.presheaf.map (homOfLE (Y.hom.preimage_mono (toOpens_mono i.unop.le))).op := rfl

@[simp]
lemma coequifiberedQCohAlgCatEquivOver_inverse_obj_unop_obj_hom_app
    (Y : MorphismProperty.Over @IsAffineHom ⊤ X) (U : X.AffineZariskiSiteᵒᵖ) :
    (X.coequifiberedQCohAlgCatEquivOver.inverse.obj Y).unop.obj.hom.app U =
      Y.hom.app U.unop.toOpens := rfl

@[simp]
lemma coequifiberedQCohAlgCatEquivOver_inverse_map_unop_hom_right_app
    {Y Z : MorphismProperty.Over @IsAffineHom ⊤ X} (f : Y ⟶ Z) (U : X.AffineZariskiSiteᵒᵖ) :
    (X.coequifiberedQCohAlgCatEquivOver.inverse.map f).unop.hom.right.app U =
    f.hom.left.appLE _ _ congr(($(MorphismProperty.Over.w f)) ⁻¹ᵁ U.unop.1).ge := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma coequifiberedQCohAlgCatEquivOver_unitIso_hom_app_unop_hom_right_app
    (F : X.CoequifiberedQCohAlgCatᵒᵖ) (U) :
    (X.coequifiberedQCohAlgCatEquivOver.unitIso.hom.app F).unop.hom.right.app U =
    (F.unop.gluingData.cover.f U.unop).appLE _ ⊤
      (by simp [← Scheme.Hom.comp_preimage]) ≫ (ΓSpecIso _).hom := by
  dsimp [coequifiberedQCohAlgCatEquivOver]
  simp [Hom.appIso_hom']
  rfl

instance : HasLimits (MorphismProperty.Over @IsAffineHom ⊤ X) :=
  hasLimits_of_hasLimits_createsLimits X.coequifiberedQCohAlgCatEquivOver.inverse

end Equivalence

section PreservesLimits

set_option backward.isDefEq.respectTransparency false in
/-- Under the equivalence of categories between affine `X`-schemes and quasi-coherent `𝒪ₓ`-algebras,
the pullback functor on affine `X`-schemes along an open immersion `U ⟶ X` corresponds
to the restriction functor `F ↦ F|ᵤ` of quasi-coherent `𝒪ₓ`-algebras. -/
noncomputable def coequifiberedQCohAlgCatRestrict [IsOpenImmersion f] :
    Y.coequifiberedQCohAlgCatEquivOver.inverse ⋙ Y.CoequifiberedQCohAlgCatForget.op ⋙
      (Under.post ((Functor.whiskeringLeft _ _ _).obj (AffineZariskiSite.image f).op) ⋙
      Under.map ((toOpensFunctor X).op.whiskerLeft (IsOpenImmersion.presheafIso f).hom)).op ≅
    MorphismProperty.Over.pullback @IsAffineHom ⊤ f ⋙
      X.coequifiberedQCohAlgCatEquivOver.inverse ⋙ X.CoequifiberedQCohAlgCatForget.op := by
  refine NatIso.ofComponents (fun F ↦ .op (Under.isoMk (NatIso.ofComponents (fun U ↦
    ((pullback.fst F.hom f).appIso _).symm ≪≫ F.left.presheaf.mapIso
      (eqToIso (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
        (.flip <| .of_hasPullback _ _) _).symm).op) ?_) ?_)) ?_
  · intros U V i; simp [← Functor.map_comp]
  · ext U : 2
    dsimp
    rw [Iso.eq_inv_comp]
    simp only [Hom.appIso_hom', Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE_assoc,
      ← pullback.condition]
    simp [Hom.comp_appLE, Hom.app_eq_appLE]
  · intros F G α
    apply Quiver.Hom.unop_inj
    ext U : 3
    dsimp
    rw [← IsIso.comp_inv_eq]
    simp only [Category.assoc, Iso.inv_comp_eq, IsIso.inv_comp, ← Functor.map_inv, ← op_inv,
      inv_eqToHom]
    simp [Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE, -Scheme.Hom.comp_appLE]

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] preservesLimitsOfSize_op in
-- This is true for arbitrary `f`. The instance is provided at the end of the file.
private instance [IsOpenImmersion f] :
    PreservesLimits (MorphismProperty.Over.pullback @IsAffineHom ⊤ f) := by
  suffices PreservesLimits (Y.coequifiberedQCohAlgCatEquivOver.functor ⋙
      MorphismProperty.Over.pullback @IsAffineHom ⊤ f) by
    exact preservesLimits_of_natIso (F := _ ⋙ Y.coequifiberedQCohAlgCatEquivOver.functor ⋙
      MorphismProperty.Over.pullback @IsAffineHom ⊤ f)
      (Functor.isoWhiskerRight Y.coequifiberedQCohAlgCatEquivOver.counitIso
        (MorphismProperty.Over.pullback @IsAffineHom ⊤ f))
  suffices PreservesLimits ((Y.coequifiberedQCohAlgCatEquivOver.functor ⋙
      MorphismProperty.Over.pullback @IsAffineHom ⊤ f) ⋙
      X.coequifiberedQCohAlgCatEquivOver.inverse ⋙ X.CoequifiberedQCohAlgCatForget.op)
    from preservesLimits_of_reflects_of_preserves _
      (X.coequifiberedQCohAlgCatEquivOver.inverse ⋙ X.CoequifiberedQCohAlgCatForget.op)
  let FF : Under ((toOpensFunctor Y).op ⋙ Y.presheaf) ⥤
      Under ((toOpensFunctor X).op ⋙ X.presheaf) :=
    Under.post ((Functor.whiskeringLeft _ _ _).obj (AffineZariskiSite.image f).op) ⋙ Under.map
    ((toOpensFunctor X).op.whiskerLeft (IsOpenImmersion.presheafIso f).hom)
  exact preservesLimits_of_natIso ((coequifiberedQCohAlgCatRestrict f).isoInverseComp
      (G := Y.coequifiberedQCohAlgCatEquivOver.symm))

set_option backward.isDefEq.respectTransparency false in
instance : PreservesLimits (MorphismProperty.Over.forget @IsAffineHom ⊤ X) := by
  clear Y f
  wlog hX : IsAffine X
  · exact ⟨fun {J} _ ↦ ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨X.affineCover.isLimitOverOfCover _ fun i ↦
      ((this inferInstance).1.1.1 (isLimitOfPreserves
      (MorphismProperty.Over.pullback _ ⊤ (X.affineCover.f i)) hc)).some⟩⟩⟩⟩
  refine ⟨fun {J} _ ↦ ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨.ofExistsUnique fun s ↦ ?_⟩⟩⟩⟩
  let f₂ (U : s.pt.left.affineOpens) :=
    hc.lift ⟨.mk _ (U.1.ι ≫ s.pt.hom) (isAffineHom_of_isAffine _),
      fun i ↦ MorphismProperty.Over.homMk (U.1.ι ≫ (s.π.app i).left) (by simp),
      fun i j e ↦ by ext; simp [← s.w e]⟩
  let f : s.pt.left ⟶ c.pt.1.left :=
    s.pt.left.directedAffineCover.glueMorphismsOfLocallyDirected (fun U ↦ (f₂ U).left)
      fun {i j} e ↦
      have : (MorphismProperty.Over.homMk (s.pt.left.homOfLE e.le) (by simp)) ≫ f₂ j = f₂ i :=
        hc.hom_ext fun k ↦ by dsimp [f₂]; ext; simp
      congr(($this).left)
  refine ⟨Over.homMk f ?_, fun j ↦ ?_, ?_⟩
  · apply s.pt.left.directedAffineCover.hom_ext _ _ fun j ↦ ?_
    rw [OpenCover.map_glueMorphismsOfLocallyDirected_assoc]
    simp
  · ext
    dsimp
    apply s.pt.left.directedAffineCover.hom_ext _ _ fun j ↦ ?_
    rw [OpenCover.map_glueMorphismsOfLocallyDirected_assoc]
    simp [← MorphismProperty.Comma.comp_left, -MorphismProperty.Comma.comp_hom, f₂]
  · intro f' hf'
    ext
    dsimp
    apply s.pt.left.directedAffineCover.hom_ext _ _ fun j ↦ ?_
    rw [OpenCover.map_glueMorphismsOfLocallyDirected]
    rw [← hc.hom_ext (f := MorphismProperty.Over.homMk (j.1.ι ≫ f'.left) (by simp))
      (f' := f₂ j) fun k ↦ ?_]
    · rfl
    dsimp
    simp only [IsLimit.fac, ← hf', f₂]
    ext
    simp

instance : ReflectsLimits (MorphismProperty.Over.forget @IsAffineHom ⊤ X) :=
  reflectsLimits_of_reflectsIsomorphisms

instance : PreservesLimits (MorphismProperty.Over.pullback @IsAffineHom ⊤ f) := by
  suffices PreservesLimits (MorphismProperty.Over.pullback @IsAffineHom ⊤ f ⋙
      MorphismProperty.Over.forget _ _ _) from
    preservesLimits_of_reflects_of_preserves _ (MorphismProperty.Over.forget _ _ _)
  change PreservesLimits (MorphismProperty.Over.forget _ _ _ ⋙ Over.pullback f)
  infer_instance

end PreservesLimits

end AlgebraicGeometry.Scheme
