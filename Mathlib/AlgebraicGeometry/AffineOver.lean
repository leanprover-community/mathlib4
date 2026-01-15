/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Schemes affine over a base

We show that the category of affine `X`-schemes is contravariantly equivalent to
`X.PreservesLocalizationCat`, a model of the category of quasi-coherent `𝒪ₓ`-algebras.
We use this to conclude that the category of affine `X`-schemes is cocomplete, and that
the forgetful functor to `X`-schemes preserves (and reflects) them.

## Main definitions
- `AlgebraicGeometry.Scheme.PreservesLocalizationCat`:
  The category of presheaf `F` of commutative rings over the affine opens of `X` together
  with a structure morphism `α : 𝒪ₓ ⟶ F` satisfying `Γ(F, D(f)) = Γ(F, U)[1/α(f)]`
  for each `f : Γ(𝒪ₓ, U)`.
  This is essentially the category of quasi-coherent `𝒪ₓ`-algebras.
- `AlgebraicGeometry.Scheme.preservesLocalizationCatEquivOver`:
  The contravariant equivalence between `X.PreservesLocalizationCat` and affine `X`-schemes.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme


universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open AffineZariskiSite

section PreservesLocalizationCat

/--
The category of presheaf `F` of commutative rings over the affine opens of `X` together
with a structure morphism `α : 𝒪ₓ ⟶ F` satisfying `Γ(F, D(f)) = Γ(F, U)[1/α(f)]`
for each `f : Γ(𝒪ₓ, U)`.

This is essentially the category of quasi-coherent `𝒪ₓ`-algebras.
Also see `Scheme.preservesLocalizationCatEquivOver` for the (contravariant) equivalence to
affine `X`-schemes. -/
abbrev PreservesLocalizationCat (X : Scheme.{u}) : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    fun F : Under ((toOpensFunctor X).op ⋙ X.presheaf) ↦ PreservesLocalization _ F.hom

/-- The forgetful functor on `preservesLocalizationCatForget`. -/
abbrev preservesLocalizationCatForget (X : Scheme) :
    X.PreservesLocalizationCat ⥤ Under ((toOpensFunctor X).op ⋙ X.presheaf) :=
  ObjectProperty.ι _

instance (F : X.PreservesLocalizationCat) :
    ((F.obj.right.rightOp ⋙ Scheme.Spec) ⋙ Scheme.forget).IsLocallyDirected :=
  F.2.isLocallyDirected

instance (F : X.PreservesLocalizationCat) {U V} (f : U ⟶ V) :
    IsOpenImmersion ((F.obj.right.rightOp ⋙ Scheme.Spec).map f) :=
  F.2.isOpenImmersion _ _ _

instance {J : Type*} [Category J] : ObjectProperty.IsClosedUnderColimitsOfShape
    (fun F : Under ((toOpensFunctor X).op ⋙ X.presheaf) ↦ PreservesLocalization _ F.hom) J := by
  wlog hJ : IsConnected J generalizing J
  · refine ⟨fun F ⟨⟨c, α, hc⟩, H⟩ U f ↦ ?_⟩
    have hc' := WithInitial.isColimitEquiv.symm hc
    have inst : IsConnected (WithInitial J) := isConnected_of_hasInitial _
    exact (this (J := WithInitial J) inst).1 F
      ⟨⟨WithInitial.liftToInitial c Under.mkIdInitial,
      { app i := i.casesOn α.app (Under.mkIdInitial.to _) },
      isColimitOfReflects (Under.forget _) (by
      refine IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_ (WithInitial.isColimitEquiv.symm hc)
      · exact NatIso.ofComponents (fun i ↦ i.casesOn (fun _ ↦ .refl _) (.refl _)) <| by
          rintro (i | _) (j | _) <;> (try rintro ⟨⟩) <;> simp
      · exact Cocones.ext (.refl _) (by rintro ⟨⟩ <;> simp))⟩, fun i ↦
        i.casesOn H X.preservesLocalization_toOpensFunctor⟩ U f
  refine ⟨fun F ⟨⟨c, α, hc⟩, H⟩ U f ↦ ?_⟩
  let hc₁ := isColimitOfPreserves (Under.forget _ ⋙ (CategoryTheory.evaluation _ _).obj (.op U)) hc
  let hc₂ := isColimitOfPreserves (Under.forget _ ⋙ (CategoryTheory.evaluation _ _).obj
    (.op (U.basicOpen f))) hc
  let (i : _) : Algebra ((c.obj i).right.obj (.op U)) ((c.obj i).right.obj
    (.op (U.basicOpen f))) := ((c.obj i).right.map (homOfLE (U.basicOpen_le f)).op).hom.toAlgebra
  let : Algebra (F.right.obj (.op U)) (F.right.obj (.op (U.basicOpen f))) :=
    (F.right.map (homOfLE (U.basicOpen_le f)).op).hom.toAlgebra
  have (i : _) : IsLocalization.Away (R := (c.obj i).right.obj (.op U))
    ((c.obj i).hom.app (.op U) f) ((c.obj i).right.obj (.op (U.basicOpen f))) := H i U f
  have (i : _) : IsLocalization.Away (R := F.right.obj (.op U))
      ((α.app i).right.app (.op U) ((c.obj i).hom.app (.op U) f))
      (Localization.Away (M := F.right.obj (.op U)) (F.hom.app _ f)) := by
    convert (inferInstanceAs <| IsLocalization.Away (R := F.right.obj (.op U))
      (F.hom.app _ f) (Localization.Away (M := F.right.obj (.op U)) (F.hom.app _ f)))
    exact congr($(Under.w (α.app i)).app (.op U) f)
  let e : F.right.obj (Opposite.op (U.basicOpen f)) ≅
      .of (Localization.Away (M := F.right.obj (.op U)) (F.hom.app _ f)) := by
    refine ⟨hc₂.desc ⟨_, fun i ↦ CommRingCat.ofHom (IsLocalization.Away.map
        (R := (c.obj i).right.obj (.op U))
        (S := (c.obj i).right.obj (.op (U.basicOpen f))) (P := F.right.obj (.op U))
        (r := (c.obj i).hom.app _ f) _ ((α.app i).right.app _).hom), ?_⟩,
      CommRingCat.ofHom (IsLocalization.Away.lift (R := F.right.obj (.op U)) (F.hom.app _ f)
        (g := (F.right.map (homOfLE (U.basicOpen_le f)).op).hom) ?_), ?_, ?_⟩
    · intro i j g
      ext1
      dsimp
      refine IsLocalization.ringHom_ext (R := (c.obj i).right.obj (.op U))
        (.powers ((c.obj i).hom.app (.op U) f)) ?_
      simp only [IsLocalization.Away.map, RingHomCompTriple.comp_eq, IsLocalization.map_comp]
      rw [RingHom.comp_assoc, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        NatTrans.naturality, CommRingCat.hom_comp, ← RingHom.comp_assoc,
        ← ((c.obj j).right.map _).hom.algebraMap_toAlgebra, IsLocalization.map_comp,
        RingHom.comp_assoc, ← CommRingCat.hom_comp, ← NatTrans.comp_app, ← Under.comp_right,
        NatTrans.naturality]
      simp
    · have := U.2.isLocalization_basicOpen f
      convert_to IsUnit (F.hom.app (.op (U.basicOpen f))
        (X.presheaf.map ((toOpensFunctor X).map (homOfLE (U.basicOpen_le f))).op f))
      · exact congr($(F.hom.naturality _) f).symm
      · dsimp; exact .map _ (IsLocalization.Away.algebraMap_isUnit _)
    · apply hc₂.hom_ext fun i ↦ ?_
      rw [hc₂.fac_assoc]
      ext1
      dsimp
      refine IsLocalization.ringHom_ext (R := (c.obj i).right.obj (.op U))
        (.powers ((c.obj i).hom.app (.op U) f)) ?_
      dsimp
      simp only [IsLocalization.Away.map, RingHom.comp_assoc,
        IsLocalization.map_comp, RingHomCompTriple.comp_eq]
      rw [← RingHom.comp_assoc, IsLocalization.Away.lift_comp, RingHom.algebraMap_toAlgebra]
      simp only [← CommRingCat.hom_comp, (α.app i).right.naturality]
      dsimp
    · ext1
      refine IsLocalization.ringHom_ext (R := F.right.obj (.op U)) (.powers (F.hom.app _ f)) ?_
      dsimp
      simp only [homOfLE_leOfHom, RingHom.comp_assoc, IsLocalization.Away.lift_comp,
        RingHomCompTriple.comp_eq]
      rw [← CommRingCat.hom_comp]
      conv_rhs => rw [← CommRingCat.hom_ofHom (algebraMap _ _)]
      congr 1
      refine hc₁.hom_ext fun i ↦ ?_
      dsimp
      erw [← (α.app i).right.naturality_assoc, hc₂.fac]
      ext1
      dsimp [IsLocalization.Away.map]
      rw [← ((c.obj i).right.map _).hom.algebraMap_toAlgebra, IsLocalization.map_comp]
  dsimp
  refine (IsLocalization.isLocalization_iff_of_ringEquiv _ e.commRingCatIsoToRingEquiv).mpr ?_
  convert (inferInstanceAs (IsLocalization (R := F.right.obj (.op U))
    (.powers (F.hom.app _ f)) (Localization.Away (M := F.right.obj (.op U)) (F.hom.app _ f))):)
  refine Algebra.algebra_ext _ _ fun r ↦ e.commRingCatIsoToRingEquiv.eq_symm_apply.mp ?_
  simp [e, Iso.commRingCatIsoToRingEquiv, RingHom.algebraMap_toAlgebra]

instance : HasColimits X.PreservesLocalizationCat where
  has_colimits_of_shape _ := hasColimitsOfShape_of_closedUnderColimits _ _

noncomputable instance : CreatesColimits X.preservesLocalizationCatForget :=
  ⟨fun {_} ↦ createsColimitsOfShapeFullSubcategoryInclusion ..⟩

end PreservesLocalizationCat

section Equivalence

instance {f : MorphismProperty.Over @IsAffineHom ⊤ X} : IsAffineHom f.hom := f.prop

/-- (Implementation). The "relative Spec" functor from quasi-coherent `𝒪ₓ`-algebras to
affine `X`-schemes. Use `preservesLocalizationCatEquivOver` directly. -/
noncomputable def preservesLocalizationCatToOver (X : Scheme.{u}) :
    X.PreservesLocalizationCatᵒᵖ ⥤ MorphismProperty.Over @IsAffineHom ⊤ X where
  obj F := .mk _ (colimit.desc (F.unop.obj.right.rightOp ⋙ Scheme.Spec)
    ⟨X, Functor.whiskerRight F.unop.obj.hom.rightOp _ ≫ (cocone X).ι⟩) <| by
    refine ⟨fun U hU ↦ ?_⟩
    rw [show (colimit.desc (F.unop.obj.right.rightOp ⋙ Scheme.Spec) ⟨X, _⟩) ⁻¹ᵁ U = _ from
      F.unop.2.colimitDesc_preimage _ _ ⟨U, hU⟩]
    dsimp
    exact isAffineOpen_opensRange _
  map {F G} α := MorphismProperty.Over.homMk
    (colimMap (Functor.whiskerRight (α.unop.hom.right.rightOp) _)) <| by
    dsimp
    ext U
    simp only [ι_colimMap_assoc, colimit.ι_desc]
    dsimp
    rw [← Spec.map_comp_assoc, ← NatTrans.comp_app, Under.w α.unop.hom]
  map_id := by intros; dsimp; ext; dsimp; ext; simp
  map_comp := by intros; dsimp; ext; dsimp; ext; simp

/-- (Implementation). The sections functor from affine `X`-schemes to quasi-coherent `𝒪ₓ`-algebras.
Use `preservesLocalizationCatEquivOver` directly. -/
noncomputable def preservesLocalizationCatOfOver (X : Scheme.{u}) :
    (MorphismProperty.Over @IsAffineHom ⊤ X)ᵒᵖ ⥤ X.PreservesLocalizationCat where
  obj f := .mk (.mk (Y := ((preimage f.unop.hom).op ⋙ (toOpensFunctor _).op) ⋙ f.unop.left.presheaf)
      (Functor.whiskerLeft _ f.unop.hom.c)) fun U r ↦
    (U.2.preimage f.unop.hom).isLocalization_of_eq_basicOpen _ _ (f.unop.hom.preimage_basicOpen r)
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

/-- The equivalence between quasi-coherent `𝒪ₓ`-algebras and affine `X`-schemes.
The forwards direction is the relative Spec functor, taking `F` to `colim (F ⋙ Spec)`.
The inverse direction takes `f : Y ⟶ X` to `f_* 𝒪_Y`. -/
noncomputable def preservesLocalizationCatEquivOver (X : Scheme.{u}) :
    X.PreservesLocalizationCatᵒᵖ ≌ MorphismProperty.Over @IsAffineHom ⊤ X where
  functor := X.preservesLocalizationCatToOver
  inverse := X.preservesLocalizationCatOfOver.rightOp
  unitIso := by
    refine NatIso.ofComponents (fun F ↦ .op (ObjectProperty.isoMk _ (Under.isoMk
    (NatIso.ofComponents (fun U ↦ (colimit (F.unop.obj.right.rightOp ⋙ Scheme.Spec)).presheaf.mapIso
        (eqToIso (colimit.ι (F.unop.obj.right.rightOp ⋙ Scheme.Spec) U.unop
        |>.image_top_eq_opensRange.trans (F.unop.2.colimitDesc_preimage _ _ U.unop).symm)).op ≪≫
        (colimit.ι (_ ⋙ Scheme.Spec) U.unop).appIso _ ≪≫ Scheme.ΓSpecIso _) ?_) ?_))) ?_
    · intros U V i
      dsimp [preservesLocalizationCatToOver, preservesLocalizationCatOfOver, toOpens]
      rw [← cancel_mono (ΓSpecIso _).inv]
      simp only [Hom.appIso_hom', Hom.map_appLE_assoc, Category.assoc, ← Scheme.ΓSpecIso_naturality,
        Iso.hom_inv_id, Category.comp_id, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      congr 1
      exact (colimit.w (F.unop.obj.right.rightOp ⋙ Scheme.Spec) i.unop).symm
    · ext U : 2
      dsimp [preservesLocalizationCatToOver, preservesLocalizationCatOfOver]
      simp only [Hom.appIso_hom', Hom.map_appLE_assoc, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.appLE_comp_appLE_assoc, colimit.ι_desc]
      dsimp
      rw [Hom.comp_appLE, IsAffineOpen.fromSpec_app_of_le _ _ le_rfl]
      simp [Iso.inv_comp_eq, ← Scheme.ΓSpecIso_naturality, Scheme.Hom.app_eq_appLE]
    · intros F G α
      apply Quiver.Hom.unop_inj
      dsimp
      ext U : 4
      dsimp [preservesLocalizationCatToOver, preservesLocalizationCatOfOver, toOpens]
      simp only [Hom.appIso_hom', Hom.map_appLE_assoc, Scheme.Hom.app_eq_appLE, Category.assoc,
        Scheme.Hom.appLE_comp_appLE_assoc, ← Scheme.ΓSpecIso_naturality, ι_colimMap]
      simp
  counitIso := by
    refine NatIso.ofComponents (fun f ↦ MorphismProperty.Over.isoMk (@asIso _ _ _ _
      (colimit.desc _ ⟨_, fun U ↦ (U.2.preimage f.hom).fromSpec, ?_⟩) ?_) ?_) ?_
    · intro U V i
      simpa [preservesLocalizationCatOfOver] using IsAffineOpen.map_fromSpec _ _ _
    · refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
        (f.left.openCoverOfIsOpenCover _ (.comap (iSup_affineOpens_eq_top X)
        f.hom.base.hom))).mpr fun U ↦ ?_
      convert (IsOpenImmersion.isoOfRangeEq (pullback.fst _ (f.hom ⁻¹ᵁ U.1).ι)
        ((U.2.preimage f.hom).isoSpec.hom ≫
        colimit.ι ((X.preservesLocalizationCatOfOver.rightOp.obj f).unop.obj.right.rightOp ⋙
          Scheme.Spec) U) ?eq).isIso_hom
      case eq =>
        rw [← Hom.coe_opensRange, ← Hom.coe_opensRange]
        congr 1
        rw [Hom.opensRange_comp_of_isIso, Hom.opensRange_pullbackFst, Opens.opensRange_ι,
          ← (X.preservesLocalizationCatOfOver.rightOp.obj f).unop.2.colimitDesc_preimage
            (F := (X.preservesLocalizationCatOfOver.rightOp.obj f).unop.obj.right),
          ← Scheme.Hom.comp_preimage]
        congr 5
        apply colimit.hom_ext fun U ↦ ?_
        have := IsAffineOpen.SpecMap_appLE_fromSpec f.hom U.2 (U.2.preimage f.hom) le_rfl
        simp [preservesLocalizationCatOfOver, ← this, Scheme.Hom.app_eq_appLE]
      · rw [← cancel_mono (f.hom ⁻¹ᵁ U.1).ι]
        refine (pullback.condition ..).symm.trans ((Iso.inv_comp_eq _).mp ?_)
        refine (IsOpenImmersion.isoOfRangeEq_inv_fac_assoc ..).trans ?_
        simp [IsAffineOpen.isoSpec_hom]
    · dsimp [preservesLocalizationCatToOver]
      ext U
      have := IsAffineOpen.SpecMap_appLE_fromSpec f.hom U.2 (U.2.preimage f.hom) le_rfl
      simp [preservesLocalizationCatOfOver, ← this, Scheme.Hom.app_eq_appLE]
    · intros g h α
      ext
      dsimp [preservesLocalizationCatToOver]
      ext
      simpa [preservesLocalizationCatOfOver, ← Spec.map_comp_assoc, -Spec.map_comp,
        Scheme.Hom.app_eq_appLE] using IsAffineOpen.SpecMap_appLE_fromSpec _ _ _ _
  functor_unitIso_comp F := by
    ext
    dsimp [preservesLocalizationCatToOver]
    ext
    dsimp [preservesLocalizationCatOfOver]
    simp only [ι_colimMap_assoc, colimit.ι_desc]
    dsimp
    simp only [eqToHom_op, Hom.appIso_hom', Hom.map_appLE_assoc, Spec.map_comp,
      SpecMap_ΓSpecIso_hom, Category.assoc, Category.comp_id]
    rw [IsAffineOpen.SpecMap_appLE_fromSpec (hV := isAffineOpen_top _), IsAffineOpen.fromSpec_top,
      isoSpec_Spec_inv, toSpecΓ_SpecMap_ΓSpecIso_inv_assoc]

attribute [simps! functor_obj_left functor_obj_hom functor_map_hom_left counitIso_hom_app_hom_left]
  preservesLocalizationCatEquivOver

@[simp]
lemma preservesLocalizationCatEquivOver_inverse_obj_unop_obj_right_obj
    (Y : MorphismProperty.Over @IsAffineHom ⊤ X) (U : X.AffineZariskiSiteᵒᵖ) :
    (X.preservesLocalizationCatEquivOver.inverse.obj Y).unop.obj.right.obj U =
      Γ(Y.left, Y.hom ⁻¹ᵁ U.unop.toOpens) := rfl

@[simp]
lemma preservesLocalizationCatEquivOver_inverse_obj_unop_obj_right_map
    (Y : MorphismProperty.Over @IsAffineHom ⊤ X) {U V : X.AffineZariskiSiteᵒᵖ} (i : U ⟶ V) :
    (X.preservesLocalizationCatEquivOver.inverse.obj Y).unop.obj.right.map i =
      Y.left.presheaf.map (homOfLE (Y.hom.preimage_mono (toOpens_mono i.unop.le))).op := rfl

@[simp]
lemma preservesLocalizationCatEquivOver_inverse_obj_unop_obj_hom_app
    (Y : MorphismProperty.Over @IsAffineHom ⊤ X) (U : X.AffineZariskiSiteᵒᵖ) :
    (X.preservesLocalizationCatEquivOver.inverse.obj Y).unop.obj.hom.app U =
      Y.hom.app U.unop.toOpens := rfl

@[simp]
lemma preservesLocalizationCatEquivOver_inverse_map_unop_hom_right_app
    {Y Z : MorphismProperty.Over @IsAffineHom ⊤ X} (f : Y ⟶ Z) (U : X.AffineZariskiSiteᵒᵖ) :
    (X.preservesLocalizationCatEquivOver.inverse.map f).unop.hom.right.app U =
    f.hom.left.appLE _ _ congr(($(MorphismProperty.Over.w f)) ⁻¹ᵁ U.unop.1).ge := rfl

@[simp]
lemma preservesLocalizationCatEquivOver_unitIso_hom_app_unop_hom_right_app
    (F : X.PreservesLocalizationCatᵒᵖ) (U) :
    (X.preservesLocalizationCatEquivOver.unitIso.hom.app F).unop.hom.right.app U =
    (colimit.ι (F.unop.obj.right.rightOp ⋙ Scheme.Spec) U.unop).appLE _ ⊤
      (by simp [← Scheme.Hom.comp_preimage]) ≫ (ΓSpecIso _).hom := by
  dsimp [preservesLocalizationCatEquivOver]
  simp [Hom.appIso_hom']
  rfl

instance : HasLimits (MorphismProperty.Over @IsAffineHom ⊤ X) :=
  hasLimits_of_hasLimits_createsLimits X.preservesLocalizationCatEquivOver.inverse

end Equivalence

section PreservesLimits

/-- Under the equivalence of categories between affine `X`-schemes and quasi-coherent `𝒪ₓ`-algebras,
the pullback functor on affine `X`-schemes along an open immersion `U ⟶ X` corresponds
to the restriction functor `F ↦ F|ᵤ` of quasi-coherent `𝒪ₓ`-algebras. -/
noncomputable def preservesLocalizationCatRestrict [IsOpenImmersion f] :
    Y.preservesLocalizationCatEquivOver.inverse ⋙ Y.preservesLocalizationCatForget.op ⋙
      (Under.post ((Functor.whiskeringLeft _ _ _).obj (AffineZariskiSite.image f).op) ⋙
      Under.map ((toOpensFunctor X).op.whiskerLeft (IsOpenImmersion.presheafIso f).hom)).op ≅
    MorphismProperty.Over.pullback @IsAffineHom ⊤ f ⋙
      X.preservesLocalizationCatEquivOver.inverse ⋙ X.preservesLocalizationCatForget.op := by
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

attribute [local instance] preservesLimitsOfSize_op in
-- This is true for arbitrary `f`. The instance is provided at the end of the file.
private instance [IsOpenImmersion f] :
    PreservesLimits (MorphismProperty.Over.pullback @IsAffineHom ⊤ f) := by
  suffices PreservesLimits (Y.preservesLocalizationCatEquivOver.functor ⋙
      MorphismProperty.Over.pullback @IsAffineHom ⊤ f) by
    exact preservesLimits_of_natIso (F := _ ⋙ Y.preservesLocalizationCatEquivOver.functor ⋙
      MorphismProperty.Over.pullback @IsAffineHom ⊤ f)
      (Functor.isoWhiskerRight Y.preservesLocalizationCatEquivOver.counitIso
        (MorphismProperty.Over.pullback @IsAffineHom ⊤ f))
  suffices PreservesLimits ((Y.preservesLocalizationCatEquivOver.functor ⋙
      MorphismProperty.Over.pullback @IsAffineHom ⊤ f) ⋙
      X.preservesLocalizationCatEquivOver.inverse ⋙ X.preservesLocalizationCatForget.op)
    from preservesLimits_of_reflects_of_preserves _
      (X.preservesLocalizationCatEquivOver.inverse ⋙ X.preservesLocalizationCatForget.op)
  let FF : Under ((toOpensFunctor Y).op ⋙ Y.presheaf) ⥤
      Under ((toOpensFunctor X).op ⋙ X.presheaf) :=
    Under.post ((Functor.whiskeringLeft _ _ _).obj (AffineZariskiSite.image f).op) ⋙ Under.map
    ((toOpensFunctor X).op.whiskerLeft (IsOpenImmersion.presheafIso f).hom)
  exact preservesLimits_of_natIso ((preservesLocalizationCatRestrict f).isoInverseComp
      (G := Y.preservesLocalizationCatEquivOver.symm))

instance : PreservesLimits (MorphismProperty.Over.forget @IsAffineHom ⊤ X) := by
  clear Y f
  wlog hX : IsAffine X
  · exact ⟨fun {J} _ ↦ ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨isLimitOverOfOpenCover _ X.affineCover fun i ↦
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
