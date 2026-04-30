/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
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

variable {X : Scheme.{u}}

variable (I : IdealSheafData X)

/-- `Spec (𝒪ₓ(U)/I(U))`, the object to be glued into the closed subscheme. -/
noncomputable
def glueDataObj (U : X.affineOpens) : Scheme :=
  Spec <| .of <| Γ(X, U) ⧸ I.ideal U

/-- `Spec (𝒪ₓ(U)/I(U)) ⟶ Spec (𝒪ₓ(U)) = U`, the closed immersion into `U`. -/
noncomputable
def glueDataObjι (U : X.affineOpens) : I.glueDataObj U ⟶ U.1 :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ U.2.isoSpec.inv

set_option backward.isDefEq.respectTransparency false in
instance (U : X.affineOpens) : IsPreimmersion (I.glueDataObjι U) :=
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)))) :=
    .mk_SpecMap
      (isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).isEmbedding
      (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
  .comp _ _

lemma glueDataObjι_ι (U : X.affineOpens) : I.glueDataObjι U ≫ U.1.ι =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ U.2.fromSpec := by
  rw [glueDataObjι, Category.assoc]; rfl

lemma ker_glueDataObjι_appTop (U : X.affineOpens) :
    RingHom.ker (I.glueDataObjι U).appTop.hom = (I.ideal U).comap U.1.topIso.hom.hom := by
  let φ : Γ(X, U) ⟶ CommRingCat.of (Γ(X, U) ⧸ I.ideal U) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))
  rw [← Ideal.mk_ker (I := I.ideal _)]
  change RingHom.ker (Spec.map φ ≫ _).appTop.hom = (RingHom.ker φ.hom).comap _
  rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv, RingHom.comap_ker,
    RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp]
  congr 2
  simp only [Scheme.Hom.comp_app, TopologicalSpace.Opens.map_top, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.Opens.topIso_hom]
  rw [← Scheme.Hom.appTop, U.2.isoSpec_inv_appTop, Category.assoc, Iso.inv_hom_id_assoc]
  simp only [Scheme.Opens.topIso_hom]

open scoped Set.Notation in
lemma range_glueDataObjι (U : X.affineOpens) :
    Set.range (I.glueDataObjι U) =
      U.2.isoSpec.inv '' PrimeSpectrum.zeroLocus (I.ideal U) := by
  simp only [glueDataObjι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  erw [range_comap_of_surjective]
  swap; · exact Ideal.Quotient.mk_surjective
  simp
  rfl

lemma range_glueDataObjι_ι (U : X.affineOpens) :
    Set.range (I.glueDataObjι U ≫ U.1.ι) = X.zeroLocus (U := U) (I.ideal U) ∩ U := by
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_glueDataObjι]
  rw [← Set.image_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, IsAffineOpen.isoSpec_inv_ι,
    IsAffineOpen.fromSpec_image_zeroLocus]

/-- The underlying space of `Spec (𝒪ₓ(U)/I(U))` is homeomorphic to its image in `X`. -/
noncomputable
def glueDataObjCarrierIso (U : X.affineOpens) :
    (I.glueDataObj U).carrier ≅ TopCat.of ↑(X.zeroLocus (U := U) (I.ideal U) ∩ U) :=
  TopCat.isoOfHomeo ((I.glueDataObjι U ≫ U.1.ι).isEmbedding.toHomeomorph.trans
    (.setCongr (I.range_glueDataObjι_ι U)))

/-- The open immersion `Spec Γ(𝒪ₓ/I, U) ⟶ Spec Γ(𝒪ₓ/I, V)` if `U ≤ V`. -/
noncomputable
def glueDataObjMap {U V : X.affineOpens} (h : U ≤ V) : I.glueDataObj U ⟶ I.glueDataObj V :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)))

lemma isLocalization_away {U V : X.affineOpens}
    (h : U ≤ V) (f : Γ(X, V.1)) (hU : U = X.affineBasicOpen f) :
      letI := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)).toAlgebra
      IsLocalization.Away (Ideal.Quotient.mk (I.ideal V) f) (Γ(X, U) ⧸ (I.ideal U)) := by
  letI := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)).toAlgebra
  letI := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  have : IsLocalization.Away f Γ(X, U) := by
    subst hU; exact V.2.isLocalization_of_eq_basicOpen _ _ rfl
  simp only [IsLocalization.Away, ← Submonoid.map_powers]
  refine IsLocalization.of_surjective _ _ _ Ideal.Quotient.mk_surjective _
    Ideal.Quotient.mk_surjective ?_ ?_
  · simp [RingHom.algebraMap_toAlgebra, Ideal.quotientMap_comp_mk]; rfl
  · simp only [Ideal.mk_ker, RingHom.algebraMap_toAlgebra, I.map_ideal', le_refl]

instance isOpenImmersion_glueDataObjMap {V : X.affineOpens} (f : Γ(X, V.1)) :
    IsOpenImmersion (I.glueDataObjMap (X.affineBasicOpen_le f)) := by
  letI := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal (X.affineBasicOpen_le f))).toAlgebra
  have := I.isLocalization_away (X.affineBasicOpen_le f) f rfl
  exact IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk _ f)

lemma opensRange_glueDataObjMap {V : X.affineOpens} (f : Γ(X, V.1)) :
      (I.glueDataObjMap (X.affineBasicOpen_le f)).opensRange =
        (I.glueDataObjι V) ⁻¹ᵁ (V.1.ι ⁻¹ᵁ X.basicOpen f) := by
  letI := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal (X.affineBasicOpen_le f))).toAlgebra
  let f' : Γ(X, V) ⧸ I.ideal V := Ideal.Quotient.mk _ f
  have := I.isLocalization_away (X.affineBasicOpen_le f) f rfl
  ext1
  refine (localization_away_comap_range _ f').trans ?_
  rw [← comap_basicOpen, ← V.2.fromSpec_preimage_basicOpen,
    ← Scheme.Hom.comp_preimage, glueDataObjι_ι]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma glueDataObjMap_glueDataObjι {U V : X.affineOpens} (h : U ≤ V) :
    I.glueDataObjMap h ≫ I.glueDataObjι V = I.glueDataObjι U ≫ X.homOfLE h := by
  rw [glueDataObjMap, glueDataObjι, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    Ideal.quotientMap_comp_mk, CommRingCat.ofHom_comp, Spec.map_comp_assoc, glueDataObjι,
    Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp, IsAffineOpen.isoSpec_hom]
  dsimp
  erw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc U.1 V.1 h]
  rw [← IsAffineOpen.isoSpec_hom V.2, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
lemma ideal_le_ker_glueDataObjι (U V : X.affineOpens) :
    I.ideal V ≤ RingHom.ker (U.1.ι.app V.1 ≫ (I.glueDataObjι U).app _).hom := by
  intro x hx
  apply (I.glueDataObj U).IsSheaf.section_ext
  intro p hp
  obtain ⟨f, g, hfg, hf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 (I.glueDataObjι U p).1
      ⟨(I.glueDataObjι U p).2, hp⟩
  refine ⟨(I.glueDataObjι U ⁻¹ᵁ U.1.ι ⁻¹ᵁ X.basicOpen f),
    fun x hx ↦ X.basicOpen_le g (hfg ▸ hx), hf, ?_⟩
  have := Hom.isIso_app (I.glueDataObjMap (X.affineBasicOpen_le f))
    (I.glueDataObjι U ⁻¹ᵁ U.1.ι ⁻¹ᵁ X.basicOpen f) (by rw [opensRange_glueDataObjMap])
  apply ((ConcreteCategory.isIso_iff_bijective _).mp this).1
  simp only [map_zero, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Category.assoc]
  simp only [Scheme.Hom.app_eq_appLE, homOfLE_leOfHom, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_comp_appLE, Category.assoc, glueDataObjMap_glueDataObjι_assoc]
  rw [Scheme.Hom.appLE]
  have H : (X.homOfLE (X.basicOpen_le f) ≫ U.1.ι) ⁻¹ᵁ V.1 = ⊤ := by
    simp only [Scheme.homOfLE_ι, ← top_le_iff]
    exact fun x _ ↦ (hfg.trans_le (X.basicOpen_le g)) x.2
  simp only [Scheme.Hom.comp_app, Scheme.Opens.ι_app, Scheme.homOfLE_app, ← Functor.map_comp_assoc,
    Scheme.Hom.app_eq _ H, Scheme.Opens.toScheme_presheaf_map, ← Functor.map_comp, Category.assoc]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  convert RingHom.map_zero _ using 2
  rw [← RingHom.mem_ker, ker_glueDataObjι_appTop, ← Ideal.mem_comap, Ideal.comap_comap,
    ← CommRingCat.hom_comp]
  simp only [Scheme.affineBasicOpen_coe, homOfLE_leOfHom, Scheme.Hom.comp_base,
    TopologicalSpace.Opens.map_comp_obj, eqToHom_op, eqToHom_unop, ← Functor.map_comp,
    Scheme.Opens.topIso_hom, Category.assoc]
  exact I.ideal_le_comap_ideal (U := X.affineBasicOpen f) (V := V)
    (hfg.trans_le (X.basicOpen_le g)) hx

/-- (Implementation) The intersections `Spec Γ(𝒪ₓ/I, U) ∩ V` useful for gluing. -/
private noncomputable
abbrev glueDataObjPullback (U V : X.affineOpens) : Scheme :=
  pullback (I.glueDataObjι U) (X.homOfLE (U := U.1 ⊓ V.1) inf_le_left)

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) Transition maps in the glue data for `𝒪ₓ/I`. -/
private noncomputable
def glueDataT (U V : X.affineOpens) :
    I.glueDataObjPullback U V ⟶ I.glueDataObjPullback V U := by
  letI F := pullback.snd (I.glueDataObjι U) (X.homOfLE (inf_le_left (b := V.1)))
  refine pullback.lift ((F ≫ X.homOfLE inf_le_right ≫
    V.2.isoSpec.hom).liftQuotient _ ?_) (F ≫ X.homOfLE (by simp)) ?_
  · intro x hx
    simp only [Hom.comp_app, Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
      TopologicalSpace.Opens.map_top, homOfLE_app, homOfLE_leOfHom, Category.assoc, RingHom.mem_ker]
    convert_to (U.1.ι.app V.1 ≫ (F ≫ X.homOfLE inf_le_left).appLE (U.1.ι ⁻¹ᵁ V.1) ⊤
      (by rw [← Scheme.Hom.comp_preimage, Category.assoc, X.homOfLE_ι]
          exact fun x _ ↦ by simpa using (F x).2.2)).hom x = 0 using 3
    · simp only [homOfLE_leOfHom, Opens.ι_app, Hom.comp_appLE, homOfLE_app]
      have H : ⊤ ≤ X.homOfLE (inf_le_left (b := V.1)) ⁻¹ᵁ U.1.ι ⁻¹ᵁ V.1 := by
        rw [← Scheme.Hom.comp_preimage, X.homOfLE_ι]; exact fun x _ ↦ by simpa using x.2.2
      rw [← F.map_appLE (show ⊤ ≤ F ⁻¹ᵁ ⊤ from le_rfl) (homOfLE H).op]
      simp only [homOfLE_leOfHom, Opens.toScheme_presheaf_map, Quiver.Hom.unop_op,
        Hom.opensFunctor_map_homOfLE, ← Functor.map_comp_assoc, IsAffineOpen.isoSpec_hom_appTop,
        Opens.topIso_inv, eqToHom_op, homOfLE_leOfHom, Category.assoc,
        Iso.inv_hom_id_assoc, F.app_eq_appLE]
      rfl
    · have : (U.1.ι.app V.1 ≫ (I.glueDataObjι U).app (U.1.ι ⁻¹ᵁ V.1)).hom x = 0 :=
        I.ideal_le_ker_glueDataObjι U V hx
      simp_rw [F, ← pullback.condition]
      simp only [Scheme.Opens.ι_app, CommRingCat.hom_comp, RingHom.coe_comp,
        Function.comp_apply, Scheme.Hom.appLE, Scheme.Hom.comp_app, Category.assoc] at this ⊢
      simp only [this, map_zero]
  · conv_lhs => enter [2]; rw [glueDataObjι]
    rw [Scheme.Hom.liftQuotient_comp_assoc, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.assoc, X.homOfLE_homOfLE]

@[reassoc (attr := simp)]
private lemma glueDataT_snd (U V : X.affineOpens) :
    I.glueDataT U V ≫ pullback.snd _ _ = pullback.snd _ _ ≫ X.homOfLE (by simp) :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma glueDataT_fst (U V : X.affineOpens) :
    I.glueDataT U V ≫ pullback.fst _ _ ≫ glueDataObjι _ _ =
      pullback.snd _ _ ≫ X.homOfLE inf_le_right := by
  refine (pullback.lift_fst_assoc _ _ _ _).trans ?_
  conv_lhs => enter [2]; rw [glueDataObjι]
  rw [Scheme.Hom.liftQuotient_comp_assoc, Category.assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- (Implementation) `t'` in the glue data for `𝒪ₓ/I`. -/
private noncomputable
def glueDataT'Aux (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W ≤ U₀) :
    pullback
      (pullback.fst _ _ : I.glueDataObjPullback U V ⟶ _)
      (pullback.fst _ _ : I.glueDataObjPullback U W ⟶ _) ⟶ I.glueDataObjPullback V U₀ :=
  pullback.lift
    (pullback.fst _ _ ≫ I.glueDataT U V ≫ pullback.fst _ _)
    (IsOpenImmersion.lift (V.1 ⊓ U₀.1).ι
      (pullback.fst _ _ ≫ pullback.fst _ _ ≫ I.glueDataObjι U ≫ U.1.ι) (by
      simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_inf, Set.subset_inter_iff]
      constructor
      · rw [pullback.condition_assoc (f := I.glueDataObjι U), X.homOfLE_ι,
          ← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp]
        exact (Set.range_comp_subset_range _ _).trans (by simp)
      · rw [pullback.condition_assoc, pullback.condition_assoc, X.homOfLE_ι,
          ← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp]
        exact (Set.range_comp_subset_range _ _).trans (by simpa using hU₀))) (by
      rw [← cancel_mono (Scheme.Opens.ι _)]
      simp [pullback.condition_assoc])

@[reassoc (attr := simp)]
private lemma glueDataT'Aux_fst (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W ≤ U₀) :
    I.glueDataT'Aux U V W U₀ hU₀ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ I.glueDataT U V ≫ pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private lemma glueDataT'Aux_snd_ι (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W ≤ U₀) :
    I.glueDataT'Aux U V W U₀ hU₀ ≫ pullback.snd _ _ ≫ (V.1 ⊓ U₀.1).ι =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ I.glueDataObjι U ≫ U.1.ι :=
  (pullback.lift_snd_assoc _ _ _ _).trans (IsOpenImmersion.lift_fac _ _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/-- (Implementation) The glue data for `𝒪ₓ/I`. -/
@[simps]
private noncomputable
def glueData : Scheme.GlueData where
  J := X.affineOpens
  U := I.glueDataObj
  V ij := I.glueDataObjPullback ij.1 ij.2
  f i j := pullback.fst _ _
  f_id i :=
    have : IsIso (X.homOfLE (inf_le_left (a := i.1) (b := i.1))) :=
      ⟨X.homOfLE (by simp), by simp, by simp⟩
    inferInstance
  t i j := I.glueDataT i j
  t_id i := by
    apply pullback.hom_ext
    · rw [← cancel_mono (glueDataObjι _ _)]
      simp [pullback.condition]
    · simp
  t' i j k := pullback.lift
    (I.glueDataT'Aux _ _ _ _ inf_le_right) (I.glueDataT'Aux _ _ _ _ inf_le_left) (by simp)
  t_fac i j k := by
    apply pullback.hom_ext
    · rw [← cancel_mono (glueDataObjι _ _)]
      simp
    · rw [← cancel_mono (Scheme.Opens.ι _)]
      simp [pullback.condition_assoc]
  cocycle i j k := by
    dsimp only
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [← cancel_mono (glueDataObjι _ _), ← cancel_mono (Scheme.Opens.ι _)]
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          glueDataT'Aux_fst, limit.lift_π_assoc, cospan_left, glueDataT_fst, Scheme.homOfLE_ι,
          glueDataT'Aux_snd_ι, glueDataT'Aux_fst_assoc, glueDataT_fst_assoc, Category.id_comp]
        rw [pullback.condition_assoc (f := I.glueDataObjι i)]
        simp
      · rw [← cancel_mono (Scheme.Opens.ι _)]
        simp [pullback.condition_assoc]
    · apply pullback.hom_ext
      · rw [← cancel_mono (glueDataObjι _ _), ← cancel_mono (Scheme.Opens.ι _)]
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          glueDataT'Aux_fst, limit.lift_π_assoc, cospan_left, glueDataT_fst, Scheme.homOfLE_ι,
          glueDataT'Aux_snd_ι, glueDataT'Aux_fst_assoc, glueDataT_fst_assoc, Category.id_comp]
        rw [← pullback.condition_assoc, pullback.condition_assoc (f := I.glueDataObjι i),
          X.homOfLE_ι]
      · rw [← cancel_mono (Scheme.Opens.ι _)]
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          glueDataT'Aux_snd_ι, limit.lift_π_assoc, cospan_left, glueDataT'Aux_fst_assoc,
          glueDataT_fst_assoc, Scheme.homOfLE_ι, Category.id_comp]
        rw [pullback.condition_assoc, pullback.condition_assoc, X.homOfLE_ι]
  f_open i j := inferInstance

set_option backward.privateInPublic true in
/-- (Implementation) The map from `Spec(𝒪ₓ/I)` to `X`. See `IdealSheafData.subschemeι` instead. -/
private noncomputable
def gluedTo : I.glueData.glued ⟶ X :=
  Multicoequalizer.desc _ _ (fun i ↦ I.glueDataObjι i ≫ i.1.ι)
    (by simp [GlueData.diagram, pullback.condition_assoc])

@[reassoc (attr := simp)]
private lemma ι_gluedTo (U : X.affineOpens) :
    I.glueData.ι U ≫ I.gluedTo = I.glueDataObjι U ≫ U.1.ι :=
  Multicoequalizer.π_desc _ _ _ _ _

@[reassoc (attr := simp)]
private lemma glueDataObjMap_ι (U V : X.affineOpens) (h : U ≤ V) :
    I.glueDataObjMap h ≫ I.glueData.ι V = I.glueData.ι U := by
  have : IsIso (X.homOfLE inf_le_left : (U.1 ⊓ V.1).toScheme ⟶ U) :=
    ⟨X.homOfLE (by simpa), by simp, by simp⟩
  have H : inv (X.homOfLE inf_le_left : (U.1 ⊓ V.1).toScheme ⟶ U) = X.homOfLE (by simpa) := by
    rw [eq_comm, ← hom_comp_eq_id]; simp
  have := I.glueData.glue_condition U V
  simp only [glueData_J, glueData_V, glueData_t, glueData_U, glueData_f] at this
  rw [← IsIso.inv_comp_eq] at this
  rw [← Category.id_comp (I.glueData.ι U), ← this]
  simp_rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (glueDataObjι _ _)]
  simp [pullback_inv_fst_snd_of_right_isIso_assoc, H]

set_option backward.isDefEq.respectTransparency false in
private lemma gluedTo_injective :
    Function.Injective I.gluedTo := by
  intro a b e
  obtain ⟨ia, a : I.glueDataObj ia, rfl⟩ :=
    I.glueData.toGlueData.ι_jointly_surjective forget a
  obtain ⟨ib, b : I.glueDataObj ib, rfl⟩ :=
    I.glueData.toGlueData.ι_jointly_surjective forget b
  change I.glueData.ι ia a = I.glueData.ι ib b
  have : (I.glueDataObjι ia a).1 = (I.glueDataObjι ib b).1 := by
    have : (I.glueData.ι ia ≫ I.gluedTo) a = (I.glueData.ι ib ≫ I.gluedTo) b := e
    rwa [ι_gluedTo, ι_gluedTo] at this
  obtain ⟨f, g, hfg, H⟩ := exists_basicOpen_le_affine_inter ia.2 ib.2
    (I.glueDataObjι ia a).1
      ⟨(I.glueDataObjι ia a).2, this ▸ (I.glueDataObjι ib b).2⟩
  have hmem (W) (hW : W = X.affineBasicOpen g) :
      b ∈ Set.range (I.glueDataObjMap (hW.trans_le (X.affineBasicOpen_le g))) := by
    subst hW
    refine (I.opensRange_glueDataObjMap g).ge ?_
    change (I.glueDataObjι ib b).1 ∈ X.basicOpen g
    rwa [← this, ← hfg]
  obtain ⟨a, rfl⟩ := (I.opensRange_glueDataObjMap f).ge H
  obtain ⟨b, rfl⟩ := hmem (X.affineBasicOpen f) (Subtype.ext hfg)
  simp only [glueData_U, ← Scheme.Hom.comp_apply, glueDataObjMap_glueDataObjι] at this ⊢
  simp only [Scheme.affineBasicOpen_coe, Scheme.Hom.comp_base, TopCat.comp_app,
    Scheme.homOfLE_apply, SetLike.coe_eq_coe] at this
  obtain rfl := (I.glueDataObjι (X.affineBasicOpen f)).isEmbedding.injective this
  simp only [glueDataObjMap_ι]

lemma range_glueDataObjι_ι_eq_support_inter (U : X.affineOpens) :
    Set.range (I.glueDataObjι U ≫ U.1.ι) = (I.support : Set X) ∩ U :=
  (I.range_glueDataObjι_ι U).trans (I.coe_support_inter U).symm

private lemma range_gluedTo :
    Set.range I.gluedTo = I.support := by
  refine subset_antisymm (Set.range_subset_iff.mpr fun x ↦ ?_) ?_
  · obtain ⟨ix, x : I.glueDataObj ix, rfl⟩ :=
      I.glueData.toGlueData.ι_jointly_surjective forget x
    change (I.glueData.ι _ ≫ I.gluedTo) x ∈ I.support
    rw [ι_gluedTo]
    exact ((I.range_glueDataObjι_ι_eq_support_inter ix).le ⟨_, rfl⟩).1
  · intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    obtain ⟨y, rfl⟩ := (I.range_glueDataObjι_ι_eq_support_inter ⟨U, hU⟩).ge ⟨hx, hxU⟩
    rw [← ι_gluedTo]
    exact ⟨_, rfl⟩

set_option backward.isDefEq.respectTransparency false in
private lemma range_glueData_ι (U : X.affineOpens) :
    Set.range (Scheme.Hom.toLRSHom' (X := I.glueDataObj U) <|
      I.glueData.ι U).base = (I.gluedTo ⁻¹ᵁ U : Set I.glueData.glued) := by
  simp only [TopologicalSpace.Opens.map_coe]
  apply I.gluedTo_injective.image_injective
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, ι_gluedTo,
    range_glueDataObjι_ι, Set.image_preimage_eq_inter_range, range_gluedTo,
    ← coe_support_inter, Set.inter_comm]

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) identifying `Spec(Γ(X, U)/I(U))` with its image in `Spec(𝒪ₓ/I)`. -/
private noncomputable
def glueDataObjIso (U : X.affineOpens) :
    I.glueDataObj U ≅ I.gluedTo ⁻¹ᵁ U :=
  IsOpenImmersion.isoOfRangeEq (I.glueData.ι U) (Scheme.Opens.ι _) (by
    simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.map_coe, range_glueData_ι])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma glueDataObjIso_hom_ι (U : X.affineOpens) :
    (I.glueDataObjIso U).hom ≫ (I.gluedTo ⁻¹ᵁ U).ι = I.glueData.ι U :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

set_option backward.isDefEq.respectTransparency false in
private lemma glueDataObjIso_hom_restrict (U : X.affineOpens) :
    (I.glueDataObjIso U).hom ≫ I.gluedTo ∣_ ↑U = I.glueDataObjι U := by
  rw [← cancel_mono U.1.ι]; simp

private instance : IsPreimmersion I.gluedTo := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsPreimmersion)
    _ (iSup_affineOpens_eq_top X)]
  intro U
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsPreimmersion (I.glueDataObjIso U).hom,
    glueDataObjIso_hom_restrict]
  infer_instance

private instance : QuasiCompact I.gluedTo :=
  ⟨fun _ _ ↦ (Topology.IsClosedEmbedding.isProperMap
    ⟨I.gluedTo.isEmbedding, I.range_gluedTo ▸ I.support.isClosed⟩).isCompact_preimage⟩

set_option backward.privateInPublic true in
/-- (Implementation) The underlying space of `Spec(𝒪ₓ/I)` is homeomorphic to the support of `I`. -/
private noncomputable
def gluedHomeo : I.glueData.glued ≃ₜ I.support :=
  I.gluedTo.isEmbedding.toHomeomorph.trans (.setCongr I.range_gluedTo)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The subscheme associated to an ideal sheaf. -/
noncomputable
def subscheme : Scheme :=
  I.glueData.glued.restrict
    (f := TopCat.ofHom (toContinuousMap I.gluedHomeo.symm))
    I.gluedHomeo.symm.isOpenEmbedding

set_option backward.isDefEq.respectTransparency false in
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
  (I.subschemeIso.hom ≫ I.gluedTo).copyBase Subtype.val <| by
    ext x
    change (I.gluedHomeo (I.gluedHomeo.symm x)).1 = x.1
    rw [I.gluedHomeo.apply_symm_apply]

lemma subschemeι_apply (x : I.subscheme) : I.subschemeι x = x.1 := rfl

private lemma subschemeι_def : I.subschemeι = I.subschemeIso.hom ≫ I.gluedTo :=
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
  simp [← range_gluedTo, I.subschemeι_def, Set.range_comp]

private lemma opensRange_glueData_ι_subschemeIso_inv (U : X.affineOpens) :
    (I.glueData.ι U ≫ I.subschemeIso.inv).opensRange = I.subschemeι ⁻¹ᵁ U := by
  ext1
  simp [Set.range_comp, I.range_glueData_ι, subschemeι_def, ← coe_homeoOfIso_symm,
    ← homeoOfIso_symm, ← Homeomorph.coe_symm_toEquiv, Equiv.image_symm_eq_preimage]

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The subscheme associated to an ideal sheaf `I` is covered by `Spec(Γ(X, U)/I(U))`. -/
noncomputable
def subschemeCover : I.subscheme.AffineOpenCover where
  I₀ := X.affineOpens
  X U := .of <| Γ(X, U) ⧸ I.ideal U
  f U := I.glueData.ι U ≫ I.subschemeIso.inv
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

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma subschemeCover_map_subschemeι (U : X.affineOpens) :
    I.subschemeCover.f U ≫ I.subschemeι = I.glueDataObjι U ≫ U.1.ι := by
  simp [subschemeCover, subschemeι_def]

set_option backward.isDefEq.respectTransparency false in
/-- `Γ(𝒪ₓ/I, U) ≅ 𝒪ₓ(U)/I(U)`. -/
noncomputable
def subschemeObjIso (U : X.affineOpens) :
    Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) ≅ .of (Γ(X, U) ⧸ I.ideal U) :=
  I.subscheme.presheaf.mapIso (eqToIso (by simp)).op ≪≫
    (I.subschemeCover.f U).appIso _ ≪≫ Scheme.ΓSpecIso (.of (Γ(X, U) ⧸ I.ideal U))

set_option backward.isDefEq.respectTransparency false in
lemma subschemeι_app (U : X.affineOpens) : I.subschemeι.app U =
    CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)) ≫
    (I.subschemeObjIso U).inv := by
  have := I.subschemeCover_map_subschemeι U
  simp only [glueDataObjι, Category.assoc, IsAffineOpen.isoSpec_inv_ι] at this
  replace this := Scheme.Hom.congr_app this U
  simp only [Hom.comp_base, TopologicalSpace.Opens.map_comp_obj, Hom.comp_app,
    IsAffineOpen.fromSpec_app_self, eqToHom_op, Category.assoc, Hom.naturality_assoc,
    TopologicalSpace.Opens.map_top, ← ΓSpecIso_inv_naturality_assoc] at this
  simp_rw [← Category.assoc, ← IsIso.comp_inv_eq] at this
  simp only [← this, ← Functor.map_inv, inv_eqToHom, Category.assoc, eqToHom_unop,
    ← Functor.map_comp, IsIso.Iso.inv_inv, subschemeObjIso, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, eqToIso.inv, eqToHom_op, Iso.hom_inv_id_assoc, Hom.appIso_inv_naturality_assoc,
    Functor.op_obj, Functor.op_map, unop_comp, unop_inv, Quiver.Hom.unop_op,
    Hom.app_appIso_inv_assoc, TopologicalSpace.Opens.carrier_eq_coe, TopologicalSpace.Opens.map_coe,
    homOfLE_leOfHom]
  convert (Category.comp_id _).symm
  exact CategoryTheory.Functor.map_id _ _

lemma subschemeι_app_surjective (U : X.affineOpens) :
    Function.Surjective (I.subschemeι.app U) := by
  rw [I.subschemeι_app U]
  exact (I.subschemeObjIso U).commRingCatIsoToRingEquiv.symm.surjective.comp
    Ideal.Quotient.mk_surjective

set_option backward.isDefEq.respectTransparency false in
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
noncomputable
def glueDataObjHom {I J : IdealSheafData X} (h : I ≤ J) (U) :
    J.glueDataObj U ⟶ I.glueDataObj U :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (h U)))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma glueDataObjHom_ι {I J : IdealSheafData X} (h : I ≤ J) (U) :
    glueDataObjHom h U ≫ I.glueDataObjι U = J.glueDataObjι U := by
  rw [glueDataObjHom, glueDataObjι, glueDataObjι, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.factor_comp_mk]

@[simp]
lemma glueDataObjHom_id {I : IdealSheafData X} (U) :
    glueDataObjHom (le_refl I) U = 𝟙 _ := by
  rw [← cancel_mono (I.glueDataObjι U)]
  simp

@[reassoc (attr := simp)]
lemma glueDataObjHom_comp {I J K : IdealSheafData X} (hIJ : I ≤ J) (hJK : J ≤ K) (U) :
    glueDataObjHom hJK U ≫ glueDataObjHom hIJ U = glueDataObjHom (hIJ.trans hJK) U := by
  rw [← cancel_mono (I.glueDataObjι U)]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of ideal sheaf induces an inclusion of subschemes -/
noncomputable
def inclusion {I J : IdealSheafData X} (h : I ≤ J) :
    J.subscheme ⟶ I.subscheme :=
  J.subschemeCover.openCover.glueMorphisms (fun U ↦ glueDataObjHom h U ≫ I.subschemeCover.f U)
  (by
    intro U V
    simp only [← cancel_mono I.subschemeι, AffineOpenCover.openCover_X, glueDataObjHom_ι_assoc,
      AffineOpenCover.openCover_f, Category.assoc, subschemeCover_map_subschemeι]
    rw [← subschemeCover_map_subschemeι, pullback.condition_assoc, subschemeCover_map_subschemeι])

@[reassoc (attr := simp)]
lemma subSchemeCover_map_inclusion {I J : IdealSheafData X} (h : I ≤ J) (U) :
    J.subschemeCover.f U ≫ inclusion h = glueDataObjHom h U ≫ I.subschemeCover.f U :=
  J.subschemeCover.openCover.ι_glueMorphisms _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inclusion_subschemeι {I J : IdealSheafData X} (h : I ≤ J) :
    inclusion h ≫ I.subschemeι = J.subschemeι :=
  J.subschemeCover.openCover.hom_ext _ _ fun _ ↦ by simp

@[simp, reassoc]
lemma inclusion_id (I : IdealSheafData X) :
    inclusion le_rfl = 𝟙 I.subscheme :=
  I.subschemeCover.openCover.hom_ext _ _ fun _ ↦ by simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inclusion_comp {I J K : IdealSheafData X} (h₁ : I ≤ J) (h₂ : J ≤ K) :
    inclusion h₂ ≫ inclusion h₁ = inclusion (h₁.trans h₂) :=
  K.subschemeCover.openCover.hom_ext _ _ fun _ ↦ by simp

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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
private noncomputable
def Hom.toImageAux : X ⟶ f.image :=
  Cover.glueMorphisms ((Y.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top Y)).pullback₁ f)
    (fun U ↦ (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).liftQuotient _
      (by exact ideal_ker_le_ker_ΓSpecIso_inv_comp f U) ≫ f.ker.subschemeCover.f U) (by
    intro U V
    rw [← cancel_mono f.imageι]
    simp [IdealSheafData.glueDataObjι, Scheme.Hom.liftQuotient_comp_assoc,
      ← pullback.condition, ← pullback.condition_assoc])

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
private lemma Hom.toImageAux_spec :
    f.toImageAux ≫ f.imageι = f := by
  apply Cover.hom_ext ((Y.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top Y)).pullback₁ f)
  intro U
  simp only [Hom.toImageAux, Cover.ι_glueMorphisms_assoc]
  simp [IdealSheafData.glueDataObjι, Scheme.Hom.liftQuotient_comp_assoc, pullback.condition]

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

lemma isIso_subschemeι_iff_eq_bot (I : X.IdealSheafData) : IsIso I.subschemeι ↔ I = ⊥ :=
  ⟨fun h ↦ by simp [← I.ker_subschemeι], fun h ↦ h ▸ inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
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
  rw [← reassoc_of% CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk,
    eqToHom_refl, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
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
