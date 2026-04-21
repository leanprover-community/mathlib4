/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!

# Colimits in `P.Over ⊤ S`

Let `P` be a morphism property in the category of schemes and `S` be a scheme. Let
`D : J ⥤ P.Over ⊤ S` be a diagram and `𝒰` a locally directed open cover of `S`
(e.g., the cover of all affine opens of `S`).
Suppose the restrictions of `D` to `Dᵢ : J ⥤ P.Over ⊤ (𝒰.X i)` have a colimit for every `i`,
then we show that also `D` has a colimit under the following assumptions:

- `P` is local on the source.
- For `i ⟶ j`, the transition map `𝒰.X i ⟶ 𝒰.X j` satisfies `P`.
- For `i ⟶ j`, the base change functor `P.Over ⊤ (𝒰.X j) ⥤ P.Over ⊤ (𝒰.X i)` preserves
  colimits of shape `J`.

This can be used to reduce existence of certain colimits in `P.Over ⊤ S` to the case where
`S` is affine.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme.Cover

variable {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange] [P.IsMultiplicative]
  {S : Scheme.{u}} {J : Type*} [Category* J] (D : J ⥤ P.Over ⊤ S)
  (𝒰 : S.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected]

/-- The data required for gluing the colimits of the `Dᵢ : J ⥤ P.Over ⊤ (𝒰.X i)`. -/
structure ColimitGluingData (D : J ⥤ P.Over ⊤ S) (𝒰 : S.OpenCover)
    [Category* 𝒰.I₀] [𝒰.LocallyDirected] where
  /-- The cocones on the `Dᵢ`. -/
  cocone (i : 𝒰.I₀) : Cocone (D ⋙ MorphismProperty.Over.pullback P ⊤ (𝒰.f i))
  /-- The cocones on the `Dᵢ` are colimiting. -/
  isColimit (i : 𝒰.I₀) : IsColimit (cocone i)
  prop_trans {i j : 𝒰.I₀} (hij : i ⟶ j) : P (𝒰.trans hij)

namespace ColimitGluingData

variable {D} {𝒰} (d : ColimitGluingData D 𝒰)

/-- (Implementation) Auxiliary natural transformation for construction of
`AlgebraicGeometry.Scheme.Cover.ColimitGluingData.functor`. -/
@[simps!]
noncomputable
def trans {i j : 𝒰.I₀} (hij : i ⟶ j) :
    D ⋙ Over.pullback P ⊤ (𝒰.f i) ⋙ Over.map _ (d.prop_trans hij) ⟶
      D ⋙ Over.pullback P ⊤ (𝒰.f j) :=
  D.whiskerLeft <| Over.pullbackMapHomPullback (P := P) (Q := ⊤) _ _ trivial _ _

/-- (Implementation) Cocone for transition map for construction of
`AlgebraicGeometry.Scheme.Cover.ColimitGluingData.functor`. -/
@[simps! pt ι_app]
noncomputable
def transitionCocone {i j : 𝒰.I₀} (hij : i ⟶ j) :
    Cocone (D ⋙ Over.pullback P ⊤ (𝒰.f i) ⋙ Over.map _ (d.prop_trans hij)) :=
  (Cocone.precompose (d.trans hij)).obj (d.cocone j)

/-- (Implementation) Transition map for construction of
`AlgebraicGeometry.Scheme.Cover.ColimitGluingData.functor`. -/
noncomputable
def transitionMap {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (Over.map ⊤ (d.prop_trans hij)).obj (d.cocone i).pt ⟶ (d.cocone j).pt :=
  (isColimitOfPreserves (Over.map ⊤ (d.prop_trans hij)) (d.isColimit i)).desc
    (d.transitionCocone hij)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma cocone_ι_transitionMap {i j : 𝒰.I₀} (hij : i ⟶ j) (a : J) :
    (Over.map ⊤ (d.prop_trans hij)).map ((d.cocone i).ι.app a) ≫
      d.transitionMap hij = (d.trans hij).app a ≫ (d.cocone j).ι.app a := by
  simp [transitionMap, ← Functor.mapCocone_ι_app, transitionCocone]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma transitionMap_id (i : 𝒰.I₀) :
    d.transitionMap (𝟙 i) = ((Over.mapId _ _ _).hom.app <| (d.cocone i).pt) := by
  apply (isColimitOfPreserves (Over.map ⊤ (d.prop_trans <| 𝟙 i)) (d.isColimit i)).hom_ext
  intro
  ext
  simp [cocone_ι_transitionMap]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma transitionMap_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    d.transitionMap (hij ≫ hjk) =
      (Over.mapComp ⊤ (d.prop_trans hij) (d.prop_trans hjk) (𝒰.trans (hij ≫ hjk))).hom.app _ ≫
      (Over.map ⊤ (d.prop_trans hjk)).map (d.transitionMap hij) ≫
        d.transitionMap hjk := by
  apply (isColimitOfPreserves (Over.map ⊤ <| d.prop_trans _) (d.isColimit i)).hom_ext
  intro
  ext
  simp [← Functor.map_comp_assoc, cocone_ι_transitionMap, pullback.map_comp_assoc]

/-- (Implementation): Underlying functor of associated relative gluing datum. -/
@[simps]
noncomputable def functor : 𝒰.I₀ ⥤ Scheme where
  obj i := (d.cocone i).pt.left
  map {i j} hij := (d.transitionMap hij).left

variable [∀ {i j} (hij : i ⟶ j), PreservesColimitsOfShape J (Over.pullback P ⊤ (𝒰.trans hij))]

set_option backward.isDefEq.respectTransparency false in
lemma isPullback {i j : 𝒰.I₀} (hij : i ⟶ j) :
    IsPullback (d.transitionMap hij).left (d.cocone i).pt.hom
      (d.cocone j).pt.hom (𝒰.trans hij) := by
  let iso1 : (d.cocone i).pt ≅ _ :=
    (d.isColimit i).coconePointsIsoOfNatIso
      (isColimitOfPreserves (Over.pullback P ⊤ (𝒰.trans hij)) (d.isColimit j)) <|
      D.isoWhiskerLeft (Over.pullbackComp _ _ _) ≪≫ (Functor.associator _ _ _).symm
  have heq : (Over.map _ (d.prop_trans hij)).map iso1.hom ≫
        (Over.mapPullbackAdj _ _ _ (d.prop_trans hij) trivial).counit.app _ =
      d.transitionMap hij := by
    apply (isColimitOfPreserves (Over.map _ (d.prop_trans hij)) (d.isColimit i)).hom_ext
    intro a
    dsimp only [Functor.comp_obj, Functor.id_obj, Functor.mapCocone_pt, Functor.const_obj_obj,
      Functor.mapCocone_ι_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom]
    rw [IsColimit.coconePointsIsoOfNatIso_hom, ← Functor.map_comp_assoc, IsColimit.ι_map,
      Functor.mapCocone_ι_app, Functor.map_comp, Category.assoc,
      Adjunction.counit_naturality, cocone_ι_transitionMap]
    ext
    dsimp
    rw [Category.comp_id, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp
  let iso2 : (d.cocone i).pt.left ≅ pullback (d.cocone j).pt.hom (𝒰.trans hij) :=
    (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mapIso iso1
  refine .of_iso (IsPullback.of_hasPullback _ _) iso2.symm (.refl _) (.refl _) (.refl _) ?_ ?_
      (by simp) (by simp)
  · simpa [← cancel_epi iso2.hom] using congr($(heq).left)
  · exact (Over.w iso1.inv).symm

set_option backward.isDefEq.respectTransparency false in
/-- The relative gluing datum associated to the family of the `colim Dᵢ`. -/
@[simps natTrans_app, simps -isSimp functor]
noncomputable
def relativeGluingData : 𝒰.RelativeGluingData where
  functor := d.functor
  natTrans.app i := (d.cocone i).pt.hom
  equifibered {i j} hij := d.isPullback hij

variable [Quiver.IsThin 𝒰.I₀] [Small.{u} 𝒰.I₀] [IsZariskiLocalAtTarget P]

set_option backward.isDefEq.respectTransparency false in
/-- The result of gluing the `colim Dᵢ`. -/
noncomputable def glued : P.Over ⊤ S :=
  Over.mk _ d.relativeGluingData.toBase <| by
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) 𝒰]
    intro i
    rw [Scheme.Cover.pullbackHom,
      ← (d.relativeGluingData.isPullback_natTrans_ι_toBase i).flip.isoPullback_inv_snd,
      P.cancel_left_of_respectsIso]
    exact (d.cocone i).pt.prop

set_option backward.isDefEq.respectTransparency false in
/-- `colim Dᵢ` is the pullback of the glued object over `S` along the inclusion `𝒰ᵢ ⟶ S`. -/
noncomputable
def pullbackGluedIso (i : 𝒰.I₀) :
    (MorphismProperty.Over.pullback P ⊤ (𝒰.f i)).obj d.glued ≅ (d.cocone i).pt :=
  Over.isoMk (d.relativeGluingData.isPullback_natTrans_ι_toBase i).flip.isoPullback.symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pullbackGluedIso_inv_fst (i : 𝒰.I₀) : (d.pullbackGluedIso i).inv.left ≫ pullback.fst _ _ =
    colimit.ι d.relativeGluingData.functor i := by
  simp [pullbackGluedIso, glued]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pullbackGluedIso_inv_snd (i : 𝒰.I₀) :
    (d.pullbackGluedIso i).inv.left ≫ pullback.snd _ _ = (d.cocone i).pt.hom := by
  simp [pullbackGluedIso, glued]

set_option backward.isDefEq.respectTransparency false in
/-- The cocone glued from the `colim Dᵢ`. -/
@[simps pt]
noncomputable def gluedCocone : Cocone D := by
  letI 𝒱 (a : J) : (D.obj a).left.OpenCover := 𝒰.pullback₁ (D.obj a).hom
  refine { pt := d.glued, ι.app a := ?_, ι.naturality {a b} f := ?_ }
  · refine ⟨(𝒱 a).glueMorphismsOverOfLocallyDirected ?_ ?_ ?_, trivial, trivial⟩
    · intro i
      exact ((d.cocone i).ι.app a).left ≫ colimit.ι d.relativeGluingData.functor i
    · intro i j hij
      conv_rhs => rw [← colimit.w d.relativeGluingData.functor hij]
      simp only [← Category.assoc]
      congr 1
      exact congr($(d.cocone_ι_transitionMap hij a).left).symm
    · intro
      simp [𝒱, pullback.condition, glued]
  · ext
    apply (𝒱 a).hom_ext
    intro i
    have : (𝒱 a).f i ≫ (D.map f).left =
        ((D ⋙ Over.pullback _ _ (𝒰.f i)).map f).left ≫ (𝒱 b).f i := by
      simp [𝒱]
    dsimp
    rw [Category.comp_id, Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left,
      reassoc_of% this, Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left,
      ← Over.comp_left_assoc, ← Comma.comp_hom, ← Functor.comp_map, Cocone.w]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma fst_gluedCocone_ι (a : J) (i : 𝒰.I₀) :
    pullback.fst (D.obj a).hom (𝒰.f i) ≫
      (d.gluedCocone.ι.app a).left =
      ((d.cocone i).ι.app a).left ≫ colimit.ι d.relativeGluingData.functor i := by
  simp only [gluedCocone]
  generalize_proofs _ _ _ _ _ _ _ _ _ _ _ _ h1 h2
  let 𝒱 : (D.obj a).left.OpenCover := 𝒰.pullback₁ (D.obj a).hom
  apply 𝒱.map_glueMorphismsOverOfLocallyDirected_left _ h1 h2

set_option backward.isDefEq.respectTransparency false in
/-- The glued cocone is colimiting. -/
noncomputable
def isColimitGluedCocone : IsColimit d.gluedCocone := by
  letI 𝒱 : d.glued.left.OpenCover := d.relativeGluingData.cover
  refine { desc s := ?_, fac := ?_, uniq := ?_ }
  · refine ⟨𝒱.glueMorphismsOverOfLocallyDirected ?_ ?_ ?_, trivial, trivial⟩
    · intro i
      exact ((d.isColimit i).desc (Functor.mapCocone _ s)).left ≫ pullback.fst _ _
    · intro i j hij
      simp only [Functor.mapCocone_pt, MorphismProperty.Over.pullback_obj_left,
        Functor.id_obj, Functor.const_obj_obj]
      change (d.transitionMap hij).left ≫ _ ≫ _ = _
      have : d.transitionMap hij ≫ (d.isColimit j).desc ((Over.pullback P ⊤ (𝒰.f j)).mapCocone s) =
          (Over.map ⊤ (d.prop_trans hij)).map
            ((d.isColimit i).desc ((MorphismProperty.Over.pullback P ⊤ (𝒰.f i)).mapCocone s)) ≫
          (Over.pullbackMapHomPullback _ (d.prop_trans hij) trivial _ _).app _ := by
        apply (isColimitOfPreserves (Over.map ⊤ <| d.prop_trans _) (d.isColimit i)).hom_ext
        intro
        ext
        apply pullback.hom_ext <;> simp [cocone_ι_transitionMap_assoc, ← Functor.map_comp_assoc]
      rw [← Over.comp_left_assoc, ← Comma.comp_hom, this]
      simp
    · intro i
      have : _ ≫ pullback.snd _ _ = _ := Over.w ((d.isColimit i).desc (Functor.mapCocone _ s))
      simp only [glued, Category.assoc, 𝒱, pullback.condition]
      rw [reassoc_of% this]
      simp
  · intro s a
    letI 𝒲 (a : J) : (D.obj a).left.OpenCover := 𝒰.pullback₁ (D.obj a).hom
    ext
    refine (𝒲 a).hom_ext _ _ fun i ↦ ?_
    dsimp
    simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_f, 𝒲, fst_gluedCocone_ι_assoc]
    change _ ≫ 𝒱.f _ ≫ _ = _
    rw [Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left, ← Over.comp_left_assoc,
      ← Comma.comp_hom]
    simp
  · intro s m hm
    ext
    refine 𝒱.hom_ext _ _ fun i ↦ ?_
    have : (d.pullbackGluedIso i).inv ≫ (Over.pullback P ⊤ (𝒰.f i)).map m =
        (d.isColimit i).desc ((Over.pullback P ⊤ (𝒰.f i)).mapCocone s) := by
      refine (d.isColimit i).hom_ext fun a ↦ ?_
      rw [IsColimit.fac]
      ext
      apply pullback.hom_ext
      · dsimp
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
          pullbackGluedIso_inv_fst_assoc]
        rw [← congr($(hm a).left)]
        simp [fst_gluedCocone_ι_assoc]
      · simp
    rw [Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left]
    simp [𝒱, ← this]

end ColimitGluingData

lemma hasColimit_of_locallyDirected
    (H : ∀ {i j} (hij : i ⟶ j), P (𝒰.trans hij))
    [∀ {i j : 𝒰.I₀} (hij : i ⟶ j), PreservesColimitsOfShape J (Over.pullback P ⊤ (𝒰.trans hij))]
    [∀ i, HasColimit (D ⋙ Over.pullback _ _ (𝒰.f i))]
    [Quiver.IsThin 𝒰.I₀] [Small.{u} 𝒰.I₀] [IsZariskiLocalAtTarget P] :
    HasColimit D :=
  let d : ColimitGluingData D 𝒰 :=
    { cocone _ := colimit.cocone _
      isColimit _ := colimit.isColimit _
      prop_trans := H }
  ⟨d.gluedCocone, d.isColimitGluedCocone⟩

end AlgebraicGeometry.Scheme.Cover
