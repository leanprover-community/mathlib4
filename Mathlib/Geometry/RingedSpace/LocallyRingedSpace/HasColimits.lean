/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

#align_import algebraic_geometry.locally_ringed_space.has_colimits from "leanprover-community/mathlib"@"533f62f4dd62a5aad24a04326e6e787c8f7e98b1"

/-!
# Colimits of LocallyRingedSpace

We construct the explicit coproducts and coequalizers of `LocallyRingedSpace`.
It then follows that `LocallyRingedSpace` has all colimits, and
`forget_to_SheafedSpace` preserves them.

-/

set_option linter.uppercaseLean3 false

namespace AlgebraicGeometry

universe v u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SheafedSpace

variable {C : Type u} [Category.{v} C] [HasLimits C]
variable {J : Type v} [Category.{v} J] (F : J ⥤ SheafedSpace.{_, _, v} C)

theorem isColimit_exists_rep {c : Cocone F} (hc : IsColimit c) (x : c.pt) :
    ∃ (i : J) (y : F.obj i), (c.ι.app i).base y = x :=
  Concrete.isColimit_exists_rep (F ⋙ forget C) (isColimitOfPreserves (forget C) hc) x
#align algebraic_geometry.SheafedSpace.is_colimit_exists_rep AlgebraicGeometry.SheafedSpaceₓ.isColimit_exists_rep

-- Porting note: argument `C` of colimit need to be made explicit, odd
theorem colimit_exists_rep (x : colimit (C := SheafedSpace C) F) :
    ∃ (i : J) (y : F.obj i), (colimit.ι F i).base y = x :=
  Concrete.isColimit_exists_rep (F ⋙ SheafedSpace.forget C)
    (isColimitOfPreserves (SheafedSpace.forget _) (colimit.isColimit F)) x
#align algebraic_geometry.SheafedSpace.colimit_exists_rep AlgebraicGeometry.SheafedSpaceₓ.colimit_exists_rep

instance {X Y : SheafedSpace C} (f g : X ⟶ Y) : Epi (coequalizer.π f g).base := by
  erw [←
    show _ = (coequalizer.π f g).base from
      ι_comp_coequalizerComparison f g (SheafedSpace.forget C)]
  rw [← PreservesCoequalizer.iso_hom]
  apply epi_comp

end SheafedSpace

namespace LocallyRingedSpace

section HasCoproducts

variable {ι : Type u} (F : Discrete ι ⥤ LocallyRingedSpace.{u})
-- Porting note: in this section, I marked `CommRingCat` as `CommRingCatMax.{u,u}`
-- This is a hack to avoid the following:
/-
```
stuck at solving universe constraint
  u =?= max u ?u.11876
while trying to unify
  HasLimits CommRingCat
with
  (HasLimitsOfSize CommRingCatMax) (HasLimitsOfSize CommRingCatMax) (HasLimitsOfSize CommRingCatMax)
```
-/
/-- The explicit coproduct for `F : discrete ι ⥤ LocallyRingedSpace`. -/
noncomputable def coproduct : LocallyRingedSpace where
  toSheafedSpace := colimit (C := SheafedSpace.{u+1, u, u} CommRingCatMax.{u, u})
    (F ⋙ forgetToSheafedSpace)
  localRing x := by
    obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forgetToSheafedSpace) x
    haveI : LocalRing (((F ⋙ forgetToSheafedSpace).obj i).toPresheafedSpace.stalk y) :=
      (F.obj i).localRing _
    exact
      (asIso (PresheafedSpace.stalkMap
        (colimit.ι (C := SheafedSpace.{u+1, u, u} CommRingCatMax.{u, u})
          (F ⋙ forgetToSheafedSpace) i : _) y)).symm.commRingCatIsoToRingEquiv.localRing
#align algebraic_geometry.LocallyRingedSpace.coproduct AlgebraicGeometry.LocallyRingedSpace.coproduct

/-- The explicit coproduct cofan for `F : discrete ι ⥤ LocallyRingedSpace`. -/
noncomputable def coproductCofan : Cocone F where
  pt := coproduct F
  ι :=
    { app := fun j => ⟨colimit.ι (C := SheafedSpace.{u+1, u, u} CommRingCatMax.{u, u})
        (F ⋙ forgetToSheafedSpace) j, inferInstance⟩
      naturality := fun ⟨j⟩ ⟨j'⟩ ⟨⟨(f : j = j')⟩⟩ => by subst f; aesop }
#align algebraic_geometry.LocallyRingedSpace.coproduct_cofan AlgebraicGeometry.LocallyRingedSpace.coproductCofan

/-- The explicit coproduct cofan constructed in `coproduct_cofan` is indeed a colimit. -/
noncomputable def coproductCofanIsColimit : IsColimit (coproductCofan F) where
  desc s :=
    ⟨colimit.desc (C := SheafedSpace.{u+1, u, u} CommRingCatMax.{u, u})
      (F ⋙ forgetToSheafedSpace) (forgetToSheafedSpace.mapCocone s), by
      intro x
      obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forgetToSheafedSpace) x
      have := PresheafedSpace.stalkMap.comp
        (colimit.ι (C := SheafedSpace.{u+1, u, u} CommRingCatMax.{u, u})
          (F ⋙ forgetToSheafedSpace) i)
        (colimit.desc (C := SheafedSpace.{u+1, u, u} CommRingCatMax.{u, u})
          (F ⋙ forgetToSheafedSpace) (forgetToSheafedSpace.mapCocone s)) y
      rw [← IsIso.comp_inv_eq] at this
      erw [← this,
        PresheafedSpace.stalkMap.congr_hom _ _
          (colimit.ι_desc (C := SheafedSpace.{u+1, u, u} CommRingCatMax.{u, u})
            (forgetToSheafedSpace.mapCocone s) i : _)]
      haveI :
        IsLocalRingHom
          (PresheafedSpace.stalkMap ((forgetToSheafedSpace.mapCocone s).ι.app i) y) :=
        (s.ι.app i).2 y
      infer_instance⟩
  fac s j := LocallyRingedSpace.Hom.ext _ _
    (colimit.ι_desc (C := SheafedSpace.{u+1, u, u} CommRingCatMax.{u, u}) _ _)
  uniq s f h :=
    LocallyRingedSpace.Hom.ext _ _
      (IsColimit.uniq _ (forgetToSheafedSpace.mapCocone s) f.1 fun j =>
        congr_arg LocallyRingedSpace.Hom.val (h j))
#align algebraic_geometry.LocallyRingedSpace.coproduct_cofan_is_colimit AlgebraicGeometry.LocallyRingedSpace.coproductCofanIsColimit

instance : HasCoproducts.{u} LocallyRingedSpace.{u} := fun _ =>
  ⟨fun F => ⟨⟨⟨_, coproductCofanIsColimit F⟩⟩⟩⟩

noncomputable instance (J : Type _) :
    PreservesColimitsOfShape (Discrete.{u} J) forgetToSheafedSpace.{u} :=
  ⟨fun {G} =>
    preservesColimitOfPreservesColimitCocone (coproductCofanIsColimit G)
      ((colimit.isColimit (C := SheafedSpace.{u+1, u, u} CommRingCatMax.{u, u}) _).ofIsoColimit
        (Cocones.ext (Iso.refl _) fun _ => Category.comp_id _))⟩

end HasCoproducts

section HasCoequalizer

variable {X Y : LocallyRingedSpace.{v}} (f g : X ⟶ Y)

namespace HasCoequalizer

instance coequalizer_π_app_isLocalRingHom
    (U : TopologicalSpace.Opens (coequalizer f.val g.val).carrier) :
    IsLocalRingHom ((coequalizer.π f.val g.val : _).c.app (op U)) := by
  have := ι_comp_coequalizerComparison f.1 g.1 SheafedSpace.forgetToPresheafedSpace
  rw [← PreservesCoequalizer.iso_hom] at this
  erw [SheafedSpace.congr_app this.symm (op U)]
  rw [PresheafedSpace.comp_c_app, ← PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
  -- Porting note (#10754): this instance has to be manually added
  haveI : IsIso (PreservesCoequalizer.iso SheafedSpace.forgetToPresheafedSpace f.val g.val).hom.c :=
    PresheafedSpace.c_isIso_of_iso _
  infer_instance
#align algebraic_geometry.LocallyRingedSpace.has_coequalizer.coequalizer_π_app_is_local_ring_hom AlgebraicGeometry.LocallyRingedSpace.HasCoequalizer.coequalizer_π_app_isLocalRingHom

/-!
We roughly follow the construction given in [MR0302656]. Given a pair `f, g : X ⟶ Y` of morphisms
of locally ringed spaces, we want to show that the stalk map of
`π = coequalizer.π f g` (as sheafed space homs) is a local ring hom. It then follows that
`coequalizer f g` is indeed a locally ringed space, and `coequalizer.π f g` is a morphism of
locally ringed space.

Given a germ `⟨U, s⟩` of `x : coequalizer f g` such that `π꙳ x : Y` is invertible, we ought to show
that `⟨U, s⟩` is invertible. That is, there exists an open set `U' ⊆ U` containing `x` such that the
restriction of `s` onto `U'` is invertible. This `U'` is given by `π '' V`, where `V` is the
basic open set of `π⋆x`.

Since `f ⁻¹' V = Y.basic_open (f ≫ π)꙳ x = Y.basic_open (g ≫ π)꙳ x = g ⁻¹' V`, we have
`π ⁻¹' (π '' V) = V` (as the underlying set map is merely the set-theoretic coequalizer).
This shows that `π '' V` is indeed open, and `s` is invertible on `π '' V` as the components of `π꙳`
are local ring homs.
-/


variable (U : Opens (coequalizer f.1 g.1).carrier)
variable (s : (coequalizer f.1 g.1).presheaf.obj (op U))

/-- (Implementation). The basic open set of the section `π꙳ s`. -/
noncomputable def imageBasicOpen : Opens Y :=
  Y.toRingedSpace.basicOpen
    (show Y.presheaf.obj (op (unop _)) from ((coequalizer.π f.1 g.1).c.app (op U)) s)
#align algebraic_geometry.LocallyRingedSpace.has_coequalizer.image_basic_open AlgebraicGeometry.LocallyRingedSpace.HasCoequalizer.imageBasicOpen

theorem imageBasicOpen_image_preimage :
    (coequalizer.π f.1 g.1).base ⁻¹' ((coequalizer.π f.1 g.1).base '' (imageBasicOpen f g U s).1) =
      (imageBasicOpen f g U s).1 := by
  fapply Types.coequalizer_preimage_image_eq_of_preimage_eq
    -- Porting note: Type of `f.1.base` and `g.1.base` needs to be explicit
    (f.1.base : X.carrier.1 ⟶ Y.carrier.1) (g.1.base : X.carrier.1 ⟶ Y.carrier.1)
  · ext
    simp_rw [types_comp_apply, ← TopCat.comp_app, ← PresheafedSpace.comp_base]
    congr 2
    exact coequalizer.condition f.1 g.1
  · apply isColimitCoforkMapOfIsColimit (forget TopCat)
    apply isColimitCoforkMapOfIsColimit (SheafedSpace.forget _)
    exact coequalizerIsCoequalizer f.1 g.1
  · suffices
      (TopologicalSpace.Opens.map f.1.base).obj (imageBasicOpen f g U s) =
        (TopologicalSpace.Opens.map g.1.base).obj (imageBasicOpen f g U s)
      by injection this
    delta imageBasicOpen
    rw [preimage_basicOpen f, preimage_basicOpen g]
    dsimp only [Functor.op, unop_op]
    -- Porting note (#11224): change `rw` to `erw`
    erw [← comp_apply, ← SheafedSpace.comp_c_app', ← comp_apply, ← SheafedSpace.comp_c_app',
      SheafedSpace.congr_app (coequalizer.condition f.1 g.1), comp_apply,
      X.toRingedSpace.basicOpen_res]
    apply inf_eq_right.mpr
    refine (RingedSpace.basicOpen_le _ _).trans ?_
    rw [coequalizer.condition f.1 g.1]
#align algebraic_geometry.LocallyRingedSpace.has_coequalizer.image_basic_open_image_preimage AlgebraicGeometry.LocallyRingedSpace.HasCoequalizer.imageBasicOpen_image_preimage

theorem imageBasicOpen_image_open :
    IsOpen ((coequalizer.π f.1 g.1).base '' (imageBasicOpen f g U s).1) := by
  rw [← (TopCat.homeoOfIso (PreservesCoequalizer.iso (SheafedSpace.forget _) f.1
    g.1)).isOpen_preimage, TopCat.coequalizer_isOpen_iff, ← Set.preimage_comp]
  erw [← TopCat.coe_comp]
  rw [PreservesCoequalizer.iso_hom, ι_comp_coequalizerComparison]
  dsimp only [SheafedSpace.forget]
  -- Porting note (#11224): change `rw` to `erw`
  erw [imageBasicOpen_image_preimage]
  exact (imageBasicOpen f g U s).2
#align algebraic_geometry.LocallyRingedSpace.has_coequalizer.image_basic_open_image_open AlgebraicGeometry.LocallyRingedSpace.HasCoequalizer.imageBasicOpen_image_open

instance coequalizer_π_stalk_isLocalRingHom (x : Y) :
    IsLocalRingHom (PresheafedSpace.stalkMap (coequalizer.π f.val g.val : _) x) := by
  constructor
  rintro a ha
  rcases TopCat.Presheaf.germ_exist _ _ a with ⟨U, hU, s, rfl⟩
  erw [PresheafedSpace.stalkMap_germ_apply (coequalizer.π f.1 g.1 : _) U ⟨_, hU⟩] at ha
  let V := imageBasicOpen f g U s
  have hV : (coequalizer.π f.1 g.1).base ⁻¹' ((coequalizer.π f.1 g.1).base '' V.1) = V.1 :=
    imageBasicOpen_image_preimage f g U s
  have hV' :
    V = ⟨(coequalizer.π f.1 g.1).base ⁻¹' ((coequalizer.π f.1 g.1).base '' V.1), hV.symm ▸ V.2⟩ :=
    SetLike.ext' hV.symm
  have V_open : IsOpen ((coequalizer.π f.val g.val).base '' V.1) :=
    imageBasicOpen_image_open f g U s
  have VleU : (⟨(coequalizer.π f.val g.val).base '' V.1, V_open⟩ : TopologicalSpace.Opens _) ≤ U :=
    Set.image_subset_iff.mpr (Y.toRingedSpace.basicOpen_le _)
  have hxV : x ∈ V := ⟨⟨_, hU⟩, ha, rfl⟩
  erw [←
    (coequalizer f.val g.val).presheaf.germ_res_apply (homOfLE VleU)
      ⟨_, @Set.mem_image_of_mem _ _ (coequalizer.π f.val g.val).base x V.1 hxV⟩ s]
  apply RingHom.isUnit_map
  rw [← isUnit_map_iff ((coequalizer.π f.val g.val : _).c.app _), ← comp_apply,
    NatTrans.naturality, comp_apply, TopCat.Presheaf.pushforwardObj_map, ←
    isUnit_map_iff (Y.presheaf.map (eqToHom hV').op)]
  -- Porting note (#11224): change `rw` to `erw`
  erw [← comp_apply, ← comp_apply, ← Y.presheaf.map_comp]
  convert @RingedSpace.isUnit_res_basicOpen Y.toRingedSpace (unop _)
      (((coequalizer.π f.val g.val).c.app (op U)) s)
#align algebraic_geometry.LocallyRingedSpace.has_coequalizer.coequalizer_π_stalk_is_local_ring_hom AlgebraicGeometry.LocallyRingedSpace.HasCoequalizer.coequalizer_π_stalk_isLocalRingHom

end HasCoequalizer

/-- The coequalizer of two locally ringed space in the category of sheafed spaces is a locally
ringed space. -/
noncomputable def coequalizer : LocallyRingedSpace where
  toSheafedSpace := Limits.coequalizer f.1 g.1
  localRing x := by
    obtain ⟨y, rfl⟩ :=
      (TopCat.epi_iff_surjective (coequalizer.π f.val g.val).base).mp inferInstance x
    exact (PresheafedSpace.stalkMap (coequalizer.π f.val g.val : _) y).domain_localRing
#align algebraic_geometry.LocallyRingedSpace.coequalizer AlgebraicGeometry.LocallyRingedSpace.coequalizer

/-- The explicit coequalizer cofork of locally ringed spaces. -/
noncomputable def coequalizerCofork : Cofork f g :=
  @Cofork.ofπ _ _ _ _ f g (coequalizer f g) ⟨coequalizer.π f.1 g.1,
    -- Porting note: this used to be automatic
    HasCoequalizer.coequalizer_π_stalk_isLocalRingHom _ _⟩
    (LocallyRingedSpace.Hom.ext _ _ (coequalizer.condition f.1 g.1))
#align algebraic_geometry.LocallyRingedSpace.coequalizer_cofork AlgebraicGeometry.LocallyRingedSpace.coequalizerCofork

theorem isLocalRingHom_stalkMap_congr {X Y : RingedSpace} (f g : X ⟶ Y) (H : f = g) (x)
    (h : IsLocalRingHom (PresheafedSpace.stalkMap f x)) :
    IsLocalRingHom (PresheafedSpace.stalkMap g x) := by
  rw [PresheafedSpace.stalkMap.congr_hom _ _ H.symm x]; infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_local_ring_hom_stalk_map_congr AlgebraicGeometry.LocallyRingedSpace.isLocalRingHom_stalkMap_congr

/-- The cofork constructed in `coequalizer_cofork` is indeed a colimit cocone. -/
noncomputable def coequalizerCoforkIsColimit : IsColimit (coequalizerCofork f g) := by
  apply Cofork.IsColimit.mk'
  intro s
  have e : f.val ≫ s.π.val = g.val ≫ s.π.val := by injection s.condition
  refine ⟨⟨coequalizer.desc s.π.1 e, ?_⟩, ?_⟩
  · intro x
    rcases (TopCat.epi_iff_surjective (coequalizer.π f.val g.val).base).mp inferInstance x with
      ⟨y, rfl⟩
    -- Porting note: was `apply isLocalRingHom_of_comp _ (PresheafedSpace.stalkMap ...)`, this
    -- used to allow you to provide the proof that `... ≫ ...` is a local ring homomorphism later,
    -- but this is no longer possible
    set h := _
    change IsLocalRingHom h
    suffices IsLocalRingHom ((PresheafedSpace.stalkMap (coequalizerCofork f g).π.1 _).comp h) from
      isLocalRingHom_of_comp _ (PresheafedSpace.stalkMap (coequalizerCofork f g).π.1 _)
    change IsLocalRingHom (_ ≫ PresheafedSpace.stalkMap (coequalizerCofork f g).π.val y)
    erw [← PresheafedSpace.stalkMap.comp]
    apply isLocalRingHom_stalkMap_congr _ _ (coequalizer.π_desc s.π.1 e).symm y
    infer_instance
  constructor
  · exact LocallyRingedSpace.Hom.ext _ _ (coequalizer.π_desc _ _)
  intro m h
  replace h : (coequalizerCofork f g).π.1 ≫ m.1 = s.π.1 := by rw [← h]; rfl
  apply LocallyRingedSpace.Hom.ext
  apply (colimit.isColimit (parallelPair f.1 g.1)).uniq (Cofork.ofπ s.π.1 e) m.1
  rintro ⟨⟩
  · rw [← (colimit.cocone (parallelPair f.val g.val)).w WalkingParallelPairHom.left,
      Category.assoc]
    change _ ≫ _ ≫ _ = _ ≫ _
    congr
  · exact h
#align algebraic_geometry.LocallyRingedSpace.coequalizer_cofork_is_colimit AlgebraicGeometry.LocallyRingedSpace.coequalizerCoforkIsColimit

instance : HasCoequalizer f g :=
  ⟨⟨⟨_, coequalizerCoforkIsColimit f g⟩⟩⟩

instance : HasCoequalizers LocallyRingedSpace :=
  hasCoequalizers_of_hasColimit_parallelPair _

noncomputable instance preservesCoequalizer :
    PreservesColimitsOfShape WalkingParallelPair forgetToSheafedSpace.{v} :=
  ⟨fun {F} => by
    -- Porting note: was `apply preservesColimitOfIsoDiagram ...` and the proof that preservation
    -- of colimit is provided later
    suffices PreservesColimit (parallelPair (F.map WalkingParallelPairHom.left)
        (F.map WalkingParallelPairHom.right)) forgetToSheafedSpace from
      preservesColimitOfIsoDiagram _ (diagramIsoParallelPair F).symm
    apply preservesColimitOfPreservesColimitCocone (coequalizerCoforkIsColimit _ _)
    apply (isColimitMapCoconeCoforkEquiv _ _).symm _
    dsimp only [forgetToSheafedSpace]
    exact coequalizerIsCoequalizer _ _⟩
#align algebraic_geometry.LocallyRingedSpace.preserves_coequalizer AlgebraicGeometry.LocallyRingedSpace.preservesCoequalizer

end HasCoequalizer

instance : HasColimits LocallyRingedSpace :=
  has_colimits_of_hasCoequalizers_and_coproducts

noncomputable instance preservesColimits_forgetToSheafedSpace :
    PreservesColimits LocallyRingedSpace.forgetToSheafedSpace.{u} :=
  preservesColimitsOfPreservesCoequalizersAndCoproducts _

end LocallyRingedSpace

end AlgebraicGeometry
