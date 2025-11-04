/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Colimits of LocallyRingedSpace

We construct the explicit coproducts and coequalizers of `LocallyRingedSpace`.
It then follows that `LocallyRingedSpace` has all colimits, and
`forgetToSheafedSpace` preserves them.

-/


namespace AlgebraicGeometry

universe w' w v u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] Opposite.small

namespace SheafedSpace

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [Category.{w'} J] [Small.{v} J] (F : J ⥤ SheafedSpace.{_, _, v} C)

theorem isColimit_exists_rep [HasLimitsOfShape Jᵒᵖ C] {c : Cocone F} (hc : IsColimit c) (x : c.pt) :
    ∃ (i : J) (y : F.obj i), (c.ι.app i).hom.base y = x :=
  Concrete.isColimit_exists_rep (F ⋙ forget C) (isColimitOfPreserves (forget C) hc) x

-- Porting note: argument `C` of colimit need to be made explicit, otherwise we get universe issues
theorem colimit_exists_rep [HasLimitsOfShape Jᵒᵖ C] (x : colimit (C := SheafedSpace C) F) :
    ∃ (i : J) (y : F.obj i), (colimit.ι F i).hom.base y = x :=
  Concrete.isColimit_exists_rep (F ⋙ SheafedSpace.forget C)
    (isColimitOfPreserves (SheafedSpace.forget _) (colimit.isColimit F)) x

instance [HasLimits C] {X Y : SheafedSpace C} (f g : X ⟶ Y) :
    Epi (coequalizer.π f g).hom.base := by
  rw [← show _ = (coequalizer.π f g).hom.base from
      ι_comp_coequalizerComparison f g (SheafedSpace.forget C),
      ← PreservesCoequalizer.iso_hom]
  apply epi_comp

end SheafedSpace

namespace LocallyRingedSpace

section HasCoproducts

variable {ι : Type v} [Small.{u} ι] (F : Discrete ι ⥤ LocallyRingedSpace.{u})

/-- The explicit coproduct for `F : discrete ι ⥤ LocallyRingedSpace`. -/
noncomputable def coproduct : LocallyRingedSpace where
  toSheafedSpace := colimit (C := SheafedSpace.{u+1, u, u} CommRingCat.{u})
    (F ⋙ forgetToSheafedSpace)
  isLocalRing x := by
    obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forgetToSheafedSpace) x
    haveI : IsLocalRing (((F ⋙ forgetToSheafedSpace).obj i).presheaf.stalk y) :=
      (F.obj i).isLocalRing _
    exact
      (asIso ((colimit.ι (C := SheafedSpace.{u+1, u, u} CommRingCat.{u})
        (F ⋙ forgetToSheafedSpace) i :).hom.stalkMap y)).symm.commRingCatIsoToRingEquiv.isLocalRing

/-- The explicit coproduct cofan for `F : discrete ι ⥤ LocallyRingedSpace`. -/
noncomputable def coproductCofan : Cocone F where
  pt := coproduct F
  ι :=
    { app j := LocallyRingedSpace.homMk (colimit.ι (F ⋙ forgetToSheafedSpace) j)
      naturality := fun ⟨j⟩ ⟨j'⟩ ⟨⟨(f : j = j')⟩⟩ => by subst f; simp }

/-- The explicit coproduct cofan constructed in `coproductCofan` is indeed a colimit. -/
noncomputable def coproductCofanIsColimit : IsColimit (coproductCofan F) where
  desc s :=
    LocallyRingedSpace.homMk (colimit.desc
      (F ⋙ forgetToSheafedSpace) (forgetToSheafedSpace.mapCocone s)) (by
        intro x
        obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forgetToSheafedSpace) x
        have := PresheafedSpace.stalkMap.comp
          (colimit.ι (F ⋙ forgetToSheafedSpace) i).hom
          (colimit.desc (F ⋙ forgetToSheafedSpace) (forgetToSheafedSpace.mapCocone s)).hom y
        rw [← IsIso.comp_inv_eq] at this
        sorry)
        --erw [← this,
        --  PresheafedSpace.stalkMap.congr_hom _ _
        --    (colimit.ι_desc
        --      (forgetToSheafedSpace.mapCocone s) i :)]
        --haveI :
        --  IsLocalHom
        --    (((forgetToSheafedSpace.mapCocone s).ι.app i).stalkMap y).hom :=
        --  (s.ι.app i).2 y
        --infer_instance)
  fac _ _ :=
    LocallyRingedSpace.forgetToSheafedSpace.map_injective
     (colimit.ι_desc (C := SheafedSpace _) _ _)
  uniq s f h :=
    LocallyRingedSpace.forgetToSheafedSpace.map_injective
      (IsColimit.uniq _ (forgetToSheafedSpace.mapCocone s) f.toShHom fun j =>
        congr_arg LocallyRingedSpace.Hom.toShHom (h j))

instance : HasColimitsOfShape (Discrete ι) LocallyRingedSpace.{u} :=
  ⟨fun F => ⟨⟨⟨_, coproductCofanIsColimit F⟩⟩⟩⟩

noncomputable instance : PreservesColimitsOfShape (Discrete.{v} ι) forgetToSheafedSpace.{u} :=
  ⟨fun {G} =>
    preservesColimit_of_preserves_colimit_cocone (coproductCofanIsColimit G)
      ((colimit.isColimit (C := SheafedSpace.{u+1, u, u} CommRingCat.{u}) _).ofIsoColimit
        (Cocones.ext (Iso.refl _) fun _ => Category.comp_id _))⟩

end HasCoproducts

section HasCoequalizer

variable {X Y : LocallyRingedSpace.{v}} (f g : X ⟶ Y)

namespace HasCoequalizer

@[instance]
theorem coequalizer_π_app_isLocalHom
    (U : TopologicalSpace.Opens (coequalizer f.toShHom g.toShHom).carrier) :
    IsLocalHom ((coequalizer.π f.toShHom g.toShHom :).hom.c.app (op U)).hom := by
  have := ι_comp_coequalizerComparison f.toShHom g.toShHom SheafedSpace.forgetToPresheafedSpace
  dsimp at this
  rw [← PreservesCoequalizer.iso_hom] at this
  rw [← this, PresheafedSpace.comp_c_app,
    ← PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10754): this instance has to be manually added
  haveI : IsIso (PreservesCoequalizer.iso
      SheafedSpace.forgetToPresheafedSpace f.toShHom g.toShHom).hom.c :=
    inferInstance
  -- Had to add this instance too.
  have := CommRingCat.equalizer_ι_isLocalHom' (PresheafedSpace.componentwiseDiagram _
        ((Opens.map
              (PreservesCoequalizer.iso SheafedSpace.forgetToPresheafedSpace (Hom.toShHom f)
                    (Hom.toShHom g)).hom.base).obj
          (unop (op U))))
  sorry--infer_instance

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


variable (U : Opens (coequalizer f.toShHom g.toShHom).carrier)
variable (s : (coequalizer f.toShHom g.toShHom).presheaf.obj (op U))

/-- (Implementation). The basic open set of the section `π꙳ s`. -/
noncomputable def imageBasicOpen : Opens Y :=
  Y.toRingedSpace.basicOpen
    (show Y.presheaf.obj (op (unop _)) from
      ((coequalizer.π f.toShHom g.toShHom).hom.c.app (op U)) s)

theorem imageBasicOpen_image_preimage :
    (coequalizer.π f.toShHom g.toShHom).hom.base ⁻¹'
      ((coequalizer.π f.toShHom g.toShHom).hom.base ''
        (imageBasicOpen f g U s).1) = (imageBasicOpen f g U s).1 := by
  fapply Types.coequalizer_preimage_image_eq_of_preimage_eq f.base
    -- Porting note: Type of `g.base` needs to be explicit
    (g.base : X.carrier.1 ⟶ Y.carrier.1)
  · ext
    simp_rw [types_comp_apply, ← TopCat.comp_app, ← PresheafedSpace.comp_base]
    congr 3
    exact SheafedSpace.forgetToPresheafedSpace.congr_map
      (coequalizer.condition f.toShHom g.toShHom)
  · exact isColimitCoforkMapOfIsColimit (forget TopCat) _
      (isColimitCoforkMapOfIsColimit (SheafedSpace.forget _)
      _ (coequalizerIsCoequalizer f.toShHom g.toShHom))
  · suffices
      (TopologicalSpace.Opens.map f.base).obj (imageBasicOpen f g U s) =
        (TopologicalSpace.Opens.map g.base).obj (imageBasicOpen f g U s)
      by injection this
    delta imageBasicOpen
    rw [preimage_basicOpen f, preimage_basicOpen g]
    dsimp only [Functor.op, unop_op]
    sorry
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
    /-erw [← CommRingCat.comp_apply, ← SheafedSpace.comp_c_app', ← CommRingCat.comp_apply,
      ← SheafedSpace.comp_c_app',
      SheafedSpace.congr_app (coequalizer.condition f.toShHom g.toShHom),
      CommRingCat.comp_apply, X.toRingedSpace.basicOpen_res]
    apply inf_eq_right.mpr
    refine (RingedSpace.basicOpen_le _ _).trans ?_
    rw [coequalizer.condition f.toShHom g.toShHom]-/

theorem imageBasicOpen_image_open :
    IsOpen ((coequalizer.π f.toShHom g.toShHom).hom.base '' (imageBasicOpen f g U s).1) := by
  rw [← (TopCat.homeoOfIso (PreservesCoequalizer.iso (SheafedSpace.forget _) f.toShHom
    g.toShHom)).isOpen_preimage, TopCat.coequalizer_isOpen_iff, ← Set.preimage_comp]
  erw [← TopCat.coe_comp]
  rw [PreservesCoequalizer.iso_hom, ι_comp_coequalizerComparison]
  dsimp only [SheafedSpace.forget]
  rw [imageBasicOpen_image_preimage]
  exact (imageBasicOpen f g U s).2

@[instance]
theorem coequalizer_π_stalk_isLocalHom (x : Y) :
    IsLocalHom ((coequalizer.π f.toShHom g.toShHom :).hom.stalkMap x).hom := by
  constructor
  rintro a ha
  rcases TopCat.Presheaf.germ_exist _ _ a with ⟨U, hU, s, rfl⟩
  sorry
  /-rw [-- Manually apply `elementwise_of%` to generate a `ConcreteCategory` lemma
    elementwise_of% PresheafedSpace.stalkMap_germ
      (coequalizer.π (C := SheafedSpace _) f.toShHom g.toShHom) U _ hU] at ha
  let V := imageBasicOpen f g U s
  have hV : (coequalizer.π f.toShHom g.toShHom).base ⁻¹'
      ((coequalizer.π f.toShHom g.toShHom).base '' V.1) = V.1 :=
    imageBasicOpen_image_preimage f g U s
  have hV' : V = ⟨(coequalizer.π f.toShHom g.toShHom).base ⁻¹'
      ((coequalizer.π f.toShHom g.toShHom).base '' V.1), hV.symm ▸ V.2⟩ :=
    SetLike.ext' hV.symm
  have V_open : IsOpen ((coequalizer.π f.toShHom g.toShHom).base '' V.1) :=
    imageBasicOpen_image_open f g U s
  have VleU : ⟨(coequalizer.π f.toShHom g.toShHom).base '' V.1, V_open⟩ ≤ U :=
    Set.image_subset_iff.mpr (Y.toRingedSpace.basicOpen_le _)
  have hxV : x ∈ V := ⟨hU, ha⟩
  rw [← (coequalizer f.toShHom g.toShHom).presheaf.germ_res_apply (homOfLE VleU) _
      (@Set.mem_image_of_mem _ _ (coequalizer.π f.toShHom g.toShHom).base x V.1 hxV) s]
  apply RingHom.isUnit_map
  rw [← isUnit_map_iff ((coequalizer.π f.toShHom g.toShHom :).c.app _).hom,
    ← CommRingCat.comp_apply, NatTrans.naturality, CommRingCat.comp_apply,
    ← isUnit_map_iff (Y.presheaf.map (eqToHom hV').op).hom]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
  erw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Y.presheaf.map_comp]
  convert @RingedSpace.isUnit_res_basicOpen Y.toRingedSpace (unop _)
      (((coequalizer.π f.toShHom g.toShHom).c.app (op U)) s)-/

end HasCoequalizer

/-- The coequalizer of two locally ringed spaces in the category of sheafed spaces is a locally
ringed space. -/
noncomputable def coequalizer : LocallyRingedSpace where
  toSheafedSpace := Limits.coequalizer f.toShHom g.toShHom
  isLocalRing x := by
    obtain ⟨y, rfl⟩ :=
      (TopCat.epi_iff_surjective (coequalizer.π f.toShHom g.toShHom).hom.base).mp inferInstance x
    exact ((coequalizer.π f.toShHom g.toShHom :).hom.stalkMap y).hom.domain_isLocalRing

/-- The explicit coequalizer cofork of locally ringed spaces. -/
noncomputable def coequalizerCofork : Cofork f g :=
  Cofork.ofπ (P := coequalizer f g)
    (homMk (coequalizer.π f.toShHom g.toShHom)
      -- Porting note: this used to be automatic
      (HasCoequalizer.coequalizer_π_stalk_isLocalHom  _ _))
    (forgetToSheafedSpace.map_injective (coequalizer.condition f.toShHom g.toShHom))

theorem isLocalHom_stalkMap_congr {X Y : RingedSpace} (f g : X ⟶ Y) (H : f = g) (x)
    (h : IsLocalHom (f.hom.stalkMap x).hom) :
    IsLocalHom (g.hom.stalkMap x).hom := by
  sorry
  --rw [PresheafedSpace.stalkMap.congr_hom _ _ H.symm x]; infer_instance

/-- The cofork constructed in `coequalizerCofork` is indeed a colimit cocone. -/
noncomputable def coequalizerCoforkIsColimit : IsColimit (coequalizerCofork f g) := by
  sorry /-
  apply Cofork.IsColimit.mk'
  intro s
  have e : f.toShHom ≫ s.π.toShHom = g.toShHom ≫ s.π.toShHom := by injection s.condition
  refine ⟨⟨coequalizer.desc s.π.toShHom e, ?_⟩, ?_⟩
  · intro x
    rcases (TopCat.epi_iff_surjective
      (coequalizer.π f.toShHom g.toShHom).base).mp inferInstance x with ⟨y, rfl⟩
    -- Porting note: was `apply isLocalHom_of_comp _ (PresheafedSpace.stalkMap ...)`, this
    -- used to allow you to provide the proof that `... ≫ ...` is a local ring homomorphism later,
    -- but this is no longer possible
    set h := _
    change IsLocalHom h
    suffices _ : IsLocalHom (((coequalizerCofork f g).π.1.stalkMap _).hom.comp h) by
      apply isLocalHom_of_comp _ ((coequalizerCofork f g).π.1.stalkMap _).hom
    rw [← CommRingCat.hom_ofHom h, ← CommRingCat.hom_comp]
    erw [← PresheafedSpace.stalkMap.comp]
    apply isLocalHom_stalkMap_congr _ _ (coequalizer.π_desc s.π.toShHom e).symm y
    infer_instance
  constructor
  · exact LocallyRingedSpace.Hom.ext' (coequalizer.π_desc _ _)
  intro m h
  replace h : (coequalizerCofork f g).π.toShHom ≫ m.1 = s.π.toShHom := by rw [← h]; rfl
  apply LocallyRingedSpace.Hom.ext'
  apply (colimit.isColimit (parallelPair f.toShHom g.toShHom)).uniq (Cofork.ofπ s.π.toShHom e) m.1
  rintro ⟨⟩
  · rw [← (colimit.cocone (parallelPair f.toShHom g.toShHom)).w WalkingParallelPairHom.left,
      Category.assoc]
    change _ ≫ _ ≫ _ = _ ≫ _
    congr
  · exact h-/

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
      preservesColimit_of_iso_diagram _ (diagramIsoParallelPair F).symm
    apply preservesColimit_of_preserves_colimit_cocone (coequalizerCoforkIsColimit _ _)
    apply (isColimitMapCoconeCoforkEquiv _ _).symm _
    dsimp only [forgetToSheafedSpace]
    exact coequalizerIsCoequalizer _ _⟩

end HasCoequalizer

instance : HasColimits LocallyRingedSpace :=
  has_colimits_of_hasCoequalizers_and_coproducts

noncomputable instance preservesColimits_forgetToSheafedSpace :
    PreservesColimits LocallyRingedSpace.forgetToSheafedSpace.{u} :=
  preservesColimits_of_preservesCoequalizers_and_coproducts _

end LocallyRingedSpace

end AlgebraicGeometry
