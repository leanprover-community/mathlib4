/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier, Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Fubini
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preservations of limits for bifunctors

Let `G : C₁ ⥤ C₂ ⥤ C` a functor. We introduce a class `PreservesLimit₂ K₁ K₂ G` that encodes
the hypothesis that the curried functor `F : C₁ × C₂ ⥤ C` preserves limits of the diagram
`K₁ × K₂ : J₁ × J₂ ⥤ C₁ × C₂`. We give a basic API to extract isomorphisms
$\lim_{(j_1,j_2)} G(K_1(j_1), K_2(j_2)) \simeq G(\lim K_1, \lim K_2)$
out of this typeclass.

We show (see `CategoryTheory.Limits.PreservesColimit₂.of_preservesColimits_in_each_variable`)
that if `G` preserves colimits in each variable, then `G` `PreservesColimit₂`.
-/

namespace CategoryTheory

open Category Limits

variable {J₁ J₂ : Type*} [Category J₁] [Category J₂]
  {C₁ C₂ C : Type*} [Category C₁] [Category C₂] [Category C]

/-- Given a bifunctor `G : C₁ ⥤ C₂ ⥤ C`, diagrams `K₁ : J₁ ⥤ C₁` and `K₂ : J₂ ⥤ C₂`, and cocones
over these diagrams, `G.mapCocone₂ c₁ c₂` is the cocone over the diagram `J₁ × J₂ ⥤ C` obtained
by applying `G` to both `c₁` and `c₂`. -/
@[simps!]
def Functor.mapCocone₂ (G : C₁ ⥤ C₂ ⥤ C) {K₁ : J₁ ⥤ C₁} {K₂ : J₂ ⥤ C₂}
    (c₁ : Cocone K₁) (c₂ : Cocone K₂) :
    Cocone <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) where
  pt := (G.obj c₁.pt).obj c₂.pt
  ι :=
    { app := fun ⟨j₁, j₂⟩ ↦ (G.map <| c₁.ι.app j₁).app _ ≫ (G.obj _).map (c₂.ι.app j₂)
      naturality := by
        rintro ⟨j₁, j₂⟩ ⟨k₁, k₂⟩ ⟨f₁, f₂⟩
        dsimp
        simp only [assoc, comp_id, NatTrans.naturality_assoc,
          ← Functor.map_comp, NatTrans.naturality, const_obj_map, const_obj_obj,
          ← NatTrans.comp_app_assoc, c₁.w] }

/-- Given a bifunctor `G : C₁ ⥤ C₂ ⥤ C`, diagrams `K₁ : J₁ ⥤ C₁` and `K₂ : J₂ ⥤ C₂`, and cones
over these diagrams, `G.mapCone₂ c₁ c₂` is the cone over the diagram `J₁ × J₂ ⥤ C` obtained
by applying `G` to both `c₁` and `c₂`. -/
@[simps!]
def Functor.mapCone₂ (G : C₁ ⥤ C₂ ⥤ C) {K₁ : J₁ ⥤ C₁} {K₂ : J₂ ⥤ C₂}
    (c₁ : Cone K₁) (c₂ : Cone K₂) :
    Cone <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) where
  pt := (G.obj c₁.pt).obj c₂.pt
  π :=
    { app := fun ⟨j₁, j₂⟩ ↦ (G.map <| c₁.π.app j₁).app _ ≫ (G.obj _).map (c₂.π.app j₂)
      naturality := by
        rintro ⟨j₁, j₂⟩ ⟨k₁, k₂⟩ ⟨f₁, f₂⟩
        dsimp
        simp only [assoc, id_comp, NatTrans.naturality_assoc,
          ← Functor.map_comp, NatTrans.naturality, const_obj_map, const_obj_obj,
          ← NatTrans.comp_app_assoc, c₁.w, c₂.w] }

namespace Limits

/-- A functor `PreservesColimit₂ K₁ K₂` if whenever `c₁` is a colimit cocone and `c₂` is a colimit
cocone then `G.mapCocone₂ c₁ c₂` is a colimit cocone. This can be thought of as the data of an
isomorphism
$\mathrm{colim}_{(j_1,j_2)} G(K_1(j_1),K_2(j_2)) \simeq G(\mathrm{colim} K_1,\mathrm{colim} K_2)$.
-/
class PreservesColimit₂ (K₁ : J₁ ⥤ C₁) (K₂ : J₂ ⥤ C₂) (G : C₁ ⥤ C₂ ⥤ C) : Prop where
  isColimit_mapCocone₂ {c₁ : Cocone K₁} (hc₁ : IsColimit c₁)
      {c₂ : Cocone K₂} (hc₂ : IsColimit c₂) :
    Nonempty <| IsColimit <| G.mapCocone₂ c₁ c₂

/-- A functor `PreservesLimit₂ K₁ K₂` if whenever `c₁` is a limit cone and `c₂` is a limit
cone then `G.mapCone₂ c₁ c₂` is a limit cone. This can be thought of as the data of an
isomorphism $\lim_{(j_1,j_2)} G(K_1(j_1), K_2(j_2)) \simeq G(\lim K_1, \lim K_2)$.
-/
class PreservesLimit₂ (K₁ : J₁ ⥤ C₁) (K₂ : J₂ ⥤ C₂) (G : C₁ ⥤ C₂ ⥤ C) : Prop where
  isLimit_mapCone₂ {c₁ : Cone K₁} (hc₁ : IsLimit c₁)
      {c₂ : Cone K₂} (hc₂ : IsLimit c₂) :
    Nonempty <| IsLimit <| G.mapCone₂ c₁ c₂

variable (K₁ : J₁ ⥤ C₁) (K₂ : J₂ ⥤ C₂) (G : C₁ ⥤ C₂ ⥤ C)

instance [HasColimit K₁] [HasColimit K₂] [PreservesColimit₂ K₁ K₂ G] :
    HasColimit <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) where
  exists_colimit := ⟨{
    cocone := _
    isColimit :=
      PreservesColimit₂.isColimit_mapCocone₂
        (getColimitCocone K₁).isColimit
        (getColimitCocone K₂).isColimit|>.some }⟩

instance [HasLimit K₁] [HasLimit K₂] [PreservesLimit₂ K₁ K₂ G] :
    HasLimit <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) where
  exists_limit := ⟨{
    cone := _
    isLimit :=
      PreservesLimit₂.isLimit_mapCone₂
        (getLimitCone K₁).isLimit
        (getLimitCone K₂).isLimit|>.some }⟩

namespace PreservesColimit₂

section

variable [PreservesColimit₂ K₁ K₂ G]

variable {K₁ K₂} in
/-- Extract the colimit cocone for `uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)`.
from the data of colimit cocones for `K₁` and `K₂`. -/
@[simps! cocone_pt cocone_ι_app]
noncomputable def mkColimitCocone₂ (c₁ : ColimitCocone K₁) (c₂ : ColimitCocone K₂) :
    ColimitCocone <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) where
  cocone := G.mapCocone₂ c₁.cocone c₂.cocone
  isColimit :=
    PreservesColimit₂.isColimit_mapCocone₂
      c₁.isColimit
      c₂.isColimit|>.some

variable [HasColimit K₁] [HasColimit K₂]

/-- Get a colimit cocone over `(whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)` provided the
relevant colimits exist. This colimit cocone has definitionally
`(G.obj <| colimit K₁).obj (colimit K₂)` as its cocone point. -/
noncomputable def getColimitCocone₂ :
    ColimitCocone <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) :=
  mkColimitCocone₂ G (getColimitCocone K₁) (getColimitCocone K₂)

-- The simp forms below are preferred over the ones generated by @[simps].

@[simp]
lemma getColimitCocone₂_cocone_pt :
    (getColimitCocone₂ K₁ K₂ G).cocone.pt = (G.obj <| colimit K₁).obj (colimit K₂) :=
  rfl

@[simp]
lemma getColimitCocone₂_cocone_ι_app (j : J₁ × J₂) :
    (getColimitCocone₂ K₁ K₂ G).cocone.ι.app j =
    (G.map <| colimit.ι K₁ j.1).app (K₂.obj j.2) ≫ (G.obj <| colimit K₁).map (colimit.ι K₂ j.2) :=
  rfl

/-- Extract the isomorphism between
`colim (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G))` and
`(G.obj (colim K₁)).obj (colim K₂)` from a `PreservesColimit₂` instance, provided the relevant
colimits exist. -/
noncomputable def isoColimitUncurryWhiskeringLeft₂ :
    colimit (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)) ≅
    (G.obj <| colimit K₁).obj (colimit K₂) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (getColimitCocone₂ K₁ K₂ G).isColimit

/-- Characterize the forward direction of the isomorphism
`PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂` w.r.t the canonical maps to the colimit. -/
@[reassoc (attr := simp)]
lemma ι_comp_isoColimitUncurryWhiskeringLeft₂_hom (j : J₁ × J₂) :
    colimit.ι (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)) j ≫
      (PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂ K₁ K₂ G).hom =
    (G.map <| colimit.ι K₁ j.1).app _ ≫ (G.obj _).map (colimit.ι K₂ j.2) := by
  dsimp [PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂, Functor.mapCocone₂]
  aesop_cat

/-- Characterize the forward direction of the isomorphism
`PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂` w.r.t the canonical maps to the colimit. -/
@[reassoc (attr := simp)]
lemma map_ι_comp_isoColimitUncurryWhiskeringLeft₂_inv (j : J₁ × J₂) :
    (G.map (colimit.ι K₁ j.1)).app _ ≫ (G.obj _).map (colimit.ι K₂ j.2) ≫
      (PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂ K₁ K₂ G).inv =
    colimit.ι (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)) j := by
  rw [← Category.assoc, Iso.comp_inv_eq]
  simp

end

/-- If a bifunctor preserves separately colimits of `K₁` in the first variable and colimits
of `K₂` in the second variable, then it preserves colimit of the pair `K₁, K₂`. -/
instance of_preservesColimits_in_each_variable
    [∀ x : C₂, PreservesColimit K₁ (G.flip.obj x)] [∀ x : C₁, PreservesColimit K₂ (G.obj x)] :
    PreservesColimit₂ K₁ K₂ G where
  isColimit_mapCocone₂ {c₁} hc₁ {c₂} hc₂ :=
    let Q₀ : DiagramOfCocones (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) :=
      { obj j₁ := G.obj (K₁.obj j₁) |>.mapCocone c₂
        map f := { hom := G.map (K₁.map f)|>.app c₂.pt }}
    let P : ∀ j₁, IsColimit (Q₀.obj j₁) := fun j ↦ (PreservesColimit.preserves hc₂).some
    let E₀ : Q₀.coconePoints ≅ K₁ ⋙ G.flip.obj c₂.pt := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    let E₁ : (Cocones.precompose E₀.hom).obj (coconeOfCoconeUncurry P <| G.mapCocone₂ c₁ c₂) ≅
        (G.flip.obj c₂.pt).mapCocone c₁ :=
      Cocones.ext
        (Iso.refl _)
        (fun j₁ => by
          dsimp [E₀, Q₀]
          simp only [id_comp, comp_id, E₀, Q₀]
          let s : Cocone (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G |>.obj j₁) := ?_
          change (P j₁).desc s = _
          symm
          apply (P j₁).hom_ext
          intro j₂
          haveI := (P j₁).fac s j₂
          simp only [NatTrans.id_app, NatTrans.comp_app, Functor.mapCocone_pt,
            Functor.const_obj_obj, Functor.mapCocone_ι_app, Q₀, E₀, s] at this
          simp only [NatTrans.id_app, NatTrans.comp_app, Functor.mapCocone_pt,
            Functor.const_obj_obj, Functor.mapCocone_ι_app, NatTrans.naturality, this, Q₀, s, E₀])
    ⟨IsColimit.ofCoconeUncurry P <| IsColimit.precomposeHomEquiv E₀ _ <|
      IsColimit.ofIsoColimit (PreservesColimit.preserves hc₁).some E₁.symm⟩

theorem of_preservesColimit₂_flip [PreservesColimit₂ K₁ K₂ G] : PreservesColimit₂ K₂ K₁ G.flip where
  isColimit_mapCocone₂ {c₁} hc₁ {c₂} hc₂ := by
    constructor
    let E₀ : uncurry.obj (whiskeringLeft₂ C|>.obj K₂|>.obj K₁|>.obj G.flip) ≅
        uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G).flip :=
      Iso.refl _
    let E₁ : uncurry.obj (whiskeringLeft₂ C|>.obj K₂|>.obj K₁|>.obj G.flip) ≅
        Prod.swap _ _ ⋙ uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) :=
      E₀ ≪≫ uncurryObjFlip _
    refine IsColimit.precomposeInvEquiv E₁ _ ?_
    apply IsColimit.ofWhiskerEquivalence (e := Prod.braiding _ _)
    refine IsColimit.equivOfNatIsoOfIso (Iso.refl _) (G.mapCocone₂ c₂ c₁) _ ?_ |>.toFun
      (PreservesColimit₂.isColimit_mapCocone₂ hc₂ hc₁).some
    refine Cocones.ext (Iso.refl _) (fun ⟨j₁, j₂⟩ ↦ by simp [E₁, E₀])

end PreservesColimit₂

namespace PreservesLimit₂

section

variable [PreservesLimit₂ K₁ K₂ G]

variable {K₁ K₂} in
/-- Extract the limit cone for `uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)`.
from the data of limit cones for `K₁` and `K₂`. -/
@[simps! cone_pt cone_π_app]
noncomputable def mkLimitCone₂ (c₁ : LimitCone K₁) (c₂ : LimitCone K₂) :
    LimitCone <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) where
  cone := G.mapCone₂ c₁.cone c₂.cone
  isLimit :=
    PreservesLimit₂.isLimit_mapCone₂
      c₁.isLimit
      c₂.isLimit|>.some

variable [HasLimit K₁] [HasLimit K₂]

/-- Get a limit cone over `(whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)` provided the
relevant limits exist. This limit cone has definitionally `(G.obj <| limit K₁).obj (limit K₂)` as
its cone point. -/
noncomputable def getLimitCone₂ :
    LimitCone <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) :=
  mkLimitCone₂ G (getLimitCone K₁) (getLimitCone K₂)

-- The simp forms below are preferred over the ones generated by @[simps].

@[simp]
lemma getLimitCone₂_cone_pt :
    (getLimitCone₂ K₁ K₂ G).cone.pt = (G.obj <| limit K₁).obj (limit K₂) :=
  rfl

@[simp]
lemma getLimitCone₂_cone_π_app (x : J₁ × J₂) :
    (getLimitCone₂ K₁ K₂ G).cone.π.app x =
    (G.map (limit.π K₁ x.1)).app (limit K₂) ≫ (G.obj (K₁.obj x.1)).map (limit.π K₂ x.2) :=
  rfl

/-- Extract the isomorphism between
`colim (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G))` and
`(G.obj (colim K₁)).obj (colim K₂)` from a `PreservesLimit₂` instance, provided the relevant
limits exist. -/
noncomputable def isoLimitUncurryWhiskeringLeft₂ :
    limit (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)) ≅
    (G.obj <| limit K₁).obj (limit K₂) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (getLimitCone₂ K₁ K₂ G).isLimit

/-- Characterize the inverse direction of the isomorphism
`PreservesLimit₂.isoLimitUncurryWhiskeringLeft₂` w.r.t the canonical maps to the limit. -/
@[reassoc (attr := simp)]
lemma π_comp_isoLimitUncurryWhiskeringLeft₂_hom (j : J₁ × J₂) :
    (PreservesLimit₂.isoLimitUncurryWhiskeringLeft₂ K₁ K₂ G).inv ≫
      limit.π (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)) j =
    (G.map <| limit.π K₁ j.1).app _ ≫ (G.obj _).map (limit.π K₂ j.2) := by
  dsimp [PreservesLimit₂.isoLimitUncurryWhiskeringLeft₂, Functor.mapCone₂]
  aesop_cat

/-- Characterize the forward direction of the isomorphism
`PreservesLimit₂.isoLimitUncurryWhiskeringLeft₂` w.r.t the canonical maps to the limit. -/
@[reassoc (attr := simp)]
lemma map_π_comp_isoLimitUncurryWhiskeringLeft₂_inv (j : J₁ × J₂) :
    (PreservesLimit₂.isoLimitUncurryWhiskeringLeft₂ K₁ K₂ G).hom ≫
      (G.map (limit.π K₁ j.1)).app _ ≫ (G.obj _).map (limit.π K₂ j.2) =
    limit.π (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)) j := by
  rw [Eq.comm, ← Iso.inv_comp_eq]
  simp

end

/-- If a bifunctor preserves separately limits of `K₁` in the first variable and limits
of `K₂` in the second variable, then it preserves colimit of the pair of cones `K₁, K₂`. -/
instance of_preservesLimits_in_each_variable
    [∀ x : C₂, PreservesLimit K₁ (G.flip.obj x)] [∀ x : C₁, PreservesLimit K₂ (G.obj x)] :
    PreservesLimit₂ K₁ K₂ G where
  isLimit_mapCone₂ {c₁} hc₁ {c₂} hc₂ :=
    let Q₀ : DiagramOfCones (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) :=
      { obj j₁ := G.obj (K₁.obj j₁) |>.mapCone c₂
        map f := { hom := G.map (K₁.map f)|>.app c₂.pt }}
    let P : ∀ j₁, IsLimit (Q₀.obj j₁) := fun _ => (PreservesLimit.preserves hc₂).some
    let E₀ : Q₀.conePoints ≅ K₁ ⋙ G.flip.obj c₂.pt := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    let E₁ : (Cones.postcompose E₀.hom).obj (coneOfConeUncurry P <| G.mapCone₂ c₁ c₂) ≅
        (G.flip.obj c₂.pt).mapCone c₁ :=
      Cones.ext
        (Iso.refl _)
        (fun j₁ => by
          dsimp [E₀, Q₀]
          simp only [id_comp, comp_id, E₀, Q₀]
          let s : Cone (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G |>.obj j₁) := ?_
          change (P j₁).lift s = _
          symm
          apply (P j₁).hom_ext
          intro j₂
          haveI := (P j₁).fac s j₂
          simp only [whiskeringLeft₂_obj_obj_obj_obj_obj, NatTrans.id_app, NatTrans.comp_app,
            Functor.mapCone_pt, Functor.mapCone_π_app, s, Q₀, E₀] at this
          simp only [whiskeringLeft₂_obj_obj_obj_obj_obj, NatTrans.id_app, NatTrans.comp_app,
            Functor.mapCone_pt, Functor.mapCone_π_app, this, Q₀, s, E₀])
    ⟨IsLimit.ofConeOfConeUncurry P <| IsLimit.postcomposeHomEquiv E₀ _ <|
      IsLimit.ofIsoLimit (PreservesLimit.preserves hc₁).some E₁.symm⟩

theorem of_preservesLimit₂_flip [PreservesLimit₂ K₁ K₂ G] : PreservesLimit₂ K₂ K₁ G.flip where
  isLimit_mapCone₂ {c₁} hc₁ {c₂} hc₂ := by
    constructor
    let E₀ : uncurry.obj (whiskeringLeft₂ C|>.obj K₂|>.obj K₁|>.obj G.flip) ≅
        uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G).flip :=
      Iso.refl _
    let E₁ : uncurry.obj (whiskeringLeft₂ C|>.obj K₂|>.obj K₁|>.obj G.flip) ≅
        Prod.swap _ _ ⋙ uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) :=
      E₀ ≪≫ uncurryObjFlip _
    refine IsLimit.postcomposeHomEquiv E₁ _ ?_
    apply IsLimit.ofWhiskerEquivalence (e := Prod.braiding _ _)
    refine IsLimit.equivOfNatIsoOfIso (Iso.refl _) (G.mapCone₂ c₂ c₁) _ ?_ |>.toFun
      (PreservesLimit₂.isLimit_mapCone₂ hc₂ hc₁).some
    refine Cones.ext (Iso.refl _) (fun ⟨j₁, j₂⟩ ↦ by simp [E₁, E₀])

end PreservesLimit₂

end Limits

end CategoryTheory
