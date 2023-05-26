/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module topology.sheaves.sheaf_condition.pairwise_intersections
! leanprover-community/mathlib commit 8a318021995877a44630c898d0b2bc376fceef3b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Sheaves.SheafCondition.OpensLeCover
import Mathbin.CategoryTheory.Limits.Final
import Mathbin.CategoryTheory.Limits.Preserves.Basic
import Mathbin.CategoryTheory.Category.Pairwise
import Mathbin.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathbin.Algebra.Category.Ring.Constructions

/-!
# Equivalent formulations of the sheaf condition

We give an equivalent formulation of the sheaf condition.

Given any indexed type `ι`, we define `overlap ι`,
a category with objects corresponding to
* individual open sets, `single i`, and
* intersections of pairs of open sets, `pair i j`,
with morphisms from `pair i j` to both `single i` and `single j`.

Any open cover `U : ι → opens X` provides a functor `diagram U : overlap ι ⥤ (opens X)ᵒᵖ`.

There is a canonical cone over this functor, `cone U`, whose cone point is `supr U`,
and in fact this is a limit cone.

A presheaf `F : presheaf C X` is a sheaf precisely if it preserves this limit.
We express this in two equivalent ways, as
* `is_limit (F.map_cone (cone U))`, or
* `preserves_limit (diagram U) F`

We show that this sheaf condition is equivalent to the `opens_le_cover` sheaf condition, and
thereby also equivalent to the default sheaf condition.
-/


noncomputable section

universe w v u

open TopologicalSpace TopCat Opposite CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}}

namespace TopCat.Presheaf

section

/-- An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`is_sheaf_iff_is_sheaf_pairwise_intersections`).

A presheaf is a sheaf if `F` sends the cone `(pairwise.cocone U).op` to a limit cone.
(Recall `pairwise.cocone U` has cone point `supr U`, mapping down to the `U i` and the `U i ⊓ U j`.)
-/
def IsSheafPairwiseIntersections (F : Presheaf C X) : Prop :=
  ∀ ⦃ι : Type w⦄ (U : ι → Opens X), Nonempty (IsLimit (F.mapCone (Pairwise.cocone U).op))
#align Top.presheaf.is_sheaf_pairwise_intersections TopCat.Presheaf.IsSheafPairwiseIntersections

/-- An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`is_sheaf_iff_is_sheaf_preserves_limit_pairwise_intersections`).

A presheaf is a sheaf if `F` preserves the limit of `pairwise.diagram U`.
(Recall `pairwise.diagram U` is the diagram consisting of the pairwise intersections
`U i ⊓ U j` mapping into the open sets `U i`. This diagram has limit `supr U`.)
-/
def IsSheafPreservesLimitPairwiseIntersections (F : Presheaf C X) : Prop :=
  ∀ ⦃ι : Type w⦄ (U : ι → Opens X), Nonempty (PreservesLimit (Pairwise.diagram U).op F)
#align Top.presheaf.is_sheaf_preserves_limit_pairwise_intersections TopCat.Presheaf.IsSheafPreservesLimitPairwiseIntersections

end

namespace SheafCondition

variable {ι : Type w} (U : ι → Opens X)

open CategoryTheory.Pairwise

/-- Implementation detail:
the object level of `pairwise_to_opens_le_cover : pairwise ι ⥤ opens_le_cover U`
-/
@[simp]
def pairwiseToOpensLeCoverObj : Pairwise ι → OpensLeCover U
  | single i => ⟨U i, ⟨i, le_rfl⟩⟩
  | pair i j => ⟨U i ⊓ U j, ⟨i, inf_le_left⟩⟩
#align Top.presheaf.sheaf_condition.pairwise_to_opens_le_cover_obj TopCat.Presheaf.SheafCondition.pairwiseToOpensLeCoverObj

open CategoryTheory.Pairwise.Hom

/-- Implementation detail:
the morphism level of `pairwise_to_opens_le_cover : pairwise ι ⥤ opens_le_cover U`
-/
def pairwiseToOpensLeCoverMap :
    ∀ {V W : Pairwise ι}, (V ⟶ W) → (pairwiseToOpensLeCoverObj U V ⟶ pairwiseToOpensLeCoverObj U W)
  | _, _, id_single i => 𝟙 _
  | _, _, id_pair i j => 𝟙 _
  | _, _, left i j => homOfLE inf_le_left
  | _, _, right i j => homOfLE inf_le_right
#align Top.presheaf.sheaf_condition.pairwise_to_opens_le_cover_map TopCat.Presheaf.SheafCondition.pairwiseToOpensLeCoverMap

/-- The category of single and double intersections of the `U i` maps into the category
of open sets below some `U i`.
-/
@[simps]
def pairwiseToOpensLeCover : Pairwise ι ⥤ OpensLeCover U
    where
  obj := pairwiseToOpensLeCoverObj U
  map V W i := pairwiseToOpensLeCoverMap U i
#align Top.presheaf.sheaf_condition.pairwise_to_opens_le_cover TopCat.Presheaf.SheafCondition.pairwiseToOpensLeCover

instance (V : OpensLeCover U) : Nonempty (StructuredArrow V (pairwiseToOpensLeCover U)) :=
  ⟨@StructuredArrow.mk _ _ _ _ _ (single V.index) _ V.hom_to_index⟩

-- This is a case bash: for each pair of types of objects in `pairwise ι`,
-- we have to explicitly construct a zigzag.
/-- The diagram consisting of the `U i` and `U i ⊓ U j` is cofinal in the diagram
of all opens contained in some `U i`.
-/
instance : Functor.Final (pairwiseToOpensLeCover U) :=
  ⟨fun V =>
    isConnected_of_zigzag fun A B =>
      by
      rcases A with ⟨⟨⟨⟩⟩, ⟨i⟩ | ⟨i, j⟩, a⟩ <;> rcases B with ⟨⟨⟨⟩⟩, ⟨i'⟩ | ⟨i', j'⟩, b⟩ <;>
        dsimp at *
      · refine'
          ⟨[{   left := ⟨⟨⟩⟩
                right := pair i i'
                Hom := (le_inf a.le b.le).Hom }, _], _, rfl⟩
        exact
          List.Chain.cons
            (Or.inr
              ⟨{  left := 𝟙 _
                  right := left i i' }⟩)
            (List.Chain.cons
              (Or.inl
                ⟨{  left := 𝟙 _
                    right := right i i' }⟩)
              List.Chain.nil)
      · refine'
          ⟨[{   left := ⟨⟨⟩⟩
                right := pair i' i
                Hom := (le_inf (b.le.trans inf_le_left) a.le).Hom },
              { left := ⟨⟨⟩⟩
                right := single i'
                Hom := (b.le.trans inf_le_left).Hom }, _], _, rfl⟩
        exact
          List.Chain.cons
            (Or.inr
              ⟨{  left := 𝟙 _
                  right := right i' i }⟩)
            (List.Chain.cons
              (Or.inl
                ⟨{  left := 𝟙 _
                    right := left i' i }⟩)
              (List.Chain.cons
                (Or.inr
                  ⟨{  left := 𝟙 _
                      right := left i' j' }⟩)
                List.Chain.nil))
      · refine'
          ⟨[{   left := ⟨⟨⟩⟩
                right := single i
                Hom := (a.le.trans inf_le_left).Hom },
              { left := ⟨⟨⟩⟩
                right := pair i i'
                Hom := (le_inf (a.le.trans inf_le_left) b.le).Hom }, _], _, rfl⟩
        exact
          List.Chain.cons
            (Or.inl
              ⟨{  left := 𝟙 _
                  right := left i j }⟩)
            (List.Chain.cons
              (Or.inr
                ⟨{  left := 𝟙 _
                    right := left i i' }⟩)
              (List.Chain.cons
                (Or.inl
                  ⟨{  left := 𝟙 _
                      right := right i i' }⟩)
                List.Chain.nil))
      · refine'
          ⟨[{   left := ⟨⟨⟩⟩
                right := single i
                Hom := (a.le.trans inf_le_left).Hom },
              { left := ⟨⟨⟩⟩
                right := pair i i'
                Hom := (le_inf (a.le.trans inf_le_left) (b.le.trans inf_le_left)).Hom },
              { left := ⟨⟨⟩⟩
                right := single i'
                Hom := (b.le.trans inf_le_left).Hom }, _], _, rfl⟩
        exact
          List.Chain.cons
            (Or.inl
              ⟨{  left := 𝟙 _
                  right := left i j }⟩)
            (List.Chain.cons
              (Or.inr
                ⟨{  left := 𝟙 _
                    right := left i i' }⟩)
              (List.Chain.cons
                (Or.inl
                  ⟨{  left := 𝟙 _
                      right := right i i' }⟩)
                (List.Chain.cons
                  (Or.inr
                    ⟨{  left := 𝟙 _
                        right := left i' j' }⟩)
                  List.Chain.nil)))⟩

/-- The diagram in `opens X` indexed by pairwise intersections from `U` is isomorphic
(in fact, equal) to the diagram factored through `opens_le_cover U`.
-/
def pairwiseDiagramIso : Pairwise.diagram U ≅ pairwiseToOpensLeCover U ⋙ fullSubcategoryInclusion _
    where
  Hom := { app := by rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }
  inv := { app := by rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }
#align Top.presheaf.sheaf_condition.pairwise_diagram_iso TopCat.Presheaf.SheafCondition.pairwiseDiagramIso

/--
The cocone `pairwise.cocone U` with cocone point `supr U` over `pairwise.diagram U` is isomorphic
to the cocone `opens_le_cover_cocone U` (with the same cocone point)
after appropriate whiskering and postcomposition.
-/
def pairwiseCoconeIso :
    (Pairwise.cocone U).op ≅
      (Cones.postcomposeEquivalence (NatIso.op (pairwiseDiagramIso U : _) : _)).Functor.obj
        ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op) :=
  Cones.ext (Iso.refl _) (by tidy)
#align Top.presheaf.sheaf_condition.pairwise_cocone_iso TopCat.Presheaf.SheafCondition.pairwiseCoconeIso

end SheafCondition

open SheafCondition

variable (F : Presheaf C X)

/-- The sheaf condition
in terms of a limit diagram over all `{ V : opens X // ∃ i, V ≤ U i }`
is equivalent to the reformulation
in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
theorem isSheafOpensLeCover_iff_isSheafPairwiseIntersections :
    F.IsSheafOpensLeCover ↔ F.IsSheafPairwiseIntersections :=
  forall₂_congr fun ι U =>
    Equiv.nonempty_congr <|
      calc
        IsLimit (F.mapCone (opensLeCoverCocone U).op) ≃
            IsLimit ((F.mapCone (opensLeCoverCocone U).op).whisker (pairwiseToOpensLeCover U).op) :=
          (Functor.Initial.isLimitWhiskerEquiv (pairwiseToOpensLeCover U).op _).symm
        _ ≃ IsLimit (F.mapCone ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op)) :=
          (IsLimit.equivIsoLimit F.mapConeWhisker.symm)
        _ ≃
            IsLimit
              ((Cones.postcomposeEquivalence _).Functor.obj
                (F.mapCone ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op))) :=
          (IsLimit.postcomposeHomEquiv _ _).symm
        _ ≃
            IsLimit
              (F.mapCone
                ((Cones.postcomposeEquivalence _).Functor.obj
                  ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op))) :=
          (IsLimit.equivIsoLimit (Functor.mapConePostcomposeEquivalenceFunctor _).symm)
        _ ≃ IsLimit (F.mapCone (Pairwise.cocone U).op) :=
          IsLimit.equivIsoLimit ((Cones.functoriality _ _).mapIso (pairwiseCoconeIso U : _).symm)
        
#align Top.presheaf.is_sheaf_opens_le_cover_iff_is_sheaf_pairwise_intersections TopCat.Presheaf.isSheafOpensLeCover_iff_isSheafPairwiseIntersections

/-- The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
theorem isSheaf_iff_isSheafPairwiseIntersections : F.IsSheaf ↔ F.IsSheafPairwiseIntersections := by
  rw [is_sheaf_iff_is_sheaf_opens_le_cover,
    is_sheaf_opens_le_cover_iff_is_sheaf_pairwise_intersections]
#align Top.presheaf.is_sheaf_iff_is_sheaf_pairwise_intersections TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections

/-- The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of the presheaf preserving the limit of the diagram
consisting of the `U i` and `U i ⊓ U j`.
-/
theorem isSheaf_iff_isSheafPreservesLimitPairwiseIntersections :
    F.IsSheaf ↔ F.IsSheafPreservesLimitPairwiseIntersections :=
  by
  rw [is_sheaf_iff_is_sheaf_pairwise_intersections]
  constructor
  · intro h ι U
    exact ⟨preserves_limit_of_preserves_limit_cone (pairwise.cocone_is_colimit U).op (h U).some⟩
  · intro h ι U
    haveI := (h U).some
    exact ⟨preserves_limit.preserves (pairwise.cocone_is_colimit U).op⟩
#align Top.presheaf.is_sheaf_iff_is_sheaf_preserves_limit_pairwise_intersections TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections

end TopCat.Presheaf

namespace TopCat.Sheaf

variable (F : X.Sheaf C) (U V : Opens X)

open CategoryTheory.Limits

/-- For a sheaf `F`, `F(U ⊔ V)` is the pullback of `F(U) ⟶ F(U ⊓ V)` and `F(V) ⟶ F(U ⊓ V)`.
This is the pullback cone. -/
def interUnionPullbackCone :
    PullbackCone (F.1.map (homOfLE inf_le_left : U ⊓ V ⟶ _).op)
      (F.1.map (homOfLE inf_le_right).op) :=
  PullbackCone.mk (F.1.map (homOfLE le_sup_left).op) (F.1.map (homOfLE le_sup_right).op)
    (by
      rw [← F.1.map_comp, ← F.1.map_comp]
      congr )
#align Top.sheaf.inter_union_pullback_cone TopCat.Sheaf.interUnionPullbackCone

@[simp]
theorem interUnionPullbackCone_pt : (interUnionPullbackCone F U V).pt = F.1.obj (op <| U ⊔ V) :=
  rfl
#align Top.sheaf.inter_union_pullback_cone_X TopCat.Sheaf.interUnionPullbackCone_pt

@[simp]
theorem interUnionPullbackCone_fst :
    (interUnionPullbackCone F U V).fst = F.1.map (homOfLE le_sup_left).op :=
  rfl
#align Top.sheaf.inter_union_pullback_cone_fst TopCat.Sheaf.interUnionPullbackCone_fst

@[simp]
theorem interUnionPullbackCone_snd :
    (interUnionPullbackCone F U V).snd = F.1.map (homOfLE le_sup_right).op :=
  rfl
#align Top.sheaf.inter_union_pullback_cone_snd TopCat.Sheaf.interUnionPullbackCone_snd

variable
  (s :
    PullbackCone (F.1.map (homOfLE inf_le_left : U ⊓ V ⟶ _).op) (F.1.map (homOfLE inf_le_right).op))

/-- (Implementation).
Every cone over `F(U) ⟶ F(U ⊓ V)` and `F(V) ⟶ F(U ⊓ V)` factors through `F(U ⊔ V)`.
-/
def interUnionPullbackConeLift : s.pt ⟶ F.1.obj (op (U ⊔ V)) :=
  by
  let ι : ULift.{w} walking_pair → opens X := fun j => walking_pair.cases_on j.down U V
  have hι : U ⊔ V = iSup ι := by
    ext
    rw [opens.coe_supr, Set.mem_iUnion]
    constructor
    · rintro (h | h)
      exacts[⟨⟨walking_pair.left⟩, h⟩, ⟨⟨walking_pair.right⟩, h⟩]
    · rintro ⟨⟨_ | _⟩, h⟩
      exacts[Or.inl h, Or.inr h]
  refine'
    (F.presheaf.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 ι).some.lift
        ⟨s.X,
          { app := _
            naturality' := _ }⟩ ≫
      F.1.map (eq_to_hom hι).op
  · apply Opposite.rec'
    rintro ((_ | _) | (_ | _))
    exacts[s.fst, s.snd, s.fst ≫ F.1.map (hom_of_le inf_le_left).op,
      s.snd ≫ F.1.map (hom_of_le inf_le_left).op]
  rintro i j f
  induction i using Opposite.rec'
  induction j using Opposite.rec'
  let g : j ⟶ i := f.unop
  have : f = g.op := rfl
  clear_value g
  subst this
  rcases i with (⟨⟨_ | _⟩⟩ | ⟨⟨_ | _⟩, ⟨_⟩⟩) <;> rcases j with (⟨⟨_ | _⟩⟩ | ⟨⟨_ | _⟩, ⟨_⟩⟩) <;>
        rcases g with ⟨⟩ <;>
      dsimp <;>
    simp only [category.id_comp, s.condition, CategoryTheory.Functor.map_id, category.comp_id]
  · rw [← cancel_mono (F.1.map (eq_to_hom <| inf_comm : U ⊓ V ⟶ _).op), category.assoc,
      category.assoc]
    erw [← F.1.map_comp, ← F.1.map_comp]
    convert s.condition.symm
#align Top.sheaf.inter_union_pullback_cone_lift TopCat.Sheaf.interUnionPullbackConeLift

theorem interUnionPullbackConeLift_left :
    interUnionPullbackConeLift F U V s ≫ F.1.map (homOfLE le_sup_left).op = s.fst :=
  by
  erw [category.assoc, ← F.1.map_comp]
  exact
    (F.presheaf.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 _).some.fac _
      (op <| pairwise.single (ULift.up walking_pair.left))
#align Top.sheaf.inter_union_pullback_cone_lift_left TopCat.Sheaf.interUnionPullbackConeLift_left

theorem interUnionPullbackConeLift_right :
    interUnionPullbackConeLift F U V s ≫ F.1.map (homOfLE le_sup_right).op = s.snd :=
  by
  erw [category.assoc, ← F.1.map_comp]
  exact
    (F.presheaf.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 _).some.fac _
      (op <| pairwise.single (ULift.up walking_pair.right))
#align Top.sheaf.inter_union_pullback_cone_lift_right TopCat.Sheaf.interUnionPullbackConeLift_right

/-- For a sheaf `F`, `F(U ⊔ V)` is the pullback of `F(U) ⟶ F(U ⊓ V)` and `F(V) ⟶ F(U ⊓ V)`. -/
def isLimitPullbackCone : IsLimit (interUnionPullbackCone F U V) :=
  by
  let ι : ULift.{w} walking_pair → opens X := fun ⟨j⟩ => walking_pair.cases_on j U V
  have hι : U ⊔ V = iSup ι := by
    ext
    rw [opens.coe_supr, Set.mem_iUnion]
    constructor
    · rintro (h | h)
      exacts[⟨⟨walking_pair.left⟩, h⟩, ⟨⟨walking_pair.right⟩, h⟩]
    · rintro ⟨⟨_ | _⟩, h⟩
      exacts[Or.inl h, Or.inr h]
  apply pullback_cone.is_limit_aux'
  intro s
  use inter_union_pullback_cone_lift F U V s
  refine' ⟨_, _, _⟩
  · apply inter_union_pullback_cone_lift_left
  · apply inter_union_pullback_cone_lift_right
  · intro m h₁ h₂
    rw [← cancel_mono (F.1.map (eq_to_hom hι.symm).op)]
    apply (F.presheaf.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 ι).some.hom_ext
    apply Opposite.rec'
    rintro ((_ | _) | (_ | _)) <;> rw [category.assoc, category.assoc]
    · erw [← F.1.map_comp]
      convert h₁
      apply inter_union_pullback_cone_lift_left
    · erw [← F.1.map_comp]
      convert h₂
      apply inter_union_pullback_cone_lift_right
    all_goals
      dsimp only [functor.op, pairwise.cocone_ι_app, functor.map_cone_π_app, cocone.op,
        pairwise.cocone_ι_app_2, unop_op, op_comp, nat_trans.op]
      simp_rw [F.1.map_comp, ← category.assoc]
      congr 1
      simp_rw [category.assoc, ← F.1.map_comp]
    · convert h₁
      apply inter_union_pullback_cone_lift_left
    · convert h₂
      apply inter_union_pullback_cone_lift_right
#align Top.sheaf.is_limit_pullback_cone TopCat.Sheaf.isLimitPullbackCone

/-- If `U, V` are disjoint, then `F(U ⊔ V) = F(U) × F(V)`. -/
def isProductOfDisjoint (h : U ⊓ V = ⊥) :
    IsLimit
      (BinaryFan.mk (F.1.map (homOfLE le_sup_left : _ ⟶ U ⊔ V).op)
        (F.1.map (homOfLE le_sup_right : _ ⟶ U ⊔ V).op)) :=
  isProductOfIsTerminalIsPullback _ _ _ _ (F.isTerminalOfEqEmpty h) (isLimitPullbackCone F U V)
#align Top.sheaf.is_product_of_disjoint TopCat.Sheaf.isProductOfDisjoint

/-- `F(U ⊔ V)` is isomorphic to the `eq_locus` of the two maps `F(U) × F(V) ⟶ F(U ⊓ V)`. -/
def objSupIsoProdEqLocus {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) :
    F.1.obj (op <| U ⊔ V) ≅ CommRingCat.of (RingHom.eqLocus _ _) :=
  (F.isLimitPullbackCone U V).conePointUniqueUpToIso (CommRingCat.pullbackConeIsLimit _ _)
#align Top.sheaf.obj_sup_iso_prod_eq_locus TopCat.Sheaf.objSupIsoProdEqLocus

theorem objSupIsoProdEqLocus_hom_fst {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    ((F.objSupIsoProdEqLocus U V).Hom x).1.fst = F.1.map (homOfLE le_sup_left).op x :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x
#align Top.sheaf.obj_sup_iso_prod_eq_locus_hom_fst TopCat.Sheaf.objSupIsoProdEqLocus_hom_fst

theorem objSupIsoProdEqLocus_hom_snd {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    ((F.objSupIsoProdEqLocus U V).Hom x).1.snd = F.1.map (homOfLE le_sup_right).op x :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x
#align Top.sheaf.obj_sup_iso_prod_eq_locus_hom_snd TopCat.Sheaf.objSupIsoProdEqLocus_hom_snd

theorem objSupIsoProdEqLocus_inv_fst {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    F.1.map (homOfLE le_sup_left).op ((F.objSupIsoProdEqLocus U V).inv x) = x.1.1 :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x
#align Top.sheaf.obj_sup_iso_prod_eq_locus_inv_fst TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst

theorem objSupIsoProdEqLocus_inv_snd {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    F.1.map (homOfLE le_sup_right).op ((F.objSupIsoProdEqLocus U V).inv x) = x.1.2 :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x
#align Top.sheaf.obj_sup_iso_prod_eq_locus_inv_snd TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd

end TopCat.Sheaf

