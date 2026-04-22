/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pullbacks and pushouts in `C` and `Cᵒᵖ`

We construct pullbacks and pushouts in the opposite categories.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {J : Type u₂} [Category.{v₂} J]

instance hasPullbacks_opposite [HasPushouts C] : HasPullbacks Cᵒᵖ := by
  haveI : HasColimitsOfShape WalkingCospanᵒᵖ C :=
    hasColimitsOfShape_of_equivalence walkingCospanOpEquiv.symm
  apply hasLimitsOfShape_op_of_hasColimitsOfShape

instance hasPushouts_opposite [HasPullbacks C] : HasPushouts Cᵒᵖ := by
  haveI : HasLimitsOfShape WalkingSpanᵒᵖ C :=
    hasLimitsOfShape_of_equivalence walkingSpanOpEquiv.symm
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism relating `Span f.op g.op` and `(Cospan f g).op` -/
@[simps!]
def spanOp {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    span f.op g.op ≅ walkingCospanOpEquiv.inverse ⋙ (cospan f g).op :=
  NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism relating `span f.unop g.unop` and `(cospan f g).leftOp` -/
@[simps!]
def spanUnop {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) :
    span f.unop g.unop ≅ walkingCospanOpEquiv.inverse ⋙ (cospan f g).leftOp :=
  NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

/-- The canonical isomorphism relating `(Cospan f g).op` and `Span f.op g.op` -/
@[simps!]
def opCospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).op ≅ walkingCospanOpEquiv.functor ⋙ span f.op g.op :=
  calc
    (cospan f g).op ≅ 𝟭 _ ⋙ (cospan f g).op := .refl _
    _ ≅ (walkingCospanOpEquiv.functor ⋙ walkingCospanOpEquiv.inverse) ⋙ (cospan f g).op :=
      isoWhiskerRight walkingCospanOpEquiv.unitIso _
    _ ≅ walkingCospanOpEquiv.functor ⋙ walkingCospanOpEquiv.inverse ⋙ (cospan f g).op :=
      Functor.associator _ _ _
    _ ≅ walkingCospanOpEquiv.functor ⋙ span f.op g.op := isoWhiskerLeft _ (spanOp f g).symm

set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism relating `Cospan f.op g.op` and `(Span f g).op` -/
@[simps!]
def cospanOp {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    cospan f.op g.op ≅ walkingSpanOpEquiv.inverse ⋙ (span f g).op :=
  NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism relating `cospan f.unop g.unop` and `(span f g).leftOp` -/
@[simps!]
def cospanUnop {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z) :
    cospan f.unop g.unop ≅ walkingSpanOpEquiv.inverse ⋙ (span f g).leftOp :=
  NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

/-- The canonical isomorphism relating `(Span f g).op` and `Cospan f.op g.op` -/
@[simps!]
def opSpan {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    (span f g).op ≅ walkingSpanOpEquiv.functor ⋙ cospan f.op g.op :=
  calc
    (span f g).op ≅ 𝟭 _ ⋙ (span f g).op := .refl _
    _ ≅ (walkingSpanOpEquiv.functor ⋙ walkingSpanOpEquiv.inverse) ⋙ (span f g).op :=
      isoWhiskerRight walkingSpanOpEquiv.unitIso _
    _ ≅ walkingSpanOpEquiv.functor ⋙ walkingSpanOpEquiv.inverse ⋙ (span f g).op :=
      Functor.associator _ _ _
    _ ≅ walkingSpanOpEquiv.functor ⋙ cospan f.op g.op := isoWhiskerLeft _ (cospanOp f g).symm

namespace PushoutCocone

/-- The obvious map `PushoutCocone f g → PullbackCone f.unop g.unop` -/
@[simps!]
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    PullbackCone f.unop g.unop :=
  Cocone.unop ((Cocone.precompose (opCospan f.unop g.unop).hom).obj
    (Cocone.whisker walkingCospanOpEquiv.functor c))

theorem unop_fst {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.unop.fst = c.inl.unop := by simp

theorem unop_snd {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.unop.snd = c.inr.unop := by simp

/-- The obvious map `PushoutCocone f.op g.op → PullbackCone f g` -/
@[simps!]
def op {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : PullbackCone f.op g.op :=
  (Cone.postcompose (cospanOp f g).symm.hom).obj
    (Cone.whisker walkingSpanOpEquiv.inverse (Cocone.op c))

theorem op_fst {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.op.fst = c.inl.op := by simp

theorem op_snd {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.op.snd = c.inr.op := by simp

end PushoutCocone

namespace PullbackCone

/-- The obvious map `PullbackCone f g → PushoutCocone f.unop g.unop` -/
@[simps!]
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    PushoutCocone f.unop g.unop :=
  Cone.unop
    ((Cone.postcompose (opSpan f.unop g.unop).symm.hom).obj
      (Cone.whisker walkingSpanOpEquiv.functor c))

theorem unop_inl {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.unop.inl = c.fst.unop := by simp

theorem unop_inr {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.unop.inr = c.snd.unop := by simp

/-- The obvious map `PullbackCone f g → PushoutCocone f.op g.op` -/
@[simps!]
def op {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : PushoutCocone f.op g.op :=
  (Cocone.precompose (spanOp f g).hom).obj
    (Cocone.whisker walkingCospanOpEquiv.inverse (Cone.op c))

theorem op_inl {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.op.inl = c.fst.op := by simp

theorem op_inr {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.op.inr = c.snd.op := by simp

/-- If `c` is a pullback cone, then `c.op.unop` is isomorphic to `c`. -/
def opUnopIso {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.op.unop ≅ c :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

/-- If `c` is a pullback cone in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
def unopOpIso {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.unop.op ≅ c :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

end PullbackCone

namespace PushoutCocone

/-- If `c` is a pushout cocone, then `c.op.unop` is isomorphic to `c`. -/
def opUnopIso {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.op.unop ≅ c :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

/-- If `c` is a pushout cocone in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
def unopOpIso {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.unop.op ≅ c :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

/-- A pushout cone is a colimit cocone if and only if the corresponding pullback cone
in the opposite category is a limit cone. -/
noncomputable -- just for performance; compilation takes several seconds
def isColimitEquivIsLimitOp {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    IsColimit c ≃ IsLimit c.op := by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact (IsLimit.postcomposeHomEquiv _ _).invFun
      ((IsLimit.whiskerEquivalenceEquiv walkingSpanOpEquiv.symm).toFun h.op)
  · intro h
    exact (IsColimit.equivIsoColimit c.opUnopIso).toFun
      (((IsLimit.postcomposeHomEquiv _ _).invFun
        ((IsLimit.whiskerEquivalenceEquiv _).toFun h)).unop)

/-- A pushout cone is a colimit cocone in `Cᵒᵖ` if and only if the corresponding pullback cone
in `C` is a limit cone. -/
noncomputable -- just for performance; compilation takes several seconds
def isColimitEquivIsLimitUnop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    IsColimit c ≃ IsLimit c.unop := by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsColimit.whiskerEquivalenceEquiv _).toFun h)).unop
  · intro h
    exact (IsColimit.equivIsoColimit c.unopOpIso).toFun
      ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsColimit.whiskerEquivalenceEquiv walkingCospanOpEquiv.symm).toFun h.op))

end PushoutCocone

namespace PullbackCone

/-- A pullback cone is a limit cone if and only if the corresponding pushout cocone
in the opposite category is a colimit cocone. -/
def isLimitEquivIsColimitOp {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    IsLimit c ≃ IsColimit c.op :=
  (IsLimit.equivIsoLimit c.opUnopIso).symm.trans c.op.isColimitEquivIsLimitUnop.symm

/-- A pullback cone is a limit cone in `Cᵒᵖ` if and only if the corresponding pushout cocone
in `C` is a colimit cocone. -/
def isLimitEquivIsColimitUnop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    IsLimit c ≃ IsColimit c.unop :=
  (IsLimit.equivIsoLimit c.unopOpIso).symm.trans c.unop.isColimitEquivIsLimitOp.symm

end PullbackCone

section Pullback

open Opposite

@[simp]
lemma hasPushout_op_iff_hasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPushout f.op g.op ↔ HasPullback f g := by
  rw [HasPushout, hasColimit_iff_of_iso (spanOp f g), hasColimit_inverse_equivalence_comp_iff,
    hasColimit_op_iff_hasLimit]

@[simp]
lemma hasPushout_unop_iff_hasPullback {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPushout f.unop g.unop ↔ HasPullback f g := by
  rw [HasPushout, hasColimit_iff_of_iso (spanUnop f g), hasColimit_inverse_equivalence_comp_iff,
    hasColimit_leftOp_iff_hasLimit]

instance {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : HasPushout f.op g.op := by
  rwa [hasPushout_op_iff_hasPullback]

instance {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : HasPushout f.unop g.unop := by
  rwa [hasPushout_unop_iff_hasPullback]

/-- The pullback of `f` and `g` in `C` is isomorphic to the pushout of
`f.op` and `g.op` in `Cᵒᵖ`. -/
noncomputable def pullbackIsoUnopPushout {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [h : HasPullback f g] :
    pullback f g ≅ unop (pushout f.op g.op) :=
  IsLimit.conePointUniqueUpToIso (@limit.isLimit _ _ _ _ _ h)
    ((PushoutCocone.isColimitEquivIsLimitUnop _) (colimit.isColimit (span f.op g.op)))

@[reassoc (attr := simp)]
theorem pullbackIsoUnopPushout_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    (pullbackIsoUnopPushout f g).inv ≫ pullback.fst f g = (pushout.inl f.op g.op).unop :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp [unop_id (X := { unop := X })])

@[reassoc (attr := simp)]
theorem pullbackIsoUnopPushout_inv_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    (pullbackIsoUnopPushout f g).inv ≫ pullback.snd f g = (pushout.inr f.op g.op).unop :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp [unop_id (X := { unop := Y })])

@[reassoc (attr := simp)]
theorem pullbackIsoUnopPushout_hom_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    pushout.inl f.op g.op ≫ (pullbackIsoUnopPushout f g).hom.op = (pullback.fst f g).op :=
  Quiver.Hom.unop_inj <| by simp [← pullbackIsoUnopPushout_inv_fst]

@[reassoc (attr := simp)]
theorem pullbackIsoUnopPushout_hom_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    pushout.inr f.op g.op ≫ (pullbackIsoUnopPushout f g).hom.op = (pullback.snd f g).op :=
  Quiver.Hom.unop_inj <| by simp [← pullbackIsoUnopPushout_inv_snd]

/-- The pullback of `f` and `g` in `Cᵒᵖ` is isomorphic to the pushout of
`f.unop` and `g.unop` in `C`. -/
noncomputable def pullbackIsoOpPushout {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [h : HasPullback f g] :
    pullback f g ≅ op (pushout f.unop g.unop) :=
  IsLimit.conePointUniqueUpToIso (@limit.isLimit _ _ _ _ _ h)
    ((PushoutCocone.isColimitEquivIsLimitOp _) (colimit.isColimit (span f.unop g.unop)))

@[reassoc (attr := simp)]
theorem pullbackIsoOpPushout_inv_fst {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    (pullbackIsoOpPushout f g).inv ≫ pullback.fst f g = (pushout.inl f.unop g.unop).op :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp)

@[reassoc (attr := simp)]
theorem pullbackIsoOpPushout_inv_snd {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    (pullbackIsoOpPushout f g).inv ≫ pullback.snd f g = (pushout.inr f.unop g.unop).op :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp)

@[reassoc (attr := simp)]
theorem pullbackIsoOpPushout_hom_inl {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    pushout.inl _ _ ≫ (pullbackIsoOpPushout f g).hom.unop = (pullback.fst f g).unop :=
  Quiver.Hom.op_inj <| by simp [← pullbackIsoOpPushout_inv_fst]

@[reassoc (attr := simp)]
theorem pullbackIsoOpPushout_hom_inr {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    pushout.inr _ _ ≫ (pullbackIsoOpPushout f g).hom.unop = (pullback.snd f g).unop :=
  Quiver.Hom.op_inj <| by simp [← pullbackIsoOpPushout_inv_snd]

end Pullback

section Pushout

@[simp]
lemma hasPullback_op_iff_hasPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    HasPullback f.op g.op ↔ HasPushout f g := by
  rw [HasPullback, hasLimit_iff_of_iso (cospanOp f g), hasLimit_inverse_equivalence_comp_iff,
    hasLimit_op_iff_hasColimit]

@[simp]
lemma hasPullback_unop_iff_hasPushout {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z) :
    HasPullback f.unop g.unop ↔ HasPushout f g := by
  rw [HasPullback, hasLimit_iff_of_iso (cospanUnop f g), hasLimit_inverse_equivalence_comp_iff,
    hasLimit_leftOp_iff_hasColimit]

instance {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : HasPullback f.op g.op := by
  rwa [hasPullback_op_iff_hasPushout]

instance {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : HasPullback f.unop g.unop := by
  rwa [hasPullback_unop_iff_hasPushout]

/-- The pushout of `f` and `g` in `C` is isomorphic to the pullback of
`f.op` and `g.op` in `Cᵒᵖ`. -/
noncomputable def pushoutIsoUnopPullback {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [h : HasPushout f g] :
    pushout f g ≅ unop (pullback f.op g.op) :=
  IsColimit.coconePointUniqueUpToIso (@colimit.isColimit _ _ _ _ _ h)
    ((PullbackCone.isLimitEquivIsColimitUnop _) (limit.isLimit (cospan f.op g.op)))

@[reassoc (attr := simp)]
theorem pushoutIsoUnopPullback_inl_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    pushout.inl _ _ ≫ (pushoutIsoUnopPullback f g).hom = (pullback.fst f.op g.op).unop :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[reassoc (attr := simp)]
theorem pushoutIsoUnopPullback_inr_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    pushout.inr _ _ ≫ (pushoutIsoUnopPullback f g).hom = (pullback.snd f.op g.op).unop :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[simp]
theorem pushoutIsoUnopPullback_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    (pushoutIsoUnopPullback f g).inv.op ≫ pullback.fst f.op g.op = (pushout.inl f g).op :=
  Quiver.Hom.unop_inj <| by simp [← pushoutIsoUnopPullback_inl_hom]

@[simp]
theorem pushoutIsoUnopPullback_inv_snd {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    (pushoutIsoUnopPullback f g).inv.op ≫ pullback.snd f.op g.op = (pushout.inr f g).op :=
  Quiver.Hom.unop_inj <| by simp [← pushoutIsoUnopPullback_inr_hom]

/-- The pushout of `f` and `g` in `Cᵒᵖ` is isomorphic to the pullback of
`f.unop` and `g.unop` in `C`. -/
noncomputable def pushoutIsoOpPullback {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [h : HasPushout f g] :
    pushout f g ≅ op (pullback f.unop g.unop) :=
  IsColimit.coconePointUniqueUpToIso (@colimit.isColimit _ _ _ _ _ h)
    ((PullbackCone.isLimitEquivIsColimitOp _) (limit.isLimit (cospan f.unop g.unop)))

@[reassoc (attr := simp)]
theorem pushoutIsoOpPullback_inl_hom {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    pushout.inl _ _ ≫ (pushoutIsoOpPullback f g).hom = (pullback.fst f.unop g.unop).op :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[reassoc (attr := simp)]
theorem pushoutIsoOpPullback_inr_hom {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    pushout.inr _ _ ≫ (pushoutIsoOpPullback f g).hom = (pullback.snd f.unop g.unop).op :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[simp]
theorem pushoutIsoOpPullback_inv_fst {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    (pushoutIsoOpPullback f g).inv.unop ≫ pullback.fst f.unop g.unop = (pushout.inl f g).unop :=
  Quiver.Hom.op_inj <| by simp [← pushoutIsoOpPullback_inl_hom]

@[simp]
theorem pushoutIsoOpPullback_inv_snd {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    (pushoutIsoOpPullback f g).inv.unop ≫ pullback.snd f.unop g.unop = (pushout.inr f g).unop :=
  Quiver.Hom.op_inj <| by simp [← pushoutIsoOpPullback_inr_hom]

end Pushout

section Map

set_option backward.isDefEq.respectTransparency false in
lemma op_pullbackMap {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂]
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁) (eq₂) :
    (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂).op =
      (pushoutIsoOpPullback _ _).inv ≫
        pushout.map g₁.op g₂.op f₁.op f₂.op i₁.op i₂.op i₃.op
        (by simp [eq₁, ← op_comp]) (by simp [eq₂, ← op_comp]) ≫
        (pushoutIsoOpPullback _ _).hom := by
  rw [Iso.eq_inv_comp]
  ext <;> simp [← op_comp]

set_option backward.isDefEq.respectTransparency false in
lemma op_pushoutMap {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂]
    (g₁ : T ⟶ Y) (g₂ : T ⟶ Z) [HasPushout g₁ g₂]
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁)
    (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) :
    (pushout.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂).op =
      (pullbackIsoOpPushout _ _).inv ≫
        pullback.map g₁.op g₂.op f₁.op f₂.op i₁.op i₂.op i₃.op
        (by simp [eq₁, ← op_comp]) (by simp [eq₂, ← op_comp]) ≫
        (pullbackIsoOpPushout _ _).hom := by
  rw [← Category.assoc, ← Iso.comp_inv_eq]
  ext <;> simp [← op_comp]

end Map

end Limits

namespace CommSq
open Limits

variable {C : Type*} [Category* C]
variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

set_option backward.isDefEq.respectTransparency false in
/-- The pushout cocone in the opposite category associated to the cone of
a commutative square identifies to the cocone of the flipped commutative square in
the opposite category -/
def coneOp (p : CommSq f g h i) : p.cone.op ≅ p.flip.op.cocone :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The pullback cone in the opposite category associated to the cocone of
a commutative square identifies to the cone of the flipped commutative square in
the opposite category -/
def coconeOp (p : CommSq f g h i) : p.cocone.op ≅ p.flip.op.cone :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The pushout cocone obtained from the pullback cone associated to a
commutative square in the opposite category identifies to the cocone associated
to the flipped square. -/
def coneUnop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) :
    p.cone.unop ≅ p.flip.unop.cocone :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The pullback cone obtained from the pushout cone associated to a
commutative square in the opposite category identifies to the cone associated
to the flipped square. -/
def coconeUnop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (p : CommSq f g h i) : p.cocone.unop ≅ p.flip.unop.cone :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

end CommSq

end CategoryTheory
