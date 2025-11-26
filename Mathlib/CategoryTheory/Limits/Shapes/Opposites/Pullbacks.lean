/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pullbacks and pushouts in `C` and `Cᵒᵖ`

We construct pullbacks and pushouts in the opposite categories.

-/

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

/-- The canonical isomorphism relating `Span f.op g.op` and `(Cospan f g).op` -/
@[simps!]
def spanOp {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    span f.op g.op ≅ walkingCospanOpEquiv.inverse ⋙ (cospan f g).op :=
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

/-- The canonical isomorphism relating `Cospan f.op g.op` and `(Span f g).op` -/
@[simps!]
def cospanOp {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    cospan f.op g.op ≅ walkingSpanOpEquiv.inverse ⋙ (span f g).op :=
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
  Cocone.unop ((Cocones.precompose (opCospan f.unop g.unop).hom).obj
    (Cocone.whisker walkingCospanOpEquiv.functor c))

theorem unop_fst {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.unop.fst = c.inl.unop := by simp

theorem unop_snd {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.unop.snd = c.inr.unop := by simp

/-- The obvious map `PushoutCocone f.op g.op → PullbackCone f g` -/
@[simps!]
def op {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : PullbackCone f.op g.op :=
  (Cones.postcompose (cospanOp f g).symm.hom).obj
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
    ((Cones.postcompose (opSpan f.unop g.unop).symm.hom).obj
      (Cone.whisker walkingSpanOpEquiv.functor c))

theorem unop_inl {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.unop.inl = c.fst.unop := by simp

theorem unop_inr {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.unop.inr = c.snd.unop := by simp

/-- The obvious map `PullbackCone f g → PushoutCocone f.op g.op` -/
@[simps!]
def op {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : PushoutCocone f.op g.op :=
  (Cocones.precompose (spanOp f g).hom).obj
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

/-- The pullback of `f` and `g` in `C` is isomorphic to the pushout of
`f.op` and `g.op` in `Cᵒᵖ`. -/
noncomputable def pullbackIsoUnopPushout {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [h : HasPullback f g]
    [HasPushout f.op g.op] : pullback f g ≅ unop (pushout f.op g.op) :=
  IsLimit.conePointUniqueUpToIso (@limit.isLimit _ _ _ _ _ h)
    ((PushoutCocone.isColimitEquivIsLimitUnop _) (colimit.isColimit (span f.op g.op)))

@[reassoc (attr := simp)]
theorem pullbackIsoUnopPushout_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.op g.op] :
    (pullbackIsoUnopPushout f g).inv ≫ pullback.fst f g = (pushout.inl f.op g.op).unop :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp [unop_id (X := { unop := X })])

@[reassoc (attr := simp)]
theorem pullbackIsoUnopPushout_inv_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.op g.op] :
    (pullbackIsoUnopPushout f g).inv ≫ pullback.snd f g = (pushout.inr f.op g.op).unop :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp [unop_id (X := { unop := Y })])

@[reassoc (attr := simp)]
theorem pullbackIsoUnopPushout_hom_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.op g.op] :
    pushout.inl f.op g.op ≫ (pullbackIsoUnopPushout f g).hom.op = (pullback.fst f g).op :=
  Quiver.Hom.unop_inj <| by simp [← pullbackIsoUnopPushout_inv_fst]

@[reassoc (attr := simp)]
theorem pullbackIsoUnopPushout_hom_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.op g.op] :
    pushout.inr f.op g.op ≫ (pullbackIsoUnopPushout f g).hom.op = (pullback.snd f g).op :=
  Quiver.Hom.unop_inj <| by simp [← pullbackIsoUnopPushout_inv_snd]

/-- The pullback of `f` and `g` in `Cᵒᵖ` is isomorphic to the pushout of
`f.unop` and `g.unop` in `C`. -/
noncomputable def pullbackIsoOpPushout {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [h : HasPullback f g]
    [HasPushout f.unop g.unop] : pullback f g ≅ op (pushout f.unop g.unop) :=
  IsLimit.conePointUniqueUpToIso (@limit.isLimit _ _ _ _ _ h)
    ((PushoutCocone.isColimitEquivIsLimitOp _) (colimit.isColimit (span f.unop g.unop)))

@[reassoc (attr := simp)]
theorem pullbackIsoOpPushout_inv_fst {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.unop g.unop] :
    (pullbackIsoOpPushout f g).inv ≫ pullback.fst f g = (pushout.inl f.unop g.unop).op :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp)

@[reassoc (attr := simp)]
theorem pullbackIsoOpPushout_inv_snd {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.unop g.unop] :
    (pullbackIsoOpPushout f g).inv ≫ pullback.snd f g = (pushout.inr f.unop g.unop).op :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp)

@[reassoc (attr := simp)]
theorem pullbackIsoOpPushout_hom_inl {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.unop g.unop] :
    pushout.inl _ _ ≫ (pullbackIsoOpPushout f g).hom.unop = (pullback.fst f g).unop :=
  Quiver.Hom.op_inj <| by simp [← pullbackIsoOpPushout_inv_fst]

@[reassoc (attr := simp)]
theorem pullbackIsoOpPushout_hom_inr {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.unop g.unop] :
    pushout.inr _ _ ≫ (pullbackIsoOpPushout f g).hom.unop = (pullback.snd f g).unop :=
  Quiver.Hom.op_inj <| by simp [← pullbackIsoOpPushout_inv_snd]

end Pullback

section Pushout

/-- The pushout of `f` and `g` in `C` is isomorphic to the pullback of
`f.op` and `g.op` in `Cᵒᵖ`. -/
noncomputable def pushoutIsoUnopPullback {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [h : HasPushout f g]
    [HasPullback f.op g.op] : pushout f g ≅ unop (pullback f.op g.op) :=
  IsColimit.coconePointUniqueUpToIso (@colimit.isColimit _ _ _ _ _ h)
    ((PullbackCone.isLimitEquivIsColimitUnop _) (limit.isLimit (cospan f.op g.op)))

@[reassoc (attr := simp)]
theorem pushoutIsoUnopPullback_inl_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.op g.op] :
    pushout.inl _ _ ≫ (pushoutIsoUnopPullback f g).hom = (pullback.fst f.op g.op).unop :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[reassoc (attr := simp)]
theorem pushoutIsoUnopPullback_inr_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.op g.op] :
    pushout.inr _ _ ≫ (pushoutIsoUnopPullback f g).hom = (pullback.snd f.op g.op).unop :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[simp]
theorem pushoutIsoUnopPullback_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.op g.op] :
    (pushoutIsoUnopPullback f g).inv.op ≫ pullback.fst f.op g.op = (pushout.inl f g).op :=
  Quiver.Hom.unop_inj <| by simp [← pushoutIsoUnopPullback_inl_hom]

@[simp]
theorem pushoutIsoUnopPullback_inv_snd {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.op g.op] :
    (pushoutIsoUnopPullback f g).inv.op ≫ pullback.snd f.op g.op = (pushout.inr f g).op :=
  Quiver.Hom.unop_inj <| by simp [← pushoutIsoUnopPullback_inr_hom]

/-- The pushout of `f` and `g` in `Cᵒᵖ` is isomorphic to the pullback of
`f.unop` and `g.unop` in `C`. -/
noncomputable def pushoutIsoOpPullback {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [h : HasPushout f g]
    [HasPullback f.unop g.unop] : pushout f g ≅ op (pullback f.unop g.unop) :=
  IsColimit.coconePointUniqueUpToIso (@colimit.isColimit _ _ _ _ _ h)
    ((PullbackCone.isLimitEquivIsColimitOp _) (limit.isLimit (cospan f.unop g.unop)))

@[reassoc (attr := simp)]
theorem pushoutIsoOpPullback_inl_hom {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.unop g.unop] :
    pushout.inl _ _ ≫ (pushoutIsoOpPullback f g).hom = (pullback.fst f.unop g.unop).op :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[reassoc (attr := simp)]
theorem pushoutIsoOpPullback_inr_hom {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.unop g.unop] :
    pushout.inr _ _ ≫ (pushoutIsoOpPullback f g).hom = (pullback.snd f.unop g.unop).op :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[simp]
theorem pushoutIsoOpPullback_inv_fst {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.unop g.unop] :
    (pushoutIsoOpPullback f g).inv.unop ≫ pullback.fst f.unop g.unop = (pushout.inl f g).unop :=
  Quiver.Hom.op_inj <| by simp [← pushoutIsoOpPullback_inl_hom]

@[simp]
theorem pushoutIsoOpPullback_inv_snd {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.unop g.unop] :
    (pushoutIsoOpPullback f g).inv.unop ≫ pullback.snd f.unop g.unop = (pushout.inr f g).unop :=
  Quiver.Hom.op_inj <| by simp [← pushoutIsoOpPullback_inr_hom]

end Pushout

end CategoryTheory.Limits
