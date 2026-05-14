/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks
public import Mathlib.Tactic.Attr.Core
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Equalizers and coequalizers in `C` and `Cᵒᵖ`

We construct equalizers and coequalizers in the opposite categories.

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

instance hasEqualizers_opposite [HasCoequalizers C] : HasEqualizers Cᵒᵖ :=
  haveI : HasColimitsOfShape WalkingParallelPairᵒᵖ C :=
    hasColimitsOfShape_of_equivalence walkingParallelPairOpEquiv
  hasLimitsOfShape_op_of_hasColimitsOfShape

instance hasCoequalizers_opposite [HasEqualizers C] : HasCoequalizers Cᵒᵖ :=
  haveI : HasLimitsOfShape WalkingParallelPairᵒᵖ C :=
    hasLimitsOfShape_of_equivalence walkingParallelPairOpEquiv
  hasColimitsOfShape_op_of_hasLimitsOfShape

/-- The canonical isomorphism relating `parallelPair f.op g.op` and `(parallelPair f g).op` -/
def parallelPairOpIso {X Y : C} (f g : X ⟶ Y) :
    parallelPair f.op g.op ≅ walkingParallelPairOpEquiv.functor ⋙ (parallelPair f g).op :=
  NatIso.ofComponents (fun
    | .zero => .refl _
    | .one => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

@[simp]
lemma parallelPairOpIso_hom_app_zero {X Y : C} (f g : X ⟶ Y) :
    (parallelPairOpIso f g).hom.app WalkingParallelPair.zero = 𝟙 _ := rfl

@[simp]
lemma parallelPairOpIso_hom_app_one {X Y : C} (f g : X ⟶ Y) :
    (parallelPairOpIso f g).hom.app WalkingParallelPair.one = 𝟙 _ := rfl

@[simp]
lemma parallelPairOpIso_inv_app_zero {X Y : C} (f g : X ⟶ Y) :
    (parallelPairOpIso f g).inv.app WalkingParallelPair.zero = 𝟙 _ := rfl

@[simp]
lemma parallelPairOpIso_inv_app_one {X Y : C} (f g : X ⟶ Y) :
    (parallelPairOpIso f g).inv.app WalkingParallelPair.one = 𝟙 _ := rfl

/-- The canonical isomorphism relating `(parallelPair f g).op` and `parallelPair f.op g.op` -/
def opParallelPairIso {X Y : C} (f g : X ⟶ Y) :
    (parallelPair f g).op ≅ walkingParallelPairOpEquiv.inverse ⋙ parallelPair f.op g.op :=
  calc
    (parallelPair f g).op ≅ 𝟭 _ ⋙ (parallelPair f g).op := .refl _
    _ ≅ (walkingParallelPairOpEquiv.inverse ⋙ walkingParallelPairOpEquiv.functor) ⋙ _ :=
      isoWhiskerRight walkingParallelPairOpEquiv.symm.unitIso _
    _ ≅ walkingParallelPairOpEquiv.inverse ⋙ walkingParallelPairOpEquiv.functor ⋙ _ :=
      Functor.associator _ _ _
    _ ≅ walkingParallelPairOpEquiv.inverse ⋙ parallelPair f.op g.op :=
      isoWhiskerLeft _ (parallelPairOpIso f g).symm

@[simp]
lemma opParallelPairIso_hom_app_zero {X Y : C} (f g : X ⟶ Y) :
    (opParallelPairIso f g).hom.app (op WalkingParallelPair.zero) = 𝟙 _ := by
  simp [opParallelPairIso]

@[simp]
lemma opParallelPairIso_hom_app_one {X Y : C} (f g : X ⟶ Y) :
    (opParallelPairIso f g).hom.app (op WalkingParallelPair.one) = 𝟙 _ := by
  simp [opParallelPairIso]

@[simp]
lemma opParallelPairIso_inv_app_zero {X Y : C} (f g : X ⟶ Y) :
    (opParallelPairIso f g).inv.app (op WalkingParallelPair.zero) = 𝟙 _ := by
  simp [opParallelPairIso]

@[simp]
lemma opParallelPairIso_inv_app_one {X Y : C} (f g : X ⟶ Y) :
    (opParallelPairIso f g).inv.app (op WalkingParallelPair.one) = 𝟙 _ := by
  simp [opParallelPairIso]

namespace Cofork

/-- The obvious map `Cofork f g → Fork f.unop g.unop` -/
def unop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) : Fork f.unop g.unop :=
   Cocone.unop ((Cocone.precompose (opParallelPairIso f.unop g.unop).hom).obj
      (Cocone.whisker walkingParallelPairOpEquiv.inverse c))

lemma unop_π_app_one {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) :
    c.unop.π.app .one = Quiver.Hom.unop (c.ι.app .zero) := by
  simp [unop]

lemma unop_π_app_zero {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) :
    c.unop.π.app .zero = Quiver.Hom.unop (c.ι.app .one) := by
  simp [unop]

theorem unop_ι {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) :
    c.unop.ι = c.π.unop := by simp [Cofork.unop, Fork.ι]

/-- The obvious map `Cofork f g → Fork f.op g.op` -/
def op {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) : Fork f.op g.op :=
  (Cone.postcompose (parallelPairOpIso f g).symm.hom).obj
    (Cone.whisker walkingParallelPairOpEquiv.functor (Cocone.op c))

lemma op_π_app_one {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) :
    c.op.π.app .one = Quiver.Hom.op (c.ι.app .zero) := by
  simp [op]

lemma op_π_app_zero {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) :
    c.op.π.app .zero = Quiver.Hom.op (c.ι.app .one) := by
  simp [op]

theorem op_ι {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) :
    c.op.ι = c.π.op := by simp [Cofork.op, Fork.ι]

end Cofork

namespace Fork

/-- The obvious map `Fork f g → Cofork f.unop g.unop` -/
def unop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) : Cofork f.unop g.unop :=
  Cone.unop ((Cone.postcompose (opParallelPairIso f.unop g.unop).symm.hom).obj
    (Cone.whisker walkingParallelPairOpEquiv.inverse c))

lemma unop_ι_app_one {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) :
    c.unop.ι.app .one = Quiver.Hom.unop (c.π.app .zero) := by
  simp [unop]

lemma unop_ι_app_zero {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) :
    c.unop.ι.app .zero = Quiver.Hom.unop (c.π.app .one) := by
  simp [unop]

theorem unop_π {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) :
    c.unop.π = c.ι.unop := by simp [Fork.unop, Cofork.π]

/-- The obvious map `Fork f g → Cofork f.op g.op` -/
@[simps!]
def op {X Y : C} {f g : X ⟶ Y} (c : Fork f g) : Cofork f.op g.op :=
  (Cocone.precompose (parallelPairOpIso f g).hom).obj
    (Cocone.whisker walkingParallelPairOpEquiv.functor (Cone.op c))

lemma op_ι_app_one {X Y : C} {f g : X ⟶ Y} (c : Fork f g) :
    c.op.ι.app .one = Quiver.Hom.op (c.π.app .zero) := by
  simp [op]

lemma op_ι_app_zero {X Y : C} {f g : X ⟶ Y} (c : Fork f g) :
    c.op.ι.app .zero = Quiver.Hom.op (c.π.app .one) := by
  simp [op]

theorem op_π {X Y : C} {f g : X ⟶ Y} (c : Fork f g) :
    c.op.π = c.ι.op := by simp [Fork.op, Cofork.π]

end Fork

namespace Cofork

set_option backward.isDefEq.respectTransparency false in
theorem op_unop_π {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) : c.op.unop.π = c.π := by
  simp [Fork.unop_π, Cofork.op_ι]

set_option backward.isDefEq.respectTransparency false in
theorem unop_op_π {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) : c.unop.op.π = c.π := by
  simp [Fork.op_π, Cofork.unop_ι]

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a cofork, then `c.op.unop` is isomorphic to `c`. -/
def opUnopIso {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) : c.op.unop ≅ c :=
  Cofork.ext (Iso.refl _) (by simp [op_unop_π])

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a cofork in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
def unopOpIso {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) : c.unop.op ≅ c :=
  Cofork.ext (Iso.refl _) (by simp [unop_op_π])

end Cofork

namespace Fork

set_option backward.isDefEq.respectTransparency false in
theorem op_unop_ι {X Y : C} {f g : X ⟶ Y} (c : Fork f g) : c.op.unop.ι = c.ι := by
  simp [Cofork.unop_ι, Fork.op_π]

set_option backward.isDefEq.respectTransparency false in
theorem unop_op_ι {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) : c.unop.op.ι = c.ι := by
  simp [Fork.unop_π, Cofork.op_ι]

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a fork, then `c.op.unop` is isomorphic to `c`. -/
def opUnopIso {X Y : C} {f g : X ⟶ Y} (c : Fork f g) : c.op.unop ≅ c :=
  Fork.ext (Iso.refl _) (by simp [op_unop_ι])

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a fork in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
def unopOpIso {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) : c.unop.op ≅ c :=
  Fork.ext (Iso.refl _) (by simp [unop_op_ι])

end Fork

namespace Cofork

/-- A cofork is a colimit cocone if and only if the corresponding fork in the opposite category is
a limit cone. -/
noncomputable -- just for performance; compilation takes several seconds
def isColimitEquivIsLimitOp {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) :
    IsColimit c ≃ IsLimit c.op := by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact (IsLimit.postcomposeHomEquiv _ _).invFun ((IsLimit.whiskerEquivalenceEquiv _).toFun h.op)
  · intro h
    exact (IsColimit.equivIsoColimit c.opUnopIso).toFun (((IsLimit.postcomposeHomEquiv _ _).invFun
      ((IsLimit.whiskerEquivalenceEquiv walkingParallelPairOpEquiv.symm).toFun h)).unop)

/-- A cofork is a colimit cocone in `Cᵒᵖ` if and only if the corresponding fork in `C` is
a limit cone. -/
noncomputable -- just for performance; compilation takes several seconds
def isColimitEquivIsLimitUnop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) :
    IsColimit c ≃ IsLimit c.unop := by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsColimit.whiskerEquivalenceEquiv walkingParallelPairOpEquiv.symm).toFun h)).unop
  · intro h
    exact (IsColimit.equivIsoColimit c.unopOpIso).toFun
      ((IsColimit.precomposeHomEquiv _ _).invFun ((IsColimit.whiskerEquivalenceEquiv _).toFun h.op))

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism between `(Cofork.ofπ π w).op` and `Fork.ofι π.op w'`. -/
def ofπOpIsoOfι {X Y P : C} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
    (w' : π'.op ≫ f.op = π'.op ≫ g.op) (h : π = π') :
    (Cofork.ofπ π w).op ≅ Fork.ofι π'.op w' :=
  Fork.ext (Iso.refl _) (by simp [Cofork.op_ι, h])

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism between `(Cofork.ofπ π w).unop` and `Fork.ofι π.unop w'`. -/
def ofπUnopIsoOfι {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
    (w' : π'.unop ≫ f.unop = π'.unop ≫ g.unop) (h : π = π') :
    (Cofork.ofπ π w).unop ≅ Fork.ofι π'.unop w' :=
  Fork.ext (Iso.refl _) (by simp [Cofork.unop_ι, h])

/-- `Cofork.ofπ π w` is a colimit cocone if and only if `Fork.ofι π.op w'` in the opposite
category is a limit cone. -/
def isColimitOfπEquivIsLimitOp {X Y P : C} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
    (w' : π'.op ≫ f.op = π'.op ≫ g.op) (h : π = π') :
    IsColimit (Cofork.ofπ π w) ≃ IsLimit (Fork.ofι π'.op w') :=
  (Cofork.ofπ π w).isColimitEquivIsLimitOp.trans (IsLimit.equivIsoLimit (ofπOpIsoOfι π π' w w' h))

/-- `Cofork.ofπ π w` is a colimit cocone in `Cᵒᵖ` if and only if `Fork.ofι π'.unop w'` in `C` is
a limit cone. -/
def isColimitOfπEquivIsLimitUnop {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
    (w' : π'.unop ≫ f.unop = π'.unop ≫ g.unop) (h : π = π') :
    IsColimit (Cofork.ofπ π w) ≃ IsLimit (Fork.ofι π'.unop w') :=
  (Cofork.ofπ π w).isColimitEquivIsLimitUnop.trans
    (IsLimit.equivIsoLimit (ofπUnopIsoOfι π π' w w' h))

end Cofork

namespace Fork

/-- A fork is a limit cone if and only if the corresponding cofork in the opposite category is
a colimit cocone. -/
def isLimitEquivIsColimitOp {X Y : C} {f g : X ⟶ Y} (c : Fork f g) :
    IsLimit c ≃ IsColimit c.op :=
  (IsLimit.equivIsoLimit c.opUnopIso).symm.trans c.op.isColimitEquivIsLimitUnop.symm

/-- A fork is a limit cone in `Cᵒᵖ` if and only if the corresponding cofork in `C` is
a colimit cocone. -/
def isLimitEquivIsColimitUnop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) :
    IsLimit c ≃ IsColimit c.unop :=
  (IsLimit.equivIsoLimit c.unopOpIso).symm.trans c.unop.isColimitEquivIsLimitOp.symm

/-- The canonical isomorphism between `(Fork.ofι ι w).op` and `Cofork.ofπ ι.op w'`. -/
def ofιOpIsoOfπ {X Y P : C} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
    (w' : f.op ≫ ι'.op = g.op ≫ ι'.op) (h : ι = ι') :
    (Fork.ofι ι w).op ≅ Cofork.ofπ ι'.op w' :=
  Cofork.ext (Iso.refl _) (by simp [Fork.op_π, h])

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism between `(Fork.ofι ι w).unop` and `Cofork.ofπ ι.unop w.unop`. -/
def ofιUnopIsoOfπ {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
    (w' : f.unop ≫ ι'.unop = g.unop ≫ ι'.unop) (h : ι = ι') :
    (Fork.ofι ι w).unop ≅ Cofork.ofπ ι'.unop w' :=
  Cofork.ext (Iso.refl _) (by simp [Fork.unop_π, h])

/-- `Fork.ofι ι w` is a limit cone if and only if `Cofork.ofπ ι'.op w'` in the opposite
category is a colimit cocone. -/
def isLimitOfιEquivIsColimitOp {X Y P : C} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
    (w' : f.op ≫ ι'.op = g.op ≫ ι'.op) (h : ι = ι') :
    IsLimit (Fork.ofι ι w) ≃ IsColimit (Cofork.ofπ ι'.op w') :=
  (Fork.ofι ι w).isLimitEquivIsColimitOp.trans (IsColimit.equivIsoColimit (ofιOpIsoOfπ ι ι' w w' h))

/-- `Fork.ofι ι w` is a limit cone in `Cᵒᵖ` if and only if `Cofork.ofπ ι.unop w.unop` in `C` is
a colimit cocone. -/
def isLimitOfιEquivIsColimitUnop {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
    (w' : f.unop ≫ ι'.unop = g.unop ≫ ι'.unop) (h : ι = ι') :
    IsLimit (Fork.ofι ι w) ≃ IsColimit (Cofork.ofπ ι'.unop w') :=
  (Fork.ofι ι w).isLimitEquivIsColimitUnop.trans
    (IsColimit.equivIsoColimit (ofιUnopIsoOfπ ι ι' w w' h))

end Fork

namespace Cofork

/-- `Cofork.ofπ f pullback.condition` is a colimit cocone if and only if
`Fork.ofι f.op pushout.condition` in the opposite category is a limit cone. -/
def isColimitCoforkPushoutEquivIsColimitForkOpPullback
    {X Y : C} {f : X ⟶ Y} [HasPullback f f] :
    IsColimit (Cofork.ofπ f pullback.condition) ≃ IsLimit (Fork.ofι f.op pushout.condition) where
  toFun h := Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitOp f f
    pullback.condition (by simp only [← op_comp, pullback.condition]) rfl h) _ (.refl _)
      (pullbackIsoUnopPushout f f).op.symm (.refl _)
        (by simp [← op_comp]) (by simp [← op_comp]) (by simp)
  invFun h := Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitUnop f.op f.op
    pushout.condition (by rw [← unop_comp, ← unop_comp, pushout.condition]) rfl h) _
      (pullbackIsoUnopPushout f f).symm (.refl _) (.refl _) (by simp) (by simp) (by simp)
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- `Cofork.ofπ f pullback.condition` is a colimit cocone in `Cᵒᵖ` if and only if
`Fork.ofι f.unop pushout.condition` in `C` is a limit cone. -/
def isColimitCoforkPushoutEquivIsColimitForkUnopPullback
    {X Y : Cᵒᵖ} {f : X ⟶ Y} [HasPullback f f] :
    IsColimit (Cofork.ofπ f pullback.condition) ≃ IsLimit (Fork.ofι f.unop pushout.condition) where
  toFun h := Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitUnop f f pullback.condition
    (by simp only [← unop_comp, pullback.condition]) rfl h) _ (.refl _)
      (pullbackIsoOpPushout f f).unop.symm (.refl _)
        (by simp [← unop_comp]) (by simp [← unop_comp]) (by simp)
  invFun h :=
    Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitOp f.unop f.unop pushout.condition
      (by rw [← op_comp, ← op_comp, pushout.condition]) rfl h) _
        (pullbackIsoOpPushout f f).symm (.refl _) (.refl _) (by simp) (by simp) (by simp)
  left_inv := by cat_disch
  right_inv := by cat_disch

end Cofork

namespace Fork

/-- `Fork.ofι f pushout.condition` is a limit cone if and only if
`Cofork.ofπ f.op pullback.condition` in the opposite category is a colimit cocone. -/
def isLimitForkPushoutEquivIsColimitForkOpPullback
    {X Y : C} {f : X ⟶ Y} [HasPushout f f] :
    IsLimit (Fork.ofι f pushout.condition) ≃ IsColimit (Cofork.ofπ f.op pullback.condition) where
  toFun h := Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitOp f f
    pushout.condition (by simp only [← op_comp, pushout.condition]) rfl h) _
      ((pushoutIsoUnopPullback f f).op.symm ≪≫ eqToIso rfl) (.refl _) (.refl _)
        (by simp) (by simp) (by simp)
  invFun h := by
    refine Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitUnop f.op f.op
      pullback.condition (by simp only [← unop_comp, pullback.condition]) rfl h) _ (.refl _)
        ((pushoutIsoUnopPullback f f).symm) (.refl _) ?_ ?_ (by simp)
    · rw [Iso.symm_hom, ← Quiver.Hom.unop_op (pushoutIsoUnopPullback f f).inv, ← unop_comp,
        pushoutIsoUnopPullback_inv_fst, Quiver.Hom.unop_op, Iso.refl_hom, Category.id_comp]
    · rw [Iso.symm_hom, ← Quiver.Hom.unop_op (pushoutIsoUnopPullback f f).inv, ← unop_comp,
        pushoutIsoUnopPullback_inv_snd, Quiver.Hom.unop_op, Iso.refl_hom, Category.id_comp]
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- `Fork.ofι f pushout.condition` is a limit cone in `Cᵒᵖ` if and only if
`Cofork.ofπ f.op pullback.condition` in `C` is a colimit cocone. -/
def isLimitForkPushoutEquivIsColimitForkUnopPullback
    {X Y : Cᵒᵖ} {f : X ⟶ Y} [HasPushout f f] :
    IsLimit (Fork.ofι f pushout.condition) ≃ IsColimit (Cofork.ofπ f.unop pullback.condition) where
  toFun h := Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitUnop f f pushout.condition
    (by simp only [← unop_comp, pushout.condition]) rfl h) _
      ((pushoutIsoOpPullback f f).unop.symm ≪≫ eqToIso rfl) (.refl _) (.refl _)
        (by simp) (by simp) (by simp)
  invFun h := by
    refine Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitOp f.unop f.unop pullback.condition
      (by simp only [← op_comp, pullback.condition]) rfl h) _ (.refl _)
        ((pushoutIsoOpPullback f f).symm) (.refl _) ?_ ?_ (by simp)
    · rw [Iso.symm_hom, ← Quiver.Hom.op_unop (pushoutIsoOpPullback f f).inv, ← op_comp,
        pushoutIsoOpPullback_inv_fst, Quiver.Hom.op_unop, Iso.refl_hom, Category.id_comp]
    · rw [Iso.symm_hom, ← Quiver.Hom.op_unop (pushoutIsoOpPullback f f).inv, ← op_comp,
        pushoutIsoOpPullback_inv_snd, Quiver.Hom.op_unop, Iso.refl_hom, Category.id_comp]
  left_inv := by cat_disch
  right_inv := by cat_disch

end Fork

end CategoryTheory.Limits
