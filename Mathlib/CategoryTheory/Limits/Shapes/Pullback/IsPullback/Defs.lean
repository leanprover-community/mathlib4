/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks


/-!
# Pullback and pushout squares

We provide another API for pullbacks and pushouts.

`IsPullback fst snd f g` is the proposition that
```
  P --fst--> X
  |          |
 snd         f
  |          |
  v          v
  Y ---g---> Z

```
is a pullback square.

(And similarly for `IsPushout`.)

We provide the glue to go back and forth to the usual `IsLimit` API for pullbacks, and prove
`IsPullback (pullback.fst f g) (pullback.snd f g) f g`
for the usual `pullback f g` provided by the `HasLimit` API.
-/

@[expose] public section

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/-- The proposition that a square
```
  P --fst--> X
  |          |
 snd         f
  |          |
  v          v
  Y ---g---> Z

```
is a pullback square. (Also known as a fibered product or Cartesian square.)
-/
structure IsPullback {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) : Prop
    extends CommSq fst snd f g where
  /-- the pullback cone is a limit -/
  isLimit' : Nonempty (IsLimit (PullbackCone.mk _ _ w))

/-- The proposition that a square
```
  Z ---f---> X
  |          |
  g         inl
  |          |
  v          v
  Y --inr--> P

```
is a pushout square. (Also known as a fiber coproduct or co-Cartesian square.)
-/
structure IsPushout {Z X Y P : C} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P) : Prop
    extends CommSq f g inl inr where
  /-- the pushout cocone is a colimit -/
  isColimit' : Nonempty (IsColimit (PushoutCocone.mk _ _ w))

namespace IsPullback
variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The (limiting) `PullbackCone f g` implicit in the statement
that we have an `IsPullback fst snd f g`.
-/
def cone (h : IsPullback fst snd f g) : PullbackCone f g :=
  h.toCommSq.cone

@[simp]
theorem cone_fst (h : IsPullback fst snd f g) : h.cone.fst = fst :=
  rfl

@[simp]
theorem cone_snd (h : IsPullback fst snd f g) : h.cone.snd = snd :=
  rfl

/-- The cone obtained from `IsPullback fst snd f g` is a limit cone.
-/
noncomputable def isLimit (h : IsPullback fst snd f g) : IsLimit h.cone :=
  h.isLimit'.some

/-- API for PullbackCone.IsLimit.lift for `IsPullback` -/
noncomputable def lift (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ P :=
  PullbackCone.IsLimit.lift hP.isLimit h k w

@[reassoc (attr := simp)]
lemma lift_fst (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ fst = h :=
  PullbackCone.IsLimit.lift_fst hP.isLimit h k w

@[reassoc (attr := simp)]
lemma lift_snd (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ snd = k :=
  PullbackCone.IsLimit.lift_snd hP.isLimit h k w

lemma exists_lift (hP : IsPullback fst snd f g)
    {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    ∃ (l : W ⟶ P), l ≫ fst = h ∧ l ≫ snd = k :=
  ⟨hP.lift h k w, by simp, by simp⟩

lemma hom_ext (hP : IsPullback fst snd f g) {W : C} {k l : W ⟶ P}
    (h₀ : k ≫ fst = l ≫ fst) (h₁ : k ≫ snd = l ≫ snd) : k = l :=
  PullbackCone.IsLimit.hom_ext hP.isLimit h₀ h₁

/-- If `c` is a limiting pullback cone, then we have an `IsPullback c.fst c.snd f g`. -/
theorem of_isLimit {c : PullbackCone f g} (h : Limits.IsLimit c) : IsPullback c.fst c.snd f g :=
  { w := c.condition
    isLimit' := ⟨IsLimit.ofIsoLimit h (Limits.PullbackCone.ext (Iso.refl _)
      (by simp) (by simp))⟩ }

/-- A variant of `of_isLimit` that is more useful with `apply`. -/
theorem of_isLimit' (w : CommSq fst snd f g) (h : Limits.IsLimit w.cone) :
    IsPullback fst snd f g :=
  of_isLimit h

/-- Variant of `of_isLimit` for an arbitrary cone on a diagram `WalkingCospan ⥤ C`. -/
lemma of_isLimit_cone {D : WalkingCospan ⥤ C} {c : Cone D} (hc : IsLimit c) :
    IsPullback (c.π.app .left) (c.π.app .right) (D.map WalkingCospan.Hom.inl)
      (D.map WalkingCospan.Hom.inr) where
  w := by simp_rw [Cone.w]
  isLimit' := ⟨IsLimit.equivOfNatIsoOfIso _ _ _ (PullbackCone.isoMk c) hc⟩

lemma hasPullback (h : IsPullback fst snd f g) : HasPullback f g where
  exists_limit := ⟨⟨h.cone, h.isLimit⟩⟩

/-- The pullback provided by `HasPullback f g` fits into an `IsPullback`. -/
theorem of_hasPullback (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
  of_isLimit (limit.isLimit (cospan f g))


section

variable (X Y)

variable {P' : C} {fst' : P' ⟶ X} {snd' : P' ⟶ Y}

/-- Any object at the top left of a pullback square is isomorphic to the object at the top left
of any other pullback square with the same cospan. -/
noncomputable def isoIsPullback (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    P ≅ P' :=
  IsLimit.conePointUniqueUpToIso h.isLimit h'.isLimit

@[reassoc (attr := simp)]
theorem isoIsPullback_hom_fst (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').hom ≫ fst' = fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp h.isLimit h'.isLimit WalkingCospan.left

@[reassoc (attr := simp)]
theorem isoIsPullback_hom_snd (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').hom ≫ snd' = snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp h.isLimit h'.isLimit WalkingCospan.right

@[reassoc (attr := simp)]
theorem isoIsPullback_inv_fst (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').inv ≫ fst = fst' := by
  simp only [Iso.inv_comp_eq, isoIsPullback_hom_fst]

@[reassoc (attr := simp)]
theorem isoIsPullback_inv_snd (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').inv ≫ snd = snd' := by
  simp only [Iso.inv_comp_eq, isoIsPullback_hom_snd]

end

/-- Any object at the top left of a pullback square is
isomorphic to the pullback provided by the `HasLimit` API. -/
noncomputable def isoPullback (h : IsPullback fst snd f g) [HasPullback f g] : P ≅ pullback f g :=
  (limit.isoLimitCone ⟨_, h.isLimit⟩).symm


@[reassoc (attr := simp)]
theorem isoPullback_hom_fst (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.hom ≫ pullback.fst _ _ = fst := by
  dsimp [isoPullback, cone, CommSq.cone]
  simp

@[reassoc (attr := simp)]
theorem isoPullback_hom_snd (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.hom ≫ pullback.snd _ _ = snd := by
  dsimp [isoPullback, cone, CommSq.cone]
  simp

@[reassoc (attr := simp)]
theorem isoPullback_inv_fst (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.inv ≫ fst = pullback.fst _ _ := by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp)]
theorem isoPullback_inv_snd (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.inv ≫ snd = pullback.snd _ _ := by simp [Iso.inv_comp_eq]

end IsPullback

namespace IsPushout

variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

/-- The (colimiting) `PushoutCocone f g` implicit in the statement
that we have an `IsPushout f g inl inr`.
-/
def cocone (h : IsPushout f g inl inr) : PushoutCocone f g :=
  h.toCommSq.cocone

@[simp]
theorem cocone_inl (h : IsPushout f g inl inr) : h.cocone.inl = inl :=
  rfl

@[simp]
theorem cocone_inr (h : IsPushout f g inl inr) : h.cocone.inr = inr :=
  rfl

/-- The cocone obtained from `IsPushout f g inl inr` is a colimit cocone.
-/
noncomputable def isColimit (h : IsPushout f g inl inr) : IsColimit h.cocone :=
  h.isColimit'.some

/-- API for PushoutCocone.IsColimit.lift for `IsPushout` -/
noncomputable def desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
    (w : f ≫ h = g ≫ k) : P ⟶ W :=
  PushoutCocone.IsColimit.desc hP.isColimit h k w

@[reassoc (attr := simp)]
lemma inl_desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
    (w : f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h :=
  PushoutCocone.IsColimit.inl_desc hP.isColimit h k w

@[reassoc (attr := simp)]
lemma inr_desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
    (w : f ≫ h = g ≫ k) : inr ≫ hP.desc h k w = k :=
  PushoutCocone.IsColimit.inr_desc hP.isColimit h k w

lemma exists_desc (hP : IsPushout f g inl inr)
    {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) :
    ∃ (d : P ⟶ W), inl ≫ d = h ∧ inr ≫ d = k :=
  ⟨hP.desc h k w, by simp, by simp⟩

lemma hom_ext (hP : IsPushout f g inl inr) {W : C} {k l : P ⟶ W}
    (h₀ : inl ≫ k = inl ≫ l) (h₁ : inr ≫ k = inr ≫ l) : k = l :=
  PushoutCocone.IsColimit.hom_ext hP.isColimit h₀ h₁

/-- If `c` is a colimiting pushout cocone, then we have an `IsPushout f g c.inl c.inr`. -/
theorem of_isColimit {c : PushoutCocone f g} (h : Limits.IsColimit c) : IsPushout f g c.inl c.inr :=
  { w := c.condition
    isColimit' :=
      ⟨IsColimit.ofIsoColimit h (Limits.PushoutCocone.ext (Iso.refl _)
        (by simp) (by simp))⟩ }

/-- A variant of `of_isColimit` that is more useful with `apply`. -/
theorem of_isColimit' (w : CommSq f g inl inr) (h : Limits.IsColimit w.cocone) :
    IsPushout f g inl inr :=
  of_isColimit h

/-- Variant of `of_isColimit` for an arbitrary cocone on a diagram `WalkingSpan ⥤ C`. -/
lemma of_isColimit_cocone {D : WalkingSpan ⥤ C} {c : Cocone D} (hc : IsColimit c) :
    IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd)
      (c.ι.app .left) (c.ι.app .right) where
  w := by simp_rw [Cocone.w]
  isColimit' := ⟨IsColimit.equivOfNatIsoOfIso _ _ _ (PushoutCocone.isoMk c) hc⟩

lemma hasPushout (h : IsPushout f g inl inr) : HasPushout f g where
  exists_colimit := ⟨⟨h.cocone, h.isColimit⟩⟩

/-- The pushout provided by `HasPushout f g` fits into an `IsPushout`. -/
theorem of_hasPushout (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g] :
    IsPushout f g (pushout.inl f g) (pushout.inr f g) :=
  of_isColimit (colimit.isColimit (span f g))

section

variable (X Y)
variable {P' : C} {inl' : X ⟶ P'} {inr' : Y ⟶ P'}

/-- Any object at the bottom right of a pushout square is isomorphic to the object at the bottom
right of any other pushout square with the same span. -/
noncomputable def isoIsPushout (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    P ≅ P' :=
  IsColimit.coconePointUniqueUpToIso h.isColimit h'.isColimit

@[reassoc (attr := simp)]
theorem inl_isoIsPushout_hom (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inl ≫ (h.isoIsPushout _ _ h').hom = inl' :=
  IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit h'.isColimit WalkingSpan.left

@[reassoc (attr := simp)]
theorem inr_isoIsPushout_hom (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inr ≫ (h.isoIsPushout _ _ h').hom = inr' :=
  IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit h'.isColimit WalkingSpan.right

@[reassoc (attr := simp)]
theorem inl_isoIsPushout_inv (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inl' ≫ (h.isoIsPushout _ _ h').inv = inl := by
  simp only [Iso.comp_inv_eq, inl_isoIsPushout_hom]

@[reassoc (attr := simp)]
theorem inr_isoIsPushout_inv (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inr' ≫ (h.isoIsPushout _ _ h').inv = inr := by
  simp only [Iso.comp_inv_eq, inr_isoIsPushout_hom]

end

/-- Any object at the top left of a pullback square is
isomorphic to the pullback provided by the `HasLimit` API. -/
noncomputable def isoPushout (h : IsPushout f g inl inr) [HasPushout f g] : P ≅ pushout f g :=
  (colimit.isoColimitCocone ⟨_, h.isColimit⟩).symm

@[reassoc (attr := simp)]
theorem inl_isoPushout_inv (h : IsPushout f g inl inr) [HasPushout f g] :
    pushout.inl _ _ ≫ h.isoPushout.inv = inl := by
  dsimp [isoPushout, cocone, CommSq.cocone]
  simp

@[reassoc (attr := simp)]
theorem inr_isoPushout_inv (h : IsPushout f g inl inr) [HasPushout f g] :
    pushout.inr _ _ ≫ h.isoPushout.inv = inr := by
  dsimp [isoPushout, cocone, CommSq.cocone]
  simp

@[reassoc (attr := simp)]
theorem inl_isoPushout_hom (h : IsPushout f g inl inr) [HasPushout f g] :
    inl ≫ h.isoPushout.hom = pushout.inl _ _ := by simp [← Iso.eq_comp_inv]

@[reassoc (attr := simp)]
theorem inr_isoPushout_hom (h : IsPushout f g inl inr) [HasPushout f g] :
    inr ≫ h.isoPushout.hom = pushout.inr _ _ := by simp [← Iso.eq_comp_inv]

end IsPushout

namespace IsPullback
variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

theorem flip (h : IsPullback fst snd f g) : IsPullback snd fst g f :=
  of_isLimit (PullbackCone.flipIsLimit h.isLimit)

theorem flip_iff : IsPullback fst snd f g ↔ IsPullback snd fst g f :=
  ⟨flip, flip⟩


theorem op (h : IsPullback fst snd f g) : IsPushout g.op f.op snd.op fst.op :=
  IsPushout.of_isColimit
    (IsColimit.ofIsoColimit (Limits.PullbackCone.isLimitEquivIsColimitOp h.flip.cone h.flip.isLimit)
      h.toCommSq.flip.coneOp)

theorem unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : IsPushout g.unop f.unop snd.unop fst.unop :=
  IsPushout.of_isColimit
    (IsColimit.ofIsoColimit
      (Limits.PullbackCone.isLimitEquivIsColimitUnop h.flip.cone h.flip.isLimit)
      h.toCommSq.flip.coneUnop)

end IsPullback

namespace IsPushout
variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

theorem flip (h : IsPushout f g inl inr) : IsPushout g f inr inl :=
  of_isColimit (PushoutCocone.flipIsColimit h.isColimit)

theorem flip_iff : IsPushout f g inl inr ↔ IsPushout g f inr inl :=
  ⟨flip, flip⟩

theorem op (h : IsPushout f g inl inr) : IsPullback inr.op inl.op g.op f.op :=
  IsPullback.of_isLimit
    (IsLimit.ofIsoLimit
      (Limits.PushoutCocone.isColimitEquivIsLimitOp h.flip.cocone h.flip.isColimit)
      h.toCommSq.flip.coconeOp)

theorem unop {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (h : IsPushout f g inl inr) : IsPullback inr.unop inl.unop g.unop f.unop :=
  IsPullback.of_isLimit
    (IsLimit.ofIsoLimit
      (Limits.PushoutCocone.isColimitEquivIsLimitUnop h.flip.cocone h.flip.isColimit)
      h.toCommSq.flip.coconeUnop)

end IsPushout

end CategoryTheory
