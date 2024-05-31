/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou
-/
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.ZeroObjects

#align_import category_theory.limits.shapes.comm_sq from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Pullback and pushout squares, and bicartesian squares

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
`IsPullback (pullback.fst : pullback f g ⟶ X) (pullback.snd : pullback f g ⟶ Y) f g`
for the usual `pullback f g` provided by the `HasLimit` API.

We don't attempt to restate everything we know about pullbacks in this language,
but do restate the pasting lemmas.

We define bicartesian squares, and
show that the pullback and pushout squares for a biproduct are bicartesian.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

attribute [simp] CommSq.mk

namespace CommSq

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

/-- The (not necessarily limiting) `PullbackCone h i` implicit in the statement
that we have `CommSq f g h i`.
-/
def cone (s : CommSq f g h i) : PullbackCone h i :=
  PullbackCone.mk _ _ s.w
#align category_theory.comm_sq.cone CategoryTheory.CommSq.cone

/-- The (not necessarily limiting) `PushoutCocone f g` implicit in the statement
that we have `CommSq f g h i`.
-/
def cocone (s : CommSq f g h i) : PushoutCocone f g :=
  PushoutCocone.mk _ _ s.w
#align category_theory.comm_sq.cocone CategoryTheory.CommSq.cocone

@[simp]
theorem cone_fst (s : CommSq f g h i) : s.cone.fst = f :=
  rfl
#align category_theory.comm_sq.cone_fst CategoryTheory.CommSq.cone_fst

@[simp]
theorem cone_snd (s : CommSq f g h i) : s.cone.snd = g :=
  rfl
#align category_theory.comm_sq.cone_snd CategoryTheory.CommSq.cone_snd

@[simp]
theorem cocone_inl (s : CommSq f g h i) : s.cocone.inl = h :=
  rfl
#align category_theory.comm_sq.cocone_inl CategoryTheory.CommSq.cocone_inl

@[simp]
theorem cocone_inr (s : CommSq f g h i) : s.cocone.inr = i :=
  rfl
#align category_theory.comm_sq.cocone_inr CategoryTheory.CommSq.cocone_inr

/-- The pushout cocone in the opposite category associated to the cone of
a commutative square identifies to the cocone of the flipped commutative square in
the opposite category -/
def coneOp (p : CommSq f g h i) : p.cone.op ≅ p.flip.op.cocone :=
  PushoutCocone.ext (Iso.refl _) (by aesop_cat) (by aesop_cat)
#align category_theory.comm_sq.cone_op CategoryTheory.CommSq.coneOp

/-- The pullback cone in the opposite category associated to the cocone of
a commutative square identifies to the cone of the flipped commutative square in
the opposite category -/
def coconeOp (p : CommSq f g h i) : p.cocone.op ≅ p.flip.op.cone :=
  PullbackCone.ext (Iso.refl _) (by aesop_cat) (by aesop_cat)
#align category_theory.comm_sq.cocone_op CategoryTheory.CommSq.coconeOp

/-- The pushout cocone obtained from the pullback cone associated to a
commutative square in the opposite category identifies to the cocone associated
to the flipped square. -/
def coneUnop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) :
    p.cone.unop ≅ p.flip.unop.cocone :=
  PushoutCocone.ext (Iso.refl _) (by aesop_cat) (by aesop_cat)
#align category_theory.comm_sq.cone_unop CategoryTheory.CommSq.coneUnop

/-- The pullback cone obtained from the pushout cone associated to a
commutative square in the opposite category identifies to the cone associated
to the flipped square. -/
def coconeUnop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (p : CommSq f g h i) : p.cocone.unop ≅ p.flip.unop.cone :=
  PullbackCone.ext (Iso.refl _) (by aesop_cat) (by aesop_cat)
#align category_theory.comm_sq.cocone_unop CategoryTheory.CommSq.coconeUnop

end CommSq

/-- The proposition that a square
```
  P --fst--> X
  |          |
 snd         f
  |          |
  v          v
  Y ---g---> Z

```
is a pullback square. (Also known as a fibered product or cartesian square.)
-/
structure IsPullback {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) extends
  CommSq fst snd f g : Prop where
  /-- the pullback cone is a limit -/
  isLimit' : Nonempty (IsLimit (PullbackCone.mk _ _ w))
#align category_theory.is_pullback CategoryTheory.IsPullback

/-- The proposition that a square
```
  Z ---f---> X
  |          |
  g         inl
  |          |
  v          v
  Y --inr--> P

```
is a pushout square. (Also known as a fiber coproduct or cocartesian square.)
-/
structure IsPushout {Z X Y P : C} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P) extends
  CommSq f g inl inr : Prop where
  /-- the pushout cocone is a colimit -/
  isColimit' : Nonempty (IsColimit (PushoutCocone.mk _ _ w))
#align category_theory.is_pushout CategoryTheory.IsPushout

section

/-- A *bicartesian* square is a commutative square
```
  W ---f---> X
  |          |
  g          h
  |          |
  v          v
  Y ---i---> Z

```
that is both a pullback square and a pushout square.
-/
structure BicartesianSq {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) extends
  IsPullback f g h i, IsPushout f g h i : Prop
#align category_theory.bicartesian_sq CategoryTheory.BicartesianSq

-- Lean should make these parent projections as `lemma`, not `def`.
attribute [nolint defLemma docBlame] BicartesianSq.toIsPullback BicartesianSq.toIsPushout

end

/-!
We begin by providing some glue between `IsPullback` and the `IsLimit` and `HasLimit` APIs.
(And similarly for `IsPushout`.)
-/


namespace IsPullback

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The (limiting) `PullbackCone f g` implicit in the statement
that we have an `IsPullback fst snd f g`.
-/
def cone (h : IsPullback fst snd f g) : PullbackCone f g :=
  h.toCommSq.cone
#align category_theory.is_pullback.cone CategoryTheory.IsPullback.cone

@[simp]
theorem cone_fst (h : IsPullback fst snd f g) : h.cone.fst = fst :=
  rfl
#align category_theory.is_pullback.cone_fst CategoryTheory.IsPullback.cone_fst

@[simp]
theorem cone_snd (h : IsPullback fst snd f g) : h.cone.snd = snd :=
  rfl
#align category_theory.is_pullback.cone_snd CategoryTheory.IsPullback.cone_snd

/-- The cone obtained from `IsPullback fst snd f g` is a limit cone.
-/
noncomputable def isLimit (h : IsPullback fst snd f g) : IsLimit h.cone :=
  h.isLimit'.some
#align category_theory.is_pullback.is_limit CategoryTheory.IsPullback.isLimit

/-- If `c` is a limiting pullback cone, then we have an `IsPullback c.fst c.snd f g`. -/
theorem of_isLimit {c : PullbackCone f g} (h : Limits.IsLimit c) : IsPullback c.fst c.snd f g :=
  { w := c.condition
    isLimit' := ⟨IsLimit.ofIsoLimit h (Limits.PullbackCone.ext (Iso.refl _)
      (by aesop_cat) (by aesop_cat))⟩ }
#align category_theory.is_pullback.of_is_limit CategoryTheory.IsPullback.of_isLimit

/-- A variant of `of_isLimit` that is more useful with `apply`. -/
theorem of_isLimit' (w : CommSq fst snd f g) (h : Limits.IsLimit w.cone) :
    IsPullback fst snd f g :=
  of_isLimit h
#align category_theory.is_pullback.of_is_limit' CategoryTheory.IsPullback.of_isLimit'

/-- The pullback provided by `HasPullback f g` fits into an `IsPullback`. -/
theorem of_hasPullback (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsPullback (pullback.fst : pullback f g ⟶ X) (pullback.snd : pullback f g ⟶ Y) f g :=
  of_isLimit (limit.isLimit (cospan f g))
#align category_theory.is_pullback.of_has_pullback CategoryTheory.IsPullback.of_hasPullback

/-- If `c` is a limiting binary product cone, and we have a terminal object,
then we have `IsPullback c.fst c.snd 0 0`
(where each `0` is the unique morphism to the terminal object). -/
theorem of_is_product {c : BinaryFan X Y} (h : Limits.IsLimit c) (t : IsTerminal Z) :
    IsPullback c.fst c.snd (t.from _) (t.from _) :=
  of_isLimit
    (isPullbackOfIsTerminalIsProduct _ _ _ _ t
      (IsLimit.ofIsoLimit h
        (Limits.Cones.ext (Iso.refl c.pt)
          (by
            rintro ⟨⟨⟩⟩ <;>
              · dsimp
                simp))))
#align category_theory.is_pullback.of_is_product CategoryTheory.IsPullback.of_is_product

/-- A variant of `of_is_product` that is more useful with `apply`. -/
theorem of_is_product' (h : Limits.IsLimit (BinaryFan.mk fst snd)) (t : IsTerminal Z) :
    IsPullback fst snd (t.from _) (t.from _) :=
  of_is_product h t
#align category_theory.is_pullback.of_is_product' CategoryTheory.IsPullback.of_is_product'

variable (X Y)

theorem of_hasBinaryProduct' [HasBinaryProduct X Y] [HasTerminal C] :
    IsPullback Limits.prod.fst Limits.prod.snd (terminal.from X) (terminal.from Y) :=
  of_is_product (limit.isLimit _) terminalIsTerminal
#align category_theory.is_pullback.of_has_binary_product' CategoryTheory.IsPullback.of_hasBinaryProduct'

open ZeroObject

theorem of_hasBinaryProduct [HasBinaryProduct X Y] [HasZeroObject C] [HasZeroMorphisms C] :
    IsPullback Limits.prod.fst Limits.prod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  convert @of_is_product _ _ X Y 0 _ (limit.isLimit _) HasZeroObject.zeroIsTerminal
    <;> apply Subsingleton.elim
#align category_theory.is_pullback.of_has_binary_product CategoryTheory.IsPullback.of_hasBinaryProduct

variable {X Y}

/-- Any object at the top left of a pullback square is
isomorphic to the pullback provided by the `HasLimit` API. -/
noncomputable def isoPullback (h : IsPullback fst snd f g) [HasPullback f g] : P ≅ pullback f g :=
  (limit.isoLimitCone ⟨_, h.isLimit⟩).symm
#align category_theory.is_pullback.iso_pullback CategoryTheory.IsPullback.isoPullback

@[simp]
theorem isoPullback_hom_fst (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.hom ≫ pullback.fst = fst := by
  dsimp [isoPullback, cone, CommSq.cone]
  simp
#align category_theory.is_pullback.iso_pullback_hom_fst CategoryTheory.IsPullback.isoPullback_hom_fst

@[simp]
theorem isoPullback_hom_snd (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.hom ≫ pullback.snd = snd := by
  dsimp [isoPullback, cone, CommSq.cone]
  simp
#align category_theory.is_pullback.iso_pullback_hom_snd CategoryTheory.IsPullback.isoPullback_hom_snd

@[simp]
theorem isoPullback_inv_fst (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.inv ≫ fst = pullback.fst := by simp [Iso.inv_comp_eq]
#align category_theory.is_pullback.iso_pullback_inv_fst CategoryTheory.IsPullback.isoPullback_inv_fst

@[simp]
theorem isoPullback_inv_snd (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.inv ≫ snd = pullback.snd := by simp [Iso.inv_comp_eq]
#align category_theory.is_pullback.iso_pullback_inv_snd CategoryTheory.IsPullback.isoPullback_inv_snd

theorem of_iso_pullback (h : CommSq fst snd f g) [HasPullback f g] (i : P ≅ pullback f g)
    (w₁ : i.hom ≫ pullback.fst = fst) (w₂ : i.hom ≫ pullback.snd = snd) : IsPullback fst snd f g :=
  of_isLimit' h
    (Limits.IsLimit.ofIsoLimit (limit.isLimit _)
      (@PullbackCone.ext _ _ _ _ _ _ _ (PullbackCone.mk _ _ _) _ i w₁.symm w₂.symm).symm)
#align category_theory.is_pullback.of_iso_pullback CategoryTheory.IsPullback.of_iso_pullback

theorem of_horiz_isIso [IsIso fst] [IsIso g] (sq : CommSq fst snd f g) : IsPullback fst snd f g :=
  of_isLimit' sq
    (by
      refine
        PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ inv fst) (by aesop_cat)
          (fun s => ?_) (by aesop_cat)
      simp only [← cancel_mono g, Category.assoc, ← sq.w, IsIso.inv_hom_id_assoc, s.condition])
#align category_theory.is_pullback.of_horiz_is_iso CategoryTheory.IsPullback.of_horiz_isIso

end IsPullback

namespace IsPushout

variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

/-- The (colimiting) `PushoutCocone f g` implicit in the statement
that we have an `IsPushout f g inl inr`.
-/
def cocone (h : IsPushout f g inl inr) : PushoutCocone f g :=
  h.toCommSq.cocone
#align category_theory.is_pushout.cocone CategoryTheory.IsPushout.cocone

@[simp]
theorem cocone_inl (h : IsPushout f g inl inr) : h.cocone.inl = inl :=
  rfl
#align category_theory.is_pushout.cocone_inl CategoryTheory.IsPushout.cocone_inl

@[simp]
theorem cocone_inr (h : IsPushout f g inl inr) : h.cocone.inr = inr :=
  rfl
#align category_theory.is_pushout.cocone_inr CategoryTheory.IsPushout.cocone_inr

/-- The cocone obtained from `IsPushout f g inl inr` is a colimit cocone.
-/
noncomputable def isColimit (h : IsPushout f g inl inr) : IsColimit h.cocone :=
  h.isColimit'.some
#align category_theory.is_pushout.is_colimit CategoryTheory.IsPushout.isColimit

/-- If `c` is a colimiting pushout cocone, then we have an `IsPushout f g c.inl c.inr`. -/
theorem of_isColimit {c : PushoutCocone f g} (h : Limits.IsColimit c) : IsPushout f g c.inl c.inr :=
  { w := c.condition
    isColimit' :=
      ⟨IsColimit.ofIsoColimit h (Limits.PushoutCocone.ext (Iso.refl _)
        (by aesop_cat) (by aesop_cat))⟩ }
#align category_theory.is_pushout.of_is_colimit CategoryTheory.IsPushout.of_isColimit

/-- A variant of `of_isColimit` that is more useful with `apply`. -/
theorem of_isColimit' (w : CommSq f g inl inr) (h : Limits.IsColimit w.cocone) :
    IsPushout f g inl inr :=
  of_isColimit h
#align category_theory.is_pushout.of_is_colimit' CategoryTheory.IsPushout.of_isColimit'

/-- The pushout provided by `HasPushout f g` fits into an `IsPushout`. -/
theorem of_hasPushout (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g] :
    IsPushout f g (pushout.inl : X ⟶ pushout f g) (pushout.inr : Y ⟶ pushout f g) :=
  of_isColimit (colimit.isColimit (span f g))
#align category_theory.is_pushout.of_has_pushout CategoryTheory.IsPushout.of_hasPushout

/-- If `c` is a colimiting binary coproduct cocone, and we have an initial object,
then we have `IsPushout 0 0 c.inl c.inr`
(where each `0` is the unique morphism from the initial object). -/
theorem of_is_coproduct {c : BinaryCofan X Y} (h : Limits.IsColimit c) (t : IsInitial Z) :
    IsPushout (t.to _) (t.to _) c.inl c.inr :=
  of_isColimit
    (isPushoutOfIsInitialIsCoproduct _ _ _ _ t
      (IsColimit.ofIsoColimit h
        (Limits.Cocones.ext (Iso.refl c.pt)
          (by
            rintro ⟨⟨⟩⟩ <;>
              · dsimp
                simp))))
#align category_theory.is_pushout.of_is_coproduct CategoryTheory.IsPushout.of_is_coproduct

/-- A variant of `of_is_coproduct` that is more useful with `apply`. -/
theorem of_is_coproduct' (h : Limits.IsColimit (BinaryCofan.mk inl inr)) (t : IsInitial Z) :
    IsPushout (t.to _) (t.to _) inl inr :=
  of_is_coproduct h t
#align category_theory.is_pushout.of_is_coproduct' CategoryTheory.IsPushout.of_is_coproduct'

variable (X Y)

theorem of_hasBinaryCoproduct' [HasBinaryCoproduct X Y] [HasInitial C] :
    IsPushout (initial.to _) (initial.to _) (coprod.inl : X ⟶ _) (coprod.inr : Y ⟶ _) :=
  of_is_coproduct (colimit.isColimit _) initialIsInitial
#align category_theory.is_pushout.of_has_binary_coproduct' CategoryTheory.IsPushout.of_hasBinaryCoproduct'

open ZeroObject

theorem of_hasBinaryCoproduct [HasBinaryCoproduct X Y] [HasZeroObject C] [HasZeroMorphisms C] :
    IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) coprod.inl coprod.inr := by
  convert @of_is_coproduct _ _ 0 X Y _ (colimit.isColimit _) HasZeroObject.zeroIsInitial
    <;> apply Subsingleton.elim
#align category_theory.is_pushout.of_has_binary_coproduct CategoryTheory.IsPushout.of_hasBinaryCoproduct

variable {X Y}

/-- Any object at the top left of a pullback square is
isomorphic to the pullback provided by the `HasLimit` API. -/
noncomputable def isoPushout (h : IsPushout f g inl inr) [HasPushout f g] : P ≅ pushout f g :=
  (colimit.isoColimitCocone ⟨_, h.isColimit⟩).symm
#align category_theory.is_pushout.iso_pushout CategoryTheory.IsPushout.isoPushout

@[simp]
theorem inl_isoPushout_inv (h : IsPushout f g inl inr) [HasPushout f g] :
    pushout.inl ≫ h.isoPushout.inv = inl := by
  dsimp [isoPushout, cocone, CommSq.cocone]
  simp
#align category_theory.is_pushout.inl_iso_pushout_inv CategoryTheory.IsPushout.inl_isoPushout_inv

@[simp]
theorem inr_isoPushout_inv (h : IsPushout f g inl inr) [HasPushout f g] :
    pushout.inr ≫ h.isoPushout.inv = inr := by
  dsimp [isoPushout, cocone, CommSq.cocone]
  simp
#align category_theory.is_pushout.inr_iso_pushout_inv CategoryTheory.IsPushout.inr_isoPushout_inv

@[simp]
theorem inl_isoPushout_hom (h : IsPushout f g inl inr) [HasPushout f g] :
    inl ≫ h.isoPushout.hom = pushout.inl := by simp [← Iso.eq_comp_inv]
#align category_theory.is_pushout.inl_iso_pushout_hom CategoryTheory.IsPushout.inl_isoPushout_hom

@[simp]
theorem inr_isoPushout_hom (h : IsPushout f g inl inr) [HasPushout f g] :
    inr ≫ h.isoPushout.hom = pushout.inr := by simp [← Iso.eq_comp_inv]
#align category_theory.is_pushout.inr_iso_pushout_hom CategoryTheory.IsPushout.inr_isoPushout_hom

theorem of_iso_pushout (h : CommSq f g inl inr) [HasPushout f g] (i : P ≅ pushout f g)
    (w₁ : inl ≫ i.hom = pushout.inl) (w₂ : inr ≫ i.hom = pushout.inr) : IsPushout f g inl inr :=
  of_isColimit' h
    (Limits.IsColimit.ofIsoColimit (colimit.isColimit _)
      (PushoutCocone.ext (s := PushoutCocone.mk ..) i w₁ w₂).symm)
#align category_theory.is_pushout.of_iso_pushout CategoryTheory.IsPushout.of_iso_pushout

end IsPushout

namespace IsPullback

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

theorem flip (h : IsPullback fst snd f g) : IsPullback snd fst g f :=
  of_isLimit (PullbackCone.flipIsLimit h.isLimit)
#align category_theory.is_pullback.flip CategoryTheory.IsPullback.flip

theorem flip_iff : IsPullback fst snd f g ↔ IsPullback snd fst g f :=
  ⟨flip, flip⟩
#align category_theory.is_pullback.flip_iff CategoryTheory.IsPullback.flip_iff

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

/-- The square with `0 : 0 ⟶ 0` on the left and `𝟙 X` on the right is a pullback square. -/
@[simp]
theorem zero_left (X : C) : IsPullback (0 : 0 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 ⟶ X) :=
  { w := by simp
    isLimit' :=
      ⟨{  lift := fun s => 0
          fac := fun s => by
            simpa [eq_iff_true_of_subsingleton] using
              @PullbackCone.equalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
                (by simpa using (PullbackCone.condition s).symm) }⟩ }
#align category_theory.is_pullback.zero_left CategoryTheory.IsPullback.zero_left

/-- The square with `0 : 0 ⟶ 0` on the top and `𝟙 X` on the bottom is a pullback square. -/
@[simp]
theorem zero_top (X : C) : IsPullback (0 : (0 : C) ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X) :=
  (zero_left X).flip
#align category_theory.is_pullback.zero_top CategoryTheory.IsPullback.zero_top

/-- The square with `0 : 0 ⟶ 0` on the right and `𝟙 X` on the left is a pullback square. -/
@[simp]
theorem zero_right (X : C) : IsPullback (0 : X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X ⟶ 0) :=
  of_iso_pullback (by simp) ((zeroProdIso X).symm ≪≫ (pullbackZeroZeroIso _ _).symm)
    (by simp [eq_iff_true_of_subsingleton]) (by simp)
#align category_theory.is_pullback.zero_right CategoryTheory.IsPullback.zero_right

/-- The square with `0 : 0 ⟶ 0` on the bottom and `𝟙 X` on the top is a pullback square. -/
@[simp]
theorem zero_bot (X : C) : IsPullback (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : (0 : C) ⟶ 0) :=
  (zero_right X).flip
#align category_theory.is_pullback.zero_bot CategoryTheory.IsPullback.zero_bot

end

-- Objects here are arranged in a 3x2 grid, and indexed by their xy coordinates.
-- Morphisms are named `hᵢⱼ` for a horizontal morphism starting at `(i,j)`,
-- and `vᵢⱼ` for a vertical morphism starting at `(i,j)`.
/-- Paste two pullback squares "vertically" to obtain another pullback square. -/
theorem paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) :
    IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
  of_isLimit (bigSquareIsPullback _ _ _ _ _ _ _ s.w t.w t.isLimit s.isLimit)
#align category_theory.is_pullback.paste_vert CategoryTheory.IsPullback.paste_vert

/-- Paste two pullback squares "horizontally" to obtain another pullback square. -/
theorem paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
  (paste_vert s.flip t.flip).flip
#align category_theory.is_pullback.paste_horiz CategoryTheory.IsPullback.paste_horiz

/-- Given a pullback square assembled from a commuting square on the top and
a pullback square on the bottom, the top square is a pullback square. -/
theorem of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁)
    (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) : IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  of_isLimit (leftSquareIsPullback _ _ _ _ _ _ _ p t.w t.isLimit s.isLimit)
#align category_theory.is_pullback.of_bot CategoryTheory.IsPullback.of_bot

/-- Given a pullback square assembled from a commuting square on the left and
a pullback square on the right, the left square is a pullback square. -/
theorem of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁)
    (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) : IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  (of_bot s.flip p.symm t.flip).flip
#align category_theory.is_pullback.of_right CategoryTheory.IsPullback.of_right

theorem paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) (e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) :
    IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ ↔ IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  ⟨fun h => h.of_bot e s, fun h => h.paste_vert s⟩
#align category_theory.is_pullback.paste_vert_iff CategoryTheory.IsPullback.paste_vert_iff

theorem paste_horiz_iff {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) (e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) :
    IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) ↔ IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  ⟨fun h => h.of_right e s, fun h => h.paste_horiz s⟩
#align category_theory.is_pullback.paste_horiz_iff CategoryTheory.IsPullback.paste_horiz_iff

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

theorem of_isBilimit {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  convert IsPullback.of_is_product' h.isLimit HasZeroObject.zeroIsTerminal
    <;> apply Subsingleton.elim
#align category_theory.is_pullback.of_is_bilimit CategoryTheory.IsPullback.of_isBilimit

@[simp]
theorem of_has_biproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback biprod.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
  of_isBilimit (BinaryBiproduct.isBilimit X Y)
#align category_theory.is_pullback.of_has_biproduct CategoryTheory.IsPullback.of_has_biproduct

theorem inl_snd' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback b.inl (0 : X ⟶ 0) b.snd (0 : 0 ⟶ Y) := by
  refine of_right ?_ (by simp) (of_isBilimit h)
  simp
#align category_theory.is_pullback.inl_snd' CategoryTheory.IsPullback.inl_snd'

/-- The square
```
  X --inl--> X ⊞ Y
  |            |
  0           snd
  |            |
  v            v
  0 ---0-----> Y
```
is a pullback square.
-/
@[simp]
theorem inl_snd (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback biprod.inl (0 : X ⟶ 0) biprod.snd (0 : 0 ⟶ Y) :=
  inl_snd' (BinaryBiproduct.isBilimit X Y)
#align category_theory.is_pullback.inl_snd CategoryTheory.IsPullback.inl_snd

theorem inr_fst' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback b.inr (0 : Y ⟶ 0) b.fst (0 : 0 ⟶ X) := by
  apply flip
  refine of_bot ?_ (by simp) (of_isBilimit h)
  simp
#align category_theory.is_pullback.inr_fst' CategoryTheory.IsPullback.inr_fst'

/-- The square
```
  Y --inr--> X ⊞ Y
  |            |
  0           fst
  |            |
  v            v
  0 ---0-----> X
```
is a pullback square.
-/
@[simp]
theorem inr_fst (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback biprod.inr (0 : Y ⟶ 0) biprod.fst (0 : 0 ⟶ X) :=
  inr_fst' (BinaryBiproduct.isBilimit X Y)
#align category_theory.is_pullback.inr_fst CategoryTheory.IsPullback.inr_fst

theorem of_is_bilimit' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.inl_snd' h).flip
  simp
#align category_theory.is_pullback.of_is_bilimit' CategoryTheory.IsPullback.of_is_bilimit'

theorem of_hasBinaryBiproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr :=
  of_is_bilimit' (BinaryBiproduct.isBilimit X Y)
#align category_theory.is_pullback.of_has_binary_biproduct CategoryTheory.IsPullback.of_hasBinaryBiproduct

instance hasPullback_biprod_fst_biprod_snd [HasBinaryBiproduct X Y] :
    HasPullback (biprod.inl : X ⟶ _) (biprod.inr : Y ⟶ _) :=
  HasLimit.mk ⟨_, (of_hasBinaryBiproduct X Y).isLimit⟩
#align category_theory.is_pullback.has_pullback_biprod_fst_biprod_snd CategoryTheory.IsPullback.hasPullback_biprod_fst_biprod_snd

/-- The pullback of `biprod.inl` and `biprod.inr` is the zero object. -/
def pullbackBiprodInlBiprodInr [HasBinaryBiproduct X Y] :
    pullback (biprod.inl : X ⟶ _) (biprod.inr : Y ⟶ _) ≅ 0 :=
  limit.isoLimitCone ⟨_, (of_hasBinaryBiproduct X Y).isLimit⟩
#align category_theory.is_pullback.pullback_biprod_inl_biprod_inr CategoryTheory.IsPullback.pullbackBiprodInlBiprodInr

end

theorem op (h : IsPullback fst snd f g) : IsPushout g.op f.op snd.op fst.op :=
  IsPushout.of_isColimit
    (IsColimit.ofIsoColimit (Limits.PullbackCone.isLimitEquivIsColimitOp h.flip.cone h.flip.isLimit)
      h.toCommSq.flip.coneOp)
#align category_theory.is_pullback.op CategoryTheory.IsPullback.op

theorem unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : IsPushout g.unop f.unop snd.unop fst.unop :=
  IsPushout.of_isColimit
    (IsColimit.ofIsoColimit
      (Limits.PullbackCone.isLimitEquivIsColimitUnop h.flip.cone h.flip.isLimit)
      h.toCommSq.flip.coneUnop)
#align category_theory.is_pullback.unop CategoryTheory.IsPullback.unop

theorem of_vert_isIso [IsIso snd] [IsIso f] (sq : CommSq fst snd f g) : IsPullback fst snd f g :=
  IsPullback.flip (of_horiz_isIso sq.flip)
#align category_theory.is_pullback.of_vert_is_iso CategoryTheory.IsPullback.of_vert_isIso

end IsPullback

namespace IsPushout

variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

theorem flip (h : IsPushout f g inl inr) : IsPushout g f inr inl :=
  of_isColimit (PushoutCocone.flipIsColimit h.isColimit)
#align category_theory.is_pushout.flip CategoryTheory.IsPushout.flip

theorem flip_iff : IsPushout f g inl inr ↔ IsPushout g f inr inl :=
  ⟨flip, flip⟩
#align category_theory.is_pushout.flip_iff CategoryTheory.IsPushout.flip_iff

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

/-- The square with `0 : 0 ⟶ 0` on the right and `𝟙 X` on the left is a pushout square. -/
@[simp]
theorem zero_right (X : C) : IsPushout (0 : X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X ⟶ 0) :=
  { w := by simp
    isColimit' :=
      ⟨{  desc := fun s => 0
          fac := fun s => by
            have c :=
              @PushoutCocone.coequalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
                (by simp [eq_iff_true_of_subsingleton]) (by simpa using PushoutCocone.condition s)
            dsimp at c
            simpa using c }⟩ }
#align category_theory.is_pushout.zero_right CategoryTheory.IsPushout.zero_right

/-- The square with `0 : 0 ⟶ 0` on the bottom and `𝟙 X` on the top is a pushout square. -/
@[simp]
theorem zero_bot (X : C) : IsPushout (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : (0 : C) ⟶ 0) :=
  (zero_right X).flip
#align category_theory.is_pushout.zero_bot CategoryTheory.IsPushout.zero_bot

/-- The square with `0 : 0 ⟶ 0` on the right left `𝟙 X` on the right is a pushout square. -/
@[simp]
theorem zero_left (X : C) : IsPushout (0 : 0 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 ⟶ X) :=
  of_iso_pushout (by simp) ((coprodZeroIso X).symm ≪≫ (pushoutZeroZeroIso _ _).symm) (by simp)
    (by simp [eq_iff_true_of_subsingleton])
#align category_theory.is_pushout.zero_left CategoryTheory.IsPushout.zero_left

/-- The square with `0 : 0 ⟶ 0` on the top and `𝟙 X` on the bottom is a pushout square. -/
@[simp]
theorem zero_top (X : C) : IsPushout (0 : (0 : C) ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X) :=
  (zero_left X).flip
#align category_theory.is_pushout.zero_top CategoryTheory.IsPushout.zero_top

end

-- Objects here are arranged in a 3x2 grid, and indexed by their xy coordinates.
-- Morphisms are named `hᵢⱼ` for a horizontal morphism starting at `(i,j)`,
-- and `vᵢⱼ` for a vertical morphism starting at `(i,j)`.
/-- Paste two pushout squares "vertically" to obtain another pushout square. -/
theorem paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPushout h₂₁ v₂₁ v₂₂ h₃₁) :
    IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
  of_isColimit (bigSquareIsPushout _ _ _ _ _ _ _ s.w t.w t.isColimit s.isColimit)
#align category_theory.is_pushout.paste_vert CategoryTheory.IsPushout.paste_vert

/-- Paste two pushout squares "horizontally" to obtain another pushout square. -/
theorem paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPushout h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
  (paste_vert s.flip t.flip).flip
#align category_theory.is_pushout.paste_horiz CategoryTheory.IsPushout.paste_horiz

/-- Given a pushout square assembled from a pushout square on the top and
a commuting square on the bottom, the bottom square is a pushout square. -/
theorem of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁)
    (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) : IsPushout h₂₁ v₂₁ v₂₂ h₃₁ :=
  of_isColimit (rightSquareIsPushout _ _ _ _ _ _ _ t.w p t.isColimit s.isColimit)
#align category_theory.is_pushout.of_bot CategoryTheory.IsPushout.of_bot

/-- Given a pushout square assembled from a pushout square on the left and
a commuting square on the right, the right square is a pushout square. -/
theorem of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂)
    (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) : IsPushout h₁₂ v₁₂ v₁₃ h₂₂ :=
  (of_bot s.flip p.symm t.flip).flip
#align category_theory.is_pushout.of_right CategoryTheory.IsPushout.of_right

theorem paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (e : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁) :
    IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ ↔ IsPushout h₂₁ v₂₁ v₂₂ h₃₁ :=
  ⟨fun h => h.of_bot e s, s.paste_vert⟩
#align category_theory.is_pushout.paste_vert_iff CategoryTheory.IsPushout.paste_vert_iff

theorem paste_horiz_iff {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (e : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂) :
    IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) ↔ IsPushout h₁₂ v₁₂ v₁₃ h₂₂ :=
  ⟨fun h => h.of_right e s, s.paste_horiz⟩
#align category_theory.is_pushout.paste_horiz_iff CategoryTheory.IsPushout.paste_horiz_iff

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

theorem of_isBilimit {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr := by
  convert IsPushout.of_is_coproduct' h.isColimit HasZeroObject.zeroIsInitial
    <;> apply Subsingleton.elim
#align category_theory.is_pushout.of_is_bilimit CategoryTheory.IsPushout.of_isBilimit

@[simp]
theorem of_has_biproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr :=
  of_isBilimit (BinaryBiproduct.isBilimit X Y)
#align category_theory.is_pushout.of_has_biproduct CategoryTheory.IsPushout.of_has_biproduct

theorem inl_snd' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout b.inl (0 : X ⟶ 0) b.snd (0 : 0 ⟶ Y) := by
  apply flip
  refine of_right ?_ (by simp) (of_isBilimit h)
  simp
#align category_theory.is_pushout.inl_snd' CategoryTheory.IsPushout.inl_snd'

/-- The square
```
  X --inl--> X ⊞ Y
  |            |
  0           snd
  |            |
  v            v
  0 ---0-----> Y
```
is a pushout square.
-/
theorem inl_snd (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout biprod.inl (0 : X ⟶ 0) biprod.snd (0 : 0 ⟶ Y) :=
  inl_snd' (BinaryBiproduct.isBilimit X Y)
#align category_theory.is_pushout.inl_snd CategoryTheory.IsPushout.inl_snd

theorem inr_fst' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout b.inr (0 : Y ⟶ 0) b.fst (0 : 0 ⟶ X) := by
  refine of_bot ?_ (by simp) (of_isBilimit h)
  simp
#align category_theory.is_pushout.inr_fst' CategoryTheory.IsPushout.inr_fst'

/-- The square
```
  Y --inr--> X ⊞ Y
  |            |
  0           fst
  |            |
  v            v
  0 ---0-----> X
```
is a pushout square.
-/
theorem inr_fst (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout biprod.inr (0 : Y ⟶ 0) biprod.fst (0 : 0 ⟶ X) :=
  inr_fst' (BinaryBiproduct.isBilimit X Y)
#align category_theory.is_pushout.inr_fst CategoryTheory.IsPushout.inr_fst

theorem of_is_bilimit' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  refine IsPushout.of_right ?_ (by simp) (IsPushout.inl_snd' h)
  simp
#align category_theory.is_pushout.of_is_bilimit' CategoryTheory.IsPushout.of_is_bilimit'

theorem of_hasBinaryBiproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout biprod.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
  of_is_bilimit' (BinaryBiproduct.isBilimit X Y)
#align category_theory.is_pushout.of_has_binary_biproduct CategoryTheory.IsPushout.of_hasBinaryBiproduct

instance hasPushout_biprod_fst_biprod_snd [HasBinaryBiproduct X Y] :
    HasPushout (biprod.fst : _ ⟶ X) (biprod.snd : _ ⟶ Y) :=
  HasColimit.mk ⟨_, (of_hasBinaryBiproduct X Y).isColimit⟩
#align category_theory.is_pushout.has_pushout_biprod_fst_biprod_snd CategoryTheory.IsPushout.hasPushout_biprod_fst_biprod_snd

/-- The pushout of `biprod.fst` and `biprod.snd` is the zero object. -/
def pushoutBiprodFstBiprodSnd [HasBinaryBiproduct X Y] :
    pushout (biprod.fst : _ ⟶ X) (biprod.snd : _ ⟶ Y) ≅ 0 :=
  colimit.isoColimitCocone ⟨_, (of_hasBinaryBiproduct X Y).isColimit⟩
#align category_theory.is_pushout.pushout_biprod_fst_biprod_snd CategoryTheory.IsPushout.pushoutBiprodFstBiprodSnd

end

theorem op (h : IsPushout f g inl inr) : IsPullback inr.op inl.op g.op f.op :=
  IsPullback.of_isLimit
    (IsLimit.ofIsoLimit
      (Limits.PushoutCocone.isColimitEquivIsLimitOp h.flip.cocone h.flip.isColimit)
      h.toCommSq.flip.coconeOp)
#align category_theory.is_pushout.op CategoryTheory.IsPushout.op

theorem unop {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (h : IsPushout f g inl inr) : IsPullback inr.unop inl.unop g.unop f.unop :=
  IsPullback.of_isLimit
    (IsLimit.ofIsoLimit
      (Limits.PushoutCocone.isColimitEquivIsLimitUnop h.flip.cocone h.flip.isColimit)
      h.toCommSq.flip.coconeUnop)
#align category_theory.is_pushout.unop CategoryTheory.IsPushout.unop

theorem of_horiz_isIso [IsIso f] [IsIso inr] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  of_isColimit' sq
    (by
      refine
        PushoutCocone.IsColimit.mk _ (fun s => inv inr ≫ s.inr) (fun s => ?_)
          (by aesop_cat) (by aesop_cat)
      simp only [← cancel_epi f, s.condition, sq.w_assoc, IsIso.hom_inv_id_assoc])
#align category_theory.is_pushout.of_horiz_is_iso CategoryTheory.IsPushout.of_horiz_isIso

theorem of_vert_isIso [IsIso g] [IsIso inl] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  (of_horiz_isIso sq.flip).flip
#align category_theory.is_pushout.of_vert_is_iso CategoryTheory.IsPushout.of_vert_isIso

end IsPushout

section Equalizer

variable {X Y Z : C} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}

/-- If `f : X ⟶ Y`, `g g' : Y ⟶ Z` forms a pullback square, then `f` is the equalizer of
`g` and `g'`. -/
noncomputable def IsPullback.isLimitFork (H : IsPullback f f g g') : IsLimit (Fork.ofι f H.w) := by
  fapply Fork.IsLimit.mk
  · exact fun s => H.isLimit.lift (PullbackCone.mk s.ι s.ι s.condition)
  · exact fun s => H.isLimit.fac _ WalkingCospan.left
  · intro s m e
    apply PullbackCone.IsLimit.hom_ext H.isLimit <;> refine e.trans ?_ <;> symm <;>
      exact H.isLimit.fac _ _
#align category_theory.is_pullback.is_limit_fork CategoryTheory.IsPullback.isLimitFork

/-- If `f f' : X ⟶ Y`, `g : Y ⟶ Z` forms a pushout square, then `g` is the coequalizer of
`f` and `f'`. -/
noncomputable def IsPushout.isLimitFork (H : IsPushout f f' g g) :
    IsColimit (Cofork.ofπ g H.w) := by
  fapply Cofork.IsColimit.mk
  · exact fun s => H.isColimit.desc (PushoutCocone.mk s.π s.π s.condition)
  · exact fun s => H.isColimit.fac _ WalkingSpan.left
  · intro s m e
    apply PushoutCocone.IsColimit.hom_ext H.isColimit <;> refine e.trans ?_ <;> symm <;>
      exact H.isColimit.fac _ _
#align category_theory.is_pushout.is_limit_fork CategoryTheory.IsPushout.isLimitFork

end Equalizer

namespace BicartesianSq

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

theorem of_isPullback_isPushout (p₁ : IsPullback f g h i) (p₂ : IsPushout f g h i) :
    BicartesianSq f g h i :=
  BicartesianSq.mk p₁ p₂.isColimit'
#align category_theory.bicartesian_sq.of_is_pullback_is_pushout CategoryTheory.BicartesianSq.of_isPullback_isPushout

theorem flip (p : BicartesianSq f g h i) : BicartesianSq g f i h :=
  of_isPullback_isPushout p.toIsPullback.flip p.toIsPushout.flip
#align category_theory.bicartesian_sq.flip CategoryTheory.BicartesianSq.flip

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

/-- ```
 X ⊞ Y --fst--> X
   |            |
  snd           0
   |            |
   v            v
   Y -----0---> 0
```
is a bicartesian square.
-/
theorem of_is_biproduct₁ {b : BinaryBicone X Y} (h : b.IsBilimit) :
    BicartesianSq b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
  of_isPullback_isPushout (IsPullback.of_isBilimit h) (IsPushout.of_is_bilimit' h)
#align category_theory.bicartesian_sq.of_is_biproduct₁ CategoryTheory.BicartesianSq.of_is_biproduct₁

/-- ```
   0 -----0---> X
   |            |
   0           inl
   |            |
   v            v
   Y --inr--> X ⊞ Y
```
is a bicartesian square.
-/
theorem of_is_biproduct₂ {b : BinaryBicone X Y} (h : b.IsBilimit) :
    BicartesianSq (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr :=
  of_isPullback_isPushout (IsPullback.of_is_bilimit' h) (IsPushout.of_isBilimit h)
#align category_theory.bicartesian_sq.of_is_biproduct₂ CategoryTheory.BicartesianSq.of_is_biproduct₂

/-- ```
 X ⊞ Y --fst--> X
   |            |
  snd           0
   |            |
   v            v
   Y -----0---> 0
```
is a bicartesian square.
-/
@[simp]
theorem of_has_biproduct₁ [HasBinaryBiproduct X Y] :
    BicartesianSq biprod.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  convert of_is_biproduct₁ (BinaryBiproduct.isBilimit X Y)
#align category_theory.bicartesian_sq.of_has_biproduct₁ CategoryTheory.BicartesianSq.of_has_biproduct₁

/-- ```
   0 -----0---> X
   |            |
   0           inl
   |            |
   v            v
   Y --inr--> X ⊞ Y
```
is a bicartesian square.
-/
@[simp]
theorem of_has_biproduct₂ [HasBinaryBiproduct X Y] :
    BicartesianSq (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr := by
  convert of_is_biproduct₂ (BinaryBiproduct.isBilimit X Y)
#align category_theory.bicartesian_sq.of_has_biproduct₂ CategoryTheory.BicartesianSq.of_has_biproduct₂

end BicartesianSq

section Functor

variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

theorem Functor.map_isPullback [PreservesLimit (cospan h i) F] (s : IsPullback f g h i) :
    IsPullback (F.map f) (F.map g) (F.map h) (F.map i) := by
  -- This is made slightly awkward because `C` and `D` have different universes,
  -- and so the relevant `WalkingCospan` diagrams live in different universes too!
  refine
    IsPullback.of_isLimit' (F.map_commSq s.toCommSq)
      (IsLimit.equivOfNatIsoOfIso (cospanCompIso F h i) _ _ (WalkingCospan.ext ?_ ?_ ?_)
        (isLimitOfPreserves F s.isLimit))
  · rfl
  · simp
  · simp
#align category_theory.functor.map_is_pullback CategoryTheory.Functor.map_isPullback

theorem Functor.map_isPushout [PreservesColimit (span f g) F] (s : IsPushout f g h i) :
    IsPushout (F.map f) (F.map g) (F.map h) (F.map i) := by
  refine
    IsPushout.of_isColimit' (F.map_commSq s.toCommSq)
      (IsColimit.equivOfNatIsoOfIso (spanCompIso F f g) _ _ (WalkingSpan.ext ?_ ?_ ?_)
        (isColimitOfPreserves F s.isColimit))
  · rfl
  · simp
  · simp
#align category_theory.functor.map_is_pushout CategoryTheory.Functor.map_isPushout

alias IsPullback.map := Functor.map_isPullback
#align category_theory.is_pullback.map CategoryTheory.IsPullback.map

alias IsPushout.map := Functor.map_isPushout
#align category_theory.is_pushout.map CategoryTheory.IsPushout.map

theorem IsPullback.of_map [ReflectsLimit (cospan h i) F] (e : f ≫ h = g ≫ i)
    (H : IsPullback (F.map f) (F.map g) (F.map h) (F.map i)) : IsPullback f g h i := by
  refine ⟨⟨e⟩, ⟨isLimitOfReflects F <| ?_⟩⟩
  refine
    (IsLimit.equivOfNatIsoOfIso (cospanCompIso F h i) _ _ (WalkingCospan.ext ?_ ?_ ?_)).symm
      H.isLimit
  exacts [Iso.refl _, (Category.comp_id _).trans (Category.id_comp _).symm,
    (Category.comp_id _).trans (Category.id_comp _).symm]
#align category_theory.is_pullback.of_map CategoryTheory.IsPullback.of_map

theorem IsPullback.of_map_of_faithful [ReflectsLimit (cospan h i) F] [F.Faithful]
    (H : IsPullback (F.map f) (F.map g) (F.map h) (F.map i)) : IsPullback f g h i :=
  H.of_map F (F.map_injective <| by simpa only [F.map_comp] using H.w)
#align category_theory.is_pullback.of_map_of_faithful CategoryTheory.IsPullback.of_map_of_faithful

theorem IsPullback.map_iff {D : Type*} [Category D] (F : C ⥤ D) [PreservesLimit (cospan h i) F]
    [ReflectsLimit (cospan h i) F] (e : f ≫ h = g ≫ i) :
    IsPullback (F.map f) (F.map g) (F.map h) (F.map i) ↔ IsPullback f g h i :=
  ⟨fun h => h.of_map F e, fun h => h.map F⟩
#align category_theory.is_pullback.map_iff CategoryTheory.IsPullback.map_iff

theorem IsPushout.of_map [ReflectsColimit (span f g) F] (e : f ≫ h = g ≫ i)
    (H : IsPushout (F.map f) (F.map g) (F.map h) (F.map i)) : IsPushout f g h i := by
  refine ⟨⟨e⟩, ⟨isColimitOfReflects F <| ?_⟩⟩
  refine
    (IsColimit.equivOfNatIsoOfIso (spanCompIso F f g) _ _ (WalkingSpan.ext ?_ ?_ ?_)).symm
      H.isColimit
  exacts [Iso.refl _, (Category.comp_id _).trans (Category.id_comp _),
    (Category.comp_id _).trans (Category.id_comp _)]
#align category_theory.is_pushout.of_map CategoryTheory.IsPushout.of_map

theorem IsPushout.of_map_of_faithful [ReflectsColimit (span f g) F] [F.Faithful]
    (H : IsPushout (F.map f) (F.map g) (F.map h) (F.map i)) : IsPushout f g h i :=
  H.of_map F (F.map_injective <| by simpa only [F.map_comp] using H.w)
#align category_theory.is_pushout.of_map_of_faithful CategoryTheory.IsPushout.of_map_of_faithful

theorem IsPushout.map_iff {D : Type*} [Category D] (F : C ⥤ D) [PreservesColimit (span f g) F]
    [ReflectsColimit (span f g) F] (e : f ≫ h = g ≫ i) :
    IsPushout (F.map f) (F.map g) (F.map h) (F.map i) ↔ IsPushout f g h i :=
  ⟨fun h => h.of_map F e, fun h => h.map F⟩
#align category_theory.is_pushout.map_iff CategoryTheory.IsPushout.map_iff

end Functor

end CategoryTheory
