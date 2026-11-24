/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pasting lemma

This file proves the pasting lemma for pullbacks. That is, given the following diagram:
```
  X₁ - f₁ -> X₂ - f₂ -> X₃
  |          |          |
  i₁         i₂         i₃
  ∨          ∨          ∨
  Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
if the right square is a pullback, then the left square is a pullback iff the big square is a
pullback.

## Main results

* `pasteHorizIsPullback` shows that the big square is a pullback if both the small squares are.
* `leftSquareIsPullback` shows that the left square is a pullback if the other two are.
* `pullbackRightPullbackFstIso` shows, using the `pullback` API, that
  `W ×[X] (X ×[Z] Y) ≅ W ×[Z] Y`.
* `pullbackLeftPullbackSndIso` shows, using the `pullback` API, that
  `(X ×[Z] Y) ×[Y] W ≅ X ×[Z] W`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

to_dual_name_hint Horiz Vert, Top Right, Left Bot

section PasteLemma
section PastePullbackHoriz

/- Let's consider the following diagram
```
X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
↓          ↓          ↓
Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
where `t₁` denotes the cone corresponding to the left square, and `t₂` denotes the cone
corresponding to the right square.
-/

variable {X₃ Y₁ Y₂ Y₃ : C} {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃} {i₃ : X₃ ⟶ Y₃}

/-- The `PullbackCone` obtained by pasting two `PullbackCone`'s horizontally -/
@[to_dual /-- The `PullbackCone` obtained by pasting two `PullbackCone`'s vertically -/]
abbrev PullbackCone.pasteHoriz
    (t₂ : PullbackCone g₂ i₃) {i₂ : t₂.pt ⟶ Y₂} (t₁ : PullbackCone g₁ i₂) (hi₂ : i₂ = t₂.fst) :
    PullbackCone (g₁ ≫ g₂) i₃ :=
  PullbackCone.mk t₁.fst (t₁.snd ≫ t₂.snd)
    (by rw [reassoc_of% t₁.condition, Category.assoc, ← t₂.condition, ← hi₂])

variable (t₂ : PullbackCone g₂ i₃) {i₂ : t₂.pt ⟶ Y₂} (t₁ : PullbackCone g₁ i₂) (hi₂ : i₂ = t₂.fst)

variable {t₁} {t₂}

/-- Given
```
X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
↓          ↓          ↓
Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
Then the big square is a pullback if both the small squares are.
-/
@[to_dual
/-- Given
```
Y₃ - i₃ -> X₃
|          |
g₂         f₂
∨          ∨
Y₂ - i₂ -> X₂
|          |
g₁         f₁
∨          ∨
Y₁ - i₁ -> X₁
```
The big square is a pushout if both the small squares are.
-/]
def pasteHorizIsPullback (H : IsLimit t₂) (H' : IsLimit t₁) : IsLimit (t₂.pasteHoriz t₁ hi₂) := by
  apply PullbackCone.isLimitAux'
  intro s
  -- Obtain the lift from lifting from both the small squares consecutively.
  obtain ⟨l₂, hl₂, hl₂'⟩ := PullbackCone.IsLimit.lift' H (s.fst ≫ g₁) s.snd
    (by rw [← s.condition, Category.assoc])
  obtain ⟨l₁, hl₁, hl₁'⟩ := PullbackCone.IsLimit.lift' H' s.fst l₂ (by rw [← hl₂, hi₂])
  refine ⟨l₁, hl₁, by simp [reassoc_of% hl₁', hl₂'], ?_⟩
  -- Uniqueness also follows from the universal property of both the small squares.
  intro m hm₁ hm₂
  apply PullbackCone.IsLimit.hom_ext H' (by simpa [hl₁] using hm₁)
  apply PullbackCone.IsLimit.hom_ext H
  · dsimp at hm₁
    rw [Category.assoc, ← hi₂, ← t₁.condition, reassoc_of% hm₁, hl₁', hi₂, hl₂]
  · simpa [hl₁', hl₂'] using hm₂

variable (t₁)

/-- Given
```
X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
↓          ↓          ↓
Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
Then the left square is a pullback if the right square and the big square are.
-/
@[to_dual
/-- Given
```
Y₃ - i₃ -> X₃
|          |
g₂         f₂
∨          ∨
Y₂ - i₂ -> X₂
|          |
g₁         f₁
∨          ∨
Y₁ - i₁ -> X₁
```
The bottom square is a pushout if the top square and the big square are.
-/]
def leftSquareIsPullback (H : IsLimit t₂) (H' : IsLimit (t₂.pasteHoriz t₁ hi₂)) : IsLimit t₁ := by
  apply PullbackCone.isLimitAux'
  intro s
  -- Obtain the induced morphism from the universal property of the big square
  obtain ⟨l, hl, hl'⟩ := PullbackCone.IsLimit.lift' H' s.fst (s.snd ≫ t₂.snd)
    (by rw [Category.assoc, ← t₂.condition, reassoc_of% s.condition, ← hi₂])
  refine ⟨l, hl, ?_, ?_⟩
  -- To check that `l` is compatible with the projections, we use the universal property of `t₂`
  · apply PullbackCone.IsLimit.hom_ext H
    · simp [← s.condition, ← hl, ← t₁.condition, ← hi₂]
    · simpa using hl'
  -- Uniqueness of the lift follows from the universal property of the big square
  · intro m hm₁ hm₂
    apply PullbackCone.IsLimit.hom_ext H'
    · simpa [hm₁] using hl.symm
    · simpa [← hm₂] using hl'.symm

/-- Given that the right square is a pullback, the pasted square is a pullback iff the left
square is. -/
@[to_dual
/-- Given that the top square is a pushout, the pasted square is a pushout iff the bottom square is.
-/]
def pasteHorizIsPullbackEquiv (H : IsLimit t₂) : IsLimit (t₂.pasteHoriz t₁ hi₂) ≃ IsLimit t₁ where
  toFun H' := leftSquareIsPullback t₁ _ H H'
  invFun H' := pasteHorizIsPullback _ H H'
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end PastePullbackHoriz

section PastePullbackVert

/- Let's consider the following diagram
```
Y₃ - i₃ -> X₃
|          |
g₂         f₂
∨          ∨
Y₂ - i₂ -> X₂
|          |
g₁         f₁
∨          ∨
Y₁ - i₁ -> X₁
```
Let `t₁` denote the cone corresponding to the bottom square, and `t₂` denote the cone corresponding
to the top square.
-/
variable {X₁ X₂ X₃ Y₁ : C} {f₁ : X₂ ⟶ X₁} {f₂ : X₃ ⟶ X₂} {i₁ : Y₁ ⟶ X₁}

/-- The `PullbackCone` obtained by pasting two `PullbackCone`'s vertically -/
@[to_dual /-- The pushout cocone obtained by pasting two pushout cocones horizontally. -/]
abbrev PullbackCone.pasteVert
    (t₁ : PullbackCone i₁ f₁) {i₂ : t₁.pt ⟶ X₂} (t₂ : PullbackCone i₂ f₂) (hi₂ : i₂ = t₁.snd) :
    PullbackCone i₁ (f₂ ≫ f₁) :=
  PullbackCone.mk (t₂.fst ≫ t₁.fst) t₂.snd
    (by rw [← reassoc_of% t₂.condition, Category.assoc, t₁.condition, ← hi₂])

variable (t₁ : PullbackCone i₁ f₁) {i₂ : t₁.pt ⟶ X₂} (t₂ : PullbackCone i₂ f₂) (hi₂ : i₂ = t₁.snd)

/-- Pasting two pullback cones vertically is isomorphic to the pullback cone obtained by flipping
them, pasting horizontally, and then flipping the result again. -/
@[to_dual
/-- Pasting two pushout cocones horizontally is isomorphic to the pushout cocone obtained by
flipping them, pasting vertically, and then flipping the result again. -/]
def PullbackCone.pasteVertFlip : (t₁.pasteVert t₂ hi₂).flip ≅ (t₁.flip.pasteHoriz t₂.flip hi₂) :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

variable {X₃ Y₁ Y₂ Y₃ : C} {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃} {i₃ : X₃ ⟶ Y₃}
  (t₂ : PullbackCone g₂ i₃) {i₂ : t₂.pt ⟶ Y₂} (t₁ : PullbackCone g₁ i₂) (hi₂ : i₂ = t₂.fst) in
/-- Pasting two pullback cones horizontally is isomorphic to the pullback cone obtained by flipping
them, pasting vertically, and then flipping the result again. -/
@[to_dual
/-- Pasting two pushout cocones vertically is isomorphic to the pushout cocone obtained by flipping
them, pasting horizontally, and then flipping the result again. -/]
def PullbackCone.pasteHorizFlip : (t₂.pasteHoriz t₁ hi₂).flip ≅ (t₂.flip.pasteVert t₁.flip hi₂) :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

variable {t₁} {t₂}

/-- Given
```
Y₃ - i₃ -> X₃
|          |
g₂         f₂
∨          ∨
Y₂ - i₂ -> X₂
|          |
g₁         f₁
∨          ∨
Y₁ - i₁ -> X₁
```
The big square is a pullback if both the small squares are.
-/
@[to_dual
/-- Given
```
X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
Then the big square is a pushout if both the small squares are.
-/]
def pasteVertIsPullback (H₁ : IsLimit t₁) (H₂ : IsLimit t₂) : IsLimit (t₁.pasteVert t₂ hi₂) := by
  apply PullbackCone.isLimitOfFlip <| IsLimit.ofIsoLimit _ (t₁.pasteVertFlip t₂ hi₂).symm
  exact pasteHorizIsPullback hi₂ (PullbackCone.flipIsLimit H₁) (PullbackCone.flipIsLimit H₂)

variable (t₂)

/-- Given
```
Y₃ - i₃ -> X₃
|          |
g₂         f₂
∨          ∨
Y₂ - i₂ -> X₂
|          |
g₁         f₁
∨          ∨
Y₁ - i₁ -> X₁
```
The top square is a pullback if the bottom square and the big square are.
-/
@[to_dual
/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the right square is a pushout if the left square and the big square are.
-/]
def topSquareIsPullback (H₁ : IsLimit t₁) (H₂ : IsLimit (t₁.pasteVert t₂ hi₂)) : IsLimit t₂ :=
  PullbackCone.isLimitOfFlip
    (leftSquareIsPullback _ hi₂ (PullbackCone.flipIsLimit H₁) (PullbackCone.flipIsLimit H₂))

/-- Given that the bottom square is a pullback, the pasted square is a pullback iff the top
square is. -/
@[to_dual
/-- Given that the left square is a pushout, the pasted square is a pushout iff the right square is.
-/]
def pasteVertIsPullbackEquiv (H : IsLimit t₁) : IsLimit (t₁.pasteVert t₂ hi₂) ≃ IsLimit t₂ where
  toFun H' := topSquareIsPullback t₂ _ H H'
  invFun H' := pasteVertIsPullback _ H H'
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end PastePullbackVert

end PasteLemma

to_dual_name_hint Left Left, Right Right, Fst Inl, Snd Inr

section
/- Let's consider the following diagram of pullbacks
```
W ×[X] (X ×[Z] Y) --snd--> X ×[Z] Y --snd--> Y
  |                           |              |
 fst                         fst             g
  v                           v              v
  W --------- f' --------->   X  ---- f ---> Y
```
In this section we show that `W ×[X] (X ×[Z] Y) ≅ W ×[Z] Y`.
-/

variable {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : W ⟶ X)
variable [HasPullback f g] [HasPullback f' (pullback.fst f g)]

@[to_dual]
instance : HasPullback (f' ≫ f) g :=
  HasLimit.mk {
    cone := (pullback.cone f g).pasteHoriz (pullback.cone f' (pullback.fst f g)) rfl
    isLimit := pasteHorizIsPullback rfl (pullback.isLimit f g)
      (pullback.isLimit f' (pullback.fst f g))
  }

/-- The canonical isomorphism `W ×[X] (X ×[Z] Y) ≅ W ×[Z] Y` -/
@[to_dual /-- The canonical isomorphism `W ⨿[X] (X ⨿[Z] Y) ≅ W ⨿[Z] Y` -/]
noncomputable def pullbackRightPullbackFstIso :
    pullback f' (pullback.fst f g) ≅ pullback (f' ≫ f) g :=
  IsLimit.conePointUniqueUpToIso
    (pasteHorizIsPullback rfl (pullback.isLimit f g) (pullback.isLimit f' (pullback.fst f g)))
    (pullback.isLimit (f' ≫ f) g)

@[to_dual (attr := reassoc (attr := simp)) inl_pushoutRightPushoutInlIso_inv]
theorem pullbackRightPullbackFstIso_hom_fst :
    (pullbackRightPullbackFstIso f g f').hom ≫ pullback.fst (f' ≫ f) g =
      pullback.fst f' (pullback.fst f g) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left

@[to_dual (attr := reassoc (attr := simp)) inr_pushoutRightPushoutInlIso_inv]
theorem pullbackRightPullbackFstIso_hom_snd :
    (pullbackRightPullbackFstIso f g f').hom ≫ pullback.snd _ _ =
      pullback.snd f' (pullback.fst f g) ≫ pullback.snd f g :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right

@[to_dual (attr := reassoc (attr := simp)) inl_pushoutRightPushoutInlIso_hom]
theorem pullbackRightPullbackFstIso_inv_fst :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.fst f' (pullback.fst f g) =
      pullback.fst (f' ≫ f) g :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_inv_snd_snd :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.right

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_inv_snd_fst :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ f' := by
  rw [← pullback.condition]
  exact pullbackRightPullbackFstIso_inv_fst_assoc f g f' _

end
section
/- Let's consider the following diagram of pullbacks
```
(X ×[Z] Y) ×[Y] W --snd--> W
    |                      |
   fst                     g'
    v                      v
 (X ×[Z] Y) --- snd --->   Y
    |                      |
   fst                     g
    v                      v
    X -------- f --------> Z

```
In this section we show that `(X ×[Z] Y) ×[Y] W ≅ X ×[Z] W`.
-/


variable {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y)
variable [HasPullback f g] [HasPullback (pullback.snd f g) g']

@[to_dual]
instance : HasPullback f (g' ≫ g) :=
  HasLimit.mk {
    cone := (pullback.cone f g).pasteVert (pullback.cone (pullback.snd f g) g') rfl
    isLimit := pasteVertIsPullback rfl (pullback.isLimit f g)
      (pullback.isLimit (pullback.snd f g) g')
  }

/-- The canonical isomorphism `(X ×[Z] Y) ×[Y] W ≅ X ×[Z] W` -/
@[to_dual /-- The canonical isomorphism `(X ⨿[Z] Y) ⨿[Y] W ≅ X ⨿[Z] W` -/]
def pullbackLeftPullbackSndIso :
    pullback (pullback.snd f g) g' ≅ pullback f (g' ≫ g) :=
  IsLimit.conePointUniqueUpToIso
      (pasteVertIsPullback rfl (pullback.isLimit f g) (pullback.isLimit (pullback.snd f g) g'))
      (pullback.isLimit f (g' ≫ g))

@[to_dual (attr := reassoc (attr := simp)) inl_pushoutLeftPushoutInrIso_inv]
theorem pullbackLeftPullbackSndIso_hom_fst :
    (pullbackLeftPullbackSndIso f g g').hom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left

@[to_dual (attr := reassoc (attr := simp)) inr_pushoutLeftPushoutInrIso_inv]
theorem pullbackLeftPullbackSndIso_hom_snd :
    (pullbackLeftPullbackSndIso f g g').hom ≫ pullback.snd _ _ = pullback.snd _ _ :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right

@[reassoc (attr := simp)]
theorem pullbackLeftPullbackSndIso_inv_fst :
    (pullbackLeftPullbackSndIso f g g').inv ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left

@[to_dual (attr := reassoc (attr := simp)) inr_pushoutLeftPushoutInrIso_hom]
theorem pullbackLeftPullbackSndIso_inv_snd_snd :
    (pullbackLeftPullbackSndIso f g g').inv ≫ pullback.snd _ _ = pullback.snd _ _ :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.right

@[reassoc (attr := simp)]
theorem pullbackLeftPullbackSndIso_inv_fst_snd :
    (pullbackLeftPullbackSndIso f g g').inv ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ g' := by
  rw [pullback.condition]
  exact pullbackLeftPullbackSndIso_inv_snd_snd_assoc f g g' g'

end

section

/- Let's consider the following diagram of pushouts
```
X ---- g ----> Z ----- g' -----> W
|              |                 |
f             inr               inr
v              v                 v
Y - inl -> Y ⨿[X] Z --inl--> (Y ⨿[X] Z) ⨿[Z] W
```
In this section we show that `(Y ⨿[X] Z) ⨿[Z] W ≅ Y ⨿[X] W`.
-/
variable {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)
variable [HasPushout f g] [HasPushout (pushout.inr f g) g']

@[reassoc (attr := simp)]
theorem inl_inl_pushoutLeftPushoutInrIso_hom :
    (pushout.inl f g) ≫ pushout.inl (pushout.inr f g) g' ≫
      (pushoutLeftPushoutInrIso f g g').hom = (pushout.inl f (g ≫ g')) := by
  rw [← Category.assoc]
  apply IsColimit.comp_coconePointUniqueUpToIso_hom (pasteHorizIsPushout _ _ _) _ WalkingSpan.left

@[reassoc (attr := simp)]
theorem inr_inl_pushoutLeftPushoutInrIso_hom :
    pushout.inr f g ≫ pushout.inl (pushout.inr f g) g' ≫ (pushoutLeftPushoutInrIso f g g').hom =
      g' ≫ pushout.inr f (g ≫ g') := by
  rw [← Category.assoc, ← Iso.eq_comp_inv, Category.assoc, inr_pushoutLeftPushoutInrIso_inv,
    pushout.condition]

end
section

/- Let's consider the diagram of pushouts
```
X ---- g ----> Z
|              |
f             inr
v              v
Y - inl -> Y ⨿[X] Z
|              |
f'            inr
v              v
W - inl -> W ⨿[Y] (Y ⨿[X] Z)
```

In this section we will construct the isomorphism `W ⨿[Y] (Y ⨿[X] Z) ≅ W ⨿[X] Z`.
-/

variable {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (f' : Y ⟶ W)
variable [HasPushout f g] [HasPushout f' (pushout.inl f g)]

@[reassoc (attr := simp)]
theorem inr_inr_pushoutRightPushoutInlIso_hom :
    pushout.inr _ _ ≫ pushout.inr _ _ ≫ (pushoutRightPushoutInlIso f g f').hom =
      pushout.inr _ _ := by
  rw [← Category.assoc]
  apply IsColimit.comp_coconePointUniqueUpToIso_hom (pasteVertIsPushout rfl _ _) _ WalkingSpan.right

@[reassoc (attr := simp)]
theorem inr_inl_pushoutRightPushoutInlIso_hom :
    pushout.inl _ _ ≫ pushout.inr _ _ ≫ (pushoutRightPushoutInlIso f g f').hom =
      f' ≫ pushout.inl _ _ := by
  rw [← Category.assoc, ← pushout.condition, Category.assoc, inl_pushoutRightPushoutInlIso_hom]

end

end CategoryTheory.Limits
