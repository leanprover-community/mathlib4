/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel, Bhavik Mehta, Andrew Yang, Emily Riehl, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
# PullbackCone

This file provides API for interacting with cones (resp. cocones) in the case of pullbacks
(resp. pushouts).

## Main definitions

* `PullbackCone f g`: Given morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`, a term `t : PullbackCone f g`
  provides the data of a cone pictured as follows
  ```
  t.pt ---t.snd---> Y
    |               |
  t.fst            g
    |               |
    v               v
    X -----f------> Z
  ```
  The type `PullbackCone f g` is implemented as an abbreviation for `Cone (cospan f g)`, so general
  results about cones are also available for `PullbackCone f g`.

* `PushoutCone f g`: Given morphisms `f : X ⟶ Y` and `g : X ⟶ Z`, a term `t : PushoutCone f g`
  provides the data of a cocone pictured as follows
  ```
    X -----f------> Y
    |               |
    g               t.inr
    |               |
    v               v
    Z ---t.inl---> t.pt
  ```
  Similar to `PullbackCone`, `PushoutCone f g` is implemented as an abbreviation for
  `Cocone (span f g)`, so general results about cocones are also available for `PushoutCone f g`.

## API
We summarize the most important parts of the API for pullback cones here. The dual notions for
pushout cones are also available in this file.

Various ways of constructing pullback cones:
* `PullbackCone.mk` constructs a term of `PullbackCone f g` given morphisms `fst` and `snd` such
  that `fst ≫ f = snd ≫ g`.
* `PullbackCone.flip` is the `PullbackCone` obtained by flipping `fst` and `snd`.

Interaction with `IsLimit`:
* `PullbackCone.isLimitAux` and `PullbackCone.isLimitAux'` provide two convenient ways to show that
  a given `PullbackCone` is a limit cone.
* `PullbackCone.isLimit.mk` provides a convenient way to show that a `PullbackCone` constructed
  using `PullbackCone.mk` is a limit cone.
* `PullbackCone.IsLimit.lift` and `PullbackCone.IsLimit.lift'` provides convenient ways for
  constructing the morphisms to the point of a limit `PullbackCone` from the universal property.
* `PullbackCone.IsLimit.hom_ext` provides a convenient way to show that two morphisms to the point
  of a limit `PullbackCone` are equal.

Interaction with `CommSq`:
* `CommSq.cone` and `CommSq.cocone` provide the implicit (non-limiting) pullback cone and pushout
  cocone associated with a commuting square

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

/-- A pullback cone is just a cone on the cospan formed by two morphisms `f : X ⟶ Z` and
`g : Y ⟶ Z`. -/
abbrev PullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) :=
  Cone (cospan f g)

namespace PullbackCone

variable {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The first projection of a pullback cone. -/
abbrev fst (t : PullbackCone f g) : t.pt ⟶ X :=
  t.π.app WalkingCospan.left

/-- The second projection of a pullback cone. -/
abbrev snd (t : PullbackCone f g) : t.pt ⟶ Y :=
  t.π.app WalkingCospan.right

theorem π_app_left (c : PullbackCone f g) : c.π.app WalkingCospan.left = c.fst := rfl

theorem π_app_right (c : PullbackCone f g) : c.π.app WalkingCospan.right = c.snd := rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
theorem condition_one (t : PullbackCone f g) : t.π.app WalkingCospan.one = t.fst ≫ f := by
  have w := t.π.naturality WalkingCospan.Hom.inl
  dsimp at w; simpa using w

set_option backward.defeqAttrib.useBackward true in
/-- A pullback cone on `f` and `g` is determined by morphisms `fst : W ⟶ X` and `snd : W ⟶ Y`
such that `fst ≫ f = snd ≫ g`. -/
@[simps]
def mk {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g := by cat_disch) :
    PullbackCone f g where
  pt := W
  π := { app := fun j => Option.casesOn j (fst ≫ f) fun j' => WalkingPair.casesOn j' fst snd
         naturality := by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) j <;> cases j <;> simp [eq] }

@[simp]
theorem mk_π_app_left {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).π.app WalkingCospan.left = fst := rfl

@[simp]
theorem mk_π_app_right {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).π.app WalkingCospan.right = snd := rfl

@[simp]
theorem mk_π_app_one {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).π.app WalkingCospan.one = fst ≫ f := rfl

@[simp]
theorem mk_fst {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).fst = fst := rfl

@[simp]
theorem mk_snd {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).snd = snd := rfl

@[reassoc]
theorem condition (t : PullbackCone f g) : fst t ≫ f = snd t ≫ g :=
  (t.w inl).trans (t.w inr).symm

set_option backward.isDefEq.respectTransparency false in
/-- To check whether two morphisms are equalized by the maps of a pullback cone, it suffices to
check it for `fst t` and `snd t` -/
theorem equalizer_ext (t : PullbackCone f g) {W : C} {k l : W ⟶ t.pt} (h₀ : k ≫ fst t = l ≫ fst t)
    (h₁ : k ≫ snd t = l ≫ snd t) : ∀ j : WalkingCospan, k ≫ t.π.app j = l ≫ t.π.app j
  | some WalkingPair.left => h₀
  | some WalkingPair.right => h₁
  | none => by rw [← t.w inl, reassoc_of% h₀]

/-- To construct an isomorphism of pullback cones, it suffices to construct an isomorphism
of the cone points and check it commutes with `fst` and `snd`. -/
def ext {s t : PullbackCone f g} (i : s.pt ≅ t.pt) (w₁ : s.fst = i.hom ≫ t.fst := by cat_disch)
    (w₂ : s.snd = i.hom ≫ t.snd := by cat_disch) : s ≅ t :=
  WalkingCospan.ext i w₁ w₂

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism between a pullback cone and the corresponding pullback cone
reconstructed using `PullbackCone.mk`. -/
@[simps!]
def eta (t : PullbackCone f g) : t ≅ mk t.fst t.snd t.condition :=
  PullbackCone.ext (Iso.refl _)

/-- This is a slightly more convenient method to verify that a pullback cone is a limit cone. It
only asks for a proof of facts that carry any mathematical content -/
def isLimitAux (t : PullbackCone f g) (lift : ∀ s : PullbackCone f g, s.pt ⟶ t.pt)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ t.fst = s.fst)
    (fac_right : ∀ s : PullbackCone f g, lift s ≫ t.snd = s.snd)
    (uniq : ∀ (s : PullbackCone f g) (m : s.pt ⟶ t.pt)
      (_ : ∀ j : WalkingCospan, m ≫ t.π.app j = s.π.app j), m = lift s) : IsLimit t :=
  { lift
    fac := fun s j => Option.casesOn j (by
        rw [← s.w inl, ← t.w inl, ← Category.assoc]
        congr
        exact fac_left s)
      fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s)
    uniq := uniq }

/-- This is another convenient method to verify that a pullback cone is a limit cone. It
only asks for a proof of facts that carry any mathematical content, and allows access to the
same `s` for all parts. -/
def isLimitAux' (t : PullbackCone f g)
    (create :
      ∀ s : PullbackCone f g,
        { l //
          l ≫ t.fst = s.fst ∧
            l ≫ t.snd = s.snd ∧ ∀ {m}, m ≫ t.fst = s.fst → m ≫ t.snd = s.snd → m = l }) :
    Limits.IsLimit t :=
  PullbackCone.isLimitAux t (fun s => (create s).1) (fun s => (create s).2.1)
    (fun s => (create s).2.2.1) fun s _ w =>
    (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)

/-- This is a more convenient formulation to show that a `PullbackCone` constructed using
`PullbackCone.mk` is a limit cone.
-/
def IsLimit.mk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
    (lift : ∀ s : PullbackCone f g, s.pt ⟶ W)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ fst = s.fst)
    (fac_right : ∀ s : PullbackCone f g, lift s ≫ snd = s.snd)
    (uniq :
      ∀ (s : PullbackCone f g) (m : s.pt ⟶ W) (_ : m ≫ fst = s.fst) (_ : m ≫ snd = s.snd),
        m = lift s) :
    IsLimit (mk fst snd eq) :=
  isLimitAux _ lift fac_left fac_right fun s m w =>
    uniq s m (w WalkingCospan.left) (w WalkingCospan.right)

theorem IsLimit.hom_ext {t : PullbackCone f g} (ht : IsLimit t) {W : C} {k l : W ⟶ t.pt}
    (h₀ : k ≫ fst t = l ≫ fst t) (h₁ : k ≫ snd t = l ≫ snd t) : k = l :=
  ht.hom_ext <| equalizer_ext _ h₀ h₁

/-- If `t` is a limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such that
`h ≫ f = k ≫ g`, then we get `l : W ⟶ t.pt`, which satisfies `l ≫ fst t = h`
and `l ≫ snd t = k`, see `IsLimit.lift_fst` and `IsLimit.lift_snd`. -/
def IsLimit.lift {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ t.pt :=
  ht.lift <| PullbackCone.mk _ _ w

@[reassoc (attr := simp)]
lemma IsLimit.lift_fst {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : IsLimit.lift ht h k w ≫ fst t = h := ht.fac _ _

@[reassoc (attr := simp)]
lemma IsLimit.lift_snd {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : IsLimit.lift ht h k w ≫ snd t = k := ht.fac _ _

/-- If `t` is a limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such that
`h ≫ f = k ≫ g`, then we have `l : W ⟶ t.pt` satisfying `l ≫ fst t = h` and `l ≫ snd t = k`.
-/
def IsLimit.lift' {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : { l : W ⟶ t.pt // l ≫ fst t = h ∧ l ≫ snd t = k } :=
  ⟨IsLimit.lift ht h k w, by simp⟩

/-- The pullback cone reconstructed using `PullbackCone.mk` from a pullback cone that is a
limit, is also a limit. -/
def mkSelfIsLimit {t : PullbackCone f g} (ht : IsLimit t) : IsLimit (mk t.fst t.snd t.condition) :=
  IsLimit.ofIsoLimit ht (eta t)

section Flip

variable (t : PullbackCone f g)

/-- The pullback cone obtained by flipping `fst` and `snd`. -/
def flip : PullbackCone g f := PullbackCone.mk _ _ t.condition.symm

@[simp] lemma flip_pt : t.flip.pt = t.pt := rfl
@[simp] lemma flip_fst : t.flip.fst = t.snd := rfl
@[simp] lemma flip_snd : t.flip.snd = t.fst := rfl

/-- Flipping a pullback cone twice gives an isomorphic cone. -/
def flipFlipIso : t.flip.flip ≅ t := PullbackCone.ext (Iso.refl _) (by simp) (by simp)

variable {t}

set_option backward.isDefEq.respectTransparency false in
/-- The flip of a pullback square is a pullback square. -/
def flipIsLimit (ht : IsLimit t) : IsLimit t.flip :=
  IsLimit.mk _ (fun s => ht.lift s.flip) (by simp) (by simp) (fun s m h₁ h₂ => by
    apply IsLimit.hom_ext ht <;> simp [h₁, h₂])

/-- A square is a pullback square if its flip is. -/
def isLimitOfFlip (ht : IsLimit t.flip) : IsLimit t :=
  IsLimit.ofIsoLimit (flipIsLimit ht) t.flipFlipIso

end Flip

end PullbackCone

/-- This is a helper construction that can be useful when verifying that a category has all
pullbacks. Given `F : WalkingCospan ⥤ C`, which is really the same as
`cospan (F.map inl) (F.map inr)`, and a pullback cone on `F.map inl` and `F.map inr`, we
get a cone on `F`.

If you're thinking about using this, have a look at `hasPullbacks_of_hasLimit_cospan`,
which you may find to be an easier way of achieving your goal. -/
@[simps]
def Cone.ofPullbackCone {F : WalkingCospan ⥤ C} (t : PullbackCone (F.map inl) (F.map inr)) :
    Cone F where
  pt := t.pt
  π := t.π ≫ (diagramIsoCospan F).inv

/-- Given `F : WalkingCospan ⥤ C`, which is really the same as `cospan (F.map inl) (F.map inr)`,
and a cone on `F`, we get a pullback cone on `F.map inl` and `F.map inr`. -/
@[simps]
def PullbackCone.ofCone {F : WalkingCospan ⥤ C} (t : Cone F) :
    PullbackCone (F.map inl) (F.map inr) where
  pt := t.pt
  π := t.π ≫ (diagramIsoCospan F).hom

set_option backward.defeqAttrib.useBackward true in
/-- A diagram `WalkingCospan ⥤ C` is isomorphic to some `PullbackCone.mk` after
composing with `diagramIsoCospan`. -/
@[simps!]
def PullbackCone.isoMk {F : WalkingCospan ⥤ C} (t : Cone F) :
    (Cone.postcompose (diagramIsoCospan.{v} _).hom).obj t ≅
      PullbackCone.mk (t.π.app WalkingCospan.left) (t.π.app WalkingCospan.right)
        ((t.π.naturality inl).symm.trans (t.π.naturality inr :)) :=
  Cone.ext (Iso.refl _) <| by
    rintro (_ | (_ | _)) <;> simp

/-- A pushout cocone is just a cocone on the span formed by two morphisms `f : X ⟶ Y` and
`g : X ⟶ Z`. -/
abbrev PushoutCocone (f : X ⟶ Y) (g : X ⟶ Z) :=
  Cocone (span f g)

namespace PushoutCocone

variable {f : X ⟶ Y} {g : X ⟶ Z}

/-- The first inclusion of a pushout cocone. -/
abbrev inl (t : PushoutCocone f g) : Y ⟶ t.pt :=
  t.ι.app WalkingSpan.left

/-- The second inclusion of a pushout cocone. -/
abbrev inr (t : PushoutCocone f g) : Z ⟶ t.pt :=
  t.ι.app WalkingSpan.right

-- This cannot be `@[simp]` because `c.inl` is reducibly defeq to the LHS.
theorem ι_app_left (c : PushoutCocone f g) : c.ι.app WalkingSpan.left = c.inl := rfl

-- This cannot be `@[simp]` because `c.inr` is reducibly defeq to the LHS.
theorem ι_app_right (c : PushoutCocone f g) : c.ι.app WalkingSpan.right = c.inr := rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
theorem condition_zero (t : PushoutCocone f g) : t.ι.app WalkingSpan.zero = f ≫ t.inl := by
  have w := t.ι.naturality WalkingSpan.Hom.fst
  dsimp at w; simpa using w.symm

set_option backward.defeqAttrib.useBackward true in
/-- A pushout cocone on `f` and `g` is determined by morphisms `inl : Y ⟶ W` and `inr : Z ⟶ W` such
that `f ≫ inl = g ↠ inr`. -/
@[simps]
def mk {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : PushoutCocone f g where
  pt := W
  ι := { app := fun j => Option.casesOn j (f ≫ inl) fun j' => WalkingPair.casesOn j' inl inr
         naturality := by
          rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) <;> intro f <;> cases f <;> dsimp <;> aesop }

@[simp]
theorem mk_ι_app_left {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).ι.app WalkingSpan.left = inl := rfl

@[simp]
theorem mk_ι_app_right {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).ι.app WalkingSpan.right = inr := rfl

@[simp]
theorem mk_ι_app_zero {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).ι.app WalkingSpan.zero = f ≫ inl := rfl

@[simp]
theorem mk_inl {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).inl = inl := rfl

@[simp]
theorem mk_inr {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).inr = inr := rfl

@[reassoc]
theorem condition (t : PushoutCocone f g) : f ≫ inl t = g ≫ inr t :=
  (t.w fst).trans (t.w snd).symm

set_option backward.isDefEq.respectTransparency false in
/-- To check whether a morphism is coequalized by the maps of a pushout cocone, it suffices to check
  it for `inl t` and `inr t` -/
theorem coequalizer_ext (t : PushoutCocone f g) {W : C} {k l : t.pt ⟶ W}
    (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) :
    ∀ j : WalkingSpan, t.ι.app j ≫ k = t.ι.app j ≫ l
  | some WalkingPair.left => h₀
  | some WalkingPair.right => h₁
  | none => by rw [← t.w fst, Category.assoc, Category.assoc, h₀]

/-- To construct an isomorphism of pushout cocones, it suffices to construct an isomorphism
of the cocone points and check it commutes with `inl` and `inr`. -/
def ext {s t : PushoutCocone f g} (i : s.pt ≅ t.pt) (w₁ : s.inl ≫ i.hom = t.inl := by cat_disch)
    (w₂ : s.inr ≫ i.hom = t.inr := by cat_disch) : s ≅ t :=
  WalkingSpan.ext i w₁ w₂

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism between a pushout cocone and the corresponding pushout cocone
reconstructed using `PushoutCocone.mk`. -/
@[simps!]
def eta (t : PushoutCocone f g) : t ≅ mk t.inl t.inr t.condition :=
  PushoutCocone.ext (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- This is a slightly more convenient method to verify that a pushout cocone is a colimit cocone.
It only asks for a proof of facts that carry any mathematical content -/
def isColimitAux (t : PushoutCocone f g) (desc : ∀ s : PushoutCocone f g, t.pt ⟶ s.pt)
    (fac_left : ∀ s : PushoutCocone f g, t.inl ≫ desc s = s.inl)
    (fac_right : ∀ s : PushoutCocone f g, t.inr ≫ desc s = s.inr)
    (uniq : ∀ (s : PushoutCocone f g) (m : t.pt ⟶ s.pt)
    (_ : ∀ j : WalkingSpan, t.ι.app j ≫ m = s.ι.app j), m = desc s) : IsColimit t :=
  { desc
    fac := fun s j =>
      Option.casesOn j (by simp [← s.w fst, ← t.w fst, fac_left s]) fun j' =>
        WalkingPair.casesOn j' (fac_left s) (fac_right s)
    uniq := uniq }

/-- This is another convenient method to verify that a pushout cocone is a colimit cocone. It
only asks for a proof of facts that carry any mathematical content, and allows access to the
same `s` for all parts. -/
def isColimitAux' (t : PushoutCocone f g)
    (create :
      ∀ s : PushoutCocone f g,
        { l //
          t.inl ≫ l = s.inl ∧
            t.inr ≫ l = s.inr ∧ ∀ {m}, t.inl ≫ m = s.inl → t.inr ≫ m = s.inr → m = l }) :
    IsColimit t :=
  isColimitAux t (fun s => (create s).1) (fun s => (create s).2.1) (fun s => (create s).2.2.1)
    fun s _ w => (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)


theorem IsColimit.hom_ext {t : PushoutCocone f g} (ht : IsColimit t) {W : C} {k l : t.pt ⟶ W}
    (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) : k = l :=
  ht.hom_ext <| coequalizer_ext _ h₀ h₁

/-- If `t` is a colimit pushout cocone over `f` and `g` and `h : Y ⟶ W` and `k : Z ⟶ W` are
morphisms satisfying `f ≫ h = g ≫ k`, then we have a factorization `l : t.pt ⟶ W` such that
`inl t ≫ l = h` and `inr t ≫ l = k`, see `IsColimit.inl_desc` and `IsColimit.inr_desc`. -/
def IsColimit.desc {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : t.pt ⟶ W :=
  ht.desc (PushoutCocone.mk _ _ w)

@[reassoc (attr := simp)]
lemma IsColimit.inl_desc {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : inl t ≫ IsColimit.desc ht h k w = h :=
  ht.fac _ _

@[reassoc (attr := simp)]
lemma IsColimit.inr_desc {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : inr t ≫ IsColimit.desc ht h k w = k :=
  ht.fac _ _

/-- If `t` is a colimit pushout cocone over `f` and `g` and `h : Y ⟶ W` and `k : Z ⟶ W` are
morphisms satisfying `f ≫ h = g ≫ k`, then we have a factorization `l : t.pt ⟶ W` such that
`inl t ≫ l = h` and `inr t ≫ l = k`. -/
def IsColimit.desc' {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : { l : t.pt ⟶ W // inl t ≫ l = h ∧ inr t ≫ l = k } :=
  ⟨IsColimit.desc ht h k w, by simp⟩

/-- This is a more convenient formulation to show that a `PushoutCocone` constructed using
`PushoutCocone.mk` is a colimit cocone.
-/
def IsColimit.mk {W : C} {inl : Y ⟶ W} {inr : Z ⟶ W} (eq : f ≫ inl = g ≫ inr)
    (desc : ∀ s : PushoutCocone f g, W ⟶ s.pt)
    (fac_left : ∀ s : PushoutCocone f g, inl ≫ desc s = s.inl)
    (fac_right : ∀ s : PushoutCocone f g, inr ≫ desc s = s.inr)
    (uniq :
      ∀ (s : PushoutCocone f g) (m : W ⟶ s.pt) (_ : inl ≫ m = s.inl) (_ : inr ≫ m = s.inr),
        m = desc s) :
    IsColimit (mk inl inr eq) :=
  isColimitAux _ desc fac_left fac_right fun s m w =>
    uniq s m (w WalkingCospan.left) (w WalkingCospan.right)

/-- The pushout cocone reconstructed using `PushoutCocone.mk` from a pushout cocone that is a
colimit, is also a colimit. -/
def mkSelfIsColimit {t : PushoutCocone f g} (ht : IsColimit t) :
    IsColimit (mk t.inl t.inr t.condition) :=
  IsColimit.ofIsoColimit ht (eta t)

section Flip

variable (t : PushoutCocone f g)

/-- The pushout cocone obtained by flipping `inl` and `inr`. -/
def flip : PushoutCocone g f := PushoutCocone.mk _ _ t.condition.symm

@[simp] lemma flip_pt : t.flip.pt = t.pt := rfl
@[simp] lemma flip_inl : t.flip.inl = t.inr := rfl
@[simp] lemma flip_inr : t.flip.inr = t.inl := rfl

/-- Flipping a pushout cocone twice gives an isomorphic cocone. -/
def flipFlipIso : t.flip.flip ≅ t := PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

variable {t}

set_option backward.isDefEq.respectTransparency false in
/-- The flip of a pushout square is a pushout square. -/
def flipIsColimit (ht : IsColimit t) : IsColimit t.flip :=
  IsColimit.mk _ (fun s => ht.desc s.flip) (by simp) (by simp) (fun s m h₁ h₂ => by
    apply IsColimit.hom_ext ht <;> simp [h₁, h₂])

/-- A square is a pushout square if its flip is. -/
def isColimitOfFlip (ht : IsColimit t.flip) : IsColimit t :=
  IsColimit.ofIsoColimit (flipIsColimit ht) t.flipFlipIso

end Flip

end PushoutCocone

/-- This is a helper construction that can be useful when verifying that a category has all
pushout. Given `F : WalkingSpan ⥤ C`, which is really the same as
`span (F.map fst) (F.map snd)`, and a pushout cocone on `F.map fst` and `F.map snd`,
we get a cocone on `F`.

If you're thinking about using this, have a look at `hasPushouts_of_hasColimit_span`, which
you may find to be an easier way of achieving your goal. -/
@[simps]
def Cocone.ofPushoutCocone {F : WalkingSpan ⥤ C} (t : PushoutCocone (F.map fst) (F.map snd)) :
    Cocone F where
  pt := t.pt
  ι := (diagramIsoSpan F).hom ≫ t.ι
/-- Given `F : WalkingSpan ⥤ C`, which is really the same as `span (F.map fst) (F.map snd)`,
and a cocone on `F`, we get a pushout cocone on `F.map fst` and `F.map snd`. -/
@[simps]
def PushoutCocone.ofCocone {F : WalkingSpan ⥤ C} (t : Cocone F) :
    PushoutCocone (F.map fst) (F.map snd) where
  pt := t.pt
  ι := (diagramIsoSpan F).inv ≫ t.ι

set_option backward.defeqAttrib.useBackward true in
/-- A diagram `WalkingSpan ⥤ C` is isomorphic to some `PushoutCocone.mk` after composing with
`diagramIsoSpan`. -/
@[simps!]
def PushoutCocone.isoMk {F : WalkingSpan ⥤ C} (t : Cocone F) :
    (Cocone.precompose (diagramIsoSpan.{v} _).inv).obj t ≅
      PushoutCocone.mk (t.ι.app WalkingSpan.left) (t.ι.app WalkingSpan.right)
        ((t.ι.naturality fst).trans (t.ι.naturality snd).symm) :=
  Cocone.ext (Iso.refl _) <| by
    rintro (_ | (_ | _)) <;> simp

end Limits

namespace CommSq
open Limits
variable {C : Type*} [Category* C]

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

/-- The (not necessarily limiting) `PullbackCone h i` implicit in the statement
that we have `CommSq f g h i`.
-/
def cone (s : CommSq f g h i) : PullbackCone h i :=
  PullbackCone.mk _ _ s.w

/-- The (not necessarily limiting) `PushoutCocone f g` implicit in the statement
that we have `CommSq f g h i`.
-/
def cocone (s : CommSq f g h i) : PushoutCocone f g :=
  PushoutCocone.mk _ _ s.w

@[simp]
theorem cone_fst (s : CommSq f g h i) : s.cone.fst = f :=
  rfl

@[simp]
theorem cone_snd (s : CommSq f g h i) : s.cone.snd = g :=
  rfl

@[simp]
theorem cocone_inl (s : CommSq f g h i) : s.cocone.inl = h :=
  rfl

@[simp]
theorem cocone_inr (s : CommSq f g h i) : s.cocone.inr = i :=
  rfl

end CommSq

end CategoryTheory
