/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong

/-! # Bicategories of spans in a category

In this file, given a category `C` and two morphism properties
Wₗ and Wᵣ in C that are stable under compositions, contain identities and
such that for any morphism `b : x₃ ⟶ x₄` in Wₗ and any morphism `r : x₂ → x₃` in Wᵣ,
there exists a pullback square
```
     t
  x₁ --> x₂
  |      |
l |      | r
  v      v
  x₃ --> x₄
     b
```
in `C` such that `t` satisfies `Wₗ` and `l` satisfies `Wᵣ`,
we construct the bicategory of spans in C with left morphism in Wₗ and right morphism
in Wᵣ (TODO @robin-carlier).

-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C]
  (Wₗ : MorphismProperty C)
  (Wᵣ : MorphismProperty C)

/-- A (Wₗ, Wᵣ)-span from c to c' is the data of an
object `a : C`, together with a morphism `a ⟶ c` in Wₗ,
and a morphism `a ⟶ c'` in Wᵣ. -/
structure Span (c c' : C) where
  /-- the apex of the span -/
  apex : C
  /-- the left map -/
  l : apex ⟶ c
  /-- the right map -/
  r : apex ⟶ c'
  wl : Wₗ l
  wr : Wᵣ r

namespace Span

variable {Wₗ Wᵣ} {c c' : C}

/-- A morphism of spans is a morphism between the apices compatible
with the projections. -/
structure Hom (S₁ S₂ : Span Wₗ Wᵣ c c') : Type _ where
  /-- the map between the apices -/
  hom : S₁.apex ⟶ S₂.apex
  hom_l : hom ≫ S₂.l = S₁.l := by cat_disch
  hom_r : hom ≫ S₂.r = S₁.r := by cat_disch

attribute [reassoc (attr := simp)] Hom.hom_l Hom.hom_r
attribute [grind =] Hom.hom_l Hom.hom_r

@[simps!]
instance : Category (Span Wₗ Wᵣ c c') where
  Hom := Hom
  comp φ φ' := { hom := φ.hom ≫ φ'.hom }
  id S := { hom := 𝟙 _ }

attribute [grind =] id_hom comp_hom

@[ext, grind ext]
lemma hom_ext {S S' : Span Wₗ Wᵣ c c'} {f g : S ⟶ S'} (h : f.hom = g.hom) :
    f = g := by
  cases f
  cases g
  grind

set_option mathlib.tactic.category.grind true in
/-- Construct an isomorphism of spans from an isomorphism between the
apices that is compatible with the projections. -/
@[simps (attr := grind =)]
def mkIso {S S' : Span Wₗ Wᵣ c c'} (e : S.apex ≅ S'.apex)
    (hₗ : e.hom ≫ S'.l = S.l := by cat_disch)
    (hᵣ : e.hom ≫ S'.r = S.r := by cat_disch) :
    S ≅ S' where
  hom.hom := e.hom
  inv.hom := e.inv

variable [Wₗ.ContainsIdentities] [Wᵣ.ContainsIdentities] [Wₗ.HasPullbacksAgainst Wᵣ]
    [Wₗ.IsStableUnderBaseChangeAgainst Wᵣ] [Wᵣ.IsStableUnderBaseChangeAgainst Wₗ]
    [Wₗ.IsStableUnderComposition] [Wᵣ.IsStableUnderComposition]

open Limits in
instance {c c' c'' : C} (S₁ : Span Wₗ Wᵣ c c') (S₂ : Span Wₗ Wᵣ c' c'') : HasPullback S₁.r S₂.l :=
  letI : HasPullback S₂.l S₁.r := hasPullback_ofHasPullbacksAgainst S₂.wl S₁.wr
  hasPullback_symmetry _ _

instance (S₁ : Span Wₗ Wᵣ c c') : Wₗ.IsStableUnderBaseChangeAlong S₁.r :=
  MorphismProperty.IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong _ S₁.wr

instance (S₁ : Span Wₗ Wᵣ c c') : Wᵣ.IsStableUnderBaseChangeAlong S₁.l :=
  MorphismProperty.IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong _ S₁.wl

/-- The identity span, where both legs are identity morphisms. -/
@[simps (attr := grind =)]
def id (c : C) :
    Span Wₗ Wᵣ c c where
  apex := c
  l := 𝟙 _
  r := 𝟙 _
  wl := MorphismProperty.ContainsIdentities.id_mem _
  wr := MorphismProperty.ContainsIdentities.id_mem _

open Limits MorphismProperty in
/-- The composition of two spans: if the relevant pullback exists and if the
morphism properties are stable under the relevant base change, it is given by the
total span
```
     P
    /  \
   /    \
  X₁     X₂
 /  \   /  \
c     c'    c''
```
where the top diamond is a pullback square
-/
@[simps (attr := grind =)]
noncomputable def comp {c c' c'' : C}
    (S₁ : Span Wₗ Wᵣ c c') (S₂ : Span Wₗ Wᵣ c' c'') :
    Span Wₗ Wᵣ c c'' where
  apex := pullback S₁.r S₂.l
  l := pullback.fst S₁.r S₂.l ≫ S₁.l
  r := pullback.snd S₁.r S₂.l ≫ S₂.r
  wl :=
    IsStableUnderComposition.comp_mem
      _ _ (IsStableUnderBaseChangeAlong.of_isPullback
      (.flip <| .of_hasPullback S₁.r S₂.l) S₂.wl) S₁.wl
  wr :=
    IsStableUnderComposition.comp_mem
    _ _ (IsStableUnderBaseChangeAlong.of_isPullback
      (.of_hasPullback S₁.r S₂.l) S₁.wr) S₂.wr

variable (C) in
/-- The bicategory of spans of `C` with left/right legs satisfying a given
morphism property. This is a one-field structure wrapper around `C`. -/
structure Spans (Wₗ Wᵣ : MorphismProperty C) : Type _ where
  /-- the underlying object of `C` of a term in `Spans C _ _` -/
  of : C

variable [Wₗ.ContainsIdentities] [Wᵣ.ContainsIdentities] [Wₗ.HasPullbacksAgainst Wᵣ]
    [Wₗ.IsStableUnderBaseChangeAgainst Wᵣ] [Wᵣ.IsStableUnderBaseChangeAgainst Wₗ]
    [Wₗ.IsStableUnderComposition] [Wᵣ.IsStableUnderComposition]

namespace Spans

noncomputable instance : CategoryStruct (Spans C Wₗ Wᵣ) where
  Hom x y := Span Wₗ Wᵣ x.of y.of
  id x := Span.id x.of
  comp S₁ S₂ := Span.comp S₁ S₂

variable {Wₗ Wᵣ}

@[simp, grind =]
lemma id_apex (X : Spans C Wₗ Wᵣ) : (𝟙 X : X ⟶ X).apex = X.of := rfl

@[simp, grind =]
lemma id_l {X : Spans C Wₗ Wᵣ} : (𝟙 X : X ⟶ X).l = 𝟙 X.of := rfl

@[simp, grind =]
lemma id_r {X : Spans C Wₗ Wᵣ} : (𝟙 X : X ⟶ X).r = 𝟙 X.of := rfl

instance {X Y : Spans C Wₗ Wᵣ} : Category (X ⟶ Y) :=
  inferInstanceAs (Category <| Span Wₗ Wᵣ X.of Y.of)

@[simp, grind =]
lemma hom₂_comp_hom {X Y : Spans C Wₗ Wᵣ} {S S' S'' : X ⟶ Y} (f : S ⟶ S')
    (g : S' ⟶ S'') :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[simp, grind =]
lemma hom₂_id_hom {X Y : Spans C Wₗ Wᵣ} (S : X ⟶ Y) :
    (𝟙 S : S ⟶ S).hom = 𝟙 S.apex := rfl

@[ext, grind ext]
lemma hom₂_ext {X Y : Spans C Wₗ Wᵣ} {S S' : X ⟶ Y} {f g : S ⟶ S'}
    (h : f.hom = g.hom) :
    f = g :=
  Span.hom_ext h

/-- Constructor for 1-morphisms in `Spans C _ _` -/
abbrev mkHom {X Y : Spans C Wₗ Wᵣ} (apex : C) (l : apex ⟶ X.of) (r : apex ⟶ Y.of)
    (wl : Wₗ l) (wr : Wᵣ r) :
    X ⟶ Y where
  apex := apex
  l := l
  r := r
  wl := wl
  wr := wr

/-- Constructor for 2-morphisms in `Spans C _ _` -/
@[simps]
def mkHom₂ {X Y : Spans C Wₗ Wᵣ} {S S' : X ⟶ Y}
    (e : S.apex ⟶ S'.apex)
    (hₗ : e ≫ S'.l = S.l := by cat_disch)
    (hᵣ : e ≫ S'.r = S.r := by cat_disch) :
    S ⟶ S' where
  hom := e

/-- Constructor for 2-isomorphisms in `Spans C _ _` -/
abbrev mkIso₂ {X Y : Spans C Wₗ Wᵣ} {S S' : X ⟶ Y}
    (e : S.apex ≅ S'.apex)
    (hₗ : e.hom ≫ S'.l = S.l := by cat_disch)
    (hᵣ : e.hom ≫ S'.r = S.r := by cat_disch) :
    S ≅ S' where
  hom.hom := e.hom
  inv.hom := e.inv
  inv.hom_l := by grind
  inv.hom_r := by grind

section compAPI

/-! The goal of this section is to abstract as much as possible the fact that the
composition uses an arbitrary pullback, and provides some "proxy" for working
with the fact that apices of compositions of spans are pullbacks.

This way, if spans ever get refactored in a way that use chosen pullbacks instead
of arbitrary ones, most of downstream applications will not be affected
as long as they are careful to use the API provided here.

The primitives of this API is the data of the two projections
`πₗ : (S₁ ≫ S₂).apex ⟶ S₁.apex` and `πᵣ : (S₁ ≫ S₂).apex ⟶ S₂.apex`, the
equalities `(S₁ ≫ S₂).l = πₗ ≫ S₁.l` and `(S₁ ≫ S₂).r = πᵣ ≫ S₂.r`,
the commutative square `πₗ ≫ S₁.r = πᵣ ≫ S₂.l` and the fact that this defines a pullback square. -/

variable {X Y Z : Spans C Wₗ Wᵣ} (S₁ : X ⟶ Y) (S₂ : Y ⟶ Z)

/-- The left projection `πₗ : (S₁ ≫ S₂).apex ⟶ S₁.apex`. -/
@[no_expose] noncomputable def πₗ :
    (S₁ ≫ S₂).apex ⟶ S₁.apex := Limits.pullback.fst _ _

/-- The right projection `πᵣ : (S₁ ≫ S₂).apex ⟶ S₂.apex`. -/
@[no_expose] noncomputable def πᵣ :
    (S₁ ≫ S₂).apex ⟶ S₂.apex := Limits.pullback.snd _ _

@[simp, reassoc, grind =] lemma comp_l : (S₁ ≫ S₂).l = πₗ S₁ S₂ ≫ S₁.l := (rfl)

@[simp, reassoc, grind =] lemma comp_r : (S₁ ≫ S₂).r = πᵣ S₁ S₂ ≫ S₂.r := (rfl)

@[reassoc (attr := simp), grind _=_] lemma comp_comm : πₗ S₁ S₂ ≫ S₁.r = πᵣ S₁ S₂ ≫ S₂.l :=
  Limits.pullback.condition

/-- The pullback cone that defines the apex for the composition of spans. -/
@[simps! (attr := grind =) pt]
noncomputable def compPullbackCone :
    Limits.PullbackCone S₁.r S₂.l :=
  Limits.PullbackCone.mk (πₗ _ _) (πᵣ _ _) (comp_comm _ _)

@[simp, grind =]
lemma compPullbackCone_fst :
  (compPullbackCone S₁ S₂).fst = πₗ S₁ S₂ := rfl

@[simp, grind =]
lemma compPullbackCone_snd :
  (compPullbackCone S₁ S₂).snd = πᵣ S₁ S₂ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The pullback cone that defines the apex for the composition of spans is a limit
cone. -/
@[no_expose] noncomputable def isLimitCompPullbackCone :
    Limits.IsLimit (compPullbackCone S₁ S₂) :=
  Limits.PullbackCone.IsLimit.mk (comp_comm S₁ S₂)
    (fun x ↦ Limits.pullback.lift x.fst x.snd x.condition)
    (fun x ↦ by simp [πₗ])
    (fun x ↦ by simp [πᵣ])
    (fun f g h k ↦ by apply Limits.pullback.hom_ext <;> cat_disch)

variable {S₁ S₂}

@[ext high, grind ext]
lemma comp_hom_ext_apex {c : C} {f g : c ⟶ (S₁ ≫ S₂).apex}
    (hₗ : f ≫ πₗ S₁ S₂ = g ≫ πₗ S₁ S₂)
    (hᵣ : f ≫ πᵣ S₁ S₂ = g ≫ πᵣ S₁ S₂) :
    f = g := by
  apply Limits.PullbackCone.IsLimit.hom_ext (isLimitCompPullbackCone S₁ S₂) <;> grind

/-- A restatement of the universal property of (S₁ ≫ S₂).apex as coming from a pullback.
This is the main intended way to produce morphisms towards the apex of a composition of spans. -/
@[no_expose]
noncomputable def compLiftApex {c : C} (fₗ : c ⟶ S₁.apex) (fᵣ : c ⟶ S₂.apex)
    (hₘ : fₗ ≫ S₁.r = fᵣ ≫ S₂.l := by cat_disch) :
    c ⟶ (S₁ ≫ S₂).apex :=
  Limits.PullbackCone.IsLimit.lift (isLimitCompPullbackCone S₁ S₂) fₗ fᵣ hₘ

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), grind =]
lemma compLiftApex_πₗ {c : C} (fₗ : c ⟶ S₁.apex) (fᵣ : c ⟶ S₂.apex)
    (hₘ : fₗ ≫ S₁.r = fᵣ ≫ S₂.l := by cat_disch) :
    compLiftApex fₗ fᵣ hₘ ≫ πₗ S₁ S₂ = fₗ := by
  simp [← compPullbackCone_fst, compLiftApex]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), grind =]
lemma compLiftApex_πᵣ {c : C} (fₗ : c ⟶ S₁.apex) (fᵣ : c ⟶ S₂.apex)
    (hₘ : fₗ ≫ S₁.r = fᵣ ≫ S₂.l := by cat_disch) :
    compLiftApex fₗ fᵣ hₘ ≫ πᵣ S₁ S₂ = fᵣ := by
  simp [← compPullbackCone_snd, compLiftApex]

/-- A restatement of the universal property of S₁ ≫ S₂ as coming from a pullback.
This is the main intended way to produce morphisms towards a composition of spans. -/
@[simps (attr := grind =)]
noncomputable def compLift {S : X ⟶ Z} (fₗ : S.apex ⟶ S₁.apex) (fᵣ : S.apex ⟶ S₂.apex)
    (hₗ : fₗ ≫ S₁.l = S.l := by cat_disch)
    (hₘ : fₗ ≫ S₁.r = fᵣ ≫ S₂.l := by cat_disch)
    (hᵣ : fᵣ ≫ S₂.r = S.r := by cat_disch) :
    S ⟶ (S₁ ≫ S₂) where
  hom := compLiftApex fₗ fᵣ

section

variable (S : X ⟶ Z) (fₗ : S.apex ⟶ S₁.apex) (fᵣ : S.apex ⟶ S₂.apex)

lemma compLift_hom_πₗ
    (hₗ : fₗ ≫ S₁.l = S.l := by cat_disch)
    (hₘ : fₗ ≫ S₁.r = fᵣ ≫ S₂.l := by cat_disch)
    (hᵣ : fᵣ ≫ S₂.r = S.r := by cat_disch) :
    (compLift fₗ fᵣ hₗ hₘ hᵣ).hom ≫ πₗ S₁ S₂ = fₗ := by
  simp

lemma compLift_hom_πᵣ
    (hₗ : fₗ ≫ S₁.l = S.l := by cat_disch)
    (hₘ : fₗ ≫ S₁.r = fᵣ ≫ S₂.l := by cat_disch)
    (hᵣ : fᵣ ≫ S₂.r = S.r := by cat_disch) :
    (compLift fₗ fᵣ hₗ hₘ hᵣ).hom ≫ πᵣ S₁ S₂ = fᵣ := by
  simp

end

end compAPI

/-- The associator isomorphisms for the bicategory structure on spans. -/
@[no_expose]
noncomputable def associator
    {c₁ c₂ c₃ c₄ : Spans C Wₗ Wᵣ}
    (S₁ : c₁ ⟶ c₂) (S₂ : c₂ ⟶ c₃) (S₃ : c₃ ⟶ c₄) :
    (S₁ ≫ S₂) ≫ S₃ ≅ S₁ ≫ (S₂ ≫ S₃) where
  hom := compLift (πₗ .. ≫ πₗ ..) (compLiftApex (πₗ .. ≫ πᵣ ..) (πᵣ ..) (by grind))
  inv := compLift (compLiftApex (πₗ ..) (πᵣ .. ≫ πₗ ..)) (πᵣ .. ≫ πᵣ ..)

set_option backward.isDefEq.respectTransparency false in
/-- The right unitor for the bicategory structure on spans. -/
@[no_expose]
noncomputable def rightUnitor {c c' : Spans C Wₗ Wᵣ} (S₁ : c ⟶ c') :
    S₁ ≫ (𝟙 c') ≅ S₁ where
  hom.hom := πₗ _ _
  inv := compLift (𝟙 _) S₁.r

/-- The left unitor for the bicategory structure on spans. -/
@[no_expose]
noncomputable def leftUnitor {c c' : Spans C Wₗ Wᵣ} (S₁ : c ⟶ c') :
    (𝟙 c) ≫ S₁ ≅ S₁ where
  hom.hom := πᵣ _ S₁
  hom.hom_l := by grind
  inv := compLift S₁.l (𝟙 _)
  hom_inv_id := by grind

attribute [local ext] Span.hom_ext in
/- @[simps] lemmas generated by this instance are unfortunately very poor, and we must
register them by hand as we do below. -/
noncomputable instance : Bicategory (Spans C Wₗ Wᵣ) where
  homCategory := inferInstance
  whiskerLeft {_ _ _} S₀ {S₁ S₂} f := compLift (πₗ ..) (πᵣ .. ≫ f.hom)
  whiskerRight {_ _ _} {S₀ S₁} f S₂ := compLift (πₗ .. ≫ f.hom) (πᵣ ..)
  associator S₀ S₁ S₂ := associator _ _ _
  leftUnitor _ := leftUnitor _
  rightUnitor _ := rightUnitor _
  id_whiskerLeft := by grind [leftUnitor]
  whiskerRight_id := by grind [rightUnitor]
  comp_whiskerLeft := by grind (ematch := 10) [associator]
  whiskerRight_comp := by grind (ematch := 10) [associator]
  whisker_assoc := by
    intros
    ext <;> simp [associator]
  pentagon := by
    intros
    ext <;> simp [associator]
  triangle := by
    intros
    ext <;> simp [associator, leftUnitor, rightUnitor]

open CategoryTheory.Bicategory

section

variable {W X Y Z : Spans C Wₗ Wᵣ}

@[reassoc (attr := simp), grind =]
lemma whiskerLeft_hom_πₗ (S : X ⟶ Y) {S₁ S₂ : Y ⟶ Z} (f : S₁ ⟶ S₂) :
    (S ◁ f).hom ≫ πₗ .. = πₗ .. := by simp [whiskerLeft]

@[reassoc (attr := simp), grind =]
lemma whiskerLeft_hom_πᵣ (S : X ⟶ Y) {S₁ S₂ : Y ⟶ Z} (f : S₁ ⟶ S₂) :
    (S ◁ f).hom ≫ πᵣ .. = πᵣ .. ≫ f.hom := by simp [whiskerLeft]

@[reassoc (attr := simp), grind =]
lemma whiskerRight_hom_πₗ {S₁ S₂ : X ⟶ Y} (f : S₁ ⟶ S₂) (S : Y ⟶ Z) :
    (f ▷ S).hom ≫ πₗ .. = (πₗ .. ≫ f.hom) := by simp [whiskerRight]

@[reassoc (attr := simp), grind =]
lemma whiskerRight_hom_πᵣ {S₁ S₂ : X ⟶ Y} (f : S₁ ⟶ S₂) (S : Y ⟶ Z) :
    (f ▷ S).hom ≫ πᵣ .. = πᵣ .. := by simp [whiskerRight]

@[reassoc (attr := simp), grind =]
lemma associator_hom_hom_πₗ (S₁ : W ⟶ X) (S₂ : X ⟶ Y) (S₃ : Y ⟶ Z) :
    (α_ S₁ S₂ S₃).hom.hom ≫ πₗ .. = πₗ .. ≫ πₗ .. := by
  simp [Bicategory.associator, Spans.associator]

@[reassoc (attr := simp), grind =]
lemma associator_hom_hom_πᵣ_πₗ (S₁ : W ⟶ X) (S₂ : X ⟶ Y) (S₃ : Y ⟶ Z) :
    (α_ S₁ S₂ S₃).hom.hom ≫ πᵣ .. ≫ πₗ .. = πₗ .. ≫ πᵣ .. := by
  simp [Bicategory.associator, Spans.associator]

@[reassoc (attr := simp), grind =]
lemma associator_hom_hom_πᵣ_πᵣ (S₁ : W ⟶ X) (S₂ : X ⟶ Y) (S₃ : Y ⟶ Z) :
    (α_ S₁ S₂ S₃).hom.hom ≫ πᵣ .. ≫ πᵣ .. = πᵣ .. := by
  simp [Bicategory.associator, Spans.associator]

@[reassoc (attr := simp), grind =]
lemma associator_inv_hom_πᵣ (S₁ : W ⟶ X) (S₂ : X ⟶ Y) (S₃ : Y ⟶ Z) :
    (α_ S₁ S₂ S₃).inv.hom ≫ πᵣ .. = πᵣ .. ≫ πᵣ .. := by
  simp [Bicategory.associator, Spans.associator]

@[reassoc (attr := simp), grind =]
lemma associator_inv_hom_πₗ_πₗ (S₁ : W ⟶ X) (S₂ : X ⟶ Y) (S₃ : Y ⟶ Z) :
    (α_ S₁ S₂ S₃).inv.hom ≫ πₗ .. ≫ πₗ .. = πₗ .. := by
  simp [Bicategory.associator, Spans.associator]

@[reassoc (attr := simp), grind =]
lemma associator_inv_hom_πₗ_πᵣ (S₁ : W ⟶ X) (S₂ : X ⟶ Y) (S₃ : Y ⟶ Z) :
    (α_ S₁ S₂ S₃).inv.hom ≫ πₗ .. ≫ πᵣ .. = πᵣ .. ≫ πₗ .. := by
  simp [Bicategory.associator, Spans.associator]

@[simp, grind =]
lemma leftUnitor_hom_hom (S : X ⟶ Y) :
    (λ_ S).hom.hom = πᵣ .. := (rfl)

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
lemma leftUnitor_inv_hom_πₗ (S : X ⟶ Y) :
    (λ_ S).inv.hom ≫ πₗ .. = S.l := by simp [Bicategory.leftUnitor, leftUnitor]

@[simp, grind =]
lemma leftUnitor_inv_hom_πᵣ (S : X ⟶ Y) :
    (λ_ S).inv.hom ≫ πᵣ .. = 𝟙 _ := by simp [Bicategory.leftUnitor, leftUnitor]

@[simp, grind =]
lemma rightUnitor_hom_hom (S : X ⟶ Y) :
    (ρ_ S).hom.hom = πₗ .. := (rfl)

@[reassoc (attr := simp), grind =]
lemma rightUnitor_inv_hom_πₗ (S : X ⟶ Y) :
    (ρ_ S).inv.hom ≫ πₗ .. = 𝟙 _ := by simp [Bicategory.rightUnitor, rightUnitor]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), grind =]
lemma rightUnitor_inv_hom_πᵣ (S : X ⟶ Y) :
    (ρ_ S).inv.hom ≫ πᵣ .. = S.r := by simp [Bicategory.rightUnitor, rightUnitor]

@[reassoc (attr := simp), grind =]
lemma hom_inv_id_hom {S S' : X ⟶ Y} (e : S ≅ S') :
    e.hom.hom ≫ e.inv.hom = 𝟙 _ := by simp [← hom₂_comp_hom]

@[reassoc (attr := simp), grind =]
lemma inv_hom_id_hom {S S' : X ⟶ Y} (e : S ≅ S') :
    e.inv.hom ≫ e.hom.hom = 𝟙 _ := by simp [← hom₂_comp_hom]

/-- Extract the isomorphisms between the apices from the data of an isomorphism of 1-morphisms
in `Spans C _ _`. -/
@[simps]
abbrev apexIso {S S' : X ⟶ Y} (e : S ≅ S') :
    S.apex ≅ S'.apex where
  hom := e.hom.hom
  inv := e.inv.hom

@[simp]
lemma apexIso_refl (S : X ⟶ Y) : apexIso (Iso.refl S) = .refl _ := rfl

instance {S S' : X ⟶ Y} (e : S ⟶ S') [IsIso e] : IsIso e.hom :=
  ⟨(inv e).hom, by simp [← hom₂_comp_hom]⟩

@[simp, push ←]
lemma inv_hom {S S' : X ⟶ Y} (e : S ⟶ S') [IsIso e] :
    (inv e).hom = inv e.hom := by
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← hom₂_comp_hom]

lemma eqToHom_hom (S S' : X ⟶ Y) (h : S = S') :
    (eqToHom h).hom = eqToHom (congr($(h).apex)) := by
  subst h
  simp

instance : IsIso (𝟙 X:).r := by dsimp; infer_instance

instance : IsIso (𝟙 X:).l := by dsimp; infer_instance

instance (S : X ⟶ Y) : IsIso (πᵣ (𝟙 _) S) := by
  have := IsPullback.isIso_snd_of_isIso
    (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone (𝟙 _) S)
  exact this

instance (S : X ⟶ Y) : IsIso (πₗ S (𝟙 _)) :=
  by
  have := IsPullback.isIso_fst_of_isIso
    (IsPullback.of_isLimit <| Spans.isLimitCompPullbackCone S (𝟙 _))
  exact this

end

end Span

end CategoryTheory
