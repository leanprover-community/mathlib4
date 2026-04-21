/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel, Bhavik Mehta, Andrew Yang, Emily Riehl, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-!
# HasPullback
`HasPullback f g` and `pullback f g` provides API for `HasLimit` and `limit` in the case of
pullbacks.

## Main definitions

* `HasPullback f g`: this is an abbreviation for `HasLimit (cospan f g)`, and is a typeclass used to
  express the fact that a given pair of morphisms has a pullback.

* `HasPullbacks`: expresses the fact that `C` admits all pullbacks, it is implemented as an
  abbreviation for `HasLimitsOfShape WalkingCospan C`

* `pullback f g`: Given a `HasPullback f g` instance, this function returns the choice of a limit
  object corresponding to the pullback of `f` and `g`. It fits into the following diagram:
  ```
    pullback f g ---pullback.fst f g---> X
        |                                |
        |                                |
  pullback.snd f g                       f
        |                                |
        v                                v
        Y --------------g--------------> Z
  ```

* `HasPushout f g`: this is an abbreviation for `HasColimit (span f g)`, and is a typeclass used to
  express the fact that a given pair of morphisms has a pushout.
* `HasPushouts`: expresses the fact that `C` admits all pushouts, it is implemented as an
  abbreviation for `HasColimitsOfShape WalkingSpan C`
* `pushout f g`: Given a `HasPushout f g` instance, this function returns the choice of a colimit
  object corresponding to the pushout of `f` and `g`. It fits into the following diagram:
  ```
      X --------------f--------------> Y
      |                                |
      g                          pushout.inl f g
      |                                |
      v                                v
      Z ---pushout.inr f g---> pushout f g
  ```

## Main results & API
* The following API is available for using the universal property of `pullback f g`:
  `lift`, `lift_fst`, `lift_snd`, `lift'`, `hom_ext` (for uniqueness).

* `pullback.map` is the induced map between pullbacks `W ×ₛ X ⟶ Y ×ₜ Z` given pointwise
  (compatible) maps `W ⟶ Y`, `X ⟶ Z` and `S ⟶ T`.

* `pullbackComparison`: Given a functor `G`, this is the natural morphism
  `G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g)`

* `pullbackSymmetry` provides the natural isomorphism `pullback f g ≅ pullback g f`

(The dual results for pushouts are also available)

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

/-- Two morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` have a pullback if the diagram `cospan f g` has a
limit. -/
abbrev HasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasLimit (cospan f g)

/-- Two morphisms `f : X ⟶ Y` and `g : X ⟶ Z` have a pushout if the diagram `span f g` has a
colimit. -/
abbrev HasPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :=
  HasColimit (span f g)

/-- `pullback f g` computes the pullback of a pair of morphisms with the same target. -/
abbrev pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :=
  limit (cospan f g)

/-- The cone associated to the pullback of `f` and `g` -/
abbrev pullback.cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : PullbackCone f g :=
  limit.cone (cospan f g)

/-- `pushout f g` computes the pushout of a pair of morphisms with the same source. -/
abbrev pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :=
  colimit (span f g)

/-- The cocone associated to the pushout of `f` and `g` -/
abbrev pushout.cocone {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : PushoutCocone f g :=
  colimit.cocone (span f g)

/-- The first projection of the pullback of `f` and `g`. -/
abbrev pullback.fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : pullback f g ⟶ X :=
  limit.π (cospan f g) WalkingCospan.left

/-- The second projection of the pullback of `f` and `g`. -/
abbrev pullback.snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : pullback f g ⟶ Y :=
  limit.π (cospan f g) WalkingCospan.right

/-- The first inclusion into the pushout of `f` and `g`. -/
abbrev pushout.inl {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : Y ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.left

/-- The second inclusion into the pushout of `f` and `g`. -/
abbrev pushout.inr {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : Z ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.right

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
`pullback.lift : W ⟶ pullback f g`. -/
abbrev pullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) : W ⟶ pullback f g :=
  limit.lift _ (PullbackCone.mk h k w)

set_option backward.isDefEq.respectTransparency false in
lemma pullback.exists_lift {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) :
    ∃ (l : W ⟶ pullback f g), l ≫ pullback.fst f g = h ∧ l ≫ pullback.snd f g = k :=
  ⟨pullback.lift h k, by simp⟩

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
`pushout.desc : pushout f g ⟶ W`. -/
abbrev pushout.desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k := by cat_disch) : pushout f g ⟶ W :=
  colimit.desc _ (PushoutCocone.mk h k w)

set_option backward.isDefEq.respectTransparency false in
lemma pushout.exists_desc {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k := by cat_disch) :
    ∃ (l : pushout f g ⟶ W), pushout.inl f g ≫ l = h ∧ pushout.inr f g ≫ l = k :=
  ⟨pushout.desc h k, by simp⟩

/-- The cone associated to a pullback is a limit cone. -/
abbrev pullback.isLimit {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsLimit (pullback.cone f g) :=
  limit.isLimit (cospan f g)

/-- The cocone associated to a pushout is a colimit cone. -/
abbrev pushout.isColimit {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    IsColimit (pushout.cocone f g) :=
  colimit.isColimit (span f g)

@[simp]
theorem PullbackCone.fst_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (cospan f g)] :
    PullbackCone.fst (limit.cone (cospan f g)) = pullback.fst f g := rfl

@[simp]
theorem PullbackCone.snd_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (cospan f g)] :
    PullbackCone.snd (limit.cone (cospan f g)) = pullback.snd f g := rfl

theorem PushoutCocone.inl_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    [HasColimit (span f g)] : PushoutCocone.inl (colimit.cocone (span f g)) = pushout.inl _ _ := rfl

theorem PushoutCocone.inr_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    [HasColimit (span f g)] : PushoutCocone.inr (colimit.cocone (span f g)) = pushout.inr _ _ := rfl

@[reassoc]
theorem pullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.fst f g = h :=
  limit.lift_π _ _

@[reassoc]
theorem pullback.lift_snd {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.snd f g = k :=
  limit.lift_π _ _

@[reassoc]
theorem pushout.inl_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
    (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inl _ _ ≫ pushout.desc h k w = h :=
  colimit.ι_desc _ _

@[reassoc]
theorem pushout.inr_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
    (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inr _ _ ≫ pushout.desc h k w = k :=
  colimit.ι_desc _ _

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
`l : W ⟶ pullback f g` such that `l ≫ pullback.fst = h` and `l ≫ pullback.snd = k`. -/
def pullback.lift' {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) :
      { l : W ⟶ pullback f g // l ≫ pullback.fst f g = h ∧ l ≫ pullback.snd f g = k } :=
  ⟨pullback.lift h k w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
`l : pushout f g ⟶ W` such that `pushout.inl _ _ ≫ l = h` and `pushout.inr _ _ ≫ l = k`. -/
def pullback.desc' {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) :
      { l : pushout f g ⟶ W // pushout.inl _ _ ≫ l = h ∧ pushout.inr _ _ ≫ l = k } :=
  ⟨pushout.desc h k w, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩

@[reassoc]
theorem pullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] :
    pullback.fst f g ≫ f = pullback.snd f g ≫ g :=
  PullbackCone.condition _

@[reassoc]
theorem pushout.condition {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] :
    f ≫ (pushout.inl f g) = g ≫ pushout.inr _ _ :=
  PushoutCocone.condition _

/-- Two morphisms into a pullback are equal if their compositions with the pullback morphisms are
equal -/
@[ext 1100]
theorem pullback.hom_ext {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] {W : C}
    {k l : W ⟶ pullback f g} (h₀ : k ≫ pullback.fst f g = l ≫ pullback.fst f g)
    (h₁ : k ≫ pullback.snd f g = l ≫ pullback.snd f g) : k = l :=
  limit.hom_ext <| PullbackCone.equalizer_ext _ h₀ h₁

/-- The pullback cone built from the pullback projections is a pullback. -/
def pullbackIsPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsLimit (PullbackCone.mk (pullback.fst f g) (pullback.snd f g) pullback.condition) :=
  PullbackCone.mkSelfIsLimit <| pullback.isLimit f g

/-- Two morphisms out of a pushout are equal if their compositions with the pushout morphisms are
equal -/
@[ext 1100]
theorem pushout.hom_ext {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] {W : C}
    {k l : pushout f g ⟶ W} (h₀ : pushout.inl _ _ ≫ k = pushout.inl _ _ ≫ l)
    (h₁ : pushout.inr _ _ ≫ k = pushout.inr _ _ ≫ l) : k = l :=
  colimit.hom_ext <| PushoutCocone.coequalizer_ext _ h₀ h₁

set_option backward.isDefEq.respectTransparency false in
/-- The pushout cocone built from the pushout coprojections is a pushout. -/
def pushoutIsPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    IsColimit (PushoutCocone.mk (pushout.inl f g) (pushout.inr _ _) pushout.condition) :=
  PushoutCocone.IsColimit.mk _ (fun s => pushout.desc s.inl s.inr s.condition) (by simp) (by simp)
    (by cat_disch)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma pullback.lift_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    lift (fst f g) (snd f g) condition = 𝟙 (pullback f g) := by
  apply hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma pushout.desc_inl_inr {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    desc (inl f g) (inr f g) condition = 𝟙 (pushout f g) := by
  apply hom_ext <;> simp

/-- Given such a diagram, then there is a natural morphism `W ×ₛ X ⟶ Y ×ₜ Z`.

```
W ⟶ Y
  ↘   ↘
  S ⟶ T
  ↗   ↗
X ⟶ Z
```
-/
abbrev pullback.map {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : pullback f₁ f₂ ⟶ pullback g₁ g₂ :=
  pullback.lift (pullback.fst f₁ f₂ ≫ i₁) (pullback.snd f₁ f₂ ≫ i₂)
    (by simp only [Category.assoc, ← eq₁, ← eq₂, pullback.condition_assoc])

/-- The canonical map `X ×ₛ Y ⟶ X ×ₜ Y` given `S ⟶ T`. -/
abbrev pullback.mapDesc {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [HasPullback f g]
    [HasPullback (f ≫ i) (g ≫ i)] : pullback f g ⟶ pullback (f ≫ i) (g ≫ i) :=
  pullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (Category.id_comp _).symm (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pullback.map_comp {X Y Z X' Y' Z' X'' Y'' Z'' : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} {f'' : X'' ⟶ Z''} {g'' : Y'' ⟶ Z''}
    (i₁ : X ⟶ X') (j₁ : X' ⟶ X'') (i₂ : Y ⟶ Y') (j₂ : Y' ⟶ Y'') (i₃ : Z ⟶ Z') (j₃ : Z' ⟶ Z'')
    [HasPullback f g] [HasPullback f' g'] [HasPullback f'' g'']
    (e₁ e₂ e₃ e₄) :
    pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ ≫ pullback.map f' g' f'' g'' j₁ j₂ j₃ e₃ e₄ =
      pullback.map f g f'' g'' (i₁ ≫ j₁) (i₂ ≫ j₂) (i₃ ≫ j₃)
        (by rw [reassoc_of% e₁, e₃, Category.assoc])
        (by rw [reassoc_of% e₂, e₄, Category.assoc]) := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma pullback.map_id {X Y Z : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] :
    pullback.map f g f g (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by ext <;> simp

/-- Given such a diagram, then there is a natural morphism `W ⨿ₛ X ⟶ Y ⨿ₜ Z`.

```
  W ⟶ Y
 ↗   ↗
S ⟶ T
 ↘   ↘
  X ⟶ Z
```
-/
abbrev pushout.map {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂] (g₁ : T ⟶ Y)
    (g₂ : T ⟶ Z) [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁)
    (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) : pushout f₁ f₂ ⟶ pushout g₁ g₂ :=
  pushout.desc (i₁ ≫ pushout.inl _ _) (i₂ ≫ pushout.inr _ _)
    (by simp only [reassoc_of% eq₁, reassoc_of% eq₂, condition])

/-- The canonical map `X ⨿ₛ Y ⟶ X ⨿ₜ Y` given `S ⟶ T`. -/
abbrev pushout.mapLift {X Y S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) [HasPushout f g]
    [HasPushout (i ≫ f) (i ≫ g)] : pushout (i ≫ f) (i ≫ g) ⟶ pushout f g :=
  pushout.map (i ≫ f) (i ≫ g) f g (𝟙 _) (𝟙 _) i (Category.comp_id _) (Category.comp_id _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pushout.map_comp {X Y Z X' Y' Z' X'' Y'' Z'' : C}
    {f : X ⟶ Y} {g : X ⟶ Z} {f' : X' ⟶ Y'} {g' : X' ⟶ Z'} {f'' : X'' ⟶ Y''} {g'' : X'' ⟶ Z''}
    (i₁ : X ⟶ X') (j₁ : X' ⟶ X'') (i₂ : Y ⟶ Y') (j₂ : Y' ⟶ Y'') (i₃ : Z ⟶ Z') (j₃ : Z' ⟶ Z'')
    [HasPushout f g] [HasPushout f' g'] [HasPushout f'' g'']
    (e₁ e₂ e₃ e₄) :
    pushout.map f g f' g' i₂ i₃ i₁ e₁ e₂ ≫ pushout.map f' g' f'' g'' j₂ j₃ j₁ e₃ e₄ =
      pushout.map f g f'' g'' (i₂ ≫ j₂) (i₃ ≫ j₃) (i₁ ≫ j₁)
        (by rw [reassoc_of% e₁, e₃, Category.assoc])
        (by rw [reassoc_of% e₂, e₄, Category.assoc]) := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma pushout.map_id {X Y Z : C}
    {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] :
    pushout.map f g f g (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
instance pullback.map_isIso {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) [IsIso i₁] [IsIso i₂] [IsIso i₃] :
    IsIso (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine ⟨⟨pullback.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) ?_ ?_, ?_, ?_⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
  · cat_disch
  · cat_disch

/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pullback f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps! hom]
def pullback.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPullback f₁ g₁] [HasPullback f₂ g₂] : pullback f₁ g₁ ≅ pullback f₂ g₂ :=
  asIso <| pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem pullback.congrHom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂)
    (h₂ : g₁ = g₂) [HasPullback f₁ g₁] [HasPullback f₂ g₂] :
    (pullback.congrHom h₁ h₂).inv =
      pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) := by
  ext <;> simp [Iso.inv_comp_eq]

set_option backward.isDefEq.respectTransparency false in
instance pushout.map_isIso {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂]
    (g₁ : T ⟶ Y) (g₂ : T ⟶ Z) [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁) (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) [IsIso i₁] [IsIso i₂] [IsIso i₃] :
    IsIso (pushout.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine ⟨⟨pushout.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) ?_ ?_, ?_, ?_⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
  · cat_disch
  · cat_disch

set_option backward.isDefEq.respectTransparency false in
theorem pullback.mapDesc_comp {X Y S T S' : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S) (i' : S ⟶ S')
    [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)] [HasPullback (f ≫ i ≫ i') (g ≫ i ≫ i')]
    [HasPullback ((f ≫ i) ≫ i') ((g ≫ i) ≫ i')] :
    pullback.mapDesc f g (i ≫ i') = pullback.mapDesc f g i ≫ pullback.mapDesc _ _ i' ≫
    (pullback.congrHom (Category.assoc _ _ _) (Category.assoc _ _ _)).hom := by
  cat_disch

/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pushout f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps! hom]
def pushout.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPushout f₁ g₁] [HasPushout f₂ g₂] : pushout f₁ g₁ ≅ pushout f₂ g₂ :=
  asIso <| pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem pushout.congrHom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂)
    (h₂ : g₁ = g₂) [HasPushout f₁ g₁] [HasPushout f₂ g₂] :
    (pushout.congrHom h₁ h₂).inv =
      pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) := by
  ext <;> simp [Iso.comp_inv_eq]

set_option backward.isDefEq.respectTransparency false in
theorem pushout.mapLift_comp {X Y S T S' : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) (i' : S' ⟶ S)
    [HasPushout f g] [HasPushout (i ≫ f) (i ≫ g)] [HasPushout (i' ≫ i ≫ f) (i' ≫ i ≫ g)]
    [HasPushout ((i' ≫ i) ≫ f) ((i' ≫ i) ≫ g)] :
    pushout.mapLift f g (i' ≫ i) =
      (pushout.congrHom (Category.assoc _ _ _) (Category.assoc _ _ _)).hom ≫
        pushout.mapLift _ _ i' ≫ pushout.mapLift f g i := by
  cat_disch

section

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

/-- The comparison morphism for the pullback of `f,g`.
This is an isomorphism iff `G` preserves the pullback of `f,g`; see
`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Pullbacks.lean`
-/
def pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g)] :
    G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g) :=
  pullback.lift (G.map (pullback.fst f g)) (G.map (pullback.snd f g))
    (by simp only [← G.map_comp, pullback.condition])

@[reassoc (attr := simp)]
theorem pullbackComparison_comp_fst (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.fst _ _ = G.map (pullback.fst f g) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackComparison_comp_snd (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.snd _ _ = G.map (pullback.snd f g) :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem map_lift_pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] {W : C} {h : W ⟶ X} {k : W ⟶ Y} (w : h ≫ f = k ≫ g) :
    G.map (pullback.lift _ _ w) ≫ pullbackComparison G f g =
      pullback.lift (G.map h) (G.map k) (by simp only [← G.map_comp, w]) := by
  ext <;> simp [← G.map_comp]

@[reassoc]
lemma pullbackComparison_comp {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E) {X Y S : C}
    (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [HasPullback (F.map f) (F.map g)]
    [HasPullback (G.map (F.map f)) (G.map (F.map g))]
    [HasPullback ((F ⋙ G).map f) ((F ⋙ G).map g)] :
    pullbackComparison (F ⋙ G) f g = G.map (pullbackComparison F f g) ≫
      pullbackComparison G (F.map f) (F.map g) := by
  ext
  · rw [pullbackComparison_comp_fst]
    simp [← Functor.map_comp]
  · rw [pullbackComparison_comp_snd]
    simp [← Functor.map_comp]

/-- The comparison morphism for the pushout of `f,g`.
This is an isomorphism iff `G` preserves the pushout of `f,g`; see
`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Pullbacks.lean`
-/
def pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.map f) (G.map g)] :
    pushout (G.map f) (G.map g) ⟶ G.obj (pushout f g) :=
  pushout.desc (G.map (pushout.inl _ _)) (G.map (pushout.inr _ _))
    (by simp only [← G.map_comp, pushout.condition])

@[reassoc (attr := simp)]
theorem inl_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] : pushout.inl _ _ ≫ pushoutComparison G f g =
      G.map (pushout.inl _ _) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem inr_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] : pushout.inr _ _ ≫ pushoutComparison G f g =
      G.map (pushout.inr _ _) :=
  pushout.inr_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pushoutComparison_map_desc (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] {W : C} {h : Y ⟶ W} {k : Z ⟶ W} (w : f ≫ h = g ≫ k) :
    pushoutComparison G f g ≫ G.map (pushout.desc _ _ w) =
      pushout.desc (G.map h) (G.map k) (by simp only [← G.map_comp, w]) := by
  ext <;> simp [← G.map_comp]

end

section PullbackSymmetry

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z)

/-- Making this a global instance would make the typeclass search go in an infinite loop. -/
theorem hasPullback_symmetry [HasPullback f g] : HasPullback g f :=
  ⟨⟨⟨_, PullbackCone.flipIsLimit (pullbackIsPullback f g)⟩⟩⟩

attribute [local instance] hasPullback_symmetry

/-- The isomorphism `X ×[Z] Y ≅ Y ×[Z] X`. -/
def pullbackSymmetry [HasPullback f g] : pullback f g ≅ pullback g f :=
  IsLimit.conePointUniqueUpToIso
    (PullbackCone.flipIsLimit (pullbackIsPullback f g)) (limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pullbackSymmetry_hom_comp_fst [HasPullback f g] :
    (pullbackSymmetry f g).hom ≫ pullback.fst g f = pullback.snd f g := by simp [pullbackSymmetry]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pullbackSymmetry_hom_comp_snd [HasPullback f g] :
    (pullbackSymmetry f g).hom ≫ pullback.snd g f = pullback.fst f g := by simp [pullbackSymmetry]

@[reassoc (attr := simp)]
theorem pullbackSymmetry_inv_comp_fst [HasPullback f g] :
    (pullbackSymmetry f g).inv ≫ pullback.fst f g = pullback.snd g f := by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp)]
theorem pullbackSymmetry_inv_comp_snd [HasPullback f g] :
    (pullbackSymmetry f g).inv ≫ pullback.snd f g = pullback.fst g f := by simp [Iso.inv_comp_eq]

end PullbackSymmetry

section PushoutSymmetry

open WalkingCospan

variable (f : X ⟶ Y) (g : X ⟶ Z)

/-- Making this a global instance would make the typeclass search go in an infinite loop. -/
theorem hasPushout_symmetry [HasPushout f g] : HasPushout g f :=
  ⟨⟨⟨_, PushoutCocone.flipIsColimit (pushoutIsPushout f g)⟩⟩⟩

attribute [local instance] hasPushout_symmetry

/-- The isomorphism `Y ⨿[X] Z ≅ Z ⨿[X] Y`. -/
def pushoutSymmetry [HasPushout f g] : pushout f g ≅ pushout g f :=
  IsColimit.coconePointUniqueUpToIso
    (PushoutCocone.flipIsColimit (pushoutIsPushout f g)) (colimit.isColimit _)

@[reassoc (attr := simp)]
theorem inl_comp_pushoutSymmetry_hom [HasPushout f g] :
    pushout.inl _ _ ≫ (pushoutSymmetry f g).hom = pushout.inr _ _ :=
  (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _

@[reassoc (attr := simp)]
theorem inr_comp_pushoutSymmetry_hom [HasPushout f g] :
    pushout.inr _ _ ≫ (pushoutSymmetry f g).hom = pushout.inl _ _ :=
  (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _

@[reassoc (attr := simp)]
theorem inl_comp_pushoutSymmetry_inv [HasPushout f g] :
    pushout.inl _ _ ≫ (pushoutSymmetry f g).inv = pushout.inr _ _ := by simp [Iso.comp_inv_eq]

@[reassoc (attr := simp)]
theorem inr_comp_pushoutSymmetry_inv [HasPushout f g] :
    pushout.inr _ _ ≫ (pushoutSymmetry f g).inv = pushout.inl _ _ := by simp [Iso.comp_inv_eq]

end PushoutSymmetry

/-- `HasPullbacksAlong f` states that pullbacks of all morphisms into `Y`
along `f : X ⟶ Y` exist. -/
abbrev HasPullbacksAlong (f : X ⟶ Y) : Prop := ∀ {W} (h : W ⟶ Y), HasPullback h f

/-- `HasPushoutsAlong f` states that pushouts of all morphisms out of `X`
along `f : X ⟶ Y` exist. -/
abbrev HasPushoutsAlong (f : X ⟶ Y) : Prop := ∀ {W} (h : X ⟶ W), HasPushout h f

variable (C)

/-- A category `HasPullbacks` if it has all limits of shape `WalkingCospan`, i.e. if it has a
pullback for every pair of morphisms with the same codomain. -/
@[stacks 001W]
abbrev HasPullbacks :=
  HasLimitsOfShape WalkingCospan C

/-- A category `HasPushouts` if it has all colimits of shape `WalkingSpan`, i.e. if it has a
pushout for every pair of morphisms with the same domain. -/
abbrev HasPushouts :=
  HasColimitsOfShape WalkingSpan C

/-- If `C` has all limits of diagrams `cospan f g`, then it has all pullbacks -/
theorem hasPullbacks_of_hasLimit_cospan
    [∀ {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g)] : HasPullbacks C :=
  { has_limit := fun F => hasLimit_of_iso (diagramIsoCospan F).symm }

/-- If `C` has all colimits of diagrams `span f g`, then it has all pushouts -/
theorem hasPushouts_of_hasColimit_span
    [∀ {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}, HasColimit (span f g)] : HasPushouts C :=
  { has_colimit := fun F => hasColimit_of_iso (diagramIsoSpan F) }

/-- The duality equivalence `WalkingSpanᵒᵖ ≌ WalkingCospan` -/
@[simps!]
def walkingSpanOpEquiv : WalkingSpanᵒᵖ ≌ WalkingCospan :=
  widePushoutShapeOpEquiv _

/-- The duality equivalence `WalkingCospanᵒᵖ ≌ WalkingSpan` -/
@[simps!]
def walkingCospanOpEquiv : WalkingCospanᵒᵖ ≌ WalkingSpan :=
  widePullbackShapeOpEquiv _

-- see Note [lower instance priority]
/-- Having wide pullback at any universe level implies having binary pullbacks. -/
instance (priority := 100) hasPullbacks_of_hasWidePullbacks (D : Type u) [Category.{v} D]
    [HasWidePullbacks.{w} D] : HasPullbacks.{v, u} D :=
  hasWidePullbacks_shrink WalkingPair

-- see Note [lower instance priority]
/-- Having wide pushout at any universe level implies having binary pushouts. -/
instance (priority := 100) hasPushouts_of_hasWidePushouts (D : Type u) [Category.{v} D]
    [HasWidePushouts.{w} D] : HasPushouts.{v, u} D :=
  hasWidePushouts_shrink WalkingPair

theorem hasPullback_symmetry_of_hasPullbacksAlong {S X Y : C} {f : X ⟶ S} [HasPullbacksAlong f]
    {g : Y ⟶ S} : HasPullback f g :=
  hasPullback_symmetry g f

theorem hasPushouts_symmetry_of_hasPushoutsAlong {S X Y : C} {f : S ⟶ X} [HasPushoutsAlong f]
    {g : S ⟶ Y} : HasPushout f g :=
  hasPushout_symmetry g f

section Products

variable {C}

set_option backward.isDefEq.respectTransparency false in
/-- `X ×[Y] (Y ⨯ Z) ≅ X ⨯ Z` -/
noncomputable def pullbackProdFstIsoProd {X Y : C} (f : X ⟶ Y) (Z : C)
    [HasBinaryProduct Y Z] [HasBinaryProduct X Z] [HasPullback f (prod.fst : Y ⨯ Z ⟶ _)] :
    pullback f (prod.fst : Y ⨯ Z ⟶ _) ≅ X ⨯ Z where
  hom := prod.lift (pullback.fst _ _) (pullback.snd _ _ ≫ prod.snd)
  inv := pullback.lift prod.fst (prod.map f (𝟙 Z))
  hom_inv_id := by
    apply pullback.hom_ext
    · simp
    · apply prod.hom_ext <;> simp [pullback.condition]

section

variable {X Y : C} (f : X ⟶ Y) (Z : C) [HasBinaryProduct Y Z] [HasBinaryProduct X Z]
  [HasPullback f (prod.fst : Y ⨯ Z ⟶ _)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pullbackProdFstIsoProd_hom_fst :
    (pullbackProdFstIsoProd f Z).hom ≫ prod.fst = pullback.fst _ _ := by
  simp [pullbackProdFstIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pullbackProdFstIsoProd_hom_snd :
    (pullbackProdFstIsoProd f Z).hom ≫ prod.snd = pullback.snd _ _ ≫ prod.snd := by
  simp [pullbackProdFstIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pullbackProdFstIsoProd_inv_fst :
    (pullbackProdFstIsoProd f Z).inv ≫ pullback.fst _ _ = prod.fst := by
  simp [pullbackProdFstIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pullbackProdFstIsoProd_inv_snd_fst :
    (pullbackProdFstIsoProd f Z).inv ≫ pullback.snd _ _ ≫ prod.fst = prod.fst ≫ f := by
  simp [pullbackProdFstIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pullbackProdFstIsoProd_inv_snd_snd :
    (pullbackProdFstIsoProd f Z).inv ≫ pullback.snd _ _ ≫ prod.snd = prod.snd := by
  simp [pullbackProdFstIsoProd]

end

section

set_option backward.isDefEq.respectTransparency false in
/-- `(Z ⨯ Y) ×[Y] X ≅ Z ⨯ X` -/
noncomputable def pullbackProdSndIsoProd {X Y : C} (f : X ⟶ Y) (Z : C)
    [HasBinaryProduct Z Y] [HasBinaryProduct Z X] [HasPullback (prod.snd : Z ⨯ Y ⟶ Y) f] :
    pullback (prod.snd : Z ⨯ Y ⟶ Y) f ≅ Z ⨯ X where
  hom := prod.lift (pullback.fst _ _ ≫ prod.fst) (pullback.snd _ _)
  inv := pullback.lift (prod.map (𝟙 Z) f) prod.snd
  hom_inv_id := by
    apply pullback.hom_ext
    · apply prod.hom_ext <;> simp [pullback.condition]
    · simp

variable {X Y : C} (f : X ⟶ Y) (Z : C) [HasBinaryProduct Z Y] [HasBinaryProduct Z X]
  [HasPullback (prod.snd : Z ⨯ Y ⟶ Y) f]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pullbackProdSndIsoProd_hom_fst :
    (pullbackProdSndIsoProd f Z).hom ≫ prod.fst = pullback.fst _ _ ≫ prod.fst := by
  simp [pullbackProdSndIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pullbackProdSndIsoProd_hom_snd :
    (pullbackProdSndIsoProd f Z).hom ≫ prod.snd = pullback.snd _ _ := by
  simp [pullbackProdSndIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pullbackProdSndIsoProd_inv_fst_fst :
    (pullbackProdSndIsoProd f Z).inv ≫ pullback.fst _ _ ≫ prod.fst = prod.fst := by
  simp [pullbackProdSndIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pullbackProdSndIsoProd_inv_fst_snd :
    (pullbackProdSndIsoProd f Z).inv ≫ pullback.fst _ _ ≫ prod.snd = prod.snd ≫ f := by
  simp [pullbackProdSndIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pullbackProdSndIsoProd_inv_snd :
    (pullbackProdSndIsoProd f Z).inv ≫ pullback.snd _ _ = prod.snd := by
  simp [pullbackProdSndIsoProd]

end

end Products

end CategoryTheory.Limits
