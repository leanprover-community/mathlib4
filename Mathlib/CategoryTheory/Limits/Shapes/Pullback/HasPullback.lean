/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel, Bhavik Mehta, Andrew Yang, Emily Riehl, Calle Sönne
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

#align_import category_theory.limits.shapes.pullbacks from "leanprover-community/mathlib"@"7316286ff2942aa14e540add9058c6b0aa1c8070"

/-!
# HasPullback
`HasPullback f g` and `pullback f g` provides API for `HasLimit` and `limit` in the case of
pullacks.

# Main definitions

* `HasPullback f g`: this is an abbreviation for `HasLimit (cospan f g)`, and is a typeclass used to
  express the fact that a given pair of morphisms has a pullback.

* `HasPullbacks`: expresses the fact that `C` admits all pullbacks, it is implemented as an
  abbrevation for `HasLimitsOfShape WalkingCospan C`

* `pullback f g`: Given a `HasPullback f g` instance, this function returns the choice of a limit
  object corresponding to the pullback of `f` and `g`. It fits into the following diagram:
```
  pullback f g ---pullback.snd f g---> Y
      |                                |
      |                                |
pullback.snd f g                       g
      |                                |
      v                                v
      X --------------f--------------> Z
```

* `HasPushout f g`: this is an abbreviation for `HasColimit (span f g)`, and is a typeclass used to
  express the fact that a given pair of morphisms has a pushout.
* `HasPushouts`: expresses the fact that `C` admits all pushouts, it is implemented as an
abbrevation for `HasColimitsOfShape WalkingSpan C`
* `pushout f g`: Given a `HasPushout f g` instance, this function returns the choice of a colimit
  object corresponding to the pushout of `f` and `g`. It fits into the following diagram:
```
      X --------------f--------------> Y
      |                                |
      g                          pushout.inr f g
      |                                |
      v                                v
      Z ---pushout.inl f g---> pushout f g
```

# Main results & API
* The following API is available for using the universal property of `pullback f g`:
`lift`, `lift_fst`, `lift_snd`, `lift'`, `hom_ext` (for uniqueness).

* `pullback.map` is the induced map between pullbacks `W ×ₛ X ⟶ Y ×ₜ Z` given pointwise
(compatible) maps `W ⟶ Y`, `X ⟶ Z` and `S ⟶ T`.

* `pullbackComparison`: Given a functor `G`, this is the natural morphism
`G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g)`

* `pullbackSymmetry` provides the natural isomorphism `pullback f g ≅ pullback g f`

(The dual results for pushouts are also available)

NOTE: golfed some proofs also

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

/-- `HasPullback f g` represents a particular choice of limiting cone
for the pair of morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`.
-/
abbrev HasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasLimit (cospan f g)
#align category_theory.limits.has_pullback CategoryTheory.Limits.HasPullback

/-- `HasPushout f g` represents a particular choice of colimiting cocone
for the pair of morphisms `f : X ⟶ Y` and `g : X ⟶ Z`.
-/
abbrev HasPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :=
  HasColimit (span f g)
#align category_theory.limits.has_pushout CategoryTheory.Limits.HasPushout

/-- `pullback f g` computes the pullback of a pair of morphisms with the same target. -/
abbrev pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :=
  limit (cospan f g)
#align category_theory.limits.pullback CategoryTheory.Limits.pullback

/-- `pushout f g` computes the pushout of a pair of morphisms with the same source. -/
abbrev pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :=
  colimit (span f g)
#align category_theory.limits.pushout CategoryTheory.Limits.pushout

/-- The first projection of the pullback of `f` and `g`. -/
abbrev pullback.fst {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] : pullback f g ⟶ X :=
  limit.π (cospan f g) WalkingCospan.left
#align category_theory.limits.pullback.fst CategoryTheory.Limits.pullback.fst

/-- The second projection of the pullback of `f` and `g`. -/
abbrev pullback.snd {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] : pullback f g ⟶ Y :=
  limit.π (cospan f g) WalkingCospan.right
#align category_theory.limits.pullback.snd CategoryTheory.Limits.pullback.snd

/-- The first inclusion into the pushout of `f` and `g`. -/
abbrev pushout.inl {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] : Y ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.left
#align category_theory.limits.pushout.inl CategoryTheory.Limits.pushout.inl

/-- The second inclusion into the pushout of `f` and `g`. -/
abbrev pushout.inr {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] : Z ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.right
#align category_theory.limits.pushout.inr CategoryTheory.Limits.pushout.inr

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `pullback.lift : W ⟶ pullback f g`. -/
abbrev pullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ pullback f g :=
  limit.lift _ (PullbackCone.mk h k w)
#align category_theory.limits.pullback.lift CategoryTheory.Limits.pullback.lift

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
    `pushout.desc : pushout f g ⟶ W`. -/
abbrev pushout.desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : pushout f g ⟶ W :=
  colimit.desc _ (PushoutCocone.mk h k w)
#align category_theory.limits.pushout.desc CategoryTheory.Limits.pushout.desc

@[simp]
theorem PullbackCone.fst_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (cospan f g)] :
    PullbackCone.fst (limit.cone (cospan f g)) = pullback.fst := rfl
#align category_theory.limits.pullback_cone.fst_colimit_cocone CategoryTheory.Limits.PullbackCone.fst_limit_cone

@[simp]
theorem PullbackCone.snd_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (cospan f g)] :
    PullbackCone.snd (limit.cone (cospan f g)) = pullback.snd := rfl
#align category_theory.limits.pullback_cone.snd_colimit_cocone CategoryTheory.Limits.PullbackCone.snd_limit_cone

-- Porting note (#10618): simp can prove this; removed simp
theorem PushoutCocone.inl_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    [HasColimit (span f g)] : PushoutCocone.inl (colimit.cocone (span f g)) = pushout.inl := rfl
#align category_theory.limits.pushout_cocone.inl_colimit_cocone CategoryTheory.Limits.PushoutCocone.inl_colimit_cocone

-- Porting note (#10618): simp can prove this; removed simp
theorem PushoutCocone.inr_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    [HasColimit (span f g)] : PushoutCocone.inr (colimit.cocone (span f g)) = pushout.inr := rfl
#align category_theory.limits.pushout_cocone.inr_colimit_cocone CategoryTheory.Limits.PushoutCocone.inr_colimit_cocone

-- Porting note (#10618): simp can prove this and reassoced version; removed simp
@[reassoc]
theorem pullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.fst = h :=
  limit.lift_π _ _
#align category_theory.limits.pullback.lift_fst CategoryTheory.Limits.pullback.lift_fst

-- Porting note (#10618): simp can prove this and reassoced version; removed simp
@[reassoc]
theorem pullback.lift_snd {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.snd = k :=
  limit.lift_π _ _
#align category_theory.limits.pullback.lift_snd CategoryTheory.Limits.pullback.lift_snd

-- Porting note (#10618): simp can prove this and reassoced version; removed simp
@[reassoc]
theorem pushout.inl_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
    (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inl ≫ pushout.desc h k w = h :=
  colimit.ι_desc _ _
#align category_theory.limits.pushout.inl_desc CategoryTheory.Limits.pushout.inl_desc

-- Porting note (#10618): simp can prove this and reassoced version; removed simp
@[reassoc]
theorem pushout.inr_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
    (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inr ≫ pushout.desc h k w = k :=
  colimit.ι_desc _ _
#align category_theory.limits.pushout.inr_desc CategoryTheory.Limits.pushout.inr_desc

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `l : W ⟶ pullback f g` such that `l ≫ pullback.fst = h` and `l ≫ pullback.snd = k`. -/
def pullback.lift' {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : { l : W ⟶ pullback f g // l ≫ pullback.fst = h ∧ l ≫ pullback.snd = k } :=
  ⟨pullback.lift h k w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
#align category_theory.limits.pullback.lift' CategoryTheory.Limits.pullback.lift'

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
    `l : pushout f g ⟶ W` such that `pushout.inl ≫ l = h` and `pushout.inr ≫ l = k`. -/
def pullback.desc' {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : { l : pushout f g ⟶ W // pushout.inl ≫ l = h ∧ pushout.inr ≫ l = k } :=
  ⟨pushout.desc h k w, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩
#align category_theory.limits.pullback.desc' CategoryTheory.Limits.pullback.desc'

@[reassoc]
theorem pullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] :
    (pullback.fst : pullback f g ⟶ X) ≫ f = pullback.snd ≫ g :=
  PullbackCone.condition _
#align category_theory.limits.pullback.condition CategoryTheory.Limits.pullback.condition

@[reassoc]
theorem pushout.condition {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] :
    f ≫ (pushout.inl : Y ⟶ pushout f g) = g ≫ pushout.inr :=
  PushoutCocone.condition _
#align category_theory.limits.pushout.condition CategoryTheory.Limits.pushout.condition

/-- Given such a diagram, then there is a natural morphism `W ×ₛ X ⟶ Y ×ₜ Z`.

    W ⟶ Y
      ↘      ↘
        S ⟶ T
      ↗      ↗
    X ⟶ Z

-/
abbrev pullback.map {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : pullback f₁ f₂ ⟶ pullback g₁ g₂ :=
  pullback.lift (pullback.fst ≫ i₁) (pullback.snd ≫ i₂)
    (by simp [← eq₁, ← eq₂, pullback.condition_assoc])
#align category_theory.limits.pullback.map CategoryTheory.Limits.pullback.map

/-- The canonical map `X ×ₛ Y ⟶ X ×ₜ Y` given `S ⟶ T`. -/
abbrev pullback.mapDesc {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [HasPullback f g]
    [HasPullback (f ≫ i) (g ≫ i)] : pullback f g ⟶ pullback (f ≫ i) (g ≫ i) :=
  pullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (Category.id_comp _).symm (Category.id_comp _).symm
#align category_theory.limits.pullback.map_desc CategoryTheory.Limits.pullback.mapDesc

/-- Given such a diagram, then there is a natural morphism `W ⨿ₛ X ⟶ Y ⨿ₜ Z`.

        W ⟶ Y
      ↗      ↗
    S ⟶ T
      ↘      ↘
        X ⟶ Z

-/
abbrev pushout.map {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂] (g₁ : T ⟶ Y)
    (g₂ : T ⟶ Z) [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁)
    (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) : pushout f₁ f₂ ⟶ pushout g₁ g₂ :=
  pushout.desc (i₁ ≫ pushout.inl) (i₂ ≫ pushout.inr)
    (by
      simp only [← Category.assoc, eq₁, eq₂]
      simp [pushout.condition])
#align category_theory.limits.pushout.map CategoryTheory.Limits.pushout.map

/-- The canonical map `X ⨿ₛ Y ⟶ X ⨿ₜ Y` given `S ⟶ T`. -/
abbrev pushout.mapLift {X Y S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) [HasPushout f g]
    [HasPushout (i ≫ f) (i ≫ g)] : pushout (i ≫ f) (i ≫ g) ⟶ pushout f g :=
  pushout.map (i ≫ f) (i ≫ g) f g (𝟙 _) (𝟙 _) i (Category.comp_id _) (Category.comp_id _)
#align category_theory.limits.pushout.map_lift CategoryTheory.Limits.pushout.mapLift

/-- Two morphisms into a pullback are equal if their compositions with the pullback morphisms are
    equal -/
@[ext 1100]
theorem pullback.hom_ext {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] {W : C}
    {k l : W ⟶ pullback f g} (h₀ : k ≫ pullback.fst = l ≫ pullback.fst)
    (h₁ : k ≫ pullback.snd = l ≫ pullback.snd) : k = l :=
  limit.hom_ext <| PullbackCone.equalizer_ext _ h₀ h₁
#align category_theory.limits.pullback.hom_ext CategoryTheory.Limits.pullback.hom_ext

/-- The pullback cone built from the pullback projections is a pullback. -/
def pullbackIsPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsLimit (PullbackCone.mk (pullback.fst : pullback f g ⟶ _) pullback.snd pullback.condition) :=
  PullbackCone.IsLimit.mk _ (fun s => pullback.lift s.fst s.snd s.condition) (by simp) (by simp)
    (by aesop_cat)
#align category_theory.limits.pullback_is_pullback CategoryTheory.Limits.pullbackIsPullback

/-- Two morphisms out of a pushout are equal if their compositions with the pushout morphisms are
    equal -/
@[ext 1100]
theorem pushout.hom_ext {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] {W : C}
    {k l : pushout f g ⟶ W} (h₀ : pushout.inl ≫ k = pushout.inl ≫ l)
    (h₁ : pushout.inr ≫ k = pushout.inr ≫ l) : k = l :=
  colimit.hom_ext <| PushoutCocone.coequalizer_ext _ h₀ h₁
#align category_theory.limits.pushout.hom_ext CategoryTheory.Limits.pushout.hom_ext

/-- The pushout cocone built from the pushout coprojections is a pushout. -/
def pushoutIsPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    IsColimit (PushoutCocone.mk (pushout.inl : _ ⟶ pushout f g) pushout.inr pushout.condition) :=
  PushoutCocone.IsColimit.mk _ (fun s => pushout.desc s.inl s.inr s.condition) (by simp) (by simp)
    (by aesop_cat)
#align category_theory.limits.pushout_is_pushout CategoryTheory.Limits.pushoutIsPushout

instance pullback.map_isIso {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) [IsIso i₁] [IsIso i₂] [IsIso i₃] :
    IsIso (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine ⟨⟨pullback.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) ?_ ?_, ?_, ?_⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
  · aesop_cat
  · aesop_cat
#align category_theory.limits.pullback.map_is_iso CategoryTheory.Limits.pullback.map_isIso

/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pullback f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps! hom]
def pullback.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPullback f₁ g₁] [HasPullback f₂ g₂] : pullback f₁ g₁ ≅ pullback f₂ g₂ :=
  asIso <| pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])
#align category_theory.limits.pullback.congr_hom CategoryTheory.Limits.pullback.congrHom

@[simp]
theorem pullback.congrHom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂)
    (h₂ : g₁ = g₂) [HasPullback f₁ g₁] [HasPullback f₂ g₂] :
    (pullback.congrHom h₁ h₂).inv =
      pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) := by
  ext
  · erw [pullback.lift_fst]
    rw [Iso.inv_comp_eq]
    erw [pullback.lift_fst_assoc]
    rw [Category.comp_id, Category.comp_id]
  · erw [pullback.lift_snd]
    rw [Iso.inv_comp_eq]
    erw [pullback.lift_snd_assoc]
    rw [Category.comp_id, Category.comp_id]
#align category_theory.limits.pullback.congr_hom_inv CategoryTheory.Limits.pullback.congrHom_inv

instance pushout.map_isIso {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂]
    (g₁ : T ⟶ Y) (g₂ : T ⟶ Z) [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁) (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) [IsIso i₁] [IsIso i₂] [IsIso i₃] :
    IsIso (pushout.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine ⟨⟨pushout.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) ?_ ?_, ?_, ?_⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
  · aesop_cat
  · aesop_cat
#align category_theory.limits.pushout.map_is_iso CategoryTheory.Limits.pushout.map_isIso

theorem pullback.mapDesc_comp {X Y S T S' : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S) (i' : S ⟶ S')
    [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)] [HasPullback (f ≫ i ≫ i') (g ≫ i ≫ i')]
    [HasPullback ((f ≫ i) ≫ i') ((g ≫ i) ≫ i')] :
    pullback.mapDesc f g (i ≫ i') = pullback.mapDesc f g i ≫ pullback.mapDesc _ _ i' ≫
    (pullback.congrHom (Category.assoc _ _ _) (Category.assoc _ _ _)).hom := by
  aesop_cat
#align category_theory.limits.pullback.map_desc_comp CategoryTheory.Limits.pullback.mapDesc_comp

/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pushout f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps! hom]
def pushout.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPushout f₁ g₁] [HasPushout f₂ g₂] : pushout f₁ g₁ ≅ pushout f₂ g₂ :=
  asIso <| pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])
#align category_theory.limits.pushout.congr_hom CategoryTheory.Limits.pushout.congrHom

@[simp]
theorem pushout.congrHom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂)
    (h₂ : g₁ = g₂) [HasPushout f₁ g₁] [HasPushout f₂ g₂] :
    (pushout.congrHom h₁ h₂).inv =
      pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) := by
  ext
  · erw [pushout.inl_desc]
    rw [Iso.comp_inv_eq, Category.id_comp]
    erw [pushout.inl_desc]
    rw [Category.id_comp]
  · erw [pushout.inr_desc]
    rw [Iso.comp_inv_eq, Category.id_comp]
    erw [pushout.inr_desc]
    rw [Category.id_comp]
#align category_theory.limits.pushout.congr_hom_inv CategoryTheory.Limits.pushout.congrHom_inv

theorem pushout.mapLift_comp {X Y S T S' : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) (i' : S' ⟶ S)
    [HasPushout f g] [HasPushout (i ≫ f) (i ≫ g)] [HasPushout (i' ≫ i ≫ f) (i' ≫ i ≫ g)]
    [HasPushout ((i' ≫ i) ≫ f) ((i' ≫ i) ≫ g)] :
    pushout.mapLift f g (i' ≫ i) =
      (pushout.congrHom (Category.assoc _ _ _) (Category.assoc _ _ _)).hom ≫
        pushout.mapLift _ _ i' ≫ pushout.mapLift f g i := by
  aesop_cat
#align category_theory.limits.pushout.map_lift_comp CategoryTheory.Limits.pushout.mapLift_comp

section

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

/-- The comparison morphism for the pullback of `f,g`.
This is an isomorphism iff `G` preserves the pullback of `f,g`; see
`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Pullbacks.lean`
-/
def pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g)] :
    G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g) :=
  pullback.lift (G.map pullback.fst) (G.map pullback.snd)
    (by simp only [← G.map_comp, pullback.condition])
#align category_theory.limits.pullback_comparison CategoryTheory.Limits.pullbackComparison

@[reassoc (attr := simp)]
theorem pullbackComparison_comp_fst (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.fst = G.map pullback.fst :=
  pullback.lift_fst _ _ _
#align category_theory.limits.pullback_comparison_comp_fst CategoryTheory.Limits.pullbackComparison_comp_fst

@[reassoc (attr := simp)]
theorem pullbackComparison_comp_snd (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.snd = G.map pullback.snd :=
  pullback.lift_snd _ _ _
#align category_theory.limits.pullback_comparison_comp_snd CategoryTheory.Limits.pullbackComparison_comp_snd

@[reassoc (attr := simp)]
theorem map_lift_pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] {W : C} {h : W ⟶ X} {k : W ⟶ Y} (w : h ≫ f = k ≫ g) :
    G.map (pullback.lift _ _ w) ≫ pullbackComparison G f g =
      pullback.lift (G.map h) (G.map k) (by simp only [← G.map_comp, w]) := by
  ext <;> simp [← G.map_comp]
#align category_theory.limits.map_lift_pullback_comparison CategoryTheory.Limits.map_lift_pullbackComparison

/-- The comparison morphism for the pushout of `f,g`.
This is an isomorphism iff `G` preserves the pushout of `f,g`; see
`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Pullbacks.lean`
-/
def pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.map f) (G.map g)] :
    pushout (G.map f) (G.map g) ⟶ G.obj (pushout f g) :=
  pushout.desc (G.map pushout.inl) (G.map pushout.inr)
    (by simp only [← G.map_comp, pushout.condition])
#align category_theory.limits.pushout_comparison CategoryTheory.Limits.pushoutComparison

@[reassoc (attr := simp)]
theorem inl_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] : pushout.inl ≫ pushoutComparison G f g = G.map pushout.inl :=
  pushout.inl_desc _ _ _
#align category_theory.limits.inl_comp_pushout_comparison CategoryTheory.Limits.inl_comp_pushoutComparison

@[reassoc (attr := simp)]
theorem inr_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] : pushout.inr ≫ pushoutComparison G f g = G.map pushout.inr :=
  pushout.inr_desc _ _ _
#align category_theory.limits.inr_comp_pushout_comparison CategoryTheory.Limits.inr_comp_pushoutComparison

@[reassoc (attr := simp)]
theorem pushoutComparison_map_desc (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] {W : C} {h : Y ⟶ W} {k : Z ⟶ W} (w : f ≫ h = g ≫ k) :
    pushoutComparison G f g ≫ G.map (pushout.desc _ _ w) =
      pushout.desc (G.map h) (G.map k) (by simp only [← G.map_comp, w]) := by
  ext <;> simp [← G.map_comp]
#align category_theory.limits.pushout_comparison_map_desc CategoryTheory.Limits.pushoutComparison_map_desc

end

section PullbackSymmetry

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z)

/-- Making this a global instance would make the typeclass search go in an infinite loop. -/
theorem hasPullback_symmetry [HasPullback f g] : HasPullback g f :=
  ⟨⟨⟨_, PullbackCone.flipIsLimit (pullbackIsPullback f g)⟩⟩⟩
#align category_theory.limits.has_pullback_symmetry CategoryTheory.Limits.hasPullback_symmetry

attribute [local instance] hasPullback_symmetry

/-- The isomorphism `X ×[Z] Y ≅ Y ×[Z] X`. -/
def pullbackSymmetry [HasPullback f g] : pullback f g ≅ pullback g f :=
  IsLimit.conePointUniqueUpToIso
    (PullbackCone.flipIsLimit (pullbackIsPullback f g)) (limit.isLimit _)
#align category_theory.limits.pullback_symmetry CategoryTheory.Limits.pullbackSymmetry

@[reassoc (attr := simp)]
theorem pullbackSymmetry_hom_comp_fst [HasPullback f g] :
    (pullbackSymmetry f g).hom ≫ pullback.fst = pullback.snd := by simp [pullbackSymmetry]
#align category_theory.limits.pullback_symmetry_hom_comp_fst CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst

@[reassoc (attr := simp)]
theorem pullbackSymmetry_hom_comp_snd [HasPullback f g] :
    (pullbackSymmetry f g).hom ≫ pullback.snd = pullback.fst := by simp [pullbackSymmetry]
#align category_theory.limits.pullback_symmetry_hom_comp_snd CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd

@[reassoc (attr := simp)]
theorem pullbackSymmetry_inv_comp_fst [HasPullback f g] :
    (pullbackSymmetry f g).inv ≫ pullback.fst = pullback.snd := by simp [Iso.inv_comp_eq]
#align category_theory.limits.pullback_symmetry_inv_comp_fst CategoryTheory.Limits.pullbackSymmetry_inv_comp_fst

@[reassoc (attr := simp)]
theorem pullbackSymmetry_inv_comp_snd [HasPullback f g] :
    (pullbackSymmetry f g).inv ≫ pullback.snd = pullback.fst := by simp [Iso.inv_comp_eq]
#align category_theory.limits.pullback_symmetry_inv_comp_snd CategoryTheory.Limits.pullbackSymmetry_inv_comp_snd

end PullbackSymmetry

section PushoutSymmetry

open WalkingCospan

variable (f : X ⟶ Y) (g : X ⟶ Z)

/-- Making this a global instance would make the typeclass search go in an infinite loop. -/
theorem hasPushout_symmetry [HasPushout f g] : HasPushout g f :=
  ⟨⟨⟨_, PushoutCocone.flipIsColimit (pushoutIsPushout f g)⟩⟩⟩
#align category_theory.limits.has_pushout_symmetry CategoryTheory.Limits.hasPushout_symmetry

attribute [local instance] hasPushout_symmetry

/-- The isomorphism `Y ⨿[X] Z ≅ Z ⨿[X] Y`. -/
def pushoutSymmetry [HasPushout f g] : pushout f g ≅ pushout g f :=
  IsColimit.coconePointUniqueUpToIso
    (PushoutCocone.flipIsColimit (pushoutIsPushout f g)) (colimit.isColimit _)
#align category_theory.limits.pushout_symmetry CategoryTheory.Limits.pushoutSymmetry

@[reassoc (attr := simp)]
theorem inl_comp_pushoutSymmetry_hom [HasPushout f g] :
    pushout.inl ≫ (pushoutSymmetry f g).hom = pushout.inr :=
  (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _
#align category_theory.limits.inl_comp_pushout_symmetry_hom CategoryTheory.Limits.inl_comp_pushoutSymmetry_hom

@[reassoc (attr := simp)]
theorem inr_comp_pushoutSymmetry_hom [HasPushout f g] :
    pushout.inr ≫ (pushoutSymmetry f g).hom = pushout.inl :=
  (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _
#align category_theory.limits.inr_comp_pushout_symmetry_hom CategoryTheory.Limits.inr_comp_pushoutSymmetry_hom

@[reassoc (attr := simp)]
theorem inl_comp_pushoutSymmetry_inv [HasPushout f g] :
    pushout.inl ≫ (pushoutSymmetry f g).inv = pushout.inr := by simp [Iso.comp_inv_eq]
#align category_theory.limits.inl_comp_pushout_symmetry_inv CategoryTheory.Limits.inl_comp_pushoutSymmetry_inv

@[reassoc (attr := simp)]
theorem inr_comp_pushoutSymmetry_inv [HasPushout f g] :
    pushout.inr ≫ (pushoutSymmetry f g).inv = pushout.inl := by simp [Iso.comp_inv_eq]
#align category_theory.limits.inr_comp_pushout_symmetry_inv CategoryTheory.Limits.inr_comp_pushoutSymmetry_inv

end PushoutSymmetry

variable (C)

/-- `HasPullbacks` represents a choice of pullback for every pair of morphisms

See <https://stacks.math.columbia.edu/tag/001W>
-/
abbrev HasPullbacks :=
  HasLimitsOfShape WalkingCospan C
#align category_theory.limits.has_pullbacks CategoryTheory.Limits.HasPullbacks

/-- `HasPushouts` represents a choice of pushout for every pair of morphisms -/
abbrev HasPushouts :=
  HasColimitsOfShape WalkingSpan C
#align category_theory.limits.has_pushouts CategoryTheory.Limits.HasPushouts

/-- If `C` has all limits of diagrams `cospan f g`, then it has all pullbacks -/
theorem hasPullbacks_of_hasLimit_cospan
    [∀ {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g)] : HasPullbacks C :=
  { has_limit := fun F => hasLimitOfIso (diagramIsoCospan F).symm }
#align category_theory.limits.has_pullbacks_of_has_limit_cospan CategoryTheory.Limits.hasPullbacks_of_hasLimit_cospan

/-- If `C` has all colimits of diagrams `span f g`, then it has all pushouts -/
theorem hasPushouts_of_hasColimit_span
    [∀ {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}, HasColimit (span f g)] : HasPushouts C :=
  { has_colimit := fun F => hasColimitOfIso (diagramIsoSpan F) }
#align category_theory.limits.has_pushouts_of_has_colimit_span CategoryTheory.Limits.hasPushouts_of_hasColimit_span

/-- The duality equivalence `WalkingSpanᵒᵖ ≌ WalkingCospan` -/
@[simps!]
def walkingSpanOpEquiv : WalkingSpanᵒᵖ ≌ WalkingCospan :=
  widePushoutShapeOpEquiv _
#align category_theory.limits.walking_span_op_equiv CategoryTheory.Limits.walkingSpanOpEquiv

/-- The duality equivalence `WalkingCospanᵒᵖ ≌ WalkingSpan` -/
@[simps!]
def walkingCospanOpEquiv : WalkingCospanᵒᵖ ≌ WalkingSpan :=
  widePullbackShapeOpEquiv _
#align category_theory.limits.walking_cospan_op_equiv CategoryTheory.Limits.walkingCospanOpEquiv

-- see Note [lower instance priority]
/-- Having wide pullback at any universe level implies having binary pullbacks. -/
instance (priority := 100) hasPullbacks_of_hasWidePullbacks (D : Type u) [h : Category.{v} D]
    [h' : HasWidePullbacks.{w} D] : HasPullbacks.{v,u} D := by
  haveI I := @hasWidePullbacks_shrink.{0, w} D h h'
  infer_instance
#align category_theory.limits.has_pullbacks_of_has_wide_pullbacks CategoryTheory.Limits.hasPullbacks_of_hasWidePullbacks

-- see Note [lower instance priority]
/-- Having wide pushout at any universe level implies having binary pushouts. -/
instance (priority := 100) hasPushouts_of_hasWidePushouts (D : Type u) [h : Category.{v} D]
    [h' : HasWidePushouts.{w} D] : HasPushouts.{v,u} D := by
  haveI I := @hasWidePushouts_shrink.{0, w} D h h'
  infer_instance


end CategoryTheory.Limits
