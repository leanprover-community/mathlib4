/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Limits.WeakLimits.WeakEqualizers

/-!
# Weak pullbacks

These are weak limits for diagrams of shape `WalkingCospan`.

-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory Category Limits

variable {C : Type*} [Category* C]

namespace CategoryTheory.Limits

variable {W X Y Z : C}

/-- Two morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` have a weak pullback if the diagram
`cospan f g` has a weak limit. -/
abbrev HasWeakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasWeakLimit (cospan f g)

/-- `weakPullback f g` computes the weak pullback of a pair of morphisms
with the same target. -/
abbrev weakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :=
  weakLimit (cospan f g)

/-- The cone associated to the weak pullback of `f` and `g` -/
abbrev weakPullback.cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasWeakPullback f g] : PullbackCone f g :=
  weakLimit.cone (cospan f g)

/-- The first projection of the weak pullback of `f` and `g`. -/
abbrev weakPullback.fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    weakPullback f g ⟶ X :=
  weakLimit.π (cospan f g) WalkingCospan.left

/-- The second projection of the weak pullback of `f` and `g`. -/
abbrev weakPullback.snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    weakPullback f g ⟶ Y :=
  weakLimit.π (cospan f g) WalkingCospan.right

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
`weakPullback.lift : W ⟶ weakPullback f g`. -/
abbrev weakPullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) : W ⟶ weakPullback f g :=
  weakLimit.lift _ (PullbackCone.mk h k w)

set_option backward.isDefEq.respectTransparency false in
lemma weakPullback.exists_lift {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) :
    ∃ (l : W ⟶ weakPullback f g),
    l ≫ weakPullback.fst f g = h ∧ l ≫ weakPullback.snd f g = k :=
  ⟨weakPullback.lift h k, by simp⟩

/-- The cone associated to a weak pullback is a weak limit cone. -/
abbrev weakPullback.isWeakLimit {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    IsWeakLimit (weakPullback.cone f g) :=
  weakLimit.isWeakLimit (cospan f g)

@[simp]
theorem WeakPullbackCone.fst_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasWeakLimit (cospan f g)] :
    PullbackCone.fst (weakLimit.cone (cospan f g)) = weakPullback.fst f g := rfl

@[simp]
theorem WeakPullbackCone.snd_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasWeakLimit (cospan f g)] :
    PullbackCone.snd (weakLimit.cone (cospan f g)) = weakPullback.snd f g := rfl

@[reassoc]
theorem weakPullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasWeakPullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    weakPullback.lift h k w ≫ weakPullback.fst f g = h :=
  weakLimit.lift_π _ _

@[reassoc]
theorem weakPullback.lift_snd {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasWeakPullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    weakPullback.lift h k w ≫ weakPullback.snd f g = k :=
  weakLimit.lift_π _ _

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
`l : W ⟶ weakPullback f g` such that `l ≫ weakPullback.fst = h` and `l ≫ weakPullback.snd = k`. -/
def weakPullback.lift' {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
      { l : W ⟶ weakPullback f g //
      l ≫ weakPullback.fst f g = h ∧ l ≫ weakPullback.snd f g = k } :=
  ⟨weakPullback.lift h k w, weakPullback.lift_fst _ _ _, weakPullback.lift_snd _ _ _⟩

@[reassoc]
theorem weakPullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g] :
    weakPullback.fst f g ≫ f = weakPullback.snd f g ≫ g :=
  PullbackCone.condition _

/-- Given such a diagram, then there is a natural morphism from the weak pullback of
`W ⟶ S` and `X ⟶ S` to the weak pullback of `Y ⟶ T` and `Z ⟶ T`.

```
W ⟶ Y
  ↘   ↘
  S ⟶ T
  ↗   ↗
X ⟶ Z
```
-/
abbrev weakPullback.map {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasWeakPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasWeakPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    weakPullback f₁ f₂ ⟶ weakPullback g₁ g₂ :=
  weakPullback.lift (weakPullback.fst f₁ f₂ ≫ i₁) (weakPullback.snd f₁ f₂ ≫ i₂)
    (by simp only [Category.assoc, ← eq₁, ← eq₂, weakPullback.condition_assoc])

/-- A morphism from the weak pullback of `W ⟶ S` and `X ⟶ S` to the weak pullback of
`Y ⟶ T` and `Z ⟶ T` given `S ⟶ T`. -/
abbrev weakPullback.mapDesc {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [HasWeakPullback f g]
    [HasWeakPullback (f ≫ i) (g ≫ i)] : weakPullback f g ⟶ weakPullback (f ≫ i) (g ≫ i) :=
  weakPullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (Category.id_comp _).symm
  (Category.id_comp _).symm

namespace PullbackCone

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- This is a slightly more convenient method to verify that a pullback cone is a weak limit cone.
It only asks for a proof of facts that carry any mathematical content -/
def isWeakLimitAux (t : PullbackCone f g) (lift : ∀ s : PullbackCone f g, s.pt ⟶ t.pt)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ t.fst = s.fst)
    (fac_right : ∀ s : PullbackCone f g, lift s ≫ t.snd = s.snd) : IsWeakLimit t :=
  { lift
    fac := fun s j => Option.casesOn j (by
        rw [← s.w WalkingCospan.Hom.inl, ← t.w WalkingCospan.Hom.inl, ← Category.assoc]
        congr
        exact fac_left s)
      fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s)}

/-- This is another convenient method to verify that a pullback cone is a weak limit cone. It
only asks for a proof of facts that carry any mathematical content, and allows access to the
same `s` for all parts. -/
def isWeakLimitAux' (t : PullbackCone f g)
    (create :
      ∀ s : PullbackCone f g,
        { l //
          l ≫ t.fst = s.fst ∧
            l ≫ t.snd = s.snd}) :
    Limits.IsWeakLimit t :=
  PullbackCone.isWeakLimitAux t (fun s => (create s).1)
    (fun s => (create s).2.1) (fun s => (create s).2.2)

/-- This is a more convenient formulation to show that a `PullbackCone` constructed using
`PullbackCone.mk` is a weak limit cone.
-/
def IsWeakLimit.mk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
    (lift : ∀ s : PullbackCone f g, s.pt ⟶ W)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ fst = s.fst)
    (fac_right : ∀ s : PullbackCone f g, lift s ≫ snd = s.snd) :
    IsWeakLimit (PullbackCone.mk fst snd eq) :=
  isWeakLimitAux _ lift fac_left fac_right

/-- If `t` is a weak limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such
that `h ≫ f = k ≫ g`, then we get `l : W ⟶ t.pt`, which satisfies `l ≫ fst t = h`
and `l ≫ snd t = k`, see `IsWeakLimit.lift_fst` and `IsWeakLimit.lift_snd`. -/
def IsWeakLimit.lift {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ t.pt :=
  ht.lift <| PullbackCone.mk _ _ w

@[reassoc (attr := simp)]
lemma IsWeakLimit.lift_fst {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : IsWeakLimit.lift ht h k w ≫ PullbackCone.fst t = h :=
  ht.fac _ _

@[reassoc (attr := simp)]
lemma IsWeakLimit.lift_snd {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : IsWeakLimit.lift ht h k w ≫ PullbackCone.snd t = k :=
  ht.fac _ _

/-- If `t` is a weak limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such
that `h ≫ f = k ≫ g`, then we have `l : W ⟶ t.pt` satisfying `l ≫ fst t = h` and `l ≫ snd t = k`.
-/
def IsWeakLimit.lift' {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) :
    { l : W ⟶ t.pt // l ≫ PullbackCone.fst t = h ∧ l ≫ PullbackCone.snd t = k } :=
  ⟨IsWeakLimit.lift ht h k w, by simp⟩

/-- The pullback cone reconstructed using `PullbackCone.mk` from a pullback cone that is a
weak limit, is also a weak limit. -/
def mkSelfIsWeakLimit {t : PullbackCone f g} (ht : IsWeakLimit t) :
    IsWeakLimit (PullbackCone.mk t.fst t.snd t.condition) :=
  IsWeakLimit.ofIsoWeakLimit ht (PullbackCone.eta t)

end PullbackCone

/-- The weak pullback cone built from the weak pullback projections is a weak pullback. -/
def weakPullbackIsWeakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    IsWeakLimit (PullbackCone.mk (weakPullback.fst f g) (weakPullback.snd f g)
    weakPullback.condition) :=
  PullbackCone.mkSelfIsWeakLimit <| weakPullback.isWeakLimit f g

variable (C)

/-- A category `HasPullbacks` if it has all weak limits of shape `WalkingCospan`, i.e. if it
has a weak pullback for every pair of morphisms with the same codomain. -/
abbrev HasWeakPullbacks :=
  HasWeakLimitsOfShape WalkingCospan C

instance (priority := 100) HasWeakPullbacksOfHasPullbacks [HasPullbacks C] :
    HasWeakPullbacks C where

variable (f : X ⟶ Z) (g : Y ⟶ Z)

set_option backward.isDefEq.respectTransparency false in
/-- If the product `X ⨯ Y` and the weak equalizer of `π₁ ≫ f` and `π₂ ≫ g` exist, then the
weak pullback of `f` and `g` exists: it is given by composing the equalizer with the projections. -/
theorem hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLimit_parallelPair [HasLimit (pair X Y)]
    [HasWeakLimit (parallelPair (prod.fst ≫ f) (prod.snd ≫ g))] : HasWeakLimit (cospan f g) :=
  let π₁ : X ⨯ Y ⟶ X := prod.fst
  let π₂ : X ⨯ Y ⟶ Y := prod.snd
  let e := weakEqualizer.ι (π₁ ≫ f) (π₂ ≫ g)
  HasWeakLimit.mk
    { cone :=
        PullbackCone.mk (e ≫ π₁) (e ≫ π₂) <| by
          rw [Category.assoc, weakEqualizer.condition]
          simp [e]
      isWeakLimit :=
        PullbackCone.IsWeakLimit.mk _ (fun s => weakEqualizer.lift
          (prod.lift (s.π.app WalkingCospan.left) (s.π.app WalkingCospan.right)) <| by
            rw [← Category.assoc, limit.lift_π, ← Category.assoc, limit.lift_π]
            exact PullbackCone.condition _)
          (by simp [π₁, e]) (by simp [π₂, e])}

section

attribute [local instance] hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLimit_parallelPair

/-- If a category has all binary products and all weak equalizers, then it also has all
weak pullbacks. As usual, this is not an instance, since there may be a more direct way to
construct weak pullbacks. -/
theorem hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakKernels
    [HasBinaryProducts C] [HasWeakEqualizers C] : HasWeakPullbacks C where
      hasWeakLimit F := hasWeakLimit_of_iso (diagramIsoCospan F).symm

end

end CategoryTheory.Limits
