/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Lifting properties and (co)limits

In this file, we show some consequences of lifting properties in the presence of
certain (co)limits.

-/

universe v

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C] {X Y Z W : C}
  {f : X ⟶ Y} {s : X ⟶ Z} {g : Z ⟶ W} {t : Y ⟶ W}

lemma IsPushout.hasLiftingProperty (h : IsPushout s f g t)
    {Z' W' : C} (g' : Z' ⟶ W') [HasLiftingProperty f g'] : HasLiftingProperty g g' where
  sq_hasLift := fun {u v} sq ↦ by
    have w : (s ≫ u) ≫ g' = f ≫ (t ≫ v) := by
      rw [← Category.assoc, ← h.w, Category.assoc, Category.assoc, sq.w]
    exact ⟨h.desc u (CommSq.mk w).lift (by rw [CommSq.fac_left]), h.inl_desc ..,
      h.hom_ext (by rw [h.inl_desc_assoc, sq.w]) (by rw [h.inr_desc_assoc, CommSq.fac_right])⟩

lemma IsPullback.hasLiftingProperty (h : IsPullback s f g t)
    {X' Y' : C} (f' : X' ⟶ Y') [HasLiftingProperty f' g] : HasLiftingProperty f' f where
  sq_hasLift := fun {u v} sq ↦ by
    have w : (u ≫ s) ≫ g = f' ≫ v ≫ t := by
      rw [Category.assoc, h.toCommSq.w, ← Category.assoc, ← Category.assoc, sq.w]
    exact ⟨h.lift (CommSq.mk w).lift v (by rw [CommSq.fac_right]),
      h.hom_ext (by rw [Category.assoc, h.lift_fst, CommSq.fac_left])
        (by rw [Category.assoc, h.lift_snd, sq.w]), h.lift_snd _ _ _⟩

instance [HasPushout s f] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasLiftingProperty f p] :
    HasLiftingProperty (pushout.inl s f) p :=
  (IsPushout.of_hasPushout s f).hasLiftingProperty p

instance [HasPushout s f] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasLiftingProperty s p] :
    HasLiftingProperty (pushout.inr s f) p :=
  (IsPushout.of_hasPushout s f).flip.hasLiftingProperty p

instance [HasPullback g t] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasLiftingProperty p g] :
    HasLiftingProperty p (pullback.snd g t) :=
  (IsPullback.of_hasPullback g t).hasLiftingProperty p

instance [HasPullback g t] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasLiftingProperty p t] :
    HasLiftingProperty p (pullback.fst g t) :=
  (IsPullback.of_hasPullback g t).flip.hasLiftingProperty p

/--
```
A ---u---> c₁.pt ---π---> X₁.obj j
|           |                |
g           |              f.app j
|           |                |
v           v                v
B ---v---> c₂.pt ---π---> X₂.obj j
```

Given lifting problems indexed by `J` of the above form, construct a cone of `X₁` with point `B`
whose components `B ⟶ X₁.obj j` are given by solutions of the lifting problems.

-/
@[simp]
noncomputable
def HasLiftingProperty.productLiftingCone {J : Type*} {X₁ X₂ : Discrete J ⥤ C}
    {c₁ : Cone X₁} {c₂ : Cone X₂} {h₂ : IsLimit c₂} {f : X₁ ⟶ X₂}
    {A B : C} {g : A ⟶ B} {u : A ⟶ c₁.pt} {v : B ⟶ c₂.pt}
    (sq : CommSq u g (h₂.lift (Cone.mk c₁.pt (c₁.π ≫ f))) v)
    [∀ j, HasLiftingProperty g (f.app j)] : Cone X₁ where
  pt := B
  π := { app j :=
          have w : (u ≫ c₁.π.app j) ≫ f.app j = g ≫ v ≫ c₂.π.app j := by
            rw [← Category.assoc, ← sq.w]
            simp only [Category.assoc, IsLimit.fac, NatTrans.comp_app, Functor.const_obj_obj]
          (CommSq.mk w).lift
         naturality := fun j j' h ↦ by
          cases j with | mk as =>
          have := Discrete.eq_of_hom h
          aesop}

/--
```
X₁.obj j ---ι---> c₁.pt ---u---> A
    |               |            |
 f.app j            |            g
    |               |            |
    v               v            v
X₂.obj j ---ι---> c₂.pt ---v---> B
```

Given lifting problems indexed by `J` of the above form, construct a cocone of `X₂` with point `A`
whose components `X₂.obj j ⟶ A` are given by solutions of the lifting problems.

-/
@[simp]
noncomputable
def HasLiftingProperty.coproductLiftingCocone {J : Type*} {X₁ X₂ : Discrete J ⥤ C}
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} {h₁ : IsColimit c₁} {f : X₁ ⟶ X₂}
    {A B : C} {g : A ⟶ B} {u : c₁.pt ⟶ A} {v : c₂.pt ⟶ B}
    (sq : CommSq u (h₁.desc (Cocone.mk c₂.pt (f ≫ c₂.ι))) g v)
    [∀ j, HasLiftingProperty (f.app j) g] : Cocone X₂ where
  pt := A
  ι := { app j :=
          have w : (c₁.ι.app j ≫ u) ≫ g = f.app j ≫ c₂.ι.app j ≫ v := by
            simp [sq.w]
          (CommSq.mk w).lift
         naturality := fun j j' h ↦ by
          cases j with | mk as =>
          have := Discrete.eq_of_hom h
          aesop}

instance {J : Type*} {A B : J → C} [HasProduct A] [HasProduct B]
    (f : (j : J) → A j ⟶ B j) {X Y : C} (p : X ⟶ Y)
    [∀ j, HasLiftingProperty p (f j)] :
    HasLiftingProperty p (Limits.Pi.map f) where
  sq_hasLift {t b} sq := by
    have sq' (j : J) :
        CommSq (t ≫ Pi.π _ j) p (f j) (b ≫ Pi.π _ j) :=
      ⟨by rw [← Category.assoc, ← sq.w]; simp⟩
    exact ⟨⟨{ l := Pi.lift (fun j ↦ (sq' j).lift) }⟩⟩

instance {J : Type*} {A B : J → C} [HasCoproduct A] [HasCoproduct B]
    (f : (j : J) → A j ⟶ B j) {X Y : C} (p : X ⟶ Y)
    [∀ j, HasLiftingProperty (f j) p] :
    HasLiftingProperty (Limits.Sigma.map f) p where
  sq_hasLift {t b} sq := by
    have sq' (j : J) :
        CommSq (Sigma.ι _ j ≫ t) (f j) p (Sigma.ι _ j ≫ b) :=
      ⟨by simp [sq.w]⟩
    exact ⟨⟨{ l := Sigma.desc (fun j ↦ (sq' j).lift) }⟩⟩

end CategoryTheory
