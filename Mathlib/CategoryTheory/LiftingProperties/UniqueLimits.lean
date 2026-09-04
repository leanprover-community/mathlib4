/-
Copyright (c) 2026 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.Unique
public import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
# Unique lifting properties and (co)limits

This file mirrors `Mathlib.CategoryTheory.LiftingProperties.Limits` for the
at-most-one and unique lifting properties: the (co)base-change lemmas along a
pushout/pullback square, and the closure of unique lifting under (co)products.

For pushouts, pullbacks, products and coproducts, existence of lifts is not
re-proved: it is taken from the ordinary lifting property in mathlib, the new
content is the uniqueness half expressed via `HasAtMostOneLiftingProperty`, and
the `HasUniqueLiftingProperty` versions follow by `HasUniqueLiftingProperty.mk'`.

For a general `J`-shaped (co)limit this is no longer possible, because the
ordinary-lifting statement is false. There `HasUniqueLiftingProperty.of_isLimit`
builds the lift itself: it lifts each component square and uses uniqueness to
show that the component lifts are compatible with the transition maps of the
diagram, so that they form a cone and induce a map to the limit.

These are the individual-morphism prerequisites for the closure instances on the
`leftOrthogonal`/`rightOrthogonal` morphism properties.

## Main declarations

* `CategoryTheory.IsPushout.hasAtMostOneLiftingProperty`
* `CategoryTheory.IsPullback.hasAtMostOneLiftingProperty`
* `CategoryTheory.IsPushout.hasUniqueLiftingProperty`
* `CategoryTheory.IsPullback.hasUniqueLiftingProperty`
* the `pushout.inl` / `pushout.inr` / `pullback.fst` / `pullback.snd` instances
* the `Pi.map` / `Sigma.map` (co)product instances
* `CategoryTheory.HasAtMostOneLiftingProperty.of_isLimit` / `.of_isColimit`
* `CategoryTheory.HasUniqueLiftingProperty.of_isLimit` / `.of_isColimit` — the
  general `J`-shaped (co)limit lifting lemmas, whose ordinary-lifting analogue is
  false and where uniqueness is what repairs it

-/

public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category* C] {X Y Z W : C}
  {f : X ⟶ Y} {s : X ⟶ Z} {g : Z ⟶ W} {t : Y ⟶ W}

/-- Base change of the at-most-one lifting property along a pushout square: if
squares with `f` on the left and `g'` on the right have at most one lift, then so
do squares with the pushout `g` on the left and `g'` on the right. -/
lemma IsPushout.hasAtMostOneLiftingProperty (h : IsPushout s f g t)
    {Z' W' : C} (g' : Z' ⟶ W') [HasAtMostOneLiftingProperty f g'] :
    HasAtMostOneLiftingProperty g g' where
  subsingleton_liftStruct {u v} sq := ⟨fun l₁ l₂ => by
    apply CommSq.LiftStruct.ext
    apply h.hom_ext
    · rw [l₁.fac_left, l₂.fac_left]
    · exact CommSq.lift_eq_of_hasAtMostOneLiftingProperty f g'
        (sq := ⟨by rw [assoc, sq.w, ← assoc, h.w, assoc]⟩)
        (by rw [← assoc, ← h.w, assoc, l₁.fac_left]) (by rw [assoc, l₁.fac_right])
        (by rw [← assoc, ← h.w, assoc, l₂.fac_left]) (by rw [assoc, l₂.fac_right])⟩

/-- Base change of the at-most-one lifting property along a pullback square: if
squares with `f'` on the left and `g` on the right have at most one lift, then so
do squares with `f'` on the left and the pullback `f` on the right. -/
lemma IsPullback.hasAtMostOneLiftingProperty (h : IsPullback s f g t)
    {X' Y' : C} (f' : X' ⟶ Y') [HasAtMostOneLiftingProperty f' g] :
    HasAtMostOneLiftingProperty f' f where
  subsingleton_liftStruct {u v} sq := ⟨fun l₁ l₂ => by
    apply CommSq.LiftStruct.ext
    apply h.hom_ext
    · exact CommSq.lift_eq_of_hasAtMostOneLiftingProperty f' g
        (sq := ⟨by rw [assoc, h.w, ← assoc, sq.w, assoc]⟩)
        (by rw [← assoc, l₁.fac_left]) (by rw [assoc, h.w, ← assoc, l₁.fac_right])
        (by rw [← assoc, l₂.fac_left]) (by rw [assoc, h.w, ← assoc, l₂.fac_right])
    · rw [l₁.fac_right, l₂.fac_right]⟩

/-- Base change of the unique lifting property along a pushout square. -/
lemma IsPushout.hasUniqueLiftingProperty (h : IsPushout s f g t)
    {Z' W' : C} (g' : Z' ⟶ W') [HasUniqueLiftingProperty f g'] :
    HasUniqueLiftingProperty g g' :=
  have : HasLiftingProperty g g' := h.hasLiftingProperty g'
  have : HasAtMostOneLiftingProperty g g' := h.hasAtMostOneLiftingProperty g'
  HasUniqueLiftingProperty.mk' g g'

/-- Base change of the unique lifting property along a pullback square. -/
lemma IsPullback.hasUniqueLiftingProperty (h : IsPullback s f g t)
    {X' Y' : C} (f' : X' ⟶ Y') [HasUniqueLiftingProperty f' g] :
    HasUniqueLiftingProperty f' f :=
  have : HasLiftingProperty f' f := h.hasLiftingProperty f'
  have : HasAtMostOneLiftingProperty f' f := h.hasAtMostOneLiftingProperty f'
  HasUniqueLiftingProperty.mk' f' f

instance [HasPushout s f] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasAtMostOneLiftingProperty f p] :
    HasAtMostOneLiftingProperty (pushout.inl s f) p :=
  (IsPushout.of_hasPushout s f).hasAtMostOneLiftingProperty p

instance [HasPushout s f] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasAtMostOneLiftingProperty s p] :
    HasAtMostOneLiftingProperty (pushout.inr s f) p :=
  (IsPushout.of_hasPushout s f).flip.hasAtMostOneLiftingProperty p

instance [HasPullback g t] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasAtMostOneLiftingProperty p g] :
    HasAtMostOneLiftingProperty p (pullback.snd g t) :=
  (IsPullback.of_hasPullback g t).hasAtMostOneLiftingProperty p

instance [HasPullback g t] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasAtMostOneLiftingProperty p t] :
    HasAtMostOneLiftingProperty p (pullback.fst g t) :=
  (IsPullback.of_hasPullback g t).flip.hasAtMostOneLiftingProperty p

instance [HasPushout s f] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasUniqueLiftingProperty f p] :
    HasUniqueLiftingProperty (pushout.inl s f) p :=
  (IsPushout.of_hasPushout s f).hasUniqueLiftingProperty p

instance [HasPushout s f] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasUniqueLiftingProperty s p] :
    HasUniqueLiftingProperty (pushout.inr s f) p :=
  (IsPushout.of_hasPushout s f).flip.hasUniqueLiftingProperty p

instance [HasPullback g t] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasUniqueLiftingProperty p g] :
    HasUniqueLiftingProperty p (pullback.snd g t) :=
  (IsPullback.of_hasPullback g t).hasUniqueLiftingProperty p

instance [HasPullback g t] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasUniqueLiftingProperty p t] :
    HasUniqueLiftingProperty p (pullback.fst g t) :=
  (IsPullback.of_hasPullback g t).flip.hasUniqueLiftingProperty p

set_option backward.isDefEq.respectTransparency false in
instance {J : Type*} {A B : J → C} [HasProduct A] [HasProduct B]
    (f : (j : J) → A j ⟶ B j) {X Y : C} (p : X ⟶ Y)
    [∀ j, HasAtMostOneLiftingProperty p (f j)] :
    HasAtMostOneLiftingProperty p (Limits.Pi.map f) where
  subsingleton_liftStruct {t b} sq := ⟨fun l₁ l₂ => by
    apply CommSq.LiftStruct.ext
    apply Pi.hom_ext
    intro j
    exact CommSq.lift_eq_of_hasAtMostOneLiftingProperty p (f j)
      (sq := ⟨by rw [assoc, ← Pi.map_π, ← assoc, sq.w, assoc]⟩)
      (by rw [← assoc, l₁.fac_left]) (by rw [assoc, ← Pi.map_π, ← assoc, l₁.fac_right])
      (by rw [← assoc, l₂.fac_left]) (by rw [assoc, ← Pi.map_π, ← assoc, l₂.fac_right])⟩

set_option backward.isDefEq.respectTransparency false in
instance {J : Type*} {A B : J → C} [HasCoproduct A] [HasCoproduct B]
    (f : (j : J) → A j ⟶ B j) {X Y : C} (p : X ⟶ Y)
    [∀ j, HasAtMostOneLiftingProperty (f j) p] :
    HasAtMostOneLiftingProperty (Limits.Sigma.map f) p where
  subsingleton_liftStruct {t b} sq := ⟨fun l₁ l₂ => by
    apply CommSq.LiftStruct.ext
    apply Sigma.hom_ext
    intro j
    exact CommSq.lift_eq_of_hasAtMostOneLiftingProperty (f j) p
      (sq := ⟨by rw [assoc, sq.w, ← assoc, Sigma.ι_map, assoc]⟩)
      (by rw [← assoc, ← Sigma.ι_map, assoc, l₁.fac_left]) (by rw [assoc, l₁.fac_right])
      (by rw [← assoc, ← Sigma.ι_map, assoc, l₂.fac_left]) (by rw [assoc, l₂.fac_right])⟩

set_option backward.isDefEq.respectTransparency false in
/-- Right-hand closure of the unique lifting property under products: if `p` on the left has
the unique lifting property against every `f j` on the right, then it has it against
`Pi.map f` on the right. -/
instance {J : Type*} {A B : J → C} [HasProduct A] [HasProduct B]
    (f : (j : J) → A j ⟶ B j) {X Y : C} (p : X ⟶ Y)
    [∀ j, HasUniqueLiftingProperty p (f j)] :
    HasUniqueLiftingProperty p (Limits.Pi.map f) :=
  HasUniqueLiftingProperty.mk' p (Limits.Pi.map f)

set_option backward.isDefEq.respectTransparency false in
/-- Left-hand closure of the unique lifting property under coproducts: if every `f j` on the
left has the unique lifting property against `p` on the right, then so does `Sigma.map f`
on the left.

This is not deduced from the product instance in `Cᵒᵖ` because `(Sigma.map f).op` is only
isomorphic to `Pi.map (fun j ↦ (f j).op)`, not equal to it, so transporting through `Cᵒᵖ`
would cost an arrow isomorphism and be no shorter than the direct proof. -/
instance {J : Type*} {A B : J → C} [HasCoproduct A] [HasCoproduct B]
    (f : (j : J) → A j ⟶ B j) {X Y : C} (p : X ⟶ Y)
    [∀ j, HasUniqueLiftingProperty (f j) p] :
    HasUniqueLiftingProperty (Limits.Sigma.map f) p :=
  HasUniqueLiftingProperty.mk' (Limits.Sigma.map f) p

section IsLimitColimit

variable {J : Type*} [Category J] {X₁ X₂ : J ⥤ C}

/-- If `i` has at most one lift against every component of a natural transformation
`f` between `J`-shaped diagrams, then it has at most one lift against any morphism
`φ` of limit cones lying over `f`. Only the source cone need be a limit. -/
lemma HasAtMostOneLiftingProperty.of_isLimit (f : X₁ ⟶ X₂)
    {c₁ : Cone X₁} {c₂ : Cone X₂} (h₁ : IsLimit c₁) {φ : c₁.pt ⟶ c₂.pt}
    (hφ : ∀ j, φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j)
    {A B : C} (i : A ⟶ B) [∀ j, HasAtMostOneLiftingProperty i (f.app j)] :
    HasAtMostOneLiftingProperty i φ where
  subsingleton_liftStruct {u v} sq := ⟨fun l l' => by
    apply CommSq.LiftStruct.ext
    apply h₁.hom_ext
    intro j
    exact CommSq.lift_eq_of_hasAtMostOneLiftingProperty i (f.app j)
      (sq := ⟨by rw [assoc, ← hφ j, ← assoc, sq.w, assoc]⟩)
      (by rw [← assoc, l.fac_left]) (by rw [assoc, ← hφ j, ← assoc, l.fac_right])
      (by rw [← assoc, l'.fac_left]) (by rw [assoc, ← hφ j, ← assoc, l'.fac_right])⟩

/-- If `i` has the unique lifting property against every component of a natural
transformation `f` between `J`-shaped diagrams, then it has the unique lifting
property against any morphism `φ` of limit cones lying over `f`.

This has no ordinary-lifting analogue: componentwise lifts need not be compatible
with the transition maps of the diagram, and it is *uniqueness* (through
`HasAtMostOneLiftingProperty.of_isLimit`) that forces the compatibility making them
assemble into a map to the limit. -/
lemma HasUniqueLiftingProperty.of_isLimit (f : X₁ ⟶ X₂)
    {c₁ : Cone X₁} {c₂ : Cone X₂} (h₁ : IsLimit c₁) (h₂ : IsLimit c₂)
    {φ : c₁.pt ⟶ c₂.pt} (hφ : ∀ j, φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j)
    {A B : C} (i : A ⟶ B) [∀ j, HasUniqueLiftingProperty i (f.app j)] :
    HasUniqueLiftingProperty i φ where
  subsingleton_liftStruct :=
    (HasAtMostOneLiftingProperty.of_isLimit f h₁ hφ i).subsingleton_liftStruct
  sq_hasLift {u v} sq := by
    -- the componentwise squares and their (unique) lifts
    have sqj : ∀ j, CommSq (u ≫ c₁.π.app j) i (f.app j) (v ≫ c₂.π.app j) :=
      fun j => ⟨by rw [assoc, ← hφ j, ← assoc, sq.w, assoc]⟩
    -- uniqueness makes the lifts into a cone over `X₁` with apex `B`
    let cone : Cone X₁ :=
      { pt := B
        π :=
          { app := fun j => (sqj j).lift
            naturality := fun j j' α => by
              simp only [Functor.const_obj_obj, Functor.const_obj_map, id_comp]
              symm
              exact CommSq.lift_eq_of_hasAtMostOneLiftingProperty i (f.app j') (sq := sqj j')
                (by rw [← assoc, (sqj j).fac_left, assoc, c₁.w α])
                (by rw [assoc, f.naturality α, ← assoc, (sqj j).fac_right, assoc, c₂.w α])
                (sqj j').fac_left (sqj j').fac_right } }
    exact CommSq.HasLift.mk'
      { l := h₁.lift cone
        fac_left := h₁.hom_ext fun j => by rw [assoc, h₁.fac]; exact (sqj j).fac_left
        fac_right := h₂.hom_ext fun j => by
          rw [assoc, hφ j, ← assoc, h₁.fac]; exact (sqj j).fac_right }

/-- Colimit dual of `HasAtMostOneLiftingProperty.of_isLimit`: if every component of
`f` has at most one lift against `p`, then so does any morphism `φ` of colimit
cocones lying over `f`. Only the target cocone need be a colimit.

Proved by passing to `Cᵒᵖ`, where `c₂.op` is a limit cone and `φ.op` lies over `NatTrans.op f`. -/
lemma HasAtMostOneLiftingProperty.of_isColimit (f : X₁ ⟶ X₂)
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} (h₂ : IsColimit c₂) {φ : c₁.pt ⟶ c₂.pt}
    (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)
    {A B : C} (p : A ⟶ B) [∀ j, HasAtMostOneLiftingProperty (f.app j) p] :
    HasAtMostOneLiftingProperty φ p :=
  haveI : ∀ j, HasAtMostOneLiftingProperty p.op ((NatTrans.op f).app j) :=
    fun j => (inferInstance : HasAtMostOneLiftingProperty (f.app j.unop) p).op
  (HasAtMostOneLiftingProperty.of_isLimit (NatTrans.op f) (c₂ := c₁.op) h₂.op (φ := φ.op)
    (fun j => Quiver.Hom.unop_inj (hφ j.unop)) p.op).unop

/-- Colimit dual of `HasUniqueLiftingProperty.of_isLimit`: the unique lifting
property against every component of `f` gives the unique lifting property against
any morphism `φ` of colimit cocones lying over `f`.

Proved by passing to `Cᵒᵖ`, where `c₁.op`, `c₂.op` are limit cones and `φ.op` lies over
`NatTrans.op f`. -/
lemma HasUniqueLiftingProperty.of_isColimit (f : X₁ ⟶ X₂)
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} (h₁ : IsColimit c₁) (h₂ : IsColimit c₂)
    {φ : c₁.pt ⟶ c₂.pt} (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)
    {A B : C} (p : A ⟶ B) [∀ j, HasUniqueLiftingProperty (f.app j) p] :
    HasUniqueLiftingProperty φ p :=
  haveI : ∀ j, HasUniqueLiftingProperty p.op ((NatTrans.op f).app j) :=
    fun j => (inferInstance : HasUniqueLiftingProperty (f.app j.unop) p).op
  (HasUniqueLiftingProperty.of_isLimit (NatTrans.op f) (c₂ := c₁.op) h₂.op h₁.op (φ := φ.op)
    (fun j => Quiver.Hom.unop_inj (hφ j.unop)) p.op).unop

end IsLimitColimit

end CategoryTheory
