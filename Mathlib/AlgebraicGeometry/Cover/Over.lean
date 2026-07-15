/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!

# Covers of schemes over a base

In this file we define the typeclass `Cover.Over`. For a cover `𝒰` of an `S`-scheme `X`,
the datum `𝒰.Over S g` asserts that the components of `𝒰` are `S`-schemes with structure
morphisms `g j` and that the component maps are morphisms of `S`-schemes.

We provide instances of `𝒰.Over S g` for standard constructions on covers.

-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P : MorphismProperty Scheme.{u}} (S : Scheme.{u})

/-- Bundle an `S`-scheme with `P` into an object of `P.Over ⊤ S`. -/
abbrev asOverProp (X : Scheme.{u}) (S : Scheme.{u}) {f : X ⟶ S} [X.Over S f] (h : P (X ↘ S)) :
    P.Over ⊤ S :=
  ⟨X.asOver S, h⟩

/-- Bundle an `S`-morphism of `S`-scheme with `P` into a morphism in `P.Over ⊤ S`. -/
abbrev Hom.asOverProp {X Y : Scheme.{u}} (f : X.Hom Y) (S : Scheme.{u}) {fX : X ⟶ S} {fY : Y ⟶ S}
    [X.Over S fX] [Y.Over S fY] [f.IsOver S] {hX : P (X ↘ S)} {hY : P (Y ↘ S)} :
    X.asOverProp S hX ⟶ Y.asOverProp S hY :=
  ⟨f.asOver S, trivial, trivial⟩

/-- A `P`-cover of a scheme `X` over `S` is a cover, where the components are over `S` with
structure morphisms `g j` and the component maps commute with the structure morphisms. -/
protected class Cover.Over {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    [IsJointlySurjectivePreserving P] {X : Scheme.{u}} {f : X ⟶ S} [X.Over S f]
    (𝒰 : X.Cover (precoverage P)) (g : outParam <| ∀ j, 𝒰.X j ⟶ S) where
  over (j : 𝒰.I₀) : (𝒰.X j).Over S (g j) := {}
  comp_over (j : 𝒰.I₀) : 𝒰.f j ≫ f = g j := by simp

attribute [instance_reducible] Cover.Over.over
attribute [instance] Cover.Over.over

variable [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]

instance Cover.Over.isOver_map {X : Scheme.{u}} {f : X ⟶ S} [X.Over S f]
    (𝒰 : X.Cover (precoverage P)) {g : ∀ j, 𝒰.X j ⟶ S} [𝒰.Over S g] (j : 𝒰.I₀) :
    (𝒰.f j).IsOver S :=
  ⟨Cover.Over.comp_over j⟩

instance [P.ContainsIdentities] [P.RespectsIso] {X Y : Scheme.{u}} (f : X ⟶ Y) {fX : X ⟶ S}
    {fY : Y ⟶ S} [X.Over S fX] [Y.Over S fY] [f.IsOver S] [IsIso f] :
    (coverOfIsIso (P := P) f).Over S (fun _ ↦ fX) where
  comp_over _ := comp_over f S

section

variable {X W : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (f : W ⟶ X) {fW : W ⟶ S} {fX : X ⟶ S}
  {g𝒰 : ∀ j, 𝒰.X j ⟶ S} [W.Over S fW] [X.Over S fX] [𝒰.Over S g𝒰] [f.IsOver S]

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of a cover of `S`-schemes along a morphism of `S`-schemes. This is not
definitionally equal to `AlgebraicGeometry.Scheme.Cover.pullback₁`, as here we take
the pullback in `Over S`, whose underlying scheme is only isomorphic but not equal to the
pullback in `Scheme`. -/
@[simps]
def Cover.pullbackCoverOver : W.Cover (precoverage P) where
  I₀ := 𝒰.I₀
  X x := (pullback (f.asOver S) ((𝒰.f x).asOver S)).left
  f x := (pullback.fst (f.asOver S) ((𝒰.f x).asOver S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun j ↦ ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₁ f) x
      use i
      exact (mem_range_iff_of_surjective ((𝒰.pullback₁ f).f i) _
        ((PreservesPullback.iso (Over.forget S) (f.asOver S) ((𝒰.f _).asOver S)).inv)
        (PreservesPullback.iso_inv_fst _ _ _) x).mp hy
    · dsimp only
      rw [← Over.forget_map, ← PreservesPullback.iso_hom_fst, P.cancel_left_of_respectsIso]
      exact P.pullback_fst _ _ (𝒰.map_prop j)

instance : (𝒰.pullbackCoverOver S f).Over S
    (fun j ↦ (pullback (f.asOver S) ((𝒰.f j).asOver S)).hom) where
  comp_over j := by exact Over.w (pullback.fst (f.asOver S) ((𝒰.f j).asOver S))

set_option backward.isDefEq.respectTransparency false in
/-- A variant of `AlgebraicGeometry.Scheme.Cover.pullbackCoverOver` with the arguments in the
fiber products flipped. -/
@[simps]
def Cover.pullbackCoverOver' : W.Cover (precoverage P) where
  I₀ := 𝒰.I₀
  X x := (pullback ((𝒰.f x).asOver S) (f.asOver S)).left
  f x := (pullback.snd ((𝒰.f x).asOver S) (f.asOver S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun j ↦ ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₂ f) x
      use i
      exact (mem_range_iff_of_surjective ((𝒰.pullback₂ f).f _) _
        ((PreservesPullback.iso (Over.forget S) ((𝒰.f _).asOver S) (f.asOver S)).inv)
        (PreservesPullback.iso_inv_snd _ _ _) x).mp hy
    · dsimp only
      rw [← Over.forget_map, ← PreservesPullback.iso_hom_snd, P.cancel_left_of_respectsIso]
      exact P.pullback_snd _ _ (𝒰.map_prop j)

instance : (𝒰.pullbackCoverOver' S f).Over S
    (fun j ↦ (pullback ((𝒰.f j).asOver S) (f.asOver S)).hom) where
  comp_over j := by exact Over.w (pullback.snd ((𝒰.f j).asOver S) (f.asOver S))

variable {Q : MorphismProperty Scheme.{u}} [Q.HasOfPostcompProperty Q]
  [Q.IsStableUnderBaseChange] [Q.IsStableUnderComposition]

variable (hX : Q (X ↘ S)) (hW : Q (W ↘ S)) (hQ : ∀ j, Q (𝒰.X j ↘ S))

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of a cover of `S`-schemes with `Q` along a morphism of `S`-schemes. This is not
definitionally equal to `AlgebraicGeometry.Scheme.Cover.pullbackCover`, as here we take
the pullback in `Q.Over ⊤ S`, whose underlying scheme is only isomorphic but not equal to the
pullback in `Scheme`. -/
@[simps -isSimp]
def Cover.pullbackCoverOverProp : W.Cover (precoverage P) where
  I₀ := 𝒰.I₀
  X x := (pullback (f.asOverProp (hX := hW) (hY := hX) S)
    ((𝒰.f x).asOverProp (hX := hQ x) (hY := hX) S)).left
  f x := (pullback.fst (f.asOverProp S) ((𝒰.f x).asOverProp S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun j ↦ ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₁ f) x
      use i
      exact (mem_range_iff_of_surjective ((𝒰.pullback₁ f).f i) _
        ((PreservesPullback.iso (MorphismProperty.Over.forget Q _ _ ⋙ Over.forget S)
          (f.asOverProp S) ((𝒰.f _).asOverProp S)).inv)
        (PreservesPullback.iso_inv_fst _ _ _) x).mp hy
    · simp only [← CategoryTheory.Over.forget_map]
      rw [MorphismProperty.Comma.toCommaMorphism_eq_hom,
        ← MorphismProperty.Comma.forget_map, ← Functor.comp_map]
      rw [← PreservesPullback.iso_hom_fst, P.cancel_left_of_respectsIso]
      exact P.pullback_fst _ _ (𝒰.map_prop j)

instance : (𝒰.pullbackCoverOverProp S f hX hW hQ).Over S
    (fun j ↦ (pullback (f.asOverProp (hX := hW) (hY := hX) S)
      ((𝒰.f j).asOverProp (hX := hQ j) (hY := hX) S)).hom) where
  comp_over j := by exact (pullback.fst (f.asOverProp S) ((𝒰.f j).asOverProp S)).w

set_option backward.isDefEq.respectTransparency false in
/-- A variant of `AlgebraicGeometry.Scheme.Cover.pullbackCoverOverProp` with the arguments in the
fiber products flipped. -/
@[simps -isSimp]
def Cover.pullbackCoverOverProp' : W.Cover (precoverage P) where
  I₀ := 𝒰.I₀
  X x := (pullback ((𝒰.f x).asOverProp (hX := hQ x) (hY := hX) S)
    (f.asOverProp (hX := hW) (hY := hX) S)).left
  f x := (pullback.snd ((𝒰.f x).asOverProp S) (f.asOverProp S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun j ↦ ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₂ f) x
      use i
      exact (mem_range_iff_of_surjective ((𝒰.pullback₂ f).f i) _
        ((PreservesPullback.iso (MorphismProperty.Over.forget Q _ _ ⋙ Over.forget S)
          ((𝒰.f _).asOverProp S) (f.asOverProp S)).inv)
        (PreservesPullback.iso_inv_snd _ _ _) x).mp hy
    · simp only [← CategoryTheory.Over.forget_map]
      rw [MorphismProperty.Comma.toCommaMorphism_eq_hom,
        ← MorphismProperty.Comma.forget_map, ← Functor.comp_map]
      rw [← PreservesPullback.iso_hom_snd, P.cancel_left_of_respectsIso]
      exact P.pullback_snd _ _ (𝒰.map_prop j)

instance : (𝒰.pullbackCoverOverProp' S f hX hW hQ).Over S
    (fun j ↦ (pullback ((𝒰.f j).asOverProp (hX := hQ j) (hY := hX) S)
      (f.asOverProp (hX := hW) (hY := hX) S)).hom) where
  comp_over j := by exact (pullback.snd ((𝒰.f j).asOverProp S) (f.asOverProp S)).w

end

variable [P.IsStableUnderComposition]

instance {X : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (𝒱 : ∀ x, (𝒰.X x).Cover (precoverage P))
    {f : X ⟶ S} {g𝒰 : ∀ x, 𝒰.X x ⟶ S} {g𝒱 : ∀ x j, (𝒱 x).X j ⟶ S} [X.Over S f]
    [𝒰.Over S g𝒰] [∀ x, (𝒱 x).Over S (g𝒱 x)] :
    Cover.Over S (𝒰.bind 𝒱) (fun j ↦ g𝒱 j.1 j.2) where
  comp_over j := by
    change ((𝒱 j.1).f j.2 ≫ 𝒰.f j.1) ≫ f = g𝒱 j.1 j.2
    rw [Category.assoc, comp_over (𝒰.f j.1) S, comp_over ((𝒱 j.1).f j.2) S]

end AlgebraicGeometry.Scheme
