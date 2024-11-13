/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!

# Covers of schemes over a base

In this file we define the typeclass `Cover.Over`. For a cover `𝒰` of an `S`-scheme `X`,
the datum `𝒰.Over S` contains `S`-scheme structures on the components of `𝒰` and asserts
that the component maps are morphisms of `S`-schemes.

We provide instances of `𝒰.Over S` for standard constructions on covers.

-/

universe v u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P : MorphismProperty Scheme.{u}} (S : Scheme.{u})

/-- Bundle an `S`-scheme with `P` into an object of `P.Over ⊤ S`. -/
abbrev asOverProp (X : Scheme.{u}) (S : Scheme.{u}) [X.Over S] (h : P (X ↘ S)) : P.Over ⊤ S :=
  ⟨X.asOver S, h⟩

/-- Bundle an `S`-morphism of `S`-scheme with `P` into a morphism in `P.Over ⊤ S`. -/
abbrev Hom.asOverProp {X Y : Scheme.{u}} (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S]
    [f.IsOver S] {hX : P (X ↘ S)} {hY : P (Y ↘ S)} : X.asOverProp S hX ⟶ Y.asOverProp S hY :=
  ⟨f.asOver S, trivial, trivial⟩

/-- A `P`-cover of a scheme `X` over `S` is a cover, where the components are over `S` and the
component maps commute with the structure morphisms. -/
protected class Cover.Over {P : MorphismProperty Scheme.{u}} {X : Scheme.{u}} [X.Over S]
    (𝒰 : X.Cover P) where
  over (j : 𝒰.J) : (𝒰.obj j).Over S := by infer_instance
  isOver_map (j : 𝒰.J) : (𝒰.map j).IsOver S := by infer_instance

attribute [instance] Cover.Over.over Cover.Over.isOver_map

instance [P.ContainsIdentities] [P.RespectsIso] {X Y : Scheme.{u}} (f : X ⟶ Y) [X.Over S] [Y.Over S]
    [f.IsOver S] [IsIso f] : (coverOfIsIso (P := P) f).Over S where
  over _ := inferInstanceAs <| X.Over S
  isOver_map _ := inferInstanceAs <| f.IsOver S

section

variable [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
variable {X W : Scheme.{u}} (𝒰 : X.Cover P) (f : W ⟶ X) [W.Over S] [X.Over S]
  [𝒰.Over S] [f.IsOver S]

/-- The pullback of a cover of `S`-schemes along a morphism of `S`-schemes. This is not
definitionally equal to `AlgebraicGeometry.Scheme.Cover.pullbackCover`, as here we take
the pullback in `Over S`, whose underlying schemes is only isomorphic but not equal to the
pullback in `Scheme`. -/
@[simps]
def Cover.pullbackCoverOver : W.Cover P where
  J := 𝒰.J
  obj x := (pullback (f.asOver S) ((𝒰.map x).asOver S)).left
  map x := (pullback.fst (f.asOver S) ((𝒰.map x).asOver S)).left
  f x := 𝒰.f (f.base x)
  covers x := by
    obtain ⟨y, hy⟩ := 𝒰.covers (f.base x)
    obtain ⟨o, ho⟩ := IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
      (𝒰.map_prop _) x y hy.symm
    use (PreservesPullback.iso (Over.forget S) (f.asOver S) ((𝒰.map _).asOver S)).inv.base o
    simp only [Over.forget_obj, Over.forget_map, OverClass.asOverHom_left]
    simp_rw [← Scheme.comp_base_apply, ← Over.forget_map, PreservesPullback.iso_inv_fst]
    simpa
  map_prop j := by
    dsimp only
    rw [← Over.forget_map, ← PreservesPullback.iso_hom_fst, P.cancel_left_of_respectsIso]
    exact P.pullback_fst _ _ (𝒰.map_prop j)

instance (j : 𝒰.J) : ((𝒰.pullbackCoverOver S f).obj j).Over S where
  hom := (pullback (f.asOver S) ((𝒰.map j).asOver S)).hom

instance : (𝒰.pullbackCoverOver S f).Over S where
  isOver_map j := { comp_over := by exact Over.w (pullback.fst (f.asOver S) ((𝒰.map j).asOver S)) }

/-- A variant of `AlgebraicGeometry.Scheme.Cover.pullbackCoverOver` with the arguments in the
fiber products flipped. -/
@[simps]
def Cover.pullbackCoverOver' : W.Cover P where
  J := 𝒰.J
  obj x := (pullback ((𝒰.map x).asOver S) (f.asOver S)).left
  map x := (pullback.snd ((𝒰.map x).asOver S) (f.asOver S)).left
  f x := 𝒰.f (f.base x)
  covers x := by
    obtain ⟨y, hy⟩ := 𝒰.covers (f.base x)
    obtain ⟨o, ho⟩ := IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop
      (𝒰.map_prop _) y x hy
    use (PreservesPullback.iso (Over.forget S) ((𝒰.map _).asOver S) (f.asOver S)).inv.base o
    simp only [Over.forget_obj, Over.forget_map, OverClass.asOverHom_left]
    simp_rw [← Scheme.comp_base_apply, ← Over.forget_map, PreservesPullback.iso_inv_snd]
    simpa
  map_prop j := by
    dsimp only
    rw [← Over.forget_map, ← PreservesPullback.iso_hom_snd, P.cancel_left_of_respectsIso]
    exact P.pullback_snd _ _ (𝒰.map_prop j)

instance (j : 𝒰.J) : ((𝒰.pullbackCoverOver' S f).obj j).Over S where
  hom := (pullback ((𝒰.map j).asOver S) (f.asOver S)).hom

instance : (𝒰.pullbackCoverOver' S f).Over S where
  isOver_map j := { comp_over := by exact Over.w (pullback.snd ((𝒰.map j).asOver S) (f.asOver S)) }

variable {Q : MorphismProperty Scheme.{u}} [Q.HasOfPostcompProperty]
  [Q.IsStableUnderBaseChange] [Q.IsStableUnderComposition]

variable (hX : Q (X ↘ S)) (hW : Q (W ↘ S)) (hQ : ∀ j, Q (𝒰.obj j ↘ S))

/-- A variant of `AlgebraicGeometry.Scheme.Cover.pullbackCoverOverProp` with the arguments in the
fiber products flipped. -/
@[simps (config := .lemmasOnly)]
def Cover.pullbackCoverOverProp : W.Cover P where
  J := 𝒰.J
  obj x := (pullback (f.asOverProp (hX := hW) (hY := hX) S)
    ((𝒰.map x).asOverProp (hX := hQ x) (hY := hX) S)).left
  map x := (pullback.fst (f.asOverProp S) ((𝒰.map x).asOverProp S)).left
  f x := 𝒰.f (f.base x)
  covers x := by
    obtain ⟨y, hy⟩ := 𝒰.covers (f.base x)
    obtain ⟨o, ho⟩ := IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
      (𝒰.map_prop _) x y hy.symm
    use (PreservesPullback.iso (MorphismProperty.Over.forget Q _ _ ⋙ Over.forget S)
      (f.asOverProp S) ((𝒰.map _).asOverProp S)).inv.base o
    simp only [Functor.comp_obj, MorphismProperty.Comma.forget_obj, Over.forget_obj,
      MorphismProperty.Comma.forget_map, MorphismProperty.Comma.Hom.hom_mk,
      Over.forget_map, OverClass.asOverHom_left]
    rw [← Scheme.comp_base_apply, ← Over.forget_map, MorphismProperty.Comma.toCommaMorphism_eq_hom]
    rw [← MorphismProperty.Comma.forget_map, ← Functor.comp_map, PreservesPullback.iso_inv_fst]
    simpa
  map_prop j := by
    dsimp only
    rw [← Over.forget_map, MorphismProperty.Comma.toCommaMorphism_eq_hom,
      ← MorphismProperty.Comma.forget_map, ← Functor.comp_map]
    rw [← PreservesPullback.iso_hom_fst, P.cancel_left_of_respectsIso]
    exact P.pullback_fst _ _ (𝒰.map_prop j)

instance (j : 𝒰.J) : ((𝒰.pullbackCoverOverProp S f hX hW hQ).obj j).Over S where
  hom := (pullback (f.asOverProp (hX := hW) (hY := hX) S)
    ((𝒰.map j).asOverProp (hX := hQ j) (hY := hX) S)).hom

instance : (𝒰.pullbackCoverOverProp S f hX hW hQ).Over S where
  isOver_map j :=
    { comp_over := by exact (pullback.fst (f.asOverProp S) ((𝒰.map j).asOverProp S)).w }

/-- A variant of `AlgebraicGeometry.Scheme.Cover.pullbackCoverOverProp` with the arguments in the
fiber products flipped. -/
@[simps (config := .lemmasOnly)]
def Cover.pullbackCoverOverProp' : W.Cover P where
  J := 𝒰.J
  obj x := (pullback ((𝒰.map x).asOverProp (hX := hQ x) (hY := hX) S)
    (f.asOverProp (hX := hW) (hY := hX) S)).left
  map x := (pullback.snd ((𝒰.map x).asOverProp S) (f.asOverProp S)).left
  f x := 𝒰.f (f.base x)
  covers x := by
    obtain ⟨y, hy⟩ := 𝒰.covers (f.base x)
    obtain ⟨o, ho⟩ := IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop
      (𝒰.map_prop _) y x hy
    use (PreservesPullback.iso (MorphismProperty.Over.forget Q _ _ ⋙ Over.forget S)
      ((𝒰.map _).asOverProp S) (f.asOverProp S)).inv.base o
    simp only [Functor.comp_obj, MorphismProperty.Comma.forget_obj, Over.forget_obj,
      MorphismProperty.Comma.forget_map, MorphismProperty.Comma.Hom.hom_mk,
      Over.forget_map, OverClass.asOverHom_left]
    rw [← Scheme.comp_base_apply, ← Over.forget_map, MorphismProperty.Comma.toCommaMorphism_eq_hom]
    rw [← MorphismProperty.Comma.forget_map, ← Functor.comp_map, PreservesPullback.iso_inv_snd]
    simpa
  map_prop j := by
    dsimp only
    rw [← Over.forget_map, MorphismProperty.Comma.toCommaMorphism_eq_hom,
      ← MorphismProperty.Comma.forget_map, ← Functor.comp_map]
    rw [← PreservesPullback.iso_hom_snd, P.cancel_left_of_respectsIso]
    exact P.pullback_snd _ _ (𝒰.map_prop j)

instance (j : 𝒰.J) : ((𝒰.pullbackCoverOverProp' S f hX hW hQ).obj j).Over S where
  hom := (pullback ((𝒰.map j).asOverProp (hX := hQ j) (hY := hX) S)
    (f.asOverProp (hX := hW) (hY := hX) S)).hom

instance : (𝒰.pullbackCoverOverProp' S f hX hW hQ).Over S where
  isOver_map j :=
    { comp_over := by exact (pullback.snd ((𝒰.map j).asOverProp S) (f.asOverProp S)).w }

end

variable [P.IsStableUnderComposition]
variable {X : Scheme.{u}} (𝒰 : X.Cover P) (𝒱 : ∀ x, (𝒰.obj x).Cover P)
  [X.Over S] [𝒰.Over S] [∀ x, (𝒱 x).Over S]

instance (j : (𝒰.bind 𝒱).J) : ((𝒰.bind 𝒱).obj j).Over S :=
  inferInstanceAs <| ((𝒱 j.1).obj j.2).Over S

instance {X : Scheme.{u}} (𝒰 : X.Cover P) (𝒱 : ∀ x, (𝒰.obj x).Cover P)
    [X.Over S] [𝒰.Over S] [∀ x, (𝒱 x).Over S] : (𝒰.bind 𝒱).Over S where
  over := fun ⟨i, j⟩ ↦ inferInstanceAs <| ((𝒱 i).obj j).Over S
  isOver_map := fun ⟨i, j⟩ ↦ { comp_over := by simp }

end AlgebraicGeometry.Scheme
