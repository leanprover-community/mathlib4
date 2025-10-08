/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
import Mathlib.CategoryTheory.Sites.Hypercover.Zero
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Locality conditions on morphism properties

In this file we define locality conditions on morphism properties in a category. Let `K` be a
precoverage in a category `C` and `P` be a morphism property on `C` that respects isomorphisms.

We say that

- `P` is local at the target if for every `f : X ⟶ Y`, `P` holds for `f` if and only if it holds
  for the restrictions of `f` to `Uᵢ` for a
  `K`-cover `{Uᵢ}` of `Y`.
- `P` is local at the source if for every `f : X ⟶ Y`, `P` holds for `f` if and only if it holds
  for the restrictions of `f` to `Uᵢ` for a `K`-cover `{Uᵢ}` of `X`.

## Implementation details

The covers appearing in the definitions have index type in the morphism universe of `C`.

## TODOs

- Define source and target local closure of a morphism property.
-/

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (K : Precoverage C)

/--
A property of morphisms `P` in `C` is local at the target with respect to the precoverage `K` if
it respects ismorphisms, and:
`P` holds for `f : X ⟶ Y` if and only if it holds for the restrictions of `f` to `Uᵢ` for a
`0`-hypercover `{Uᵢ}` of `Y` in the precoverage `K`.
-/
class IsLocalAtTarget (P : MorphismProperty C) (K : Precoverage C) [K.HasPullbacks]
    extends RespectsIso P where
  /-- If `P` holds for `f : X ⟶ Y`, it also holds for `f` restricted to `Uᵢ` for any
  `K`-cover `𝒰` of `Y`. -/
  pullbackSnd {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{v} K Y)
    (i : 𝒰.I₀) (hf : P f) : P (pullback.snd f (𝒰.f i))
  /-- If `P` holds for `f` restricted to `Uᵢ` for all `i`, it also holds for `f : X ⟶ Y` for any
  `K`-cover `𝒰` of `Y`. -/
  of_zeroHypercover {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{v} K Y)
    (h : ∀ i, P (pullback.snd f (𝒰.f i))) : P f

namespace IsLocalAtTarget

variable {P : MorphismProperty C} {K L : Precoverage C} [K.HasPullbacks]

lemma mk_of_iff [P.RespectsIso]
    (H : ∀ {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{v} K Y),
      P f ↔ ∀ i, P (pullback.snd f (𝒰.f i))) :
    P.IsLocalAtTarget K where
  pullbackSnd 𝒰 i h := (H _ 𝒰).mp h i
  of_zeroHypercover 𝒰 h := (H _ 𝒰).mpr h

lemma mk_of_isStableUnderBaseChange [P.IsStableUnderBaseChange]
    (H : ∀ {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{v} K Y),
      (∀ i, P (pullback.snd f (𝒰.f i))) → P f) :
    P.IsLocalAtTarget K where
  pullbackSnd _ _ hf := P.pullback_snd _ _ hf
  of_zeroHypercover _ := H _ _

lemma of_le [L.HasPullbacks] [IsLocalAtTarget P L] (hle : K ≤ L) : IsLocalAtTarget P K where
  pullbackSnd 𝒰 i hf := pullbackSnd (𝒰.weaken hle) i hf
  of_zeroHypercover 𝒰 := of_zeroHypercover (𝒰.weaken hle)

instance top : IsLocalAtTarget (⊤ : MorphismProperty C) K where
  pullbackSnd := by simp
  of_zeroHypercover := by simp

variable [IsLocalAtTarget P K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{v} K Y)

lemma of_isPullback {X' : C} (i : 𝒰.I₀) {fst : X' ⟶ X} {snd : X' ⟶ 𝒰.X i}
    (h : IsPullback fst snd f (𝒰.f i)) (hf : P f) :
    P snd := by
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv, h.isoPullback_inv_snd]
  exact pullbackSnd _ _ hf

lemma iff_of_zeroHypercover : P f ↔ ∀ i, P (pullback.snd f (𝒰.f i)) :=
  ⟨fun hf _ ↦ pullbackSnd _ _ hf, fun h ↦ of_zeroHypercover _ h⟩

instance inf (P Q : MorphismProperty C) [IsLocalAtTarget P K] [IsLocalAtTarget Q K] :
    IsLocalAtTarget (P ⊓ Q) K where
  pullbackSnd _ i h := ⟨pullbackSnd _ i h.1, pullbackSnd _ i h.2⟩
  of_zeroHypercover _ h :=
    ⟨of_zeroHypercover _ fun i ↦ (h i).1, of_zeroHypercover _ fun i ↦ (h i).2⟩

end IsLocalAtTarget

alias of_zeroHypercover_target := IsLocalAtTarget.of_zeroHypercover
alias iff_of_zeroHypercover_target := IsLocalAtTarget.iff_of_zeroHypercover

/--
A property of morphisms `P` in `C` is local at the source with respect to the precoverage `K` if
it respects ismorphisms, and:
`P` holds for `f : X ⟶ Y` if and only if it holds for the restrictions of `f` to `Uᵢ` for a
`0`-hypercover `{Uᵢ}` of `X` in the precoverage `K`.
-/
class IsLocalAtSource (P : MorphismProperty C) (K : Precoverage C) extends RespectsIso P where
  /-- If `P` holds for `f : X ⟶ Y`, it also holds for `𝒰.f i ≫ f` for any `K`-cover `𝒰` of `X`. -/
  comp {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{v} K X) (i : 𝒰.I₀)
    (hf : P f) : P (𝒰.f i ≫ f)
  /-- If `P` holds for `𝒰.f i ≫ f` for all `i`, it holds for `f : X ⟶ Y` for any `K`-cover
  `𝒰` of X. -/
  of_zeroHypercover {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{v} K X) :
    (∀ i, P (𝒰.f i ≫ f)) → P f

namespace IsLocalAtSource

variable {P : MorphismProperty C} {K L : Precoverage C}

lemma mk_of_iff [P.RespectsIso]
    (H : ∀ {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{v} K X),
      P f ↔ ∀ i, P (𝒰.f i ≫ f)) :
    P.IsLocalAtSource K where
  comp 𝒰 i h := (H _ 𝒰).mp h i
  of_zeroHypercover 𝒰 h := (H _ 𝒰).mpr h

lemma of_le [IsLocalAtSource P L] (hle : K ≤ L) : IsLocalAtSource P K where
  comp 𝒰 i hf := comp (𝒰.weaken hle) i hf
  of_zeroHypercover 𝒰 h := of_zeroHypercover (𝒰.weaken hle) h

instance top : IsLocalAtSource (⊤ : MorphismProperty C) K where
  comp := by simp
  of_zeroHypercover := by simp

variable [IsLocalAtSource P K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{v} K X)

lemma iff_of_zeroHypercover : P f ↔ ∀ i, P (𝒰.f i ≫ f) :=
  ⟨fun hf i ↦ comp _ i hf, fun h ↦ of_zeroHypercover _ h⟩

instance inf (P Q : MorphismProperty C) [IsLocalAtSource P K] [IsLocalAtSource Q K] :
    IsLocalAtSource (P ⊓ Q) K where
  comp 𝒰 i hf := ⟨comp 𝒰 i hf.1, comp 𝒰 i hf.2⟩
  of_zeroHypercover _ h :=
    ⟨of_zeroHypercover _ fun i ↦ (h i).1, of_zeroHypercover _ fun i ↦ (h i).2⟩

end IsLocalAtSource

alias of_zeroHypercover_source := IsLocalAtSource.of_zeroHypercover
alias iff_of_zeroHypercover_source := IsLocalAtSource.iff_of_zeroHypercover

end MorphismProperty

end CategoryTheory
