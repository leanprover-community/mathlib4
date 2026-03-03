/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.SetLike.Basic

/-! # Class of grading-preserving functions

We define `GradedFunLike F 𝒜 ℬ` where `𝒜` and `ℬ` represent some sort of grading. This class
assumes `FunLike A B` where `A` and `B` are the underlying types.
-/

@[expose] public section

/-- The class `GradedFunLike F 𝒜 ℬ` expresses that terms of type `F` have an injective coercion to
grading-preserving functions from `A` to `B`, where `𝒜` is a grading on `A` and `ℬ` is a grading on
`B`. This typeclass has `[FunLike F A B]` as one of the assumptions. This typeclass is used in the
charactersation of certain types of graded homomorphisms, such as `GradedRingHom` and
`GradedAlgHom`. For example, what would be called `"GradedRingHomClass F 𝒜 ℬ`" would be expressed
as `[FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]`.
-/
class GradedFunLike (F : Type*) {A B σ τ ι : outParam Type*}
    [SetLike σ A] [SetLike τ B] (𝒜 : outParam <| ι → σ) (ℬ : outParam <| ι → τ)
    [FunLike F A B] where
  map_mem (f : F) {i x} : x ∈ 𝒜 i → f x ∈ ℬ i

section GradedFunLike

variable {F A B σ τ ι : Type*}
  [SetLike σ A] [SetLike τ B] {𝒜 : ι → σ} {ℬ : ι → τ} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]

lemma map_mem (f : F) {i x} (h : x ∈ 𝒜 i) : f x ∈ ℬ i :=
  GradedFunLike.map_mem f h

/-- A graded map descends to a map on each component. -/
def mapGraded (f : F) (i : ι) (x : 𝒜 i) : ℬ i :=
  ⟨f x, map_mem f x.2⟩

end GradedFunLike
