/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Data.SetLike.Basic

/-! # Class of grading-preserving functions

We define `GradedFunLike F 𝒜 ℬ` where `𝒜` and `ℬ` represent some sort of grading. This class
extends `FunLike A B` where `A` and `B` are the underlying types.
-/

/-- The class `GradedFunLike F 𝒜 ℬ` expresses that terms of type `F` have an injective coercion to
grading-preserving functions from `A` to `B`, where `𝒜` is a grading on `A` and `ℬ` is a grading on
`B`. This typeclass extends `FunLike F A B`, so it is **not** necessary to repeat `[FunLike F A B]`
in the assumptions. This typeclass is used in the charactersation of certain types of graded
homomorphisms, such as `GradedRingHom` and `GradedAlgHom`. For example, what would be called
`"GradedRingHomClass F 𝒜 ℬ`" would be expressed as `[GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]`.
-/
class GradedFunLike (F : Type*) {A B σ τ ι : outParam Type*}
    [SetLike σ A] [SetLike τ B] (𝒜 : outParam <| ι → σ) (ℬ : outParam <| ι → τ)
    extends FunLike F A B where
  map_mem (f : F) {i x} : x ∈ 𝒜 i → f x ∈ ℬ i
export GradedFunLike (map_mem)

attribute [instance 100] GradedFunLike.toDFunLike

variable {F A B σ τ ι : Type*}
  [SetLike σ A] [SetLike τ B] {𝒜 : ι → σ} {ℬ : ι → τ} [GradedFunLike F 𝒜 ℬ] (f : F)

/-- A graded map descends to a map on each component. -/
def mapGraded (i : ι) (x : 𝒜 i) : ℬ i :=
  ⟨f x, map_mem f x.2⟩
