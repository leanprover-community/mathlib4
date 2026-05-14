/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.SetLike.Basic
import Mathlib.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

/-! # Class of grading-preserving functions and isomorphisms

We define `GradedFunLike F 𝒜 ℬ` where `𝒜` and `ℬ` represent some sort of grading. This class
assumes `FunLike A B` where `A` and `B` are the underlying types.

We also define `GradedEquivLike E 𝒜 ℬ`, which is similar to `EquivLike`, where here `e : E` is
required to satisfy `x ∈ 𝒜 i ↔ e x ∈ ℬ i`.
-/

@[expose] public section

/-- The class `GradedFunLike F 𝒜 ℬ` expresses that terms of type `F` have an injective coercion to
grading-preserving functions from `A` to `B`, where `𝒜` is a grading on `A` and `ℬ` is a grading on
`B`. This typeclass has `[FunLike F A B]` as one of the assumptions. This typeclass is used in the
characterisation of certain types of graded homomorphisms, such as `GradedRingHom` and
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

lemma Graded.map_mem (f : F) {i x} (h : x ∈ 𝒜 i) : f x ∈ ℬ i :=
  GradedFunLike.map_mem f h

/-- A graded map descends to a map on each component. -/
def Graded.subtypeMap (f : F) (i : ι) (x : 𝒜 i) : ℬ i :=
  ⟨f x, map_mem f x.2⟩

end GradedFunLike

/-- The class `GradedEquivLike E 𝒜 ℬ` says that `E` is a type of grading-preserving isomorphisms
between `𝒜` and `ℬ`. It is the combination of `GradedFunLike E 𝒜 ℬ` and `EquivLike E A B`. -/
class GradedEquivLike (E : Type*) {A B σ τ ι : outParam Type*}
    [SetLike σ A] [SetLike τ B] (𝒜 : outParam <| ι → σ) (ℬ : outParam <| ι → τ)
    [EquivLike E A B] where
  map_mem_iff (e : E) {i x} : e x ∈ ℬ i ↔ x ∈ 𝒜 i

section GradedEquivLike

variable (E : Type*) {A B σ τ ι : Type*} [SetLike σ A] [SetLike τ B]
  (𝒜 : ι → σ) (ℬ : ι → τ) [EquivLike E A B] [GradedEquivLike E 𝒜 ℬ]

instance (priority := 100) GradedEquivLike.toGradedFunLike : GradedFunLike E 𝒜 ℬ where
  __ := (inferInstance : FunLike E A B)
  map_mem e := (map_mem_iff e).mpr

variable {E 𝒜 ℬ}

lemma Graded.map_mem_iff (e : E) {i x} : e x ∈ ℬ i ↔ x ∈ 𝒜 i :=
  GradedEquivLike.map_mem_iff e
alias ⟨Graded.mem_of_map_mem, Graded.map_mem_of_mem⟩ := Graded.map_mem_iff

/-- A graded isomorphism descends to an isomorphism on each component. -/
@[simps] def Graded.equiv (e : E) (i : ι) : 𝒜 i ≃ ℬ i where
  toFun := subtypeMap e i
  invFun y := ⟨EquivLike.inv e (y : B),
    mem_of_map_mem e <| by rw [EquivLike.apply_inv_apply]; exact y.2⟩
  left_inv _ := by ext; exact EquivLike.inv_apply_apply e _
  right_inv _ := by ext; exact EquivLike.apply_inv_apply e _

end GradedEquivLike
