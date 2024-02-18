/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.FunLike.Equiv
import Mathlib.Logic.Pairwise

/-!
# Interaction of equivalences with `Pairwise`
-/

lemma EquivLike.pairwise_comp_iff {X : Type*} {Y : Type*} {F} [EquivLike F Y X]
    (f : F) (p : X → X → Prop) : Pairwise (fun y z ↦ p (f y) (f z)) ↔ Pairwise p := by
  refine ⟨fun h ↦ fun i j hij ↦ ?_,
          fun h ↦ fun i j hij ↦ h <| (EquivLike.injective f).ne hij⟩
  convert h (?_ : EquivLike.inv f i ≠ EquivLike.inv f j)
  · simp
  · simp
  · refine Function.Injective.ne ((EquivLike.injective_comp f _).1 (fun x y hxy ↦ ?_)) hij
    simpa using hxy
