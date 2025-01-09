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

open scoped Function -- required for scoped `on` notation

lemma EmbeddingLike.pairwise_comp {X : Type*} {Y : Type*} {F} [FunLike F Y X] [EmbeddingLike F Y X]
    (f : F) {p : X → X → Prop} (h : Pairwise p) : Pairwise (p on f) :=
  h.comp_of_injective <| EmbeddingLike.injective f

lemma EquivLike.pairwise_comp_iff {X : Type*} {Y : Type*} {F} [EquivLike F Y X]
    (f : F) (p : X → X → Prop) : Pairwise (p on f) ↔ Pairwise p :=
  (EquivLike.bijective f).pairwise_comp_iff
