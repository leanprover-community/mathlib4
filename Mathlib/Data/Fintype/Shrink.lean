/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Countable.Small
import Mathlib.Data.Fintype.EquivFin

/-!
# Fintype instance for `Shrink`
-/

universe u v
variable {α : Type u} [Fintype α]

noncomputable instance Shrink.instFintype : Fintype (Shrink.{v} α) := .ofEquiv _ (equivShrink _)

instance Shrink.instFinite {α : Type u} [Finite α] : Finite (Shrink.{v} α) :=
  .of_equiv _ (equivShrink _)

@[simp] lemma Fintype.card_shrink [Fintype (Shrink.{v} α)] : card (Shrink.{v} α) = card α :=
  card_congr (equivShrink _).symm
