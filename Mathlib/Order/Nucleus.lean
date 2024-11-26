/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Nucleus
Locales are the dual concept to Frames.
A Nucleus is a function between Frames which corresponds to a sublocale.
https://ncatlab.org/nlab/show/nucleus
-/
variable {X : Type*} [Order.Frame X]

/--
A Nucleus is a function which is
* idempotent
* increasing
* and preserves infima
-/
structure Nucleus (X : Type*) [Order.Frame X] where
  toFun : X → X
  idempotent (x : X) : toFun (toFun x) = toFun x
  increasing (x : X) : x ≤ toFun x
  preserves_inf (x y : X) : toFun (x ⊓ y) = toFun x ⊓ toFun y

/--
A Nucleus preserves ⊤
-/
lemma nucleus_preserves_top (n : Nucleus X) : n.toFun ⊤ = ⊤ :=
   top_le_iff.mp (n.increasing ⊤)

/--
A Nucleus is montone
-/
lemma nucleus_monotone (n : Nucleus X) : Monotone n.toFun := by
  rw [Monotone]
  intro a b h
  have h1 : a ⊓ b = a := inf_eq_left.mpr h
  have h2 := n.preserves_inf a b
  rw [h1] at h2
  exact left_eq_inf.mp h2
