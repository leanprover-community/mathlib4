/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
import Mathlib.Order.CompleteLattice
import Mathlib.Order.Hom.Lattice

/-!
# Nucleus
Locales are the dual concept to Frames.
A Nucleus is a function between Frames which corresponds to a sublocale.
https://ncatlab.org/nlab/show/nucleus
-/

open Order

variable {X : Type*} [CompleteLattice X]

/-- A nucleus is an inflationary idempotent `inf`-preserving endomorphism of a semilattice.
In a frame, nuclei correspond to sublocales. -/ -- TODO: Formalise that claim
-- TODO Nucleus extends InfHom
structure Nucleus (X : Type*) [SemilatticeInf X] where
  /-- The underlying Function.
  Do not use this function directly. Instead use the coercion coming from the `FunLike` instance. -/
  toFun : X → X
  /-- A `Nucleus` is idempotent.
  Do not use this directly. Instead use `Nucleus.idempotent`. -/
  idempotent' (x : X) : toFun (toFun x) ≤ toFun x
  /-- A `Nucleus` is increasing.
  Do not use this directly. Instead use `Nucleus.increasing`. -/
  increasing' (x : X) : x ≤ toFun x
  /-- A `Nucleus` preserves infima.
  Do not use this directly. Instead use `Nucleus.map_inf`. -/
  map_inf' (x y: X) : toFun (x ⊓ y) = toFun x ⊓ toFun y

/-- `NucleusClass F X` states that F is a type of Nuclei. -/
class NucleusClass (F X : Type*) [SemilatticeInf X] [FunLike F X X] extends InfHomClass F X X :
    Prop where
  /-- A Nucleus is idempotent.-/
  idempotent (x : X) (f : F) : f (f x) ≤ f x
  /-- A Nucleus is increasing.-/
  increasing (x : X) (f : F) : x ≤ f x

open Nucleus

variable {n : Nucleus X} {x y : X}

instance : FunLike (Nucleus X) X X where
  coe x := x.toFun
  coe_injective' f g h := by cases f; cases g; simp_all

lemma coe_eq_toFun (n : Nucleus X) : n x = n.toFun x := by rfl

lemma idempotent : n (n x) = n x := by
  apply le_antisymm
  · exact n.idempotent' x
  · exact n.increasing' (n.toFun x)

lemma increasing : x ≤ n x := by
  apply n.increasing'

lemma map_inf : n (x ⊓ y) = n x ⊓ n y := by
  apply n.map_inf'

instance : NucleusClass (Nucleus X) X where
  idempotent _ _ := le_of_eq idempotent
  increasing _ _ := increasing
  map_inf _ _ _ := map_inf


/--
We can proove that two Nuclei are equal by showing that their functions are the same.
-/
@[ext]
lemma Nucleus.ext {n m : Nucleus X} (h: ∀ a, n.toFun a = m.toFun a) : n = m :=
  DFunLike.ext n m h

/--
A Nucleus preserves ⊤
-/
@[simp] lemma map_top (n : Nucleus X) : n ⊤ = ⊤ :=
   top_le_iff.mp increasing

instance : LE (Nucleus X) where
  le x y := ∀ v : X, x.toFun v ≤ y.toFun v

lemma Nucleus.le_iff {n m : Nucleus X} : m ≤ n ↔ ∀ v : X, m.toFun v ≤ n.toFun v := by rfl

instance : Preorder (Nucleus X) where
  le_refl := (by simp only [Nucleus.le_iff, le_refl, implies_true])
  le_trans := (by simp only [Nucleus.le_iff]; exact fun a b c a_1 a_2 v ↦
    Preorder.le_trans (a.toFun v) (b.toFun v) (c.toFun v) (a_1 v) (a_2 v))

/--
The smallest Nucleus is the identity Nucleus.
-/
instance Nucleus.bot : Bot (Nucleus X) where
  bot.toFun x := x
  bot.idempotent' := by simp
  bot.increasing' := by simp
  bot.map_inf' := by simp

instance : OrderBot (Nucleus X) where
  bot_le := (by simp only [Nucleus.bot];exact fun a v ↦ a.increasing' v)

/--
The biggest Nucleus sends everything to ⊤.
-/
instance Nucleus.top : Top (Nucleus X) where
  top.toFun := ⊤
  top.idempotent' := by simp
  top.increasing' := by simp
  top.map_inf' := by simp

instance : OrderTop (Nucleus X) where
  le_top := (by simp [Nucleus.top, Nucleus.le_iff])
