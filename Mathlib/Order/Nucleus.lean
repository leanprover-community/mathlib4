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

/--
A Nucleus is a function between Frames which corresponds to a sublocle. It is idempotent,
increasing and preserves infima.
-/
structure Nucleus (X : Type*) [SemilatticeInf X] extends InfHom X X where
  /-- A Nucleus is idempotent.-/
  idempotent' (x : X) : toFun (toFun x) ≤ toFun x
  /-- A Nucleus is increasing.-/
  increasing' (x : X) : x ≤ toFun x

/--
A stronger version of Nucleus.idempotent which follows from Nucleus.increasing.
-/
lemma Nucleus.idempotent {n : Nucleus X} {x : X} : n.toFun (n.toFun x) = n.toFun x := by
  apply le_antisymm
  · exact n.idempotent' x
  · exact n.increasing' (n.toFun x)

instance : FunLike (Nucleus X) X X where
  coe x := x.toFun
  coe_injective' f g h := by cases f; cases g; simp_all

/--
`NucleusClass F X` states that F is a type of Nuclei.
-/
class NucleusClass (F X : Type*) [SemilatticeInf X] [FunLike F X X] extends InfHomClass F X X :
    Prop where
  /-- A Nucleus is idempotent.-/
  idempotent (x : X) (f : F) : f (f x) ≤ f x
  /-- A Nucleus is increasing.-/
  increasing (x : X) (f : F) : x ≤ f x

lemma Nucleus.coe_eq_toFun (n : Nucleus X) {x : X} : n x = n.toFun x := by rfl

instance : NucleusClass (Nucleus X) X where
  idempotent := (by simp[Nucleus.coe_eq_toFun];exact fun x f ↦ f.idempotent' x)
  increasing := (by simp[Nucleus.coe_eq_toFun];exact fun x f ↦ f.increasing' x)
  map_inf := (by simp[Nucleus.coe_eq_toFun])

/--
We can proove that two Nuclei are equal by showing that their functions are the same.
-/
@[ext]
lemma Nucleus.ext {n m : Nucleus X} (h: ∀ a, n.toFun a = m.toFun a) : n = m :=
  DFunLike.ext n m h

/--
A Nucleus preserves ⊤
-/
lemma nucleus_preserves_top (n : Nucleus X) : n.toFun ⊤ = ⊤ :=
   top_le_iff.mp (n.increasing' ⊤)

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
