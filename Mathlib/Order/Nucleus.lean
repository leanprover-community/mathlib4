/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
import Mathlib.Order.CompleteLattice
import Mathlib.Tactic.ApplyFun

/-!
# Nucleus
Locales are the dual concept to Frames.
A Nucleus is a function between Frames which corresponds to a sublocale.
https://ncatlab.org/nlab/show/nucleus
-/
variable {X : Type*} [CompleteLattice X]

/--
The Type of Nuclei on a Frame.
-/
structure Nucleus (X : Type*) [SemilatticeInf X] where
  /-- The function of the nucleus.-/
  toFun : X → X
  /-- A Nucleus is idempotent.-/
  idempotent (x : X) : toFun (toFun x) ≤ toFun x
  /-- A Nucleus is increasing.-/
  increasing (x : X) : x ≤ toFun x
  /-- A Nucleus preserves infima.-/
  preserves_inf (x y : X) : toFun (x ⊓ y) = toFun x ⊓ toFun y

/--
A stronger version of Nucleus.idempotent which follows from Nucleus.increasing.
-/
lemma Nucleus.idempotent' {n : Nucleus X} {x : X} : n.toFun (n.toFun x) = n.toFun x := by
  apply le_antisymm
  · exact n.idempotent x
  · exact n.increasing (n.toFun x)

instance : FunLike (Nucleus X) X X where
  coe := Nucleus.toFun
  coe_injective' f g h := by cases f; cases g; congr

/--
`NucleusClass F X` states that F is a type of Nuclei.
-/
class NucleusClass (F X : Type*) [SemilatticeInf X] [FunLike F X X] : Prop where
  /-- A Nucleus is idempotent.-/
  idempotent (x : X) (f : F) : f (f x) ≤ f x
  /-- A Nucleus is increasing.-/
  increasing (x : X) (f : F) : x ≤ f x
  /-- A Nucleus preserves infima.-/
  preserves_inf (x y : X) (f : F) : f (x ⊓ y) = f x ⊓ f y


instance (F X : Type*) [SemilatticeInf X] [FunLike F X X] [n : NucleusClass F X]
  : OrderHomClass F X X where
  map_rel := fun f a b h => by
    have h1 : a ⊓ b = a := inf_eq_left.mpr h
    have h2 := n.preserves_inf a b
    rw [h1] at h2
    exact left_eq_inf.mp (h2 f)

lemma Nucleus.coe_eq_toFun (n : Nucleus X) {x : X} : n x = n.toFun x := by rfl


instance : NucleusClass (Nucleus X) X where
  idempotent := (by simp[Nucleus.coe_eq_toFun];exact fun x f ↦ f.idempotent x)
  increasing := (by simp[Nucleus.coe_eq_toFun];exact fun x f ↦ f.increasing x)
  preserves_inf := (by simp[Nucleus.coe_eq_toFun]; exact fun x y f ↦ f.preserves_inf x y)


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
   top_le_iff.mp (n.increasing ⊤)


instance : LE (Nucleus X) where
  le x y := ∀ v : X, x.toFun v ≤ y.toFun v

lemma Nucleus.le_iff {n m : Nucleus X} : m ≤ n ↔ ∀ v : X, m.toFun v ≤ n.toFun v := by rfl

instance : Preorder (Nucleus X) where
  le_refl := (by simp only [Nucleus.le_iff, le_refl, implies_true])
  le_trans := (by simp only [Nucleus.le_iff]; exact fun a b c a_1 a_2 v ↦
    Preorder.le_trans (a.toFun v) (b.toFun v) (c.toFun v) (a_1 v) (a_2 v))

/--
The identity Nucleus is the biggest sublocale.
-/
instance Nucleus.bot : Bot (Nucleus X) where
  bot := ⟨fun x ↦ x, Preorder.le_refl,Preorder.le_refl, fun _ _ ↦ rfl⟩

instance : OrderBot (Nucleus X) where
  bot_le := (by simp only [Nucleus.bot];exact fun a v ↦ a.increasing v)

/--
The nucleus which sends everything to ⊤ is the ⊥ sublocale.
-/
instance Nucleus.top : Top (Nucleus X) where
  top := ⟨fun _ ↦ ⊤,(by simp only [le_refl, implies_true]), OrderTop.le_top,
    fun _ _ ↦ Eq.symm (top_inf_eq _)⟩
-- Question for the reviewer: Should these small proofs be simp's or written out statements?

instance : OrderTop (Nucleus X) where
  le_top := (by simp only [Nucleus.top, Nucleus.le_iff, le_top, implies_true])
