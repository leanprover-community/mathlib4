/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
import Mathlib.Order.Closure
import Mathlib.Order.CompleteLattice
import Mathlib.Order.Hom.Lattice

/-!
# Nucleus

Locales are the dual concept to frames. Locale theory is a branch of point-free topology, where
intuitively locales are like topological spaces which may or may not have enough points.
Sublocales of a locale generalize the concept of subspaces in topology to the point-free setting.

A nucleus is an endomorphism of a frame which corresponds to a sublocale.

## References
https://ncatlab.org/nlab/show/sublocale
https://ncatlab.org/nlab/show/nucleus
-/

open Order InfHom

variable {X : Type*} [CompleteLattice X]

/-- A nucleus is an inflationary idempotent `inf`-preserving endomorphism of a semilattice.
In a frame, nuclei correspond to sublocales. -/ -- TODO: Formalise that claim
structure Nucleus (X : Type*) [SemilatticeInf X] extends InfHom X X where
  /-- A `Nucleus` is idempotent.

  Do not use this directly. Instead use `NucleusClass.idempotent`. -/
  idempotent' (x : X) : toFun (toFun x) ≤ toFun x
  /-- A `Nucleus` is increasing.

  Do not use this directly. Instead use `NucleusClass.le_apply`. -/
  le_apply' (x : X) : x ≤ toFun x

/-- `NucleusClass F X` states that F is a type of nuclei. -/
class NucleusClass (F X : Type*) [SemilatticeInf X] [FunLike F X X] extends InfHomClass F X X :
    Prop where
  /-- A nucleus is idempotent. -/
  idempotent (x : X) (f : F) : f (f x) ≤ f x
  /-- A nucleus is increasing. -/
  le_apply (x : X) (f : F) : x ≤ f x

namespace Nucleus

variable {n m : Nucleus X} {x y : X}

instance : FunLike (Nucleus X) X X where
  coe x := x.toFun
  coe_injective' f g h := by  obtain ⟨⟨_, _⟩, _⟩ := f; congr!

lemma toFun_eq_coe (n : Nucleus X) : n.toFun = n := rfl
@[simp] lemma coe_toInfHom (n : Nucleus X) : ⇑n.toInfHom = n := rfl
@[simp] lemma coe_mk (f : InfHom X X) (h1 h2) : ⇑(mk f h1 h2) = f := rfl

instance : NucleusClass (Nucleus X) X where
  idempotent _ _ := idempotent' ..
  le_apply _ _ := le_apply' ..
  map_inf _ _ _ := map_inf' ..

/-- Every `Nucleus` is a `ClosureOperator`. -/
def toClosureOperator (n : Nucleus X) : ClosureOperator X :=
   ClosureOperator.mk' n (OrderHomClass.mono n) n.le_apply' n.idempotent'

lemma idempotent : n (n x) = n x :=
  n.toClosureOperator.idempotent x

lemma le_apply : x ≤ n x :=
  n.toClosureOperator.le_closure x

lemma map_inf : n (x ⊓ y) = n x ⊓ n y :=
  InfHomClass.map_inf n x y

@[ext] lemma ext {m n : Nucleus X} (h : ∀ a, m a = n a) : m = n :=
  DFunLike.ext m n h

/-- A `Nucleus` preserves ⊤. -/
instance : TopHomClass (Nucleus X) X X where
  map_top _ := eq_top_iff.mpr le_apply

instance : PartialOrder (Nucleus X) := .lift (⇑) DFunLike.coe_injective

@[simp, norm_cast] lemma coe_le_coe : ⇑m ≤ n ↔ m ≤ n := .rfl
@[simp, norm_cast] lemma coe_lt_coe : ⇑m < n ↔ m < n := .rfl

/-- The smallest `Nucleus` is the identity. -/
instance instBot : Bot (Nucleus X) where
  bot.toFun x := x
  bot.idempotent' := by simp
  bot.le_apply' := by simp
  bot.map_inf' := by simp

/-- The biggest `Nucleus` sends everything to `⊤`. -/
instance instTop : Top (Nucleus X) where
  top.toFun := ⊤
  top.idempotent' := by simp
  top.le_apply' := by simp
  top.map_inf' := by simp

@[simp, norm_cast] lemma coe_bot : ⇑(⊥ : Nucleus X) = id := rfl
@[simp, norm_cast] lemma coe_top : ⇑(⊤ : Nucleus X) = ⊤ := rfl

@[simp] lemma bot_apply (x : X) : (⊥ : Nucleus X) x = x := rfl
@[simp] lemma top_apply (x : X) : (⊤ : Nucleus X) x = ⊤ := rfl

instance : BoundedOrder (Nucleus X) where
  bot_le _ _ := le_apply
  le_top _ _ := by simp

variable {s : Set (Nucleus X)}

def sInf_fun (s : Set (Nucleus X)) (x : X) := sInf {j x | j ∈ s}

def sInf_fun_increasing : ∀ (x : X), x ≤ sInf_fun s x := by
  simp [sInf_fun, le_apply]

def sInf_fun_idempotent : ∀ (x : X), sInf_fun s (sInf_fun s x) ≤ sInf_fun s x := by
  intro x
  simp only [sInf_fun, le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, sInf_le_iff, lowerBounds]
  intro a ha b h
  rw [← idempotent]
  apply le_trans (h a ha)
  refine OrderHomClass.GCongr.mono a ?_
  simp only [sInf_le_iff, lowerBounds, Set.mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  exact fun b a_1 ↦ a_1 a ha

def sInf_preserves_inf : ∀ (x y : X), sInf_fun s (x ⊓ y) = sInf_fun s x ⊓ sInf_fun s y := by
  simp [sInf_fun]
  intro x y
  apply le_antisymm
  · simp_all only [le_inf_iff, le_sInf_iff, Set.mem_setOf_eq, sInf_le_iff, lowerBounds,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, implies_true, and_self]
  . simp [le_sInf_iff]
    intro a ha

    . apply sInf_le_iff.mpr
      simp only [lowerBounds, Set.mem_setOf_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      exact fun b a_1 => a_1 a ha
    . apply sInf_le_iff.mpr
      simp only [lowerBounds, Set.mem_setOf_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      exact fun b a_1 => a_1 a ha

/--
Quelle Stonespaces S.51
-/
instance : InfSet (Nucleus X) where
  sInf s := ⟨⟨sInf_fun s, sInf_preserves_inf⟩, sInf_fun_idempotent, sInf_fun_increasing⟩

end Nucleus
