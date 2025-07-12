/-
Copyright (c) 2024 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Algebra.Clone.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fin.Basic

/-! This file defines `Clone`s, which represent functions (or generally, some sort of composable
  objects) of different arities that can be "superposed": if the type is indiced as `A : ℕ → Type*`,
  the superposition has signature `A n → (Fin n → A m) → A m`. This is captured in the typeclass
  `Superposable A`.

  A clone must have a `1` element (an arity-1 identity), projection functions of all arities and
  indices, and superposition must be associative.

  The main proofs in this file are how Clones behave with single-argument composition.
  The "usual" operation `Superposable.superpose` takes `n` elements of arity `m` to compose
  into an arity `m` parent, but since Clones also have identities (projections), we can also
  have a way to insert just one argument of arity `k`, resulting in arity `m+k-1`. We define
  this in `Clone.cloneCompose` and prove that it behaves correctl. This is the operation which
  turns Clones into operads (which themselves are absent from Mathlib as of Jan 2025), which is
  why it deserves some interest.

  Interesting examples of Clones are given in `Mathlib.Algebra.Clone.Instances`.
-/

open Superposable

/-- An abstract clone is a set of operations that have composition and all projections.
  Here we define it with the multi-argument composition, typically called "superposition".
  Single-argument composition can be built from this using the identity `proj 1 default`. -/
class Clone {ι : Type*} [One ι] (T : outParam (ι → Type*)) [Unique (T 1)] (A : (ι → Type*))
    extends Superposable T A, OneGradedOne A where
  /-- Superposition is associative -/
  superpose_assoc {n m k : ι} (a : A n) (bs : T n → A m) (cs : T m → A k) :
    (a ∘⚟ bs) ∘⚟ cs = a ∘⚟ (bs · ∘⚟ cs)
  /-- All projections are accessible -/
  proj (n : ι) (k : T n) : A n
  /-- Projections are compatible on the left -/
  proj_left {n m : ι} (l : T n) (cs : T n → A m) : proj n l ∘⚟ cs = cs l
  /-- Projections are compatible on the right -/
  proj_right {n : ι} (c : A n) : c ∘⚟ (proj n ·) = c
  /-- The "1" element is the unary projection -/
  one_proj : 1 = proj 1 default

namespace Clone
section generic

variable {ι : Type*} [One ι] {T A : ι → Type*} [Unique (T 1)] [Clone T A]

@[simp]
theorem clone_proj_left {m n : ι} (l : T n) (cs : T n → A m) :
    proj n l ∘⚟ cs = cs l :=
  proj_left l cs

@[simp]
theorem clone_proj_right {n : ι} (c : A n) : c ∘⚟ (proj n ·) = c :=
  proj_right c

@[simp]
theorem clone_id_left {n : ι} (a : T 1 → A n) : 1 ∘⚟ a = a default := by
  rw [one_proj]
  exact clone_proj_left default a

end generic
section nat
--This padding is fairly specialized to nats / fins

variable {A : ℕ → Type*} [Clone Fin A]

/-- Pad a m-arity element of a clone to a larger arity, by adding projections that ignore
 the left- and right-most elements. This replaces the `k`th element out of `n` with the `m`
 many arguments of `p`. -/
def clonePadTo {m : ℕ} (p : A m) (n : ℕ) (k : Fin n) : A (n+m-1) :=
  p ∘⚟ fun (i : Fin _) ↦ proj (n+m-1) ⟨k + i, by omega⟩

@[simp]
theorem clonePadTo_zero {m} (p : A m) (k : Fin 1) :
    clonePadTo p 1 k = (Nat.one_add_sub_one m).symm ▸ p := by
  apply eq_of_heq
  have := Nat.one_add_sub_one m
  nth_rewrite 2 [← proj_right p]
  simp only [heq_rec_iff_heq, clonePadTo, Fin.val_eq_zero, zero_add]
  congr!

/-- Clones are defined with the multi-argument superpose operation, but this gives a natural
 one-argument composition operation. -/
def cloneCompose {n m : ℕ} (a : A n) (p : Fin n) (b : A m) : A (n + m - 1) :=
  a ∘⚟ (
    fun k ↦ if hkp1 : k = p.1 then
        clonePadTo b n k
      else if hkp : k < p.1 then
        proj (n+m-1) ⟨k.val, by omega⟩
      else
        proj (n+m-1) ⟨k.val+m-1, by omega⟩
      )

@[simp]
theorem cloneCompose_id {n : ℕ} (a : A n) (b : Fin n) : cloneCompose a b (1 : A 1) = a := by
  simp [cloneCompose, clonePadTo]

/-- The `cloneCompose` one-argument composition induced by a clone's
  superpose operation is associative. -/
theorem cloneCompose_assoc (a b c : Sigma A) (p1 : Fin a.fst) (p2 : Fin b.fst) :
  HEq (cloneCompose a.snd p1 (cloneCompose b.snd p2 c.snd))
  (cloneCompose (cloneCompose a.snd p1 b.snd) (p1.hAdd p2) c.snd) := by
    dsimp [cloneCompose]
    rw [superpose_assoc]
    congr! 2 with _ x y hxy
    · have := p2.2; omega
    subst hxy
    simp only [Fin.val_inj, Fin.val_fin_lt]
    split
    next hyp1 =>
      simp only [hyp1, clonePadTo, superpose_assoc, Fin.hAdd]
      congr! 2 with k _ hk
      subst hk
      rw [clone_proj_left]
      simp only [Fin.val_inj, Fin.val_fin_lt]
      split
      next hkp2 =>
        subst hkp2
        simp only [dite_true, superpose_assoc, clone_proj_left, clonePadTo]
        congr! 4 with a b rfl
        rw [add_assoc]
      next hkp2 =>
        simp only [Fin.mk.injEq, add_right_inj, Fin.mk_lt_mk, add_lt_add_iff_left,
          Fin.val_fin_lt, Fin.val_inj, if_neg hkp2]
        split <;> simp only [clone_proj_left] <;> congr! 2
        next hkp2' =>
          rw [← Nat.add_sub_assoc, add_assoc]
          omega
    next hyp1 =>
      split
      next hxp1 =>
        have : x.1 < p1.1 + p2.1 := by exact Nat.lt_add_right p2.1 hxp1
        simp only [Fin.hAdd, clonePadTo, clone_proj_left, Fin.mk.injEq, this, this.ne, Fin.mk_lt_mk,
          dite_true, dite_false]
        congr!
      next hxp1 =>
        simp only [Fin.hAdd, clone_proj_left, Fin.mk.injEq, Fin.mk_lt_mk]
        rw [dif_neg, dif_neg]
        · congr! 2
          omega
        · omega
        · omega

/-- The `cloneCompose` one-argument composition induced by a clone's superpose operation
  is commutative: it doesn't matter whether the p1'th or p2'th argument is provided first. -/
theorem cloneCompse_comm (a b c : Sigma A) (p1 p2 : Fin a.fst) (hp: p1 < p2)
  (p1' : Fin (a.fst + c.fst - 1)) (p2' : Fin (a.fst + b.fst - 1))
  (hp1' : p1.val = p1'.val) (hp2' : p2'.val = p2.val + b.fst - 1) :
  HEq (cloneCompose (cloneCompose a.snd p1 b.snd) p2' c.snd)
      (cloneCompose (cloneCompose a.snd p2 c.snd) p1' b.snd) := by
  rcases p1 with ⟨p1, hp1⟩
  rcases p2 with ⟨p2, hp2⟩
  rcases p1' with ⟨p1', _⟩
  rcases p2' with ⟨p2', _⟩
  subst hp2'
  subst hp1'
  dsimp [cloneCompose]
  rw [superpose_assoc, superpose_assoc]
  congr! 1
  · omega
  congr! 1 with ⟨k, hk⟩ ⟨k2, hk2⟩ hkk2
  rw [Fin.mk.injEq] at hkk2
  subst hkk2
  dsimp [Fin.val, Fin.addNat, Fin.hAdd]
  replace hp : p1 < p2 := hp
  split
  next hkp1 =>
    subst k
    have hp1p2 : p1 ≠ p2 := hp.ne
    simp only [hp1p2, hp, clonePadTo, superpose_assoc]
    simp only [clone_proj_left, lt_self_iff_false, ↓reduceDIte]
    congr! with ⟨k2, hk2⟩ ⟨k3, hk3⟩ hk2k3
    have h₁ : p1 + k2 < p2 + b.fst - 1 := by omega
    simp only [h₁, h₁.ne, ↓reduceDIte]
    congr!
    rwa [Fin.mk.injEq] at hk2k3
  next =>
    split
    next hkp1 =>
      have h₁ : k < p2 := by omega
      have h₂ : k < p2 + b.fst - 1 := by omega
      simp only [clone_proj_left, hkp1, h₁, h₂, hkp1.ne, h₁.ne, h₂.ne, dite_true, dite_false]
      congr!
    next =>
      have hkp1 : k > p1 := by omega
      split
      next hkp2 =>
        rw [clone_proj_left, dif_pos, clonePadTo, clonePadTo, superpose_assoc]
        swap
        · dsimp
          omega
        congr! with ⟨k2, hk2⟩ ⟨k3, hk3⟩ hk2k3
        rw [Fin.mk.injEq] at hk2k3
        subst hk2k3
        rw [clone_proj_left]
        dsimp
        rw [dif_neg, dif_neg]
        · congr! 2
          omega
        · omega
        · omega
      next hkp2 =>
        split
        next hkp2 =>
          simp only [clone_proj_left]
          have hkbp2 : k + b.fst - 1 < p2 + b.fst - 1 := by omega
          rw [dif_neg hkbp2.ne, dif_pos hkbp2, dif_neg hkp1.ne.symm, dif_neg (Nat.lt_asymm hkp1)]
          congr!
        next =>
          simp only [clone_proj_left]
          replace hkp2 : k > p2 := by omega
          have hkbp2 : k + b.fst - 1 > p2 + b.fst - 1 := by omega
          have hkcp1 : k + c.fst - 1 > p1 := by omega
          rw [dif_neg hkbp2.ne.symm, dif_neg (Nat.lt_asymm hkbp2)]
          rw [dif_neg hkcp1.ne.symm, dif_neg (Nat.lt_asymm hkcp1)]
          congr! 2
          omega

end nat
end Clone
