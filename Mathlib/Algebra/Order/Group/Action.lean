/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Cases

/-!
# Results about `SMulLeftMono G α`

When working with group actions rather than modules, we drop the `0 < c` condition.

Notably these are relevant for pointwise actions on set-like objects.
-/

variable {ι : Sort*} {M α : Type*}

theorem smul_mono_right [SMul M α] [Preorder α] [SMulLeftMono M α]
    (m : M) : Monotone (HSMul.hSMul m : α → α) :=
  fun _ _ => smul_le_smul_left _

theorem smul_inf_le [SMul M α] [SemilatticeInf α] [SMulLeftMono M α]
    (m : M) (a₁ a₂ : α) : m • (a₁ ⊓ a₂) ≤ m • a₁ ⊓ m • a₂ :=
  (smul_mono_right _).map_inf_le _ _

theorem smul_iInf_le [SMul M α] [CompleteLattice α] [SMulLeftMono M α]
    {m : M} {t : ι → α} :
    m • iInf t ≤ ⨅ i, m • t i :=
  le_iInf fun _ => smul_mono_right _ (iInf_le _ _)

theorem smul_strictMono_right [SMul M α] [Preorder α] [SMulLeftStrictMono M α]
    (m : M) : StrictMono (HSMul.hSMul m : α → α) :=
  fun _ _ => smul_lt_smul_left _

lemma le_pow_smul {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [SMulLeftMono G α]
    (h : a ≤ g • a) (n : ℕ) : a ≤ g ^ n • a := by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n hn =>
    rw [pow_succ', mul_smul]
    exact h.trans (smul_mono_right g hn)

lemma pow_smul_le {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [SMulLeftMono G α]
    (h : g • a ≤ a) (n : ℕ) : g ^ n • a ≤ a := by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n hn =>
    rw [pow_succ', mul_smul]
    exact (smul_mono_right g hn).trans h
