/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Results about `CovariantClass G α HSMul.hSMul LE.le`

When working with group actions rather than modules, we drop the `0 < c` condition.

Notably these are relevant for pointwise actions on set-like objects.
-/

public section

variable {ι : Sort*} {M α : Type*}

theorem smul_mono_right [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) : Monotone (HSMul.hSMul m : α → α) :=
  fun _ _ => CovariantClass.elim _

/-- A copy of `smul_mono_right` that is understood by `gcongr`. -/
@[gcongr]
theorem smul_le_smul_left [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) {a b : α} (h : a ≤ b) :
    m • a ≤ m • b :=
  smul_mono_right _ h

theorem smul_inf_le [SMul M α] [SemilatticeInf α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) (a₁ a₂ : α) : m • (a₁ ⊓ a₂) ≤ m • a₁ ⊓ m • a₂ :=
  (smul_mono_right _).map_inf_le _ _

theorem smul_iInf_le [SMul M α] [CompleteLattice α] [CovariantClass M α HSMul.hSMul LE.le]
    {m : M} {t : ι → α} :
    m • iInf t ≤ ⨅ i, m • t i :=
  le_iInf fun _ => smul_mono_right _ (iInf_le _ _)

theorem smul_strictMono_right [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LT.lt]
    (m : M) : StrictMono (HSMul.hSMul m : α → α) :=
  fun _ _ => CovariantClass.elim _

section Monoid

variable [Monoid M] [Preorder α] [MulAction M α] [CovariantClass M α HSMul.hSMul LE.le]

lemma le_pow_smul {m : M} {a : α} (h : a ≤ m • a) (n : ℕ) : a ≤ m ^ n • a := by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n hn =>
    rw [pow_succ', mul_smul]
    exact h.trans (smul_mono_right m hn)

lemma pow_smul_le {m : M} {a : α} (h : m • a ≤ a) (n : ℕ) : m ^ n • a ≤ a := by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n hn =>
    rw [pow_succ', mul_smul]
    exact (smul_mono_right m hn).trans h

end Monoid

section Group

variable {G : Type*} [Group G] [PartialOrder α] [MulAction G α]
  [CovariantClass G α HSMul.hSMul LE.le]

/-- A group acting monotonically fixes `⊥`. -/
@[simp]
theorem smul_bot [OrderBot α] (g : G) : g • (⊥ : α) = ⊥ := by
  simpa using smul_le_smul_left g (bot_le : (⊥ : α) ≤ g⁻¹ • ⊥)

/-- A group acting monotonically fixes `⊤`. -/
@[simp]
theorem smul_top [OrderTop α] (g : G) : g • (⊤ : α) = ⊤ := by
  simpa using smul_le_smul_left g (le_top : g⁻¹ • (⊤ : α) ≤ ⊤)

end Group
