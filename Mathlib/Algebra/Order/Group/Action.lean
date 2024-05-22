/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Order.CompleteLattice

/-!
# Results about `CovariantClass G α HSMul.hSMul LE.le`

When working with group actions rather than modules, we drop the `0 < c` condition.

Notably these are relevant for pointwise actions on set-like objects.
-/

variable {ι : Sort*} {M α : Type*}

/-- TODO -/
class SMulLeftMono (M α : Type*) [SMul M α] [LE α] : Prop where
  /-- TODO -/
  protected elim : Covariant M α (· • ·) (· ≤ ·)

/-- TODO -/
class SMulStrictMono (M α : Type*) [SMul M α] [LT α] : Prop where
  /-- TODO -/
  protected elim : Covariant M α (· • ·) (· < ·)

theorem smul_mono_right [SMul M α] [Preorder α] [SMulLeftMono M α]
    (m : M) : Monotone (HSMul.hSMul m : α → α) :=
  fun _ _ => SMulLeftMono.elim _

/-- A copy of `smul_mono_right` that is understood by `gcongr`. -/
@[gcongr]
theorem smul_le_smul_left [SMul M α] [Preorder α] [SMulLeftMono M α]
    (m : M) {a b : α} (h : a ≤ b) :
    m • a ≤ m • b :=
  smul_mono_right _ h

theorem smul_inf_le [SMul M α] [SemilatticeInf α] [SMulLeftMono M α]
    (m : M) (a₁ a₂ : α) : m • (a₁ ⊓ a₂) ≤ m • a₁ ⊓ m • a₂ :=
  (smul_mono_right _).map_inf_le _ _

theorem smul_iInf_le [SMul M α] [CompleteLattice α] [SMulLeftMono M α]
    {m : M} {t : ι → α} :
    m • iInf t ≤ ⨅ i, m • t i :=
  le_iInf fun _ => smul_mono_right _ (iInf_le _ _)

theorem smul_strictMono_right [SMul M α] [Preorder α] [SMulStrictMono M α]
    (m : M) : StrictMono (HSMul.hSMul m : α → α) :=
  fun _ _ => SMulStrictMono.elim _
