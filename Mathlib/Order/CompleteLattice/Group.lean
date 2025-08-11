/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
import Mathlib.Order.CompleteLattice.Basic

/-! # Complete lattices and groups -/

variable {α : Type*} {ι : Sort*} {κ : ι → Sort*}
  [CompleteLattice α] [Mul α] [MulLeftMono α] [MulRightMono α]

@[to_additive]
lemma iSup_mul_le (u v : ι → α) :
    ⨆ i, u i * v i ≤ (⨆ i, u i) * ⨆ i, v i :=
  iSup_le fun _ ↦ mul_le_mul' (le_iSup ..) (le_iSup ..)

@[to_additive]
lemma le_iInf_mul (u v : ι → α) :
    (⨅ i, u i) * ⨅ i, v i ≤ ⨅ i, u i * v i :=
  iSup_mul_le (α := αᵒᵈ) ..

@[to_additive]
lemma iSup₂_mul_le (u v : (i : ι) → κ i → α) :
    ⨆ (i) (j), u i j * v i j ≤ (⨆ (i) (j), u i j) * ⨆ (i) (j), v i j := by
  refine le_trans ?_ (iSup_mul_le ..)
  gcongr
  exact iSup_mul_le ..

@[to_additive]
lemma le_iInf₂_mul (u v : (i : ι) → κ i → α) :
    (⨅ (i) (j), u i j) * ⨅ (i) (j), v i j ≤ ⨅ (i) (j), u i j * v i j :=
  iSup₂_mul_le (α := αᵒᵈ) ..
