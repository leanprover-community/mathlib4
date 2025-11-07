/-
Copyright (c) 2025 María Inés de Frutos-Fernández . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Bounds.Image

/-!
# Lemmas about `BddAbove`
-/

open Set

/-- A variant of `BddAbove.range_comp` that assumes that `f` is nonnegative and `g` is monotone on
  nonnegative values. -/
lemma BddAbove.range_comp_of_nonneg {α β γ : Type*} [Nonempty α] [Preorder β] [Zero β] [Preorder γ]
    {f : α → β} {g : β → γ} (hf : BddAbove (range f)) (hf0 : 0 ≤ f)
    (hg : MonotoneOn g {x : β | 0 ≤ x}) : BddAbove (range (fun x => g (f x))) := by
  suffices hg' : BddAbove (g '' range f) by
    rwa [← Function.comp_def, Set.range_comp]
  apply hg.map_bddAbove (by rintro x ⟨a, rfl⟩; exact hf0 a)
  obtain ⟨b, hb⟩ := hf
  use b, hb
  simp only [mem_upperBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hb
  exact le_trans (hf0 Classical.ofNonempty) (hb Classical.ofNonempty)

/-- If `u v : α → β` are nonnegative and bounded above, then `u * v` is bounded above. -/
theorem bddAbove_range_mul {α β : Type*} [Nonempty α] {u v : α → β} [Preorder β] [Zero β] [Mul β]
    [PosMulMono β] [MulPosMono β] (hu : BddAbove (Set.range u)) (hu0 : 0 ≤ u)
    (hv : BddAbove (Set.range v)) (hv0 : 0 ≤ v) : BddAbove (Set.range (u * v)) :=
  letI : Zero (β × β) := ⟨(0, 0)⟩
  BddAbove.range_comp_of_nonneg (f := fun i ↦ (u i, v i)) (g := fun x ↦ x.1 * x.2)
    (bddAbove_range_prod.mpr ⟨hu, hv⟩) (fun x ↦ ⟨hu0 x, hv0 x⟩) ((monotone_fst.monotoneOn _).mul
      (monotone_snd.monotoneOn _) (fun _ hx ↦ hx.1) (fun _ hx ↦ hx.2))
