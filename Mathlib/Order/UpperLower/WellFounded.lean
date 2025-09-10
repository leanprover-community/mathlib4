/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Order.WellQuasiOrder

/-!
# Well-founded instances

We show that `LowerSet α` and `UpperSet α` are well-founded whenever `α` is a WQO.
-/

variable {α : Type*} [Preorder α] [WellQuasiOrderedLE α]

instance : WellFoundedLT (LowerSet α) where
  wf := by
    rw [RelEmbedding.wellFounded_iff_isEmpty]
    refine ⟨fun f ↦ ?_⟩
    have hf' (n : ℕ) := Set.diff_nonempty.2 (f.2.2 n.lt_succ_self).not_ge
    choose g hg using hf'
    obtain ⟨m, n, h, h'⟩ := wellQuasiOrdered_le g
    apply not_not.2 <| (f n).lower' h' (hg n).1
    obtain rfl | h := h.nat_succ_le.eq_or_lt
    · exact (hg _).2
    · exact ((hg _).2 <| (f.map_rel_iff.2 h).le ·)

instance : WellFoundedLT (UpperSet α) :=
  upperSetIsoLowerSet.toRelIsoLT.toRelEmbedding.isWellFounded
