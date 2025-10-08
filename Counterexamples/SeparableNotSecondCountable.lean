/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Real.Cardinality

/-!
# Example of a linear order which is a separable space but is not a second countable topology

In this file we provide an example of a linear order
such that the order topology is a separable space but is not a second countable topology.

The example is `ℝ ×ₗ Bool` which is the real line with each point duplicated
so that the duplicate is greater than the original point
and points with different real values are compared by these values.
-/

open Set TopologicalSpace

namespace RealProdLexBool

instance instTopologicalSpace : TopologicalSpace (ℝ ×ₗ Bool) := Preorder.topology _
instance instOrderTopology : OrderTopology (ℝ ×ₗ Bool) := ⟨rfl⟩
noncomputable instance instLinearOrder : LinearOrder (ℝ ×ₗ Bool) := inferInstance

instance instSeparableSpace : SeparableSpace (ℝ ×ₗ Bool) := by
  refine ⟨⟨range fun q : ℚ ↦ toLex (q, false), countable_range _, ?_⟩⟩
  simp only [dense_iff_inter_open, Set.Nonempty, toLex.surjective.exists]
  rintro U hUo ⟨⟨x, _ | _⟩, hx⟩
  · rcases exists_Ioc_subset_of_mem_nhds (hUo.mem_nhds hx) (exists_lt _) with ⟨y, hyx, hyU⟩
    rcases toLex.surjective y with ⟨y, rfl⟩
    have : y.1 < x := by simpa [Prod.Lex.toLex_lt_toLex, y.2.false_le.not_gt] using hyx
    rcases exists_rat_btwn this with ⟨q, hyq, hqx⟩
    refine ⟨(q, false), hyU ?_, mem_range_self _⟩
    simp [Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_lt_toLex, hyq, hqx]
  · rcases exists_Ico_subset_of_mem_nhds (hUo.mem_nhds hx) (exists_gt _) with ⟨y, hyx, hyU⟩
    rcases toLex.surjective y with ⟨y, rfl⟩
    have : x < y.1 := by simpa [Prod.Lex.toLex_lt_toLex, y.2.le_true.not_gt] using hyx
    rcases exists_rat_btwn this with ⟨q, hyq, hqx⟩
    refine ⟨(q, false), hyU ?_, mem_range_self _⟩
    simp [Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_lt_toLex, hyq, hqx]

theorem not_secondCountableTopology : ¬SecondCountableTopology (ℝ ×ₗ Bool) := by
  intro h
  have : {x : ℝ ×ₗ Bool | (ofLex x).2}.Countable := by
    simpa [Prod.Lex.covBy_iff, Bool.covBy_iff, exists_or, not_covBy, (Bool.le_true _).not_gt,
      (Bool.false_le _).lt_iff_ne] using countable_setOf_covBy_left (α := ℝ ×ₗ Bool)
  refine not_countable_univ <| (this.image fun x ↦ (ofLex x).1).mono fun x _ ↦ ?_
  exact ⟨toLex (x, true), rfl, rfl⟩

end RealProdLexBool
