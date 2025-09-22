/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# The nondegenerate simplices in the nerve of partially ordered type

In this file, we show that if `X` is a partially ordered type,
then a `n`-simplex `s` of the nerve is nondegenerate iff
the monotone map `s.obj : Fin (n + 1) → X` is strictly monotone.

-/

universe u

open CategoryTheory Simplicial

namespace PartialOrder

variable {X : Type*} [PartialOrder X] {n : ℕ}

lemma mem_range_nerve_σ_iff (s : (nerve X) _⦋n + 1⦌) (i : Fin (n + 1)) :
    s ∈ Set.range ((nerve X).σ i) ↔
      s.obj i.castSucc = s.obj i.succ := by
  constructor
  · rintro ⟨s, rfl⟩
    simp [nerve.σ_obj]
  · intro h
    refine ⟨(nerve X).δ i.castSucc s, ?_⟩
    ext j
    rw [nerve.σ_obj, nerve.δ_obj]
    by_cases h₁ : i.castSucc < j
    · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h₁)
      rw [Fin.predAbove_of_castSucc_lt _ _ h₁, Fin.pred_succ,
        Fin.succAbove_of_le_castSucc _ _ (Fin.le_castSucc_iff.2 h₁)]
    · simp only [not_lt] at h₁
      grind [SimplexCategory.len_mk, → Fin.succAbove_of_castSucc_lt,
        → Fin.predAbove_of_le_castSucc, Fin.castSucc_castPred, Fin.castPred_castSucc,
        Fin.succAbove_castSucc_self, → LE.le.lt_or_eq]

lemma mem_nerve_degenerate_of_eq (s : (nerve X) _⦋n + 1⦌) {i : Fin (n + 1)}
    (hi : s.obj i.castSucc = s.obj i.succ) :
    s ∈ (nerve X).degenerate (n + 1) := by
  simp only [nerve_obj, SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion]
  exact ⟨i, by rwa [mem_range_nerve_σ_iff]⟩

lemma mem_nerve_nonDegenerate_iff_strictMono (s : (nerve X) _⦋n⦌) :
    s ∈ (nerve X).nonDegenerate n ↔ StrictMono s.obj := by
  obtain _ | n := n
  · simpa using Subsingleton.strictMono _
  · rw [← not_iff_not, ← SSet.mem_degenerate_iff_notMem_nonDegenerate,
      Fin.strictMono_iff_lt_succ, SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion]
    simp only [mem_range_nerve_σ_iff, not_forall]
    apply exists_congr
    intro i
    have := s.monotone i.castSucc_le_succ
    grind [SimplexCategory.len_mk, lt_self_iff_false, LE.le.lt_or_eq]

lemma mem_nerve_nonDegenerate_iff_injective (s : (nerve X) _⦋n⦌) :
    s ∈ (nerve X).nonDegenerate n ↔ Function.Injective s.obj := by
  rw [mem_nerve_nonDegenerate_iff_strictMono]
  refine ⟨fun h ↦ h.injective, fun h i j hij ↦ ?_⟩
  obtain h' | h' := (s.monotone hij.le).lt_or_eq
  · exact h'
  · exact ((h h').not_lt hij).elim

end PartialOrder
