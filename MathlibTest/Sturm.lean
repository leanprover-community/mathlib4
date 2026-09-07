import Mathlib.Analysis.Polynomial.Sturm.Certificate
import Mathlib.Tactic.NormNum

open Polynomial Sturm

private theorem linearChain : IsSturmChain (X : ℝ[X]) [X, 1] := by
  have h : RemainderChain [(X : ℝ[X]), 1] := by
    simpa using RemainderChain.pair X_ne_zero (one_ne_zero : (1 : ℝ) ≠ 0)
  exact h.isSturmChain (a := 1) (by norm_num) (by simp)

-- A root at the right endpoint is counted.
example : ((X : ℝ[X]).roots.filter (fun r => r ∈ Set.Ioc (-1) 0)).card = 1 := by
  simpa [sturmVar, signVariations, countSignChanges] using
    linearChain.sturm_Ioc (by simp) (show (-1 : ℝ) ≤ 0 by norm_num)

-- A root at the left endpoint is excluded.
example : ((X : ℝ[X]).roots.filter (fun r => r ∈ Set.Ioc 0 1)).card = 0 := by
  convert linearChain.sturm_Ioc (by simp) (show (0 : ℝ) ≤ 1 by norm_num) using 1 <;>
    norm_num [sturmVar, signVariations, countSignChanges]

-- Equal endpoints are permitted, including when that endpoint is a root.
example : ((X : ℝ[X]).roots.filter (fun r => r ∈ Set.Ioc 0 0)).card = 0 := by
  convert linearChain.sturm_Ioc (by simp) (le_refl (0 : ℝ)) using 1 <;>
    norm_num [sturmVar, signVariations, countSignChanges]

-- The single-entry chain of a nonzero constant is a valid Sturm chain.
private theorem constantChain : IsSturmChain (1 : ℝ[X]) [1] where
  head := rfl
  root_flank := by simp [Polynomial.IsRoot]
  nonzero_mem := by simp
  interior_alternates := by
    intro i x a b c ha hb hc
    cases i <;> simp at hc
  last_no_root := by simp

example : (1 : ℝ[X]).roots.card = 0 := by
  convert constantChain.sturm (by simp) using 1 <;>
    norm_num [sturmVarNegInf, sturmVarPosInf, signVariations, countSignChanges]
