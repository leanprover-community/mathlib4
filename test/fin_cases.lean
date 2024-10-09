import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Order.Interval.Finset.Nat

example {x : Nat} (h : x ∈ [0, 2, 37]) : x ≤ 57 := by
  fin_cases h
  repeat decide

example {x : Nat} (h : x ∈ [0, 2, 37]) : x = 0 ∨ x = 2 ∨ x = 37 := by
  fin_cases h
  repeat simp

example {x : Nat} (h : x ∈ List.range 5) : x ≤ 4 := by
  fin_cases h
  repeat decide

example {p : Fin 4 → Prop} (i : Fin 4) (h : p i) : p i := by
  fin_cases i
  repeat exact h

example (f : Nat → Prop) (p : Fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val := by
  fin_cases p
  all_goals
    assumption

example (f : Nat → Prop) (p : Fin 0) : f p.val := by
  fin_cases p

example (x2 : Fin 2) (x3 : Fin 3) : True := by
  fin_cases x2, x3
  all_goals trivial

-- Checking that `fin_cases` can handle a metavariable for the type
example (p : ℕ) (h2 : 2 < p) (h5 : p < 5) : p = 3 ∨ p = 4 := by
  have hp : ?_ := ?foo
  case foo => exact (Finset.mem_Ioo).2 ⟨h2, h5⟩
  fin_cases hp
  · norm_num
  · norm_num

-- TODO Restore the remaining tests from mathlib3:
-- Some of these test the `with` and `using` clauses which haven't been re-implemented.

example (x2 : Fin 2) (x3 : Fin 3) (n : Nat) (y : Fin n) : x2.val * x3.val = x3.val * x2.val := by
  fin_cases x2 <;> fin_cases x3
  fail_if_success
    fin_cases y
  all_goals rfl

-- example (x : ℕ) (h : x ∈ [2,3,5,7]) : True := by
--   fail_if_success
--     fin_cases h with [3,3,5,7]
--   trivial

-- example (x : List Nat) (h : x ∈ [[1],[2]]) : x.length = 1 := by
--   fin_cases h with [[1],[1+1]]
--   · simp
--   · guard_target = [1 + 1].length = 1
--     simp

--  -- testing that `with` arguments are elaborated with respect to the expected type:
-- example (x : Int) (h : x ∈ ([2,3] : List Int)) : x = 2 ∨ x = 3 := by
--   fin_cases h with [2,3]
--   all_goals simp

-- example (n : ℕ) (h : n % 3 ∈ [0,1]) : True := by
--   fin_cases h
--   · guard_hyp h : n % 3 = 0
--     trivial
--   · guard_hyp h : n % 3 = 1
--     trivial

-- instance (n : ℕ) : Decidable (Nat.Prime n) := decidablePrime_1 n
-- example (x : ℕ) (h : x ∈ (List.range 10).filter Nat.prime) : x = 2 ∨ x = 3 ∨ x = 5 ∨ x = 7 := by
--   fin_cases h <;> decide

-- open Equiv.Perm
-- example (x : (Σ (a : Fin 4), Fin 4)) (h : x ∈ finPairsLT 4) : x.1.val < 4 := by
--   fin_cases h; simp
--   any_goals exact dec_trivial

-- /-
-- In some circumstances involving `let`,
-- the temporary hypothesis that `fin_cases` creates does not get deleted.
-- We test that this is correctly named and that the name can be changed.

-- Note: after `fin_cases`, we have `this : (a : Fin 3) = (0 : Fin (2 + 1))`
-- for some reason. I don't know why, and it complicates the test.
-- -/
-- example (f : ℕ → Fin 3) : true := by
--   let a := f 3
--   fin_cases a
--   guard_hyp a := f 3
--   guard_hyp this : a = (0 : Fin (2 + 1))
--   trivial; trivial

--   let b := f 2
--   fin_cases b using what
--   guard_hyp what : b = (0 : Fin (2 + 1))

--   all_goals trivial

-- /-
-- The behavior above can be worked around with `fin_cases with`.
-- -/
-- example (f : ℕ → Fin 3) : true := by
--   let a := f 3
--   fin_cases a with [0, 1, 2]
--   guard_hyp a := f 3
--   guard_hyp this : a = 0
--   trivial
--   guard_hyp this : a = 1
--   trivial
--   guard_hyp this : a = 2
--   let b := f 2
--   fin_cases b with [0, 1, 2] using what
--   guard_hyp what : b = 0
--   all_goals trivial
