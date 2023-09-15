import Std
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Have

/-!
# Abstract description of integer linear programming problems.

We define `LinearCombo`, `Problem`, and `DisjunctiveProblem`.
These are abstract descriptions of integer linear programming problems.

In particular, they are intended to be easy to reason about,
but need not be fast to compute with.

-/

structure LinearCombo where
  const : Int
  coeffs : List Int
deriving DecidableEq

namespace LinearCombo

def eval (lc : LinearCombo) (values : List Int) : Int :=
  (lc.coeffs.zip values).foldl (fun r ⟨c, v⟩ => r + c * v) lc.const

-- Prove some alternative formulas for `eval`? Which to use?
-- theorem eval_eq (lc : LinearCombo) (values : List Int) :
--   lc.eval values = lc.const + (List.zipWith (· * ·) lc.coeffs values).sum := sorry

def evalZero (lc : LinearCombo) (values : List Int) : Prop := lc.eval values = 0
def evalNonneg (lc : LinearCombo) (values : List Int) : Prop := lc.eval values ≥ 0

end LinearCombo

structure Problem where
  possible : Bool
  equalities : List LinearCombo
  inequalities : List LinearCombo

namespace Problem

structure sat (p : Problem) (values : List Int) : Prop where
  possible : p.possible = true
  equalities : lc ∈ p.equalities → lc.evalZero values
  inequalities : lc ∈ p.inequalities → lc.evalNonneg values

def solutions (p : Problem) : Type :=
  { values // p.sat values }

instance : CoeSort Problem Type where
  coe := solutions

def unsat (p : Problem) : Prop := p → False

inductive Solution (p : Problem)
| sat : p.solutions → Solution p
| unsat : p.unsat → Solution p

end Problem

structure DisjunctiveProblem where
  problems : List Problem

namespace DisjunctiveProblem

def sat (d : DisjunctiveProblem) (values : List Int) : Prop :=
  ∃ p ∈ d.problems, p.sat values

def solutions (p : DisjunctiveProblem) : Type :=
  { values // p.sat values }

instance : CoeSort DisjunctiveProblem Type where
  coe := solutions

def unsat (p : DisjunctiveProblem) : Prop := p → False

inductive Solution (d : DisjunctiveProblem)
| sat : d.sat values → Solution d
| unsat : d.unsat → Solution d

end DisjunctiveProblem

namespace Problem

@[simps]
def eraseInequality (p : Problem) (lc : LinearCombo) : Problem :=
  { p with inequalities := p.inequalities.erase lc }

/-- Any solution gives a solution after erasing an inequality. -/
def eraseInequality_map (p : Problem) (lc : LinearCombo) : p → p.eraseInequality lc :=
  fun ⟨v, s⟩ => ⟨v, { s with
    inequalities := fun m => s.inequalities (by simp at m; apply List.mem_of_mem_erase m) }⟩

end Problem

/-!
Define `a ≤ b` on linear combinations to mean that the coefficients are identical,
and the constant terms satisfy `≤`.

We show:
```
a < b → a ∈ p.inequalities → p.eraseInequality b → p
```
-/

namespace LinearCombo

def le (a b : LinearCombo) : Prop :=
  a.coeffs = b.coeffs ∧ a.const ≤ b.const

instance : LE LinearCombo := ⟨le⟩

theorem eval_le_of_le {a b : LinearCombo} (h : a ≤ b) : a.eval v ≤ b.eval v := by
  simp [LinearCombo.eval]
  rcases a with ⟨a, coeffs⟩; rcases b with ⟨b, bcoeffs⟩
  rcases h with ⟨rfl, h⟩
  simp_all
  generalize List.zip _ _ = p
  -- This should be some general fact, but we can just bash it out.
  -- Perhaps might be easier with alternative formulas for `eval`.
  induction p generalizing a b h with
  | nil => simpa
  | cons x p ih =>
    simp only [List.foldl_cons]
    apply ih
    apply Int.add_le_add_right h

theorem evalNonneg_of_le {a b : LinearCombo} (h : a ≤ b) : a.evalNonneg v → b.evalNonneg v :=
  fun w => Int.le_trans w (eval_le_of_le h)

def lt (a b : LinearCombo) : Prop :=
  a ≤ b ∧ a ≠ b

instance : LT LinearCombo := ⟨lt⟩

-- theorem eval_lt_of_lt {a b : LinearCombo} (h : a < b) : a.eval v < b.eval c := sorry

def neg (lc : LinearCombo) : LinearCombo where
  const := -lc.const
  coeffs := lc.coeffs.map (- ·)

end LinearCombo

namespace Problem

-- TODO find a home
theorem List.mem_iff_mem_erase_or_eq [DecidableEq α] (l : List α) (a b : α) :
    a ∈ l ↔ (a ∈ l.erase b ∨ (a = b ∧ b ∈ l)) := by
  by_cases h : a = b
  · subst h
    simp [or_iff_right_of_imp List.mem_of_mem_erase]
  · simp_all

def eraseRedundantInequality
    (p : Problem) {a b : LinearCombo} (lt : a < b) (m : a ∈ p.inequalities) :
    p.eraseInequality b → p :=
  fun ⟨v, s⟩ => ⟨v, { s with
    inequalities := fun m' => by
      rw [List.mem_iff_mem_erase_or_eq _ _ b] at m'
      rcases m' with m' | ⟨rfl, m'⟩
      · apply s.inequalities
        exact m'
      · rcases lt with ⟨le, ne⟩
        apply LinearCombo.evalNonneg_of_le le
        apply s.inequalities
        simpa using (List.mem_erase_of_ne ne).mpr m }⟩

end Problem
