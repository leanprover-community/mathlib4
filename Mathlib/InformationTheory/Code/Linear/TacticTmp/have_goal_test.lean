import Mathlib.InformationTheory.Code.Linear.TacticTmp.have_goal
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases

opaque T:Type
axiom func : T → T → T


lemma foo (a b c d:T) (h1 : a = c) (h2:b = d) : ![a,b,func a b] = ![c,d,func c d] := by
  ext i
  fin_cases i <;> simp
  have_goal n1 := h1
  have_goal n2 := h2
  rw [n1,n2]

example (f:Fin 4 → Fin 4): f = f := by
  ext i : 1
  let foo : f i = f i := rfl
  fin_cases i <;> exact foo



lemma bar (a b c d:T) : True ∧ (a = c ∧ b = d → ![func a b,b,a] = ![func c d,d,c]) := by
  constructor
  skip_goal
  intro ⟨h1,h2⟩
  ext i
  fin_cases i <;> simp
  skip_goal
  have_goal n2 := h2
  have_goal n3 := h1
  skip_goal
  rw [n2,n3]
  -- neither n2 nor n3 are in context here, as those statements aren't valid in this context.
  trivial
