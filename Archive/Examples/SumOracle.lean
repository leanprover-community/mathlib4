import Mathlib.Computability.QueryComplexity.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.FreeMonoid.Basic

namespace ArithOracle

inductive AddQuery (α : Type*)
| add (x y : α)
| zero

open QueryComplexity.Comp (query)

abbrev Comp (α : Type*) := QueryComplexity.Comp (AddQuery α) (fun _ => α)

variable {α β}

/-- Sum the elements of `A`. -/
def sum {n : ℕ} (A : Fin n → α) : Comp α α := do
  List.ofFn A |>.foldrM
    (fun x a => query (.add x a))
    (← query .zero)

/-- The cost and output of a computation in `Comp`. -/
def Comp.run [Zero α] [Add α] (f : Comp α β) : β × ℕ :=
  StateT.run (s := 0) (m := Id) <|
    f.runM fun
      | .add x y => do
        modify fun n => n + 1
        return x + y
      | .zero => return 0

/-- `sum` computes the sum of a list, using `n` additions. -/
theorem sum_run [Zero α] [Add α] (n : ℕ) (A : Fin n → α) :
    (sum A).run = ((List.ofFn A).sum, n) := by
  induction n with
  | zero =>
    simp [sum, Comp.run]
  | succ n hn =>
    simp_all [sum, Comp.run]

/-- The computation must use at least `n` additions to sum `n` elements. -/
-- TODO: is this false because `sum` can be `if α = ℕ then cheat else dont_cheat`?
theorem infi_sum_run_le (n : ℕ)
    (sum : type_of% @sum)
    (h : ∀ {α} [Zero α] [Add α] (A : Fin n → α), (sum A).run.1 = (List.ofFn A).sum) :
    (⨅ (h : Σ (α: Type) (_ : Zero α) (_ : Add α), (Fin n → α)), match h with
      | ⟨α, _, _, A⟩ => (sum A).run.2 : ℕ∞) ≤ n := by
  specialize h (fun _ => 1)
  refine (iInf_le (α := ℕ∞) _ ⟨Nat, inferInstance, inferInstance, fun _ => 1⟩).trans ?_
  dsimp [Comp.run]
  simp
  induction' sum  (fun _ => 1)
  · simp
  · case queryBind i cont k =>
    cases i
    · case add x y =>
      simp [StateT.run]
      sorry
    · simp
      apply k

end ArithOracle
