import Mathlib.ModelTheory.FieldTheory.CharP
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace FirstOrder

namespace Language

def pow (a : Language.field.Term α) (n : ℕ) : Language.field.Term α :=
  Nat.recOn n 1 (λ _ x => a * x)

instance : Pow (Language.field.Term α) ℕ := ⟨pow⟩

theorem pow_def (a : Language.field.Term α) (n : ℕ) :
    a ^ n = pow a n := rfl

@[simp]
theorem realize_pow {K : Type _} [Field K]
    (n : ℕ) (a : Language.field.Term α) (v : α → K) :
    (a ^ n).realize v = (a.realize v) ^ n := by
  induction n <;> simp_all [pow_def, pow, field.one_def, constantMap,
    Term.realize, pow_succ]

def polyOfDegree : ∀ (n : ℕ),
    Language.field.Term (Empty ⊕ Fin (n+2))
  | 0 => &1
  | n+1 => &(Fin.last (n+2)) * ((&0) ^ n : Language.field.Term (Empty ⊕ Fin (n+3))) +
    (polyOfDegree n).relabel (Sum.map id (Fin.castLE (by simp)))



end Language

end FirstOrder
