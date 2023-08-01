import Mathlib.ModelTheory.FieldTheory.CharP
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace FirstOrder

namespace Language

def pow (a : Language.field.Term α) (n : ℕ) : Language.field.Term α :=
  Nat.recOn n a (λ _ x => a * x)

instance : Pow (Language.field.Term α) ℕ := ⟨pow⟩

def polyOfDegree : ∀ (n : ℕ),
    Language.field.Term (Empty ⊕ Fin (n+2))
  | 0 => &1
  | n+1 => &(Fin.last (n+2)) * ((&0) ^ n : Language.field.Term (Empty ⊕ Fin (n+3))) +
    (polyOfDegree n).relabel (Sum.map id (Fin.castLE (by simp)))



end Language

end FirstOrder
