import Mathlib.ModelTheory.FieldTheory.CharP
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Polynomial.EraseLead

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
  | n+1 => (polyOfDegree n).relabel (Sum.map id (Fin.castLE (by simp))) +
    &(Fin.last (n+2)) * ((&0) ^ n : Language.field.Term (Empty ⊕ Fin (n+3)))


variable {K : Type _} [Field K]
#print Polynomial.natDegree_eq_z
theorem realize_polyOfDegree (n : ℕ) (p : Polynomial K)
    (hpn : p.natDegree ≤ n) (x : K) :
    (polyOfDegree n).realize (Sum.elim (Empty.elim)
      (fun i : Fin (n+2) => Fin.cases x (fun i => p.coeff i) i))
        = p.eval x := by
  induction n generalizing p with
  | zero =>
    simp only [Nat.zero_eq, CharP.cast_eq_zero] at hpn
    conv_rhs => rw [Polynomial.degree_le_zero_iff.1
      (Polynomial.natDegree_eq_zero_iff_degree_le_zero.1 (Nat.le_zero.1 hpn))]
    simp [polyOfDegree, Fin.cases, Fin.induction]
  | succ n ih =>
    rw [← p.eraseLead_add_C_mul_X_pow, Polynomial.eval_add,
      ← ih p.eraseLead (nat)]
    simp [Term.realize]
    congr 1
    -- . ext a
    --   rcases a with a | a
    --   . cases a
    --   . dsimp
    --     refine Fin.cases  ?_ ?_ a
    --     . simp
    --     . intro i
    --       simp only [Fin.castLE_succ, Fin.cases_succ,
    --         Fin.coe_castLE, Polynomial.eraseLead_coeff, hpn,
    --         if_neg (ne_of_lt i.2)]







end Language

end FirstOrder
