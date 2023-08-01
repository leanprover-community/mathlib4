import Mathlib.ModelTheory.Algebra.Field.CharP
import Mathlib.ModelTheory.Algebra.Field.FreeCommRing
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FreeCommRing

namespace FirstOrder

namespace Language

open field FreeCommRing BigOperators Polynomial

variable {K : Type _} [Field K]

def genericMonicPoly (n : ℕ) : FreeCommRing (Fin (n + 1)) :=
    of (Fin.last _) ^ n + ∑ i : Fin n, of i.castSucc * of (Fin.last _) ^ (i : ℕ)

theorem lift_genericPoly {p : Polynomial K} (hpm : p.Monic) (x : K) :
    FreeCommRing.lift
      (Fin.snoc (fun i => p.coeff i) x)
      (genericMonicPoly p.natDegree) = p.eval x := by
  simp only [genericMonicPoly, map_add, map_pow, lift_of, Fin.snoc_last,
    map_sum, map_mul, Fin.snoc_castSucc, eval_eq_sum_range, Finset.sum_range_succ, coeff_natDegree]
  rw [Monic.def.1 hpm, add_comm, one_mul, Finset.sum_range]

noncomputable def genericMonicPolyHasRoot (n : ℕ) : Language.field.Sentence :=
  (∃' ((termOfFreeCommRing (genericMonicPoly n)).relabel Sum.inr =' 0)).alls

theorem realize_genericMonicPolyHasRoot (n : ℕ) :
    K ⊨ genericMonicPolyHasRoot n ↔ ∀ p : K[X],
      p.natDegree = n → p.Monic → ∃ x, p.eval x = 0 := by
  simp only [Sentence.Realize, genericMonicPolyHasRoot, BoundedFormula.realize_alls,
    BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual, Term.realize_relabel,
    Sum.elim_comp_inr, realize_termOfFreeCommRing, Term.realize, instStructureField_funMap]
  constructor
  . rintro h p rfl hpm
    rcases h (fun i => p.coeff i) with ⟨x, hx⟩
    use x
    rwa [← lift_genericPoly hpm]
  . rintro h xs
    let p : K[X] := X ^ n + ∑ i : Fin n, C (xs i) * X ^ (i : ℕ)
    have hpc : p.coeff = fun i => if h : i < n then xs ⟨i, h⟩
        else if i = n then 1 else 0 := by
      ext i
      simp only [coeff_add, coeff_X_pow, finset_sum_coeff, coeff_C_mul,
        mul_ite, mul_one, mul_zero]
      split_ifs with hin₁ hin₂ hin₃
      . subst i
        simp [lt_irrefl] at hin₂
      . subst i
        rw [add_right_eq_self]
        exact Finset.sum_eq_zero (fun i _ => by rw [if_neg (ne_of_gt i.2)])
      . simp only [zero_add]
        rw [Finset.sum_eq_single ⟨i, hin₃⟩]
        . simp
        . simp only [Finset.mem_univ, ne_eq, ite_eq_right_iff,
            forall_true_left]
          rintro _ _ rfl
          simp_all
        . simp
      . rw [add_right_eq_self]
        exact Finset.sum_eq_zero (fun i _ => by rw [if_neg (ne_of_gt i.2)])
    have hpn : p.natDegree = n := by
      rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
      rw [natDegree_X_pow]
      sorry
    have hpm : p.Monic := by
      simp only [Monic.def, leadingCoeff, hpn, coeff_add, coeff_X_pow_self, finset_sum_coeff,
        coeff_C_mul, add_right_eq_self]
      exact Finset.sum_eq_zero (fun i _ =>
        by rw [coeff_X_pow, if_neg (ne_of_gt i.2), mul_zero])
    rcases h p hpn hpm with x
    simp [lift_genericPoly hpm]





end Language

end FirstOrder
