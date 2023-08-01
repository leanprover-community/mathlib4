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

noncomputable def genMonicPolyHasRoot (n : ℕ) : Language.field.Sentence :=
  (∃' ((termOfFreeCommRing (genericMonicPoly n)).relabel Sum.inr =' 0)).alls

theorem realize_genMonicPolyHasRoot (n : ℕ) :
    K ⊨ genMonicPolyHasRoot n ↔ ∀ p : K[X],
      p.natDegree = n → p.Monic → ∃ x, p.eval x = 0 := by
  simp only [Sentence.Realize, genMonicPolyHasRoot, BoundedFormula.realize_alls,
    BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual, Term.realize_relabel,
    Sum.elim_comp_inr, realize_termOfFreeCommRing, Term.realize, instStructureField_funMap]
  constructor
  . rintro h p rfl hpm
    rcases h (fun i => p.coeff i) with ⟨x, hx⟩
    use x
    rwa [← lift_genericPoly hpm]
  . rintro h xs
    let p : K[X] := X ^ n + ∑ i : Fin n, C (xs i) * X ^ (i : ℕ)
    have hpm : p.natDegree = n := by
      rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
      rw [natDegree_X_pow]
      sorry
    have := h (X ^ n + ∑ i : Fin n, ∑ i : Fin n, C (xs i) * X ^ (i : ℕ))





end Language

end FirstOrder
