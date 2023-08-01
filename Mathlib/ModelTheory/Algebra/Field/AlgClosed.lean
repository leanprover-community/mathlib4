import Mathlib.ModelTheory.Algebra.Field.CharP
import Mathlib.ModelTheory.Algebra.Field.FreeCommRing
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FreeCommRing

namespace FirstOrder

namespace Language

open field FreeCommRing BigOperators Polynomial

variable {K : Type _} [Field K]

def genericMonicPoly (n : ℕ) : FreeCommRing (Option (Fin n)) :=
    of none ^ n + ∑ i : Fin n, of (some i) * of none ^ (i : ℕ)

theorem lift_genericPoly (p : Polynomial K) (hpm : p.Monic) (x : K) :
    FreeCommRing.lift
      (fun i => Option.elim i x (fun (i : Fin p.natDegree) => p.coeff i))
      (genericMonicPoly p.natDegree) = p.eval x := by
  simp only [genericMonicPoly, Option.elim, map_add, map_pow, lift_of,
    map_sum, map_mul, eval_eq_sum_range, Finset.sum_range_succ]
  rw [← leadingCoeff, Monic.def.1 hpm, add_comm, one_mul, Finset.sum_range]

noncomputable def genMonicPolyHasRoot (n : ℕ) : Language.field.Sentence :=
  (∃' ((termOfFreeCommRing (genericPoly n)).relabel Sum.inr =' 0)).alls

theorem realize_genMonicPolyHasRoot (n : ℕ) :
    K ⊨ genMonicPolyHasRoot n ↔ ∀ p : K[X],
      p.natDegree = n → p.Monic → ∃ x, p.eval x = 0 := by
  simp only [Sentence.Realize, genMonicPolyHasRoot,
    BoundedFormula.realize_alls, BoundedFormula.realize_ex,
    BoundedFormula.realize_bdEqual, Term.realize_relabel,
    Sum.elim_comp_inr, realize_termOfFreeCommRing]
  constructor
  . rintro h p rfl hpm
    rcases h (fun i => p.coeff i) with ⟨x, hx⟩
    use x




end Language

end FirstOrder
