import Mathlib.ModelTheory.Algebra.Field.CharP
import Mathlib.ModelTheory.Algebra.Field.FreeCommRing
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FreeCommRing

namespace FirstOrder

namespace Language

open field FreeCommRing BigOperators Polynomial

variable {K : Type _} [Field K]

def genericPoly (supp : Finset ℕ) : FreeCommRing (Option supp) :=
  ∑ i : supp, of (some i) * of none ^ (i : ℕ)

theorem lift_genericPoly (p : Polynomial K) (x : K) :
   FreeCommRing.lift
    (fun i => Option.elim i x (fun (i : p.support) => p.coeff i))
    (genericPoly p.support) = p.eval x := by
  simp only [genericPoly, Finset.univ_eq_attach, Option.elim, map_sum,
    map_mul, lift_of, map_pow, Polynomial.eval_eq_sum, Polynomial.sum]
  exact @Finset.sum_attach _ _ _ _ (fun i => p.coeff i * x ^ (i : ℕ))

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
