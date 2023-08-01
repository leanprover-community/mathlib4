import Mathlib.ModelTheory.Algebra.Field.CharP
import Mathlib.ModelTheory.Algebra.Field.FreeCommRing
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FreeCommRing

namespace FirstOrder

namespace Language

open field FreeCommRing BigOperators Polynomial

variable {K : Type _} [Field K]

def genericPoly (supp : Finset ℕ) : FreeCommRing (Fin (n + 1)) :=
  ∑ i ∈ supp, of

theorem lift_genericMonicPoly (p : Polynomial K)
    (hm : p.Monic) (x : K) : FreeCommRing.lift
    (fun i => Fin.cases x (fun i => p.coeff i) i)
    (genericMonicPoly p.natDegree) = p.eval x := by
  simp only [genericMonicPoly, map_add, map_pow, lift_of,
    Fin.cases_zero]
  rw [map_sum]
  simp




noncomputable def genMonicPolyHasRoot (n : ℕ) : Language.field.Sentence :=
  (∃' ((termOfFreeCommRing (genericMonicPoly n)).relabel Sum.inr =' 0)).alls

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
