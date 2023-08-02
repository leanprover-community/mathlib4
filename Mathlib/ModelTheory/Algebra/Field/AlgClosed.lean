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
      by_cases hin : i = n
      . subst i
        simp only [ite_true, lt_self_iff_false, dite_false, add_right_eq_self]
        exact Finset.sum_eq_zero (fun i _ => by rw [if_neg (ne_of_gt i.2)])
      . by_cases hin₂ : i < n
        . simp only [hin, ite_false, zero_add, hin₂, dite_true]
          rw [Finset.sum_eq_single ⟨i, hin₂⟩]
          . simp
          . simp only [Finset.mem_univ, ne_eq, ite_eq_right_iff, forall_true_left]
            rintro _ _ rfl
            simp_all
          . simp
        . simp only [hin, ite_false, zero_add, hin₂, dite_false]
          refine Finset.sum_eq_zero (fun i _ => ?_)
          simp [ne_of_gt (lt_of_lt_of_le i.2 (le_of_not_lt hin₂))]
    have hpn : p.natDegree = n := by
      refine le_antisymm ?_ ?_
      . refine natDegree_le_iff_coeff_eq_zero.2 ?_
        rw [hpc]
        intro i hi
        simp [not_lt_of_gt hi, ne_of_gt hi]
      . refine le_natDegree_of_ne_zero ?_
        simp only [coeff_add, coeff_X_pow_self, finset_sum_coeff, coeff_C_mul, ne_eq]
        rw [Finset.sum_eq_zero, add_zero]
        . simp
        . rintro ⟨i, hi⟩ _
          simp [coeff_X_pow, ne_of_gt hi]
    have hpm : p.Monic := by
      simp only [Monic.def, leadingCoeff, hpn, coeff_add, coeff_X_pow_self, finset_sum_coeff,
        coeff_C_mul, add_right_eq_self]
      exact Finset.sum_eq_zero (fun i _ =>
        by rw [coeff_X_pow, if_neg (ne_of_gt i.2), mul_zero])
    rcases h p hpn hpm with ⟨x, hx⟩
    use x
    rw [← lift_genericPoly hpm] at hx
    convert hx
    rw [hpn]
    congr
    rw [hpc]
    simp

def Theory.ACF (p : ℕ) : Theory Language.field :=
  Theory.fieldOfChar p ∪ ⋃ (n : ℕ) (_ : 0 < n), {genericMonicPolyHasRoot n}

instance {K : Type _} [Field K] [CharP K p] [IsAlgClosed K] :
    (Theory.ACF p).Model K := by
  refine Theory.model_union_iff.2 ⟨by infer_instance, ?_⟩
  simp only [Theory.model_iff, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop, forall_exists_index, and_imp]
  rintro _ n hn0 rfl
  rw [realize_genericMonicPolyHasRoot]
  rintro p rfl _
  exact IsAlgClosed.exists_root p (ne_of_gt
    (natDegree_pos_iff_degree_pos.1 hn0))

@[reducible]
def fieldOfModelACF {K : Type _} [Language.field.Structure K]
    (h : (Theory.ACF p).Model K) : Field K :=
  @fieldOfModelFieldOfCharP p _ _ (Theory.Model.mono h (by simp [Theory.ACF]))

theorem isAlgClosedOfModelACF {p : ℕ} (M : Type _)
    [Language.field.Structure M] [h : (Theory.ACF p).Model M] : by
    letI := fieldOfModelACF h; exact IsAlgClosed M := by
  letI := fieldOfModelACF h
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hpi
  have h : M ⊨ (⋃ (n : ℕ) (_ : 0 < n), {genericMonicPolyHasRoot n}) :=
    Theory.Model.mono h (by simp [Theory.ACF])
  simp only [Theory.model_iff, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop, forall_exists_index, and_imp] at h
  have := h _ p.natDegree (natDegree_pos_iff_degree_pos.2
    (degree_pos_of_irreducible hpi)) rfl
  have : ∀ q : M[X],
      q.natDegree = p.natDegree → q.Monic → ∃ x, q.eval x = 0 := by
    rw [← realize_genericMonicPolyHasRoot]
    convert this
    ext _ f x
    . cases f <;> simp





end Language

end FirstOrder
