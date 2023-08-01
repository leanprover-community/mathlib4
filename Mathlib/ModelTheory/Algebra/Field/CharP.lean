import Mathlib.ModelTheory.Algebra.Field.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Nat.Prime

namespace FirstOrder

namespace Language

namespace field

def ofNat {α : Type} : ℕ → Language.field.Term α
  | 0 => 0
  | n+1 => ofNat n + 1

def eqZero (n : ℕ) : Language.field.Sentence :=
  Term.equal (ofNat n) 0

theorem realize_ofNat {α K : Type _} [Field K] (p : ℕ) (v : α → K) :
    (Term.realize v (@ofNat α p) : K) = p := by
  induction p <;>
    simp [ofNat, *, zero_def,add_def, one_def, constantMap]

end field

open field

def Theory.fieldOfChar (p : ℕ) : Language.field.Theory :=
  ({eqZero p} ∪ (⋃ (n : ℕ) (_ : ¬ p ∣ n), {∼ (eqZero n)})) ∪
   Theory.field

instance {K : Type _} [Field K] (p : ℕ) [CharP K p] :
    (Theory.fieldOfChar p).Model K := by
  rw [Theory.fieldOfChar]
  refine Theory.model_union_iff.2 ⟨?_, by infer_instance⟩
  refine Theory.model_union_iff.2 ⟨?_, ?_⟩
  . simp [eqZero, Sentence.Realize, realize_ofNat, zero_def,
      constantMap, Structure.funMap]
  . simp only [Nat.isUnit_iff, Theory.model_iff, Set.mem_iUnion,
      Set.mem_singleton_iff, exists_prop,
      forall_exists_index, and_imp]
    rintro φ n hnp rfl
    simp only [Sentence.Realize, eqZero, zero_def, Formula.realize_not,
      Formula.realize_equal, realize_ofNat, Term.realize_constants,
      constantMap, Structure.funMap]
    exact (not_iff_not.2 (CharP.cast_eq_zero_iff K p n)).2 hnp

@[reducible]
def fieldOfModelFieldOfCharP {K : Type _} [Language.field.Structure K]
    (h : (Theory.fieldOfChar p).Model K) : Field K :=
  @fieldOfModelField _ _ (Theory.Model.mono h (by simp [Theory.fieldOfChar]))

theorem realize_ofNat' {K : Type _} [Language.field.Structure K]
    (h : (Theory.field).Model K)
    (p : ℕ) (v : α → K) : by
    letI := fieldOfModelField K;
      exact (Term.realize v (@ofNat α p) : K) = p := by
  induction p <;>
    simp [ofNat, *, zero_def, add_def, one_def, constantMap] <;> rfl

def charPOfModelFieldOfCharP {K : Type _} [Language.field.Structure K]
    (h : (Theory.fieldOfChar p).Model K) : by
      letI := fieldOfModelFieldOfCharP h; exact CharP K p := by
  letI := fieldOfModelFieldOfCharP h
  rw [charP_iff]
  intro x
  constructor
  . intro hx
    have h : K ⊨ (⋃ (n : ℕ) (_ : ¬ p ∣ n), {∼ (eqZero n)}) :=
      Theory.Model.mono h
        (Set.subset_union_of_subset_left (Set.subset_union_right _ _) _)
    simp only [Nat.isUnit_iff, Theory.model_iff, Set.mem_iUnion,
      Set.mem_singleton_iff, exists_prop, Sentence.Realize,
      forall_exists_index, and_imp] at h
    by_contra hpx
    have := h _ x hpx rfl
    rw [eqZero, Formula.realize_not, Formula.realize_equal,
      realize_ofNat'] at this
    erw [Term.realize, funMap_eq_coe_constants] at this
    exact this hx
  . rintro ⟨y, rfl⟩
    have h : K ⊨ {eqZero p} :=
      Theory.Model.mono h
        (Set.subset_union_of_subset_left (Set.subset_union_left _ _) _)
    simp only [eqZero._eq_1, Theory.model_iff, Set.mem_singleton_iff,
      Sentence.Realize, forall_eq, Formula.realize_equal] at h
    rw [realize_ofNat'] at h
    erw [Nat.cast_mul, h, Term.realize, funMap_eq_coe_constants]
    exact zero_mul _

end Language

end FirstOrder
