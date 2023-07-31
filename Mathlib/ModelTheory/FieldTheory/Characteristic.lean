import Mathlib.ModelTheory.FieldTheory.Basic
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

def Theory.fieldOfChar (p : ℕ) : Language.field.Theory :=
  ({eqZero p} ∪ (⋃ (n : ℕ) (_ : ¬ p ∣ n), {∼ (eqZero n)})) ∪
   Theory.field

section

attribute [local instance] structureFieldOfField

theorem realize_ofNat {α K : Type _} [Field K] (p : ℕ) (v : α → K) :
    (Term.realize v (@ofNat α p) : K) = p := by
  induction p <;>
    simp [ofNat, *, zero_def, structureFieldOfField, add_def, one_def,
      constantMap]

def modelFieldOfCharOfField {K : Type _} [Field K] (p : ℕ) [CharP K p] :
    (Theory.fieldOfChar p).Model K := by
  rw [Theory.fieldOfChar]
  refine Theory.model_union_iff.2 ⟨?_, modelFieldOfField⟩
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



end

end field

end Language

end FirstOrder
