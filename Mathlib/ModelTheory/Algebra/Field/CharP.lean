import Mathlib.ModelTheory.Algebra.Field.FreeCommRing
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Nat.Prime

namespace FirstOrder

namespace Language

namespace field

noncomputable def eqZero (n : ℕ) : Language.field.Sentence :=
  Term.equal (termOfFreeCommRing n) 0

end field

open field

def Theory.hasChar (p : ℕ) : Language.field.Theory :=
  ({eqZero p} ∪ (⋃ (n : ℕ) (_ : ¬ p ∣ n), {∼ (eqZero n)}))

theorem model_hasChar_of_charP {K : Type _} [ModelField K] (p : ℕ) [CharP K p] :
    (Theory.hasChar p).Model K := by
  rw [Theory.hasChar]
  refine Theory.model_union_iff.2 ⟨?_, ?_⟩
  . simp [eqZero, Sentence.Realize, zero_def,
      constantMap, Structure.funMap]
  . simp only [Nat.isUnit_iff, Theory.model_iff, Set.mem_iUnion,
      Set.mem_singleton_iff, exists_prop,
      forall_exists_index, and_imp]
    rintro φ n hnp rfl
    simp only [Sentence.Realize, eqZero, zero_def, Formula.realize_not, Formula.realize_equal,
      realize_termOfFreeCommRing, map_natCast, Term.realize_constants, constantMap,
      ModelField.funMap_zero]
    exact (not_iff_not.2 (CharP.cast_eq_zero_iff K p n)).2 hnp

theorem charP_of_model_hasChar {K : Type _} [ModelField K]
    [h : (Theory.hasChar p).Model K] : CharP K p := by
  rw [charP_iff]
  intro x
  constructor
  . intro hx
    have h : K ⊨ (⋃ (n : ℕ) (_ : ¬ p ∣ n), {∼ (eqZero n)}) :=
      Theory.Model.mono h (Set.subset_union_right _ _)
    simp only [Nat.isUnit_iff, Theory.model_iff, Set.mem_iUnion,
      Set.mem_singleton_iff, exists_prop, Sentence.Realize,
      forall_exists_index, and_imp] at h
    by_contra hpx
    have := h _ x hpx rfl
    simp only [eqZero, Formula.realize_not, Formula.realize_equal, realize_termOfFreeCommRing,
      map_natCast, Term.realize, ModelField.funMap_zero] at this
    exact this hx
  . rintro ⟨y, rfl⟩
    have h : K ⊨ {eqZero p} :=
      Theory.Model.mono h (Set.subset_union_left _ _)
    simp only [eqZero, Theory.model_iff, Set.mem_singleton_iff, Sentence.Realize, forall_eq,
      Formula.realize_equal, realize_termOfFreeCommRing, map_natCast, Term.realize,
      ModelField.funMap_zero] at h
    simp [h]

end Language

end FirstOrder
