import Mathlib.ModelTheory.FieldTheory.Basic
import Mathlib.Algebra.CharP.Basic

namespace FirstOrder

namespace Language

namespace field

def ofNat {α : Type} : ℕ → Language.field.Term α
  | 0 => 0
  | n+1 => ofNat n + 1

def eqZero (n : ℕ) : Language.field.Sentence :=
  Term.equal (ofNat n) 0

def Theory.fieldOfChar (n : ℕ) : Language.field.Theory :=
  {eqZero n} ∪ (⋃ (i : ℕ) (_ : n ≠ i) (_ : n ≠ 0), {∼ (eqZero i)}) ∪ Theory.field

section

attribute [local instance] structureFieldOfField

theorem realize_ofNat {α K : Type _} [Field K] (p : ℕ) (v : α → K) :
    (Term.realize v (@ofNat α p) : K) = p := by
  induction p <;>
    simp [ofNat, *, zero_def, structureFieldOfField, add_def, one_def,
      constantMap]

def ModelFieldOfCharOfField {K : Type _} [Field K] (p : ℕ) [CharP K p] :
    (Theory.fieldOfChar p).Model K := by
  rw [Theory.fieldOfChar]
  refine Theory.model_union_iff.2 ⟨?_, modelFieldOfField⟩
  refine Theory.model_union_iff.2 ⟨?_, ?_⟩
  . simp [eqZero, Sentence.Realize, realize_ofNat,
      zero_def, constantMap, structureFieldOfField]
  . simp (config := {contextual := true}) [eqZero,
      Sentence.Realize, realize_ofNat, structureFieldOfField,
      zero_def, one_def, constantMap]
    intro _ hp0 q hpq _


end

end field

end Language

end FirstOrder
