import Mathlib.ModelTheory.FieldTheory.Basic

namespace FirstOrder

namespace Language

namespace field

def ofNat {α : Type} : ℕ → Language.field.Term α
  | 0 => 0
  | n+1 => ofNat n + 1

def eqZero (n : ℕ) : Language.field.Sentence :=
  Term.equal (ofNat n) 0

def Theory.fieldOfChar (n : ℕ) : Language.field.Theory :=
  Theory.field ∪ {eqZero n} ∪ ⋃ (i : ℕ) (_ : n ≠ i), {∼ (eqZero i)}

attribute [local instance] structureFieldOfField

def ModelFieldOfCharOfField {K : Type _} [Field K] (n : ℕ) (h : n ≠ 0)
    (M : (Theory.fieldOfChar n).Model) : Theory.field.Model := sorry

end field

end Language

end FirstOrder
