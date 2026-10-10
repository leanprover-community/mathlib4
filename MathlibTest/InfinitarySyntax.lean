import Mathlib.ModelTheory.Infinitary.Semantics

/-!
Regression probes for the carrier-parameterized infinitary syntax. Each example is stated so
that it fails to elaborate if the design regresses: the universe ascriptions ARE the claims,
the `simp only` probes detect lemmas that only close by definitional unfolding, and the
induction probe guards structural recursion through the `ι := ℕ` abbreviation.
-/

universe u v u' uι w

namespace FirstOrder.Language

open BoundedFormulaInf

/-- The syntax lives at `max` of its parameters' universes: no `+ 1` bump. -/
example (L : Language.{u, v}) (ι : Type uι) (α : Type u') (n : ℕ) :
    Type (max u v u' uι) :=
  L.BoundedFormulaInf ι α n

/-- The `ι := ℕ` specialization has EXACTLY the finitary `BoundedFormula` universe. -/
example (L : Language.{u, v}) (α : Type u') (n : ℕ) : Type (max u v u') :=
  L.BoundedFormulaω α n

/-- Realization applies by `simp only` at a literal nonzero index universe. -/
example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    {ι : Type 1} (φs : ι → L.BoundedFormulaInf ι α n) (v : α → M) (xs : Fin n → M) :
    (iInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  simp only [realize_iInf]

/-- The finitary embedding is carrier-generic: realization is preserved even at an
uncountable carrier in a higher universe. -/
example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M) :
    (φ.toInf (ι := Type)).Realize v xs ↔ φ.Realize v xs :=
  BoundedFormula.realize_toInf φ v xs

/-- Structural induction still yields all seven cases, with `ℕ`-indexed induction
hypotheses, through the `BoundedFormulaω` abbreviation; dot-notation elaborates. -/
example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {k : ℕ}
    (φ : L.BoundedFormulaω α k) (v : α → M) (xs : Fin k → M) :
    φ.Realize v xs ∨ ¬φ.Realize v xs := by
  induction φ <;> exact Classical.em _

example {L : Language.{u, v}} {α : Type u'} (φs : ℕ → L.BoundedFormulaω α 0) :
    L.BoundedFormulaω α 0 :=
  .iInf φs

/-! ### The `L_{ω₁ω}` abbreviation chain stays extensible

`Formulaω` and `Sentenceω` are routed through `BoundedFormulaω`, not stated directly as
`FormulaInf ℕ` / `SentenceInf ℕ`. All four spellings denote the same types, but dot-notation
resolution walks the chain one unfolding at a time and tries each head constant's namespace as
it goes. Were the chain to bypass `BoundedFormulaω`, a downstream file could add operations to
the `BoundedFormulaω` namespace and find them unreachable as `φ.op` on any formula or sentence —
the errors read `The environment does not contain BoundedFormulaInf.op`, naming only the last
namespace tried. These probes fail to elaborate if that regresses. -/

section AbbrevChain

variable {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}

/-- Stands in for a downstream extension of the `L_{ω₁ω}` namespace. -/
private def BoundedFormulaω.selfImp (φ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  φ.imp φ

/-- Reachable by dot-notation on a bounded formula … -/
example (φ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n := φ.selfImp

/-- … on a formula … -/
example (φ : L.Formulaω α) : L.Formulaω α := φ.selfImp

/-- … and on a sentence. -/
example (φ : L.Sentenceω) : L.Sentenceω := φ.selfImp

/-- The generic `BoundedFormulaInf` namespace remains reachable at the end of the chain, from
every ω spelling: these are `BoundedFormulaInf.not`, not an ω-specific copy. -/
example (φ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n := φ.not

example (φ : L.Formulaω α) : L.Formulaω α := φ.not

example (φ : L.Sentenceω) : L.Sentenceω := φ.not

/-- Realization still elaborates for a formula, and is the one generic recursion. -/
example (φ : L.Formulaω α) (v : α → M) : Prop := φ.Realize v default

example (φ : L.Formulaω α) (v : α → M) :
    φ.Realize v default ↔ FormulaInf.Realize φ v := Iff.rfl

/-- Realization still elaborates for a sentence. -/
example (φ : L.Sentenceω) : Prop := SentenceInf.Realize φ M

example (φ : L.Sentenceω) :
    SentenceInf.Realize φ M ↔ φ.Realize (Empty.elim : Empty → M) default := Iff.rfl

/-- `not` and `ex` carry `@[match_pattern]`, matching the finitary `BoundedFormula` API, so they
are usable in pattern position rather than only as constructors' derived forms. -/
example (φ : L.BoundedFormulaω α n) : Bool :=
  match φ with
  | BoundedFormulaInf.not _ => true
  | _ => false

example (φ : L.BoundedFormulaω α n) : Bool :=
  match φ with
  | BoundedFormulaInf.ex _ => true
  | _ => false

end AbbrevChain

end FirstOrder.Language
