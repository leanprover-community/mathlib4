/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.ModelTheory.Syntax

/-!
# Infinitary first-order formulas

This file defines the syntax of `L_{∞ω}`: first-order formulas with conjunctions and
disjunctions indexed by a *fixed branching carrier* `ι`, one per formula. `L_{ω₁ω}` is the
definitional specialization `ι := ℕ`.

## Design

The infinitary constructors `iSup`/`iInf` branch over the single type parameter `ι` rather than
quantifying over a fresh index type at every node. Consequences:

- `BoundedFormulaInf L ι α n : Type (max u v u' uι)` — the syntax lives in the `max` of its
  parameters' universes, with no `+ 1` bump. In particular
  `BoundedFormulaω L α n := BoundedFormulaInf L ℕ α n` has exactly the universe
  `Type (max u v u')` of the finitary `BoundedFormula`.
- An `ι`-indexed conjunction at a larger carrier `κ`, and transport of whole formulas
  between carriers, are expressed through codings, arriving with the follow-up transport
  layer. In particular, Karp's theorem, the consumer that forces arbitrary index types, needs
  only the single carrier `M ⊕ N`.

## Main definitions

- `FirstOrder.Language.BoundedFormulaInf`: infinitary formulas with carrier `ι`, free variables
  in `α`, and `n` free *bound-variable* slots.
- `FirstOrder.Language.BoundedFormulaω`: the `ι := ℕ` specialization (an `abbrev`, so all
  `BoundedFormulaInf` API applies definitionally).
- Derived connectives and quantifier closures (`not`, `⊤`/`⊥`, `ex`, `alls`, `exs`), and the
  carrier-generic finitary embedding `BoundedFormula.toInf`.
-/

@[expose] public section

universe u v u' uι w

namespace FirstOrder

namespace Language

variable (L : Language.{u, v})

/-- An infinitary bounded formula of `L_{∞ω}`, with infinitary conjunctions and disjunctions
branching over the fixed carrier `ι`, free variables indexed by `α`, and `n` additional bound
variables available. -/
inductive BoundedFormulaInf (ι : Type uι) (α : Type u') : ℕ → Type (max u v u' uι) where
  /-- The false formula. -/
  | falsum {n} : BoundedFormulaInf ι α n
  /-- Equality of two terms. -/
  | equal {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) : BoundedFormulaInf ι α n
  /-- A relation symbol applied to terms. -/
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
      BoundedFormulaInf ι α n
  /-- Implication. -/
  | imp {n} (φ ψ : BoundedFormulaInf ι α n) : BoundedFormulaInf ι α n
  /-- Universal quantification over the last bound variable. -/
  | all {n} (φ : BoundedFormulaInf ι α (n + 1)) : BoundedFormulaInf ι α n
  /-- Infinitary disjunction over the carrier. -/
  | iSup {n} (φs : ι → BoundedFormulaInf ι α n) : BoundedFormulaInf ι α n
  /-- Infinitary conjunction over the carrier. -/
  | iInf {n} (φs : ι → BoundedFormulaInf ι α n) : BoundedFormulaInf ι α n

/-- A bounded formula of `L_{ω₁ω}`: the definitional `ι := ℕ` specialization of
`BoundedFormulaInf`. Its universe is exactly that of the finitary `BoundedFormula`. -/
abbrev BoundedFormulaω (α : Type u') (n : ℕ) := L.BoundedFormulaInf ℕ α n

/-- An `L_{∞ω}` formula: a bounded formula with no free bound variables. -/
abbrev FormulaInf (ι : Type uι) (α : Type u') := L.BoundedFormulaInf ι α 0

/-- An `L_{∞ω}` sentence: a formula with no free variables at all. -/
abbrev SentenceInf (ι : Type uι) := L.FormulaInf ι Empty

/-- An `L_{ω₁ω}` formula.

Routed through `BoundedFormulaω` rather than stated as `FormulaInf ℕ α`, though the two are the
same type. Dot-notation resolution walks an abbreviation chain one unfolding at a time, trying
each head constant's namespace in turn, so this routing keeps declarations in a downstream
`BoundedFormulaω` namespace reachable as `φ.op` on an `L_{ω₁ω}` formula while the generic
`BoundedFormulaInf` namespace stays reachable at the end of the chain. -/
abbrev Formulaω (α : Type u') := L.BoundedFormulaω α 0

/-- An `L_{ω₁ω}` sentence. Routed through `Formulaω` for the reason given there. -/
abbrev Sentenceω := L.Formulaω Empty

variable {L} {ι : Type uι} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

/-- The negation of an infinitary formula. -/
@[match_pattern]
protected def not (φ : L.BoundedFormulaInf ι α n) : L.BoundedFormulaInf ι α n :=
  φ.imp .falsum

/-- The true formula. -/
protected def verum : L.BoundedFormulaInf ι α n :=
  BoundedFormulaInf.not .falsum

instance : Bot (L.BoundedFormulaInf ι α n) :=
  ⟨.falsum⟩

instance : Top (L.BoundedFormulaInf ι α n) :=
  ⟨BoundedFormulaInf.verum⟩

instance : Inhabited (L.BoundedFormulaInf ι α n) :=
  ⟨⊥⟩

/-- Existential quantification over the last bound variable. -/
@[match_pattern]
protected def ex (φ : L.BoundedFormulaInf ι α (n + 1)) : L.BoundedFormulaInf ι α n :=
  φ.not.all.not

/-- Places universal quantifiers on all in-scope bound variables of an infinitary bounded
formula (mirrors the finitary `BoundedFormula.alls`). -/
def alls : ∀ {n}, L.BoundedFormulaInf ι α n → L.FormulaInf ι α
  | 0, φ => φ
  | _ + 1, φ => φ.all.alls

/-- Places existential quantifiers on all in-scope bound variables of an infinitary bounded
formula (mirrors the finitary `BoundedFormula.exs`). -/
def exs : ∀ {n}, L.BoundedFormulaInf ι α n → L.FormulaInf ι α
  | 0, φ => φ
  | _ + 1, φ => φ.ex.exs

end BoundedFormulaInf

namespace BoundedFormula

/-- The embedding of finitary bounded formulas into the infinitary syntax. Since finitary
formulas have no infinitary nodes, the target carrier is arbitrary: there is one embedding for
all carriers and universes, rather than an embedding into `L_{ω₁ω}` followed by a lift. -/
def toInf : ∀ {n}, L.BoundedFormula α n → L.BoundedFormulaInf ι α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal t₁ t₂
  | _, .rel R ts => .rel R ts
  | _, .imp φ ψ => (toInf φ).imp (toInf ψ)
  | _, .all φ => (toInf φ).all

/-- The embedding of finitary bounded formulas into `L_{ω₁ω}`. -/
abbrev toOmega (φ : L.BoundedFormula α n) : L.BoundedFormulaω α n :=
  toInf φ

end BoundedFormula

end Language

end FirstOrder
