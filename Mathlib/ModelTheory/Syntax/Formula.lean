/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.ModelTheory.Syntax.Relabel


/-!
# Basics on First-Order Syntax
This file defines first-order terms, formulas, sentences, and theories in a style inspired by the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions


## Implementation Notes


## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/


universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {L' : Language}
variable {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variable {α : Type u'} {β : Type v'} {γ : Type*}
variable {n : ℕ}

open FirstOrder

open Structure Fin Finset

namespace Formula

/-- Relabels a formula's variables along a particular function. -/
def relabel (g : α → β) : L.Formula α → L.Formula β :=
  @BoundedFormula.relabel _ _ _ 0 (Sum.inl ∘ g) 0

/-- The graph of a function as a first-order formula. -/
def graph (f : L.Functions n) : L.Formula (Fin (n + 1)) :=
  Term.equal (var 0) (func f fun i => var i.succ)

/-- The negation of a formula. -/
protected nonrec abbrev not (φ : L.Formula α) : L.Formula α :=
  φ.not

/-- The implication between formulas, as a formula. -/
protected abbrev imp : L.Formula α → L.Formula α → L.Formula α :=
  BoundedFormula.imp

/-- Given a map `f : α → β ⊕ γ`, `iAlls f φ` transforms a `L.Formula α`
into a `L.Formula β` by renaming variables with the map `f` and then universally
quantifying over all variables `Sum.inr _`. -/
noncomputable def iAlls [Finite γ] (f : α → β ⊕ γ)
    (φ : L.Formula α) : L.Formula β :=
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin γ))
  (BoundedFormula.relabel (fun a => Sum.map id e (f a)) φ).alls

/-- Given a map `f : α → β ⊕ γ`, `iExs f φ` transforms a `L.Formula α`
into a `L.Formula β` by renaming variables with the map `f` and then universally
quantifying over all variables `Sum.inr _`. -/
noncomputable def iExs [Finite γ] (f : α → β ⊕ γ)
    (φ : L.Formula α) : L.Formula β :=
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin γ))
  (BoundedFormula.relabel (fun a => Sum.map id e (f a)) φ).exs

/-- The biimplication between formulas, as a formula. -/
protected nonrec abbrev iff (φ ψ : L.Formula α) : L.Formula α :=
  φ.iff ψ

/-- A bijection sending formulas to sentences with constants. -/
def equivSentence : L.Formula α ≃ L[[α]].Sentence :=
  (BoundedFormula.constantsVarsEquiv.trans (BoundedFormula.relabelEquiv (Equiv.sumEmpty _ _))).symm

theorem equivSentence_not (φ : L.Formula α) : equivSentence φ.not = (equivSentence φ).not :=
  rfl

theorem equivSentence_inf (φ ψ : L.Formula α) :
    equivSentence (φ ⊓ ψ) = equivSentence φ ⊓ equivSentence ψ :=
  rfl

end Formula

end Language

end FirstOrder
