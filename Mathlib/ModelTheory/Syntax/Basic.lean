/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.Data.Set.Prod
import Mathlib.Logic.Equiv.Fin
import Mathlib.ModelTheory.LanguageMap

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

variable (L : Language.{u, v}) {L' : Language}
variable {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variable {α : Type u'} {β : Type v'} {γ : Type*}

open FirstOrder

open Structure Fin

/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive Term (α : Type u') : Type max u u'
  | var : α → Term α
  | func : ∀ {l : ℕ} (_f : L.Functions l) (_ts : Fin l → Term α), Term α
export Term (var func)

variable {L}

/-- The representation of a constant symbol as a term. -/
def Constants.term (c : L.Constants) : L.Term α :=
  func c default

/-- Applies a unary function to a term. -/
def Functions.apply₁ (f : L.Functions 1) (t : L.Term α) : L.Term α :=
  func f ![t]

/-- Applies a binary function to two terms. -/
def Functions.apply₂ (f : L.Functions 2) (t₁ t₂ : L.Term α) : L.Term α :=
  func f ![t₁, t₂]

namespace Term

instance inhabitedOfVar [Inhabited α] : Inhabited (L.Term α) :=
  ⟨var default⟩

instance inhabitedOfConstant [Inhabited L.Constants] : Inhabited (L.Term α) :=
  ⟨(default : L.Constants).term⟩

end Term

scoped[FirstOrder] prefix:arg "&" => FirstOrder.Language.Term.var ∘ Sum.inr


variable (L) (α)

/-- `BoundedFormula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive BoundedFormula : ℕ → Type max u v u'
  | falsum {n} : BoundedFormula n
  | equal {n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : BoundedFormula n
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : BoundedFormula n
  | imp {n} (f₁ f₂ : BoundedFormula n) : BoundedFormula n
  | all {n} (f : BoundedFormula (n + 1)) : BoundedFormula n

/-- `Formula α` is the type of formulas with all free variables indexed by `α`. -/
abbrev Formula :=
  L.BoundedFormula α 0

/-- A sentence is a formula with no free variables. -/
abbrev Sentence :=
  L.Formula Empty

/-- A theory is a set of sentences. -/
abbrev Theory :=
  Set L.Sentence

variable {L} {α} {n : ℕ}

/-- Applies a relation to terms as a bounded formula. -/
def Relations.boundedFormula {l : ℕ} (R : L.Relations n) (ts : Fin n → L.Term (α ⊕ (Fin l))) :
    L.BoundedFormula α l :=
  BoundedFormula.rel R ts

/-- Applies a unary relation to a term as a bounded formula. -/
def Relations.boundedFormula₁ (r : L.Relations 1) (t : L.Term (α ⊕ (Fin n))) :
    L.BoundedFormula α n :=
  r.boundedFormula ![t]

/-- Applies a binary relation to two terms as a bounded formula. -/
def Relations.boundedFormula₂ (r : L.Relations 2) (t₁ t₂ : L.Term (α ⊕ (Fin n))) :
    L.BoundedFormula α n :=
  r.boundedFormula ![t₁, t₂]

/-- The equality of two terms as a bounded formula. -/
def Term.bdEqual (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  BoundedFormula.equal t₁ t₂

namespace BoundedFormula

instance : Inhabited (L.BoundedFormula α n) :=
  ⟨falsum⟩

instance : Bot (L.BoundedFormula α n) :=
  ⟨falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[match_pattern]
protected def not (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  φ.imp ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
@[match_pattern]
protected def ex (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  φ.not.all.not

instance : Top (L.BoundedFormula α n) :=
  ⟨BoundedFormula.not ⊥⟩

instance : Inf (L.BoundedFormula α n) :=
  ⟨fun f g => (f.imp g.not).not⟩

instance : Sup (L.BoundedFormula α n) :=
  ⟨fun f g => f.not.imp g⟩

/-- The biimplication between two bounded formulas. -/
protected def iff (φ ψ : L.BoundedFormula α n) :=
  φ.imp ψ ⊓ ψ.imp φ

/-- take the disjunction of a finite set of formulas -/
noncomputable def iSup (s : Finset β) (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  (s.toList.map f).foldr (· ⊔ ·) ⊥

/-- take the conjunction of a finite set of formulas -/
noncomputable def iInf (s : Finset β) (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  (s.toList.map f).foldr (· ⊓ ·) ⊤


-- Porting note: universes in different order
/-- Places universal quantifiers on all extra variables of a bounded formula. -/
def alls : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | _n + 1, φ => φ.all.alls

-- Porting note: universes in different order
/-- Places existential quantifiers on all extra variables of a bounded formula. -/
def exs : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | _n + 1, φ => φ.ex.exs

end BoundedFormula

scoped[FirstOrder] infixl:88 " =' " => FirstOrder.Language.Term.bdEqual
-- input \~- or \simeq

scoped[FirstOrder] infixr:62 " ⟹ " => FirstOrder.Language.BoundedFormula.imp
-- input \==>

scoped[FirstOrder] prefix:110 "∀'" => FirstOrder.Language.BoundedFormula.all

scoped[FirstOrder] prefix:arg "∼" => FirstOrder.Language.BoundedFormula.not
-- input \~, the ASCII character ~ has too low precedence

scoped[FirstOrder] infixl:61 " ⇔ " => FirstOrder.Language.BoundedFormula.iff
-- input \<=>

scoped[FirstOrder] prefix:110 "∃'" => FirstOrder.Language.BoundedFormula.ex
-- input \ex








end Language

end FirstOrder
