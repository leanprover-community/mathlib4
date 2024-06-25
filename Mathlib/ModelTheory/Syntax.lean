/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.Data.Set.Prod
import Mathlib.Logic.Equiv.Fin
import Mathlib.ModelTheory.LanguageMap

#align_import model_theory.syntax from "leanprover-community/mathlib"@"d565b3df44619c1498326936be16f1a935df0728"

/-!
# Basics on First-Order Syntax
This file defines first-order terms, formulas, sentences, and theories in a style inspired by the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions
* A `FirstOrder.Language.Term` is defined so that `L.Term α` is the type of `L`-terms with free
  variables indexed by `α`.
* A `FirstOrder.Language.Formula` is defined so that `L.Formula α` is the type of `L`-formulas with
  free variables indexed by `α`.
* A `FirstOrder.Language.Sentence` is a formula with no free variables.
* A `FirstOrder.Language.Theory` is a set of sentences.
* The variables of terms and formulas can be relabelled with `FirstOrder.Language.Term.relabel`,
`FirstOrder.Language.BoundedFormula.relabel`, and `FirstOrder.Language.Formula.relabel`.
* Given an operation on terms and an operation on relations,
  `FirstOrder.Language.BoundedFormula.mapTermRel` gives an operation on formulas.
* `FirstOrder.Language.BoundedFormula.castLE` adds more `Fin`-indexed variables.
* `FirstOrder.Language.BoundedFormula.liftAt` raises the indexes of the `Fin`-indexed variables
above a particular index.
* `FirstOrder.Language.Term.subst` and `FirstOrder.Language.BoundedFormula.subst` substitute
variables with given terms.
* Language maps can act on syntactic objects with functions such as
`FirstOrder.Language.LHom.onFormula`.
* `FirstOrder.Language.Term.constantsVarsEquiv` and
`FirstOrder.Language.BoundedFormula.constantsVarsEquiv` switch terms and formulas between having
constants in the language and having extra variables indexed by the same type.

## Implementation Notes
* Formulas use a modified version of de Bruijn variables. Specifically, a `L.BoundedFormula α n`
is a formula with some variables indexed by a type `α`, which cannot be quantified over, and some
indexed by `Fin n`, which can. For any `φ : L.BoundedFormula α (n + 1)`, we define the formula
`∀' φ : L.BoundedFormula α n` by universally quantifying over the variable indexed by
`n : Fin (n + 1)`.

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
#align first_order.language.term FirstOrder.Language.Term
export Term (var func)

variable {L}

namespace Term

open Finset

/-- The `Finset` of variables used in a given term. -/
@[simp]
def varFinset [DecidableEq α] : L.Term α → Finset α
  | var i => {i}
  | func _f ts => univ.biUnion fun i => (ts i).varFinset
#align first_order.language.term.var_finset FirstOrder.Language.Term.varFinset

-- Porting note: universes in different order
/-- The `Finset` of variables from the left side of a sum used in a given term. -/
@[simp]
def varFinsetLeft [DecidableEq α] : L.Term (Sum α β) → Finset α
  | var (Sum.inl i) => {i}
  | var (Sum.inr _i) => ∅
  | func _f ts => univ.biUnion fun i => (ts i).varFinsetLeft
#align first_order.language.term.var_finset_left FirstOrder.Language.Term.varFinsetLeft

-- Porting note: universes in different order
@[simp]
def relabel (g : α → β) : L.Term α → L.Term β
  | var i => var (g i)
  | func f ts => func f fun {i} => (ts i).relabel g
#align first_order.language.term.relabel FirstOrder.Language.Term.relabel

theorem relabel_id (t : L.Term α) : t.relabel id = t := by
  induction' t with _ _ _ _ ih
  · rfl
  · simp [ih]
#align first_order.language.term.relabel_id FirstOrder.Language.Term.relabel_id

@[simp]
theorem relabel_id_eq_id : (Term.relabel id : L.Term α → L.Term α) = id :=
  funext relabel_id
#align first_order.language.term.relabel_id_eq_id FirstOrder.Language.Term.relabel_id_eq_id

@[simp]
theorem relabel_relabel (f : α → β) (g : β → γ) (t : L.Term α) :
    (t.relabel f).relabel g = t.relabel (g ∘ f) := by
  induction' t with _ _ _ _ ih
  · rfl
  · simp [ih]
#align first_order.language.term.relabel_relabel FirstOrder.Language.Term.relabel_relabel

@[simp]
theorem relabel_comp_relabel (f : α → β) (g : β → γ) :
    (Term.relabel g ∘ Term.relabel f : L.Term α → L.Term γ) = Term.relabel (g ∘ f) :=
  funext (relabel_relabel f g)
#align first_order.language.term.relabel_comp_relabel FirstOrder.Language.Term.relabel_comp_relabel

/-- Relabels a term's variables along a bijection. -/
@[simps]
def relabelEquiv (g : α ≃ β) : L.Term α ≃ L.Term β :=
  ⟨relabel g, relabel g.symm, fun t => by simp, fun t => by simp⟩
#align first_order.language.term.relabel_equiv FirstOrder.Language.Term.relabelEquiv

-- Porting note: universes in different order
/-- Restricts a term to use only a set of the given variables. -/
def restrictVar [DecidableEq α] : ∀ (t : L.Term α) (_f : t.varFinset → β), L.Term β
  | var a, f => var (f ⟨a, mem_singleton_self a⟩)
  | func F ts, f =>
    func F fun i => (ts i).restrictVar (f ∘ Set.inclusion
      (subset_biUnion_of_mem (fun i => varFinset (ts i)) (mem_univ i)))
#align first_order.language.term.restrict_var FirstOrder.Language.Term.restrictVar

-- Porting note: universes in different order
/-- Restricts a term to use only a set of the given variables on the left side of a sum. -/
def restrictVarLeft [DecidableEq α] {γ : Type*} :
    ∀ (t : L.Term (Sum α γ)) (_f : t.varFinsetLeft → β), L.Term (Sum β γ)
  | var (Sum.inl a), f => var (Sum.inl (f ⟨a, mem_singleton_self a⟩))
  | var (Sum.inr a), _f => var (Sum.inr a)
  | func F ts, f =>
    func F fun i =>
      (ts i).restrictVarLeft (f ∘ Set.inclusion (subset_biUnion_of_mem
        (fun i => varFinsetLeft (ts i)) (mem_univ i)))
#align first_order.language.term.restrict_var_left FirstOrder.Language.Term.restrictVarLeft

end Term

/-- The representation of a constant symbol as a term. -/
def Constants.term (c : L.Constants) : L.Term α :=
  func c default
#align first_order.language.constants.term FirstOrder.Language.Constants.term

/-- Applies a unary function to a term. -/
def Functions.apply₁ (f : L.Functions 1) (t : L.Term α) : L.Term α :=
  func f ![t]
#align first_order.language.functions.apply₁ FirstOrder.Language.Functions.apply₁

/-- Applies a binary function to two terms. -/
def Functions.apply₂ (f : L.Functions 2) (t₁ t₂ : L.Term α) : L.Term α :=
  func f ![t₁, t₂]
#align first_order.language.functions.apply₂ FirstOrder.Language.Functions.apply₂

namespace Term

-- Porting note: universes in different order
/-- Sends a term with constants to a term with extra variables. -/
@[simp]
def constantsToVars : L[[γ]].Term α → L.Term (Sum γ α)
  | var a => var (Sum.inr a)
  | @func _ _ 0 f ts =>
    Sum.casesOn f (fun f => func f fun i => (ts i).constantsToVars) fun c => var (Sum.inl c)
  | @func _ _ (_n + 1) f ts =>
    Sum.casesOn f (fun f => func f fun i => (ts i).constantsToVars) fun c => isEmptyElim c
#align first_order.language.term.constants_to_vars FirstOrder.Language.Term.constantsToVars

-- Porting note: universes in different order
/-- Sends a term with extra variables to a term with constants. -/
@[simp]
def varsToConstants : L.Term (Sum γ α) → L[[γ]].Term α
  | var (Sum.inr a) => var a
  | var (Sum.inl c) => Constants.term (Sum.inr c)
  | func f ts => func (Sum.inl f) fun i => (ts i).varsToConstants
#align first_order.language.term.vars_to_constants FirstOrder.Language.Term.varsToConstants

/-- A bijection between terms with constants and terms with extra variables. -/
@[simps]
def constantsVarsEquiv : L[[γ]].Term α ≃ L.Term (Sum γ α) :=
  ⟨constantsToVars, varsToConstants, by
    intro t
    induction' t with _ n f _ ih
    · rfl
    · cases n
      · cases f
        · simp [constantsToVars, varsToConstants, ih]
        · simp [constantsToVars, varsToConstants, Constants.term, eq_iff_true_of_subsingleton]
      · cases' f with f f
        · simp [constantsToVars, varsToConstants, ih]
        · exact isEmptyElim f, by
    intro t
    induction' t with x n f _ ih
    · cases x <;> rfl
    · cases n <;> · simp [varsToConstants, constantsToVars, ih]⟩
#align first_order.language.term.constants_vars_equiv FirstOrder.Language.Term.constantsVarsEquiv

/-- A bijection between terms with constants and terms with extra variables. -/
def constantsVarsEquivLeft : L[[γ]].Term (Sum α β) ≃ L.Term (Sum (Sum γ α) β) :=
  constantsVarsEquiv.trans (relabelEquiv (Equiv.sumAssoc _ _ _)).symm
#align first_order.language.term.constants_vars_equiv_left FirstOrder.Language.Term.constantsVarsEquivLeft

@[simp]
theorem constantsVarsEquivLeft_apply (t : L[[γ]].Term (Sum α β)) :
    constantsVarsEquivLeft t = (constantsToVars t).relabel (Equiv.sumAssoc _ _ _).symm :=
  rfl
#align first_order.language.term.constants_vars_equiv_left_apply FirstOrder.Language.Term.constantsVarsEquivLeft_apply

@[simp]
theorem constantsVarsEquivLeft_symm_apply (t : L.Term (Sum (Sum γ α) β)) :
    constantsVarsEquivLeft.symm t = varsToConstants (t.relabel (Equiv.sumAssoc _ _ _)) :=
  rfl
#align first_order.language.term.constants_vars_equiv_left_symm_apply FirstOrder.Language.Term.constantsVarsEquivLeft_symm_apply

instance inhabitedOfVar [Inhabited α] : Inhabited (L.Term α) :=
  ⟨var default⟩
#align first_order.language.term.inhabited_of_var FirstOrder.Language.Term.inhabitedOfVar

instance inhabitedOfConstant [Inhabited L.Constants] : Inhabited (L.Term α) :=
  ⟨(default : L.Constants).term⟩
#align first_order.language.term.inhabited_of_constant FirstOrder.Language.Term.inhabitedOfConstant

/-- Raises all of the `Fin`-indexed variables of a term greater than or equal to `m` by `n'`. -/
def liftAt {n : ℕ} (n' m : ℕ) : L.Term (Sum α (Fin n)) → L.Term (Sum α (Fin (n + n'))) :=
  relabel (Sum.map id fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n')
#align first_order.language.term.lift_at FirstOrder.Language.Term.liftAt

-- Porting note: universes in different order
/-- Substitutes the variables in a given term with terms. -/
@[simp]
def subst : L.Term α → (α → L.Term β) → L.Term β
  | var a, tf => tf a
  | func f ts, tf => func f fun i => (ts i).subst tf
#align first_order.language.term.subst FirstOrder.Language.Term.subst

end Term

scoped[FirstOrder] prefix:arg "&" => FirstOrder.Language.Term.var ∘ Sum.inr

namespace LHom

open Term

-- Porting note: universes in different order
/-- Maps a term's symbols along a language map. -/
@[simp]
def onTerm (φ : L →ᴸ L') : L.Term α → L'.Term α
  | var i => var i
  | func f ts => func (φ.onFunction f) fun i => onTerm φ (ts i)
set_option linter.uppercaseLean3 false in
#align first_order.language.LHom.on_term FirstOrder.Language.LHom.onTerm

@[simp]
theorem id_onTerm : ((LHom.id L).onTerm : L.Term α → L.Term α) = id := by
  ext t
  induction' t with _ _ _ _ ih
  · rfl
  · simp_rw [onTerm, ih]
    rfl
set_option linter.uppercaseLean3 false in
#align first_order.language.LHom.id_on_term FirstOrder.Language.LHom.id_onTerm

@[simp]
theorem comp_onTerm {L'' : Language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onTerm : L.Term α → L''.Term α) = φ.onTerm ∘ ψ.onTerm := by
  ext t
  induction' t with _ _ _ _ ih
  · rfl
  · simp_rw [onTerm, ih]
    rfl
set_option linter.uppercaseLean3 false in
#align first_order.language.LHom.comp_on_term FirstOrder.Language.LHom.comp_onTerm

end LHom

/-- Maps a term's symbols along a language equivalence. -/
@[simps]
def Lequiv.onTerm (φ : L ≃ᴸ L') : L.Term α ≃ L'.Term α where
  toFun := φ.toLHom.onTerm
  invFun := φ.invLHom.onTerm
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LHom.comp_onTerm, φ.left_inv, LHom.id_onTerm]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LHom.comp_onTerm, φ.right_inv, LHom.id_onTerm]
set_option linter.uppercaseLean3 false in
#align first_order.language.Lequiv.on_term FirstOrder.Language.Lequiv.onTerm

variable (L) (α)

/-- `BoundedFormula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive BoundedFormula : ℕ → Type max u v u'
  | falsum {n} : BoundedFormula n
  | equal {n} (t₁ t₂ : L.Term (Sum α (Fin n))) : BoundedFormula n
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (Sum α (Fin n))) : BoundedFormula n
  | imp {n} (f₁ f₂ : BoundedFormula n) : BoundedFormula n
  | all {n} (f : BoundedFormula (n + 1)) : BoundedFormula n
#align first_order.language.bounded_formula FirstOrder.Language.BoundedFormula

/-- `Formula α` is the type of formulas with all free variables indexed by `α`. -/
abbrev Formula :=
  L.BoundedFormula α 0
#align first_order.language.formula FirstOrder.Language.Formula

/-- A sentence is a formula with no free variables. -/
abbrev Sentence :=
  L.Formula Empty
#align first_order.language.sentence FirstOrder.Language.Sentence

/-- A theory is a set of sentences. -/
abbrev Theory :=
  Set L.Sentence
set_option linter.uppercaseLean3 false in
#align first_order.language.Theory FirstOrder.Language.Theory

variable {L} {α} {n : ℕ}

/-- Applies a relation to terms as a bounded formula. -/
def Relations.boundedFormula {l : ℕ} (R : L.Relations n) (ts : Fin n → L.Term (Sum α (Fin l))) :
    L.BoundedFormula α l :=
  BoundedFormula.rel R ts
#align first_order.language.relations.bounded_formula FirstOrder.Language.Relations.boundedFormula

/-- Applies a unary relation to a term as a bounded formula. -/
def Relations.boundedFormula₁ (r : L.Relations 1) (t : L.Term (Sum α (Fin n))) :
    L.BoundedFormula α n :=
  r.boundedFormula ![t]
#align first_order.language.relations.bounded_formula₁ FirstOrder.Language.Relations.boundedFormula₁

/-- Applies a binary relation to two terms as a bounded formula. -/
def Relations.boundedFormula₂ (r : L.Relations 2) (t₁ t₂ : L.Term (Sum α (Fin n))) :
    L.BoundedFormula α n :=
  r.boundedFormula ![t₁, t₂]
#align first_order.language.relations.bounded_formula₂ FirstOrder.Language.Relations.boundedFormula₂

/-- The equality of two terms as a bounded formula. -/
def Term.bdEqual (t₁ t₂ : L.Term (Sum α (Fin n))) : L.BoundedFormula α n :=
  BoundedFormula.equal t₁ t₂
#align first_order.language.term.bd_equal FirstOrder.Language.Term.bdEqual

/-- Applies a relation to terms as a bounded formula. -/
def Relations.formula (R : L.Relations n) (ts : Fin n → L.Term α) : L.Formula α :=
  R.boundedFormula fun i => (ts i).relabel Sum.inl
#align first_order.language.relations.formula FirstOrder.Language.Relations.formula

/-- Applies a unary relation to a term as a formula. -/
def Relations.formula₁ (r : L.Relations 1) (t : L.Term α) : L.Formula α :=
  r.formula ![t]
#align first_order.language.relations.formula₁ FirstOrder.Language.Relations.formula₁

/-- Applies a binary relation to two terms as a formula. -/
def Relations.formula₂ (r : L.Relations 2) (t₁ t₂ : L.Term α) : L.Formula α :=
  r.formula ![t₁, t₂]
#align first_order.language.relations.formula₂ FirstOrder.Language.Relations.formula₂

/-- The equality of two terms as a first-order formula. -/
def Term.equal (t₁ t₂ : L.Term α) : L.Formula α :=
  (t₁.relabel Sum.inl).bdEqual (t₂.relabel Sum.inl)
#align first_order.language.term.equal FirstOrder.Language.Term.equal

namespace BoundedFormula

instance : Inhabited (L.BoundedFormula α n) :=
  ⟨falsum⟩

instance : Bot (L.BoundedFormula α n) :=
  ⟨falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[match_pattern]
protected def not (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  φ.imp ⊥
#align first_order.language.bounded_formula.not FirstOrder.Language.BoundedFormula.not

/-- Puts an `∃` quantifier on a bounded formula. -/
@[match_pattern]
protected def ex (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  φ.not.all.not
#align first_order.language.bounded_formula.ex FirstOrder.Language.BoundedFormula.ex

instance : Top (L.BoundedFormula α n) :=
  ⟨BoundedFormula.not ⊥⟩

instance : Inf (L.BoundedFormula α n) :=
  ⟨fun f g => (f.imp g.not).not⟩

instance : Sup (L.BoundedFormula α n) :=
  ⟨fun f g => f.not.imp g⟩

/-- The biimplication between two bounded formulas. -/
protected def iff (φ ψ : L.BoundedFormula α n) :=
  φ.imp ψ ⊓ ψ.imp φ
#align first_order.language.bounded_formula.iff FirstOrder.Language.BoundedFormula.iff

open Finset

-- Porting note: universes in different order
/-- The `Finset` of variables used in a given formula. -/
@[simp]
def freeVarFinset [DecidableEq α] : ∀ {n}, L.BoundedFormula α n → Finset α
  | _n, falsum => ∅
  | _n, equal t₁ t₂ => t₁.varFinsetLeft ∪ t₂.varFinsetLeft
  | _n, rel _R ts => univ.biUnion fun i => (ts i).varFinsetLeft
  | _n, imp f₁ f₂ => f₁.freeVarFinset ∪ f₂.freeVarFinset
  | _n, all f => f.freeVarFinset
#align first_order.language.bounded_formula.free_var_finset FirstOrder.Language.BoundedFormula.freeVarFinset

-- Porting note: universes in different order
/-- Casts `L.BoundedFormula α m` as `L.BoundedFormula α n`, where `m ≤ n`. -/
@[simp]
def castLE : ∀ {m n : ℕ} (_h : m ≤ n), L.BoundedFormula α m → L.BoundedFormula α n
  | _m, _n, _h, falsum => falsum
  | _m, _n, h, equal t₁ t₂ =>
    equal (t₁.relabel (Sum.map id (Fin.castLE h))) (t₂.relabel (Sum.map id (Fin.castLE h)))
  | _m, _n, h, rel R ts => rel R (Term.relabel (Sum.map id (Fin.castLE h)) ∘ ts)
  | _m, _n, h, imp f₁ f₂ => (f₁.castLE h).imp (f₂.castLE h)
  | _m, _n, h, all f => (f.castLE (add_le_add_right h 1)).all
#align first_order.language.bounded_formula.cast_le FirstOrder.Language.BoundedFormula.castLE

@[simp]
theorem castLE_rfl {n} (h : n ≤ n) (φ : L.BoundedFormula α n) : φ.castLE h = φ := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp [Fin.castLE_of_eq]
  · simp [Fin.castLE_of_eq]
  · simp [Fin.castLE_of_eq, ih1, ih2]
  · simp [Fin.castLE_of_eq, ih3]
#align first_order.language.bounded_formula.cast_le_rfl FirstOrder.Language.BoundedFormula.castLE_rfl

@[simp]
theorem castLE_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) (φ : L.BoundedFormula α k) :
    (φ.castLE km).castLE mn = φ.castLE (km.trans mn) := by
  revert m n
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3 <;> intro m n km mn
  · rfl
  · simp
  · simp only [castLE, eq_self_iff_true, heq_iff_eq, true_and_iff]
    rw [← Function.comp.assoc, Term.relabel_comp_relabel]
    simp
  · simp [ih1, ih2]
  · simp only [castLE, ih3]
#align first_order.language.bounded_formula.cast_le_cast_le FirstOrder.Language.BoundedFormula.castLE_castLE

@[simp]
theorem castLE_comp_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) :
    (BoundedFormula.castLE mn ∘ BoundedFormula.castLE km :
        L.BoundedFormula α k → L.BoundedFormula α n) =
      BoundedFormula.castLE (km.trans mn) :=
  funext (castLE_castLE km mn)
#align first_order.language.bounded_formula.cast_le_comp_cast_le FirstOrder.Language.BoundedFormula.castLE_comp_castLE

-- Porting note: universes in different order
/-- Restricts a bounded formula to only use a particular set of free variables. -/
def restrictFreeVar [DecidableEq α] :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (_f : φ.freeVarFinset → β), L.BoundedFormula β n
  | _n, falsum, _f => falsum
  | _n, equal t₁ t₂, f =>
    equal (t₁.restrictVarLeft (f ∘ Set.inclusion subset_union_left))
      (t₂.restrictVarLeft (f ∘ Set.inclusion subset_union_right))
  | _n, rel R ts, f =>
    rel R fun i => (ts i).restrictVarLeft (f ∘ Set.inclusion
      (subset_biUnion_of_mem (fun i => Term.varFinsetLeft (ts i)) (mem_univ i)))
  | _n, imp φ₁ φ₂, f =>
    (φ₁.restrictFreeVar (f ∘ Set.inclusion subset_union_left)).imp
      (φ₂.restrictFreeVar (f ∘ Set.inclusion subset_union_right))
  | _n, all φ, f => (φ.restrictFreeVar f).all
#align first_order.language.bounded_formula.restrict_free_var FirstOrder.Language.BoundedFormula.restrictFreeVar

-- Porting note: universes in different order
/-- Places universal quantifiers on all extra variables of a bounded formula. -/
def alls : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | _n + 1, φ => φ.all.alls
#align first_order.language.bounded_formula.alls FirstOrder.Language.BoundedFormula.alls

-- Porting note: universes in different order
/-- Places existential quantifiers on all extra variables of a bounded formula. -/
def exs : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | _n + 1, φ => φ.ex.exs
#align first_order.language.bounded_formula.exs FirstOrder.Language.BoundedFormula.exs

-- Porting note: universes in different order
/-- Maps bounded formulas along a map of terms and a map of relations. -/
def mapTermRel {g : ℕ → ℕ} (ft : ∀ n, L.Term (Sum α (Fin n)) → L'.Term (Sum β (Fin (g n))))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (h : ∀ n, L'.BoundedFormula β (g (n + 1)) → L'.BoundedFormula β (g n + 1)) :
    ∀ {n}, L.BoundedFormula α n → L'.BoundedFormula β (g n)
  | _n, falsum => falsum
  | _n, equal t₁ t₂ => equal (ft _ t₁) (ft _ t₂)
  | _n, rel R ts => rel (fr _ R) fun i => ft _ (ts i)
  | _n, imp φ₁ φ₂ => (φ₁.mapTermRel ft fr h).imp (φ₂.mapTermRel ft fr h)
  | n, all φ => (h n (φ.mapTermRel ft fr h)).all
#align first_order.language.bounded_formula.map_term_rel FirstOrder.Language.BoundedFormula.mapTermRel

/-- Raises all of the `Fin`-indexed variables of a formula greater than or equal to `m` by `n'`. -/
def liftAt : ∀ {n : ℕ} (n' _m : ℕ), L.BoundedFormula α n → L.BoundedFormula α (n + n') :=
  fun {n} n' m φ =>
  φ.mapTermRel (fun k t => t.liftAt n' m) (fun _ => id) fun _ =>
    castLE (by rw [add_assoc, add_comm 1, add_assoc])
#align first_order.language.bounded_formula.lift_at FirstOrder.Language.BoundedFormula.liftAt

@[simp]
theorem mapTermRel_mapTermRel {L'' : Language}
    (ft : ∀ n, L.Term (Sum α (Fin n)) → L'.Term (Sum β (Fin n)))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (ft' : ∀ n, L'.Term (Sum β (Fin n)) → L''.Term (Sum γ (Fin n)))
    (fr' : ∀ n, L'.Relations n → L''.Relations n) {n} (φ : L.BoundedFormula α n) :
    ((φ.mapTermRel ft fr fun _ => id).mapTermRel ft' fr' fun _ => id) =
      φ.mapTermRel (fun _ => ft' _ ∘ ft _) (fun _ => fr' _ ∘ fr _) fun _ => id := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp [mapTermRel]
  · simp [mapTermRel]
  · simp [mapTermRel, ih1, ih2]
  · simp [mapTermRel, ih3]
#align first_order.language.bounded_formula.map_term_rel_map_term_rel FirstOrder.Language.BoundedFormula.mapTermRel_mapTermRel

@[simp]
theorem mapTermRel_id_id_id {n} (φ : L.BoundedFormula α n) :
    (φ.mapTermRel (fun _ => id) (fun _ => id) fun _ => id) = φ := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp [mapTermRel]
  · simp [mapTermRel]
  · simp [mapTermRel, ih1, ih2]
  · simp [mapTermRel, ih3]
#align first_order.language.bounded_formula.map_term_rel_id_id_id FirstOrder.Language.BoundedFormula.mapTermRel_id_id_id

/-- An equivalence of bounded formulas given by an equivalence of terms and an equivalence of
relations. -/
@[simps]
def mapTermRelEquiv (ft : ∀ n, L.Term (Sum α (Fin n)) ≃ L'.Term (Sum β (Fin n)))
    (fr : ∀ n, L.Relations n ≃ L'.Relations n) {n} : L.BoundedFormula α n ≃ L'.BoundedFormula β n :=
  ⟨mapTermRel (fun n => ft n) (fun n => fr n) fun _ => id,
    mapTermRel (fun n => (ft n).symm) (fun n => (fr n).symm) fun _ => id, fun φ => by simp, fun φ =>
    by simp⟩
#align first_order.language.bounded_formula.map_term_rel_equiv FirstOrder.Language.BoundedFormula.mapTermRelEquiv

/-- A function to help relabel the variables in bounded formulas. -/
def relabelAux (g : α → Sum β (Fin n)) (k : ℕ) : Sum α (Fin k) → Sum β (Fin (n + k)) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id
#align first_order.language.bounded_formula.relabel_aux FirstOrder.Language.BoundedFormula.relabelAux

@[simp]
theorem sum_elim_comp_relabelAux {m : ℕ} {g : α → Sum β (Fin n)} {v : β → M}
    {xs : Fin (n + m) → M} : Sum.elim v xs ∘ relabelAux g m =
    Sum.elim (Sum.elim v (xs ∘ castAdd m) ∘ g) (xs ∘ natAdd n) := by
  ext x
  cases' x with x x
  · simp only [BoundedFormula.relabelAux, Function.comp_apply, Sum.map_inl, Sum.elim_inl]
    cases' g x with l r <;> simp
  · simp [BoundedFormula.relabelAux]
#align first_order.language.bounded_formula.sum_elim_comp_relabel_aux FirstOrder.Language.BoundedFormula.sum_elim_comp_relabelAux

@[simp]
theorem relabelAux_sum_inl (k : ℕ) :
    relabelAux (Sum.inl : α → Sum α (Fin n)) k = Sum.map id (natAdd n) := by
  ext x
  cases x <;> · simp [relabelAux]
#align first_order.language.bounded_formula.relabel_aux_sum_inl FirstOrder.Language.BoundedFormula.relabelAux_sum_inl

/-- Relabels a bounded formula's variables along a particular function. -/
def relabel (g : α → Sum β (Fin n)) {k} (φ : L.BoundedFormula α k) : L.BoundedFormula β (n + k) :=
  φ.mapTermRel (fun _ t => t.relabel (relabelAux g _)) (fun _ => id) fun _ =>
    castLE (ge_of_eq (add_assoc _ _ _))
#align first_order.language.bounded_formula.relabel FirstOrder.Language.BoundedFormula.relabel

/-- Relabels a bounded formula's free variables along a bijection. -/
def relabelEquiv (g : α ≃ β) {k} : L.BoundedFormula α k ≃ L.BoundedFormula β k :=
  mapTermRelEquiv (fun _n => Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)))
    fun _n => _root_.Equiv.refl _
#align first_order.language.bounded_formula.relabel_equiv FirstOrder.Language.BoundedFormula.relabelEquiv

@[simp]
theorem relabel_falsum (g : α → Sum β (Fin n)) {k} :
    (falsum : L.BoundedFormula α k).relabel g = falsum :=
  rfl
#align first_order.language.bounded_formula.relabel_falsum FirstOrder.Language.BoundedFormula.relabel_falsum

@[simp]
theorem relabel_bot (g : α → Sum β (Fin n)) {k} : (⊥ : L.BoundedFormula α k).relabel g = ⊥ :=
  rfl
#align first_order.language.bounded_formula.relabel_bot FirstOrder.Language.BoundedFormula.relabel_bot

@[simp]
theorem relabel_imp (g : α → Sum β (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ.imp ψ).relabel g = (φ.relabel g).imp (ψ.relabel g) :=
  rfl
#align first_order.language.bounded_formula.relabel_imp FirstOrder.Language.BoundedFormula.relabel_imp

@[simp]
theorem relabel_not (g : α → Sum β (Fin n)) {k} (φ : L.BoundedFormula α k) :
    φ.not.relabel g = (φ.relabel g).not := by simp [BoundedFormula.not]
#align first_order.language.bounded_formula.relabel_not FirstOrder.Language.BoundedFormula.relabel_not

@[simp]
theorem relabel_all (g : α → Sum β (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.all.relabel g = (φ.relabel g).all := by
  rw [relabel, mapTermRel, relabel]
  simp
#align first_order.language.bounded_formula.relabel_all FirstOrder.Language.BoundedFormula.relabel_all

@[simp]
theorem relabel_ex (g : α → Sum β (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.ex.relabel g = (φ.relabel g).ex := by simp [BoundedFormula.ex]
#align first_order.language.bounded_formula.relabel_ex FirstOrder.Language.BoundedFormula.relabel_ex

@[simp]
theorem relabel_sum_inl (φ : L.BoundedFormula α n) :
    (φ.relabel Sum.inl : L.BoundedFormula α (0 + n)) = φ.castLE (ge_of_eq (zero_add n)) := by
  simp only [relabel, relabelAux_sum_inl]
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]
  · simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]; rfl
  · simp [mapTermRel, ih1, ih2]
  · simp [mapTermRel, ih3, castLE]
#align first_order.language.bounded_formula.relabel_sum_inl FirstOrder.Language.BoundedFormula.relabel_sum_inl

/-- Substitutes the variables in a given formula with terms. -/
def subst {n : ℕ} (φ : L.BoundedFormula α n) (f : α → L.Term β) : L.BoundedFormula β n :=
  φ.mapTermRel (fun _ t => t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (var ∘ Sum.inr)))
    (fun _ => id) fun _ => id
#align first_order.language.bounded_formula.subst FirstOrder.Language.BoundedFormula.subst

/-- A bijection sending formulas with constants to formulas with extra variables. -/
def constantsVarsEquiv : L[[γ]].BoundedFormula α n ≃ L.BoundedFormula (Sum γ α) n :=
  mapTermRelEquiv (fun _ => Term.constantsVarsEquivLeft) fun _ => Equiv.sumEmpty _ _
#align first_order.language.bounded_formula.constants_vars_equiv FirstOrder.Language.BoundedFormula.constantsVarsEquiv

-- Porting note: universes in different order
/-- Turns the extra variables of a bounded formula into free variables. -/
@[simp]
def toFormula : ∀ {n : ℕ}, L.BoundedFormula α n → L.Formula (Sum α (Fin n))
  | _n, falsum => falsum
  | _n, equal t₁ t₂ => t₁.equal t₂
  | _n, rel R ts => R.formula ts
  | _n, imp φ₁ φ₂ => φ₁.toFormula.imp φ₂.toFormula
  | _n, all φ =>
    (φ.toFormula.relabel
        (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ finSumFinEquiv.symm))).all
#align first_order.language.bounded_formula.to_formula FirstOrder.Language.BoundedFormula.toFormula

/-- take the disjunction of a finite set of formulas -/
noncomputable def iSup (s : Finset β) (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  (s.toList.map f).foldr (· ⊔ ·) ⊥

/-- take the conjunction of a finite set of formulas -/
noncomputable def iInf (s : Finset β) (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  (s.toList.map f).foldr (· ⊓ ·) ⊤


variable {l : ℕ} {φ ψ : L.BoundedFormula α l} {θ : L.BoundedFormula α l.succ}
variable {v : α → M} {xs : Fin l → M}

/-- An atomic formula is either equality or a relation symbol applied to terms.
  Note that `⊥` and `⊤` are not considered atomic in this convention. -/
inductive IsAtomic : L.BoundedFormula α n → Prop
  | equal (t₁ t₂ : L.Term (Sum α (Fin n))) : IsAtomic (t₁.bdEqual t₂)
  | rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (Sum α (Fin n))) :
    IsAtomic (R.boundedFormula ts)
#align first_order.language.bounded_formula.is_atomic FirstOrder.Language.BoundedFormula.IsAtomic

theorem not_all_isAtomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsAtomic := fun con => by
  cases con
#align first_order.language.bounded_formula.not_all_is_atomic FirstOrder.Language.BoundedFormula.not_all_isAtomic

theorem not_ex_isAtomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsAtomic := fun con => by cases con
#align first_order.language.bounded_formula.not_ex_is_atomic FirstOrder.Language.BoundedFormula.not_ex_isAtomic

theorem IsAtomic.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsAtomic)
    (f : α → Sum β (Fin n)) : (φ.relabel f).IsAtomic :=
  IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _
#align first_order.language.bounded_formula.is_atomic.relabel FirstOrder.Language.BoundedFormula.IsAtomic.relabel

theorem IsAtomic.liftAt {k m : ℕ} (h : IsAtomic φ) : (φ.liftAt k m).IsAtomic :=
  IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _
#align first_order.language.bounded_formula.is_atomic.lift_at FirstOrder.Language.BoundedFormula.IsAtomic.liftAt

theorem IsAtomic.castLE {h : l ≤ n} (hφ : IsAtomic φ) : (φ.castLE h).IsAtomic :=
  IsAtomic.recOn hφ (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _
#align first_order.language.bounded_formula.is_atomic.cast_le FirstOrder.Language.BoundedFormula.IsAtomic.castLE

/-- A quantifier-free formula is a formula defined without quantifiers. These are all equivalent
to boolean combinations of atomic formulas. -/
inductive IsQF : L.BoundedFormula α n → Prop
  | falsum : IsQF falsum
  | of_isAtomic {φ} (h : IsAtomic φ) : IsQF φ
  | imp {φ₁ φ₂} (h₁ : IsQF φ₁) (h₂ : IsQF φ₂) : IsQF (φ₁.imp φ₂)
#align first_order.language.bounded_formula.is_qf FirstOrder.Language.BoundedFormula.IsQF

theorem IsAtomic.isQF {φ : L.BoundedFormula α n} : IsAtomic φ → IsQF φ :=
  IsQF.of_isAtomic
#align first_order.language.bounded_formula.is_atomic.is_qf FirstOrder.Language.BoundedFormula.IsAtomic.isQF

theorem isQF_bot : IsQF (⊥ : L.BoundedFormula α n) :=
  IsQF.falsum
#align first_order.language.bounded_formula.is_qf_bot FirstOrder.Language.BoundedFormula.isQF_bot

theorem IsQF.not {φ : L.BoundedFormula α n} (h : IsQF φ) : IsQF φ.not :=
  h.imp isQF_bot
#align first_order.language.bounded_formula.is_qf.not FirstOrder.Language.BoundedFormula.IsQF.not

theorem IsQF.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsQF) (f : α → Sum β (Fin n)) :
    (φ.relabel f).IsQF :=
  IsQF.recOn h isQF_bot (fun h => (h.relabel f).isQF) fun _ _ h1 h2 => h1.imp h2
#align first_order.language.bounded_formula.is_qf.relabel FirstOrder.Language.BoundedFormula.IsQF.relabel

theorem IsQF.liftAt {k m : ℕ} (h : IsQF φ) : (φ.liftAt k m).IsQF :=
  IsQF.recOn h isQF_bot (fun ih => ih.liftAt.isQF) fun _ _ ih1 ih2 => ih1.imp ih2
#align first_order.language.bounded_formula.is_qf.lift_at FirstOrder.Language.BoundedFormula.IsQF.liftAt

theorem IsQF.castLE {h : l ≤ n} (hφ : IsQF φ) : (φ.castLE h).IsQF :=
  IsQF.recOn hφ isQF_bot (fun ih => ih.castLE.isQF) fun _ _ ih1 ih2 => ih1.imp ih2
#align first_order.language.bounded_formula.is_qf.cast_le FirstOrder.Language.BoundedFormula.IsQF.castLE

theorem not_all_isQF (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsQF := fun con => by
  cases' con with _ con
  exact φ.not_all_isAtomic con
#align first_order.language.bounded_formula.not_all_is_qf FirstOrder.Language.BoundedFormula.not_all_isQF

theorem not_ex_isQF (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsQF := fun con => by
  cases' con with _ con _ _ con
  · exact φ.not_ex_isAtomic con
  · exact not_all_isQF _ con
#align first_order.language.bounded_formula.not_ex_is_qf FirstOrder.Language.BoundedFormula.not_ex_isQF

/-- Indicates that a bounded formula is in prenex normal form - that is, it consists of quantifiers
  applied to a quantifier-free formula. -/
inductive IsPrenex : ∀ {n}, L.BoundedFormula α n → Prop
  | of_isQF {n} {φ : L.BoundedFormula α n} (h : IsQF φ) : IsPrenex φ
  | all {n} {φ : L.BoundedFormula α (n + 1)} (h : IsPrenex φ) : IsPrenex φ.all
  | ex {n} {φ : L.BoundedFormula α (n + 1)} (h : IsPrenex φ) : IsPrenex φ.ex
#align first_order.language.bounded_formula.is_prenex FirstOrder.Language.BoundedFormula.IsPrenex

theorem IsQF.isPrenex {φ : L.BoundedFormula α n} : IsQF φ → IsPrenex φ :=
  IsPrenex.of_isQF
#align first_order.language.bounded_formula.is_qf.is_prenex FirstOrder.Language.BoundedFormula.IsQF.isPrenex

theorem IsAtomic.isPrenex {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsPrenex φ :=
  h.isQF.isPrenex
#align first_order.language.bounded_formula.is_atomic.is_prenex FirstOrder.Language.BoundedFormula.IsAtomic.isPrenex

theorem IsPrenex.induction_on_all_not {P : ∀ {n}, L.BoundedFormula α n → Prop}
    {φ : L.BoundedFormula α n} (h : IsPrenex φ)
    (hq : ∀ {m} {ψ : L.BoundedFormula α m}, ψ.IsQF → P ψ)
    (ha : ∀ {m} {ψ : L.BoundedFormula α (m + 1)}, P ψ → P ψ.all)
    (hn : ∀ {m} {ψ : L.BoundedFormula α m}, P ψ → P ψ.not) : P φ :=
  IsPrenex.recOn h hq (fun _ => ha) fun _ ih => hn (ha (hn ih))
#align first_order.language.bounded_formula.is_prenex.induction_on_all_not FirstOrder.Language.BoundedFormula.IsPrenex.induction_on_all_not

theorem IsPrenex.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsPrenex)
    (f : α → Sum β (Fin n)) : (φ.relabel f).IsPrenex :=
  IsPrenex.recOn h (fun h => (h.relabel f).isPrenex) (fun _ h => by simp [h.all])
    fun _ h => by simp [h.ex]
#align first_order.language.bounded_formula.is_prenex.relabel FirstOrder.Language.BoundedFormula.IsPrenex.relabel

theorem IsPrenex.castLE (hφ : IsPrenex φ) : ∀ {n} {h : l ≤ n}, (φ.castLE h).IsPrenex :=
  IsPrenex.recOn (motive := @fun l φ _ => ∀ (n : ℕ) (h : l ≤ n), (φ.castLE h).IsPrenex) hφ
    (@fun _ _ ih _ _ => ih.castLE.isPrenex)
    (@fun _ _ _ ih _ _ => (ih _ _).all)
    (@fun _ _ _ ih _ _ => (ih _ _).ex) _ _
#align first_order.language.bounded_formula.is_prenex.cast_le FirstOrder.Language.BoundedFormula.IsPrenex.castLE

theorem IsPrenex.liftAt {k m : ℕ} (h : IsPrenex φ) : (φ.liftAt k m).IsPrenex :=
  IsPrenex.recOn h (fun ih => ih.liftAt.isPrenex) (fun _ ih => ih.castLE.all)
    fun _ ih => ih.castLE.ex
#align first_order.language.bounded_formula.is_prenex.lift_at FirstOrder.Language.BoundedFormula.IsPrenex.liftAt

-- Porting note: universes in different order
/-- An auxiliary operation to `FirstOrder.Language.BoundedFormula.toPrenex`.
  If `φ` is quantifier-free and `ψ` is in prenex normal form, then `φ.toPrenexImpRight ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def toPrenexImpRight : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n
  | n, φ, BoundedFormula.ex ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).ex
  | n, φ, all ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).all
  | _n, φ, ψ => φ.imp ψ
#align first_order.language.bounded_formula.to_prenex_imp_right FirstOrder.Language.BoundedFormula.toPrenexImpRight

theorem IsQF.toPrenexImpRight {φ : L.BoundedFormula α n} :
    ∀ {ψ : L.BoundedFormula α n}, IsQF ψ → φ.toPrenexImpRight ψ = φ.imp ψ
  | _, IsQF.falsum => rfl
  | _, IsQF.of_isAtomic (IsAtomic.equal _ _) => rfl
  | _, IsQF.of_isAtomic (IsAtomic.rel _ _) => rfl
  | _, IsQF.imp IsQF.falsum _ => rfl
  | _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.equal _ _)) _ => rfl
  | _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.rel _ _)) _ => rfl
  | _, IsQF.imp (IsQF.imp _ _) _ => rfl
#align first_order.language.bounded_formula.is_qf.to_prenex_imp_right FirstOrder.Language.BoundedFormula.IsQF.toPrenexImpRight

theorem isPrenex_toPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImpRight ψ) := by
  induction' hψ with _ _ hψ _ _ _ ih1 _ _ _ ih2
  · rw [hψ.toPrenexImpRight]
    exact (hφ.imp hψ).isPrenex
  · exact (ih1 hφ.liftAt).all
  · exact (ih2 hφ.liftAt).ex
#align first_order.language.bounded_formula.is_prenex_to_prenex_imp_right FirstOrder.Language.BoundedFormula.isPrenex_toPrenexImpRight

-- Porting note: universes in different order
/-- An auxiliary operation to `FirstOrder.Language.BoundedFormula.toPrenex`.
  If `φ` and `ψ` are in prenex normal form, then `φ.toPrenexImp ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def toPrenexImp : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n
  | n, BoundedFormula.ex φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).all
  | n, all φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).ex
  | _, φ, ψ => φ.toPrenexImpRight ψ
#align first_order.language.bounded_formula.to_prenex_imp FirstOrder.Language.BoundedFormula.toPrenexImp

theorem IsQF.toPrenexImp :
    ∀ {φ ψ : L.BoundedFormula α n}, φ.IsQF → φ.toPrenexImp ψ = φ.toPrenexImpRight ψ
  | _, _, IsQF.falsum => rfl
  | _, _, IsQF.of_isAtomic (IsAtomic.equal _ _) => rfl
  | _, _, IsQF.of_isAtomic (IsAtomic.rel _ _) => rfl
  | _, _, IsQF.imp IsQF.falsum _ => rfl
  | _, _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.equal _ _)) _ => rfl
  | _, _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.rel _ _)) _ => rfl
  | _, _, IsQF.imp (IsQF.imp _ _) _ => rfl
#align first_order.language.bounded_formula.is_qf.to_prenex_imp FirstOrder.Language.BoundedFormula.IsQF.toPrenexImp

theorem isPrenex_toPrenexImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImp ψ) := by
  induction' hφ with _ _ hφ _ _ _ ih1 _ _ _ ih2
  · rw [hφ.toPrenexImp]
    exact isPrenex_toPrenexImpRight hφ hψ
  · exact (ih1 hψ.liftAt).ex
  · exact (ih2 hψ.liftAt).all
#align first_order.language.bounded_formula.is_prenex_to_prenex_imp FirstOrder.Language.BoundedFormula.isPrenex_toPrenexImp

-- Porting note: universes in different order
/-- For any bounded formula `φ`, `φ.toPrenex` is a semantically-equivalent formula in prenex normal
  form. -/
def toPrenex : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n
  | _, falsum => ⊥
  | _, equal t₁ t₂ => t₁.bdEqual t₂
  | _, rel R ts => rel R ts
  | _, imp f₁ f₂ => f₁.toPrenex.toPrenexImp f₂.toPrenex
  | _, all f => f.toPrenex.all
#align first_order.language.bounded_formula.to_prenex FirstOrder.Language.BoundedFormula.toPrenex

theorem toPrenex_isPrenex (φ : L.BoundedFormula α n) : φ.toPrenex.IsPrenex :=
  BoundedFormula.recOn φ isQF_bot.isPrenex (fun _ _ => (IsAtomic.equal _ _).isPrenex)
    (fun _ _ => (IsAtomic.rel _ _).isPrenex) (fun _ _ h1 h2 => isPrenex_toPrenexImp h1 h2)
    fun _ => IsPrenex.all
#align first_order.language.bounded_formula.to_prenex_is_prenex FirstOrder.Language.BoundedFormula.toPrenex_isPrenex

end BoundedFormula

namespace LHom

open BoundedFormula

-- Porting note: universes in different order
/-- Maps a bounded formula's symbols along a language map. -/
@[simp]
def onBoundedFormula (g : L →ᴸ L') : ∀ {k : ℕ}, L.BoundedFormula α k → L'.BoundedFormula α k
  | _k, falsum => falsum
  | _k, equal t₁ t₂ => (g.onTerm t₁).bdEqual (g.onTerm t₂)
  | _k, rel R ts => (g.onRelation R).boundedFormula (g.onTerm ∘ ts)
  | _k, imp f₁ f₂ => (onBoundedFormula g f₁).imp (onBoundedFormula g f₂)
  | _k, all f => (onBoundedFormula g f).all
set_option linter.uppercaseLean3 false in
#align first_order.language.Lhom.on_bounded_formula FirstOrder.Language.LHom.onBoundedFormula

@[simp]
theorem id_onBoundedFormula :
    ((LHom.id L).onBoundedFormula : L.BoundedFormula α n → L.BoundedFormula α n) = id := by
  ext f
  induction' f with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · rw [onBoundedFormula, LHom.id_onTerm, id, id, id, Term.bdEqual]
  · rw [onBoundedFormula, LHom.id_onTerm]
    rfl
  · rw [onBoundedFormula, ih1, ih2, id, id, id]
  · rw [onBoundedFormula, ih3, id, id]
set_option linter.uppercaseLean3 false in
#align first_order.language.Lhom.id_on_bounded_formula FirstOrder.Language.LHom.id_onBoundedFormula

@[simp]
theorem comp_onBoundedFormula {L'' : Language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onBoundedFormula : L.BoundedFormula α n → L''.BoundedFormula α n) =
      φ.onBoundedFormula ∘ ψ.onBoundedFormula := by
  ext f
  induction' f with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp only [onBoundedFormula, comp_onTerm, Function.comp_apply]
  · simp only [onBoundedFormula, comp_onRelation, comp_onTerm, Function.comp_apply]
    rfl
  · simp only [onBoundedFormula, Function.comp_apply, ih1, ih2, eq_self_iff_true, and_self_iff]
  · simp only [ih3, onBoundedFormula, Function.comp_apply]
set_option linter.uppercaseLean3 false in
#align first_order.language.Lhom.comp_on_bounded_formula FirstOrder.Language.LHom.comp_onBoundedFormula

/-- Maps a formula's symbols along a language map. -/
def onFormula (g : L →ᴸ L') : L.Formula α → L'.Formula α :=
  g.onBoundedFormula
set_option linter.uppercaseLean3 false in
#align first_order.language.Lhom.on_formula FirstOrder.Language.LHom.onFormula

/-- Maps a sentence's symbols along a language map. -/
def onSentence (g : L →ᴸ L') : L.Sentence → L'.Sentence :=
  g.onFormula
set_option linter.uppercaseLean3 false in
#align first_order.language.Lhom.on_sentence FirstOrder.Language.LHom.onSentence

/-- Maps a theory's symbols along a language map. -/
def onTheory (g : L →ᴸ L') (T : L.Theory) : L'.Theory :=
  g.onSentence '' T
set_option linter.uppercaseLean3 false in
#align first_order.language.Lhom.on_Theory FirstOrder.Language.LHom.onTheory

@[simp]
theorem mem_onTheory {g : L →ᴸ L'} {T : L.Theory} {φ : L'.Sentence} :
    φ ∈ g.onTheory T ↔ ∃ φ₀, φ₀ ∈ T ∧ g.onSentence φ₀ = φ :=
  Set.mem_image _ _ _
set_option linter.uppercaseLean3 false in
#align first_order.language.Lhom.mem_on_Theory FirstOrder.Language.LHom.mem_onTheory

end LHom

namespace LEquiv

/-- Maps a bounded formula's symbols along a language equivalence. -/
@[simps]
def onBoundedFormula (φ : L ≃ᴸ L') : L.BoundedFormula α n ≃ L'.BoundedFormula α n where
  toFun := φ.toLHom.onBoundedFormula
  invFun := φ.invLHom.onBoundedFormula
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LHom.comp_onBoundedFormula, φ.left_inv,
      LHom.id_onBoundedFormula]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LHom.comp_onBoundedFormula, φ.right_inv,
      LHom.id_onBoundedFormula]
set_option linter.uppercaseLean3 false in
#align first_order.language.Lequiv.on_bounded_formula FirstOrder.Language.LEquiv.onBoundedFormula

theorem onBoundedFormula_symm (φ : L ≃ᴸ L') :
    (φ.onBoundedFormula.symm : L'.BoundedFormula α n ≃ L.BoundedFormula α n) =
      φ.symm.onBoundedFormula :=
  rfl
set_option linter.uppercaseLean3 false in
#align first_order.language.Lequiv.on_bounded_formula_symm FirstOrder.Language.LEquiv.onBoundedFormula_symm

/-- Maps a formula's symbols along a language equivalence. -/
def onFormula (φ : L ≃ᴸ L') : L.Formula α ≃ L'.Formula α :=
  φ.onBoundedFormula
set_option linter.uppercaseLean3 false in
#align first_order.language.Lequiv.on_formula FirstOrder.Language.LEquiv.onFormula

@[simp]
theorem onFormula_apply (φ : L ≃ᴸ L') :
    (φ.onFormula : L.Formula α → L'.Formula α) = φ.toLHom.onFormula :=
  rfl
set_option linter.uppercaseLean3 false in
#align first_order.language.Lequiv.on_formula_apply FirstOrder.Language.LEquiv.onFormula_apply

@[simp]
theorem onFormula_symm (φ : L ≃ᴸ L') :
    (φ.onFormula.symm : L'.Formula α ≃ L.Formula α) = φ.symm.onFormula :=
  rfl
set_option linter.uppercaseLean3 false in
#align first_order.language.Lequiv.on_formula_symm FirstOrder.Language.LEquiv.onFormula_symm

/-- Maps a sentence's symbols along a language equivalence. -/
@[simps!] -- Porting note: add `!` to `simps`
def onSentence (φ : L ≃ᴸ L') : L.Sentence ≃ L'.Sentence :=
  φ.onFormula
set_option linter.uppercaseLean3 false in
#align first_order.language.Lequiv.on_sentence FirstOrder.Language.LEquiv.onSentence

end LEquiv

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

namespace Formula

/-- Relabels a formula's variables along a particular function. -/
def relabel (g : α → β) : L.Formula α → L.Formula β :=
  @BoundedFormula.relabel _ _ _ 0 (Sum.inl ∘ g) 0
#align first_order.language.formula.relabel FirstOrder.Language.Formula.relabel

/-- The graph of a function as a first-order formula. -/
def graph (f : L.Functions n) : L.Formula (Fin (n + 1)) :=
  Term.equal (var 0) (func f fun i => var i.succ)
#align first_order.language.formula.graph FirstOrder.Language.Formula.graph

/-- The negation of a formula. -/
protected nonrec abbrev not (φ : L.Formula α) : L.Formula α :=
  φ.not
#align first_order.language.formula.not FirstOrder.Language.Formula.not

/-- The implication between formulas, as a formula. -/
protected abbrev imp : L.Formula α → L.Formula α → L.Formula α :=
  BoundedFormula.imp
#align first_order.language.formula.imp FirstOrder.Language.Formula.imp

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
#align first_order.language.formula.iff FirstOrder.Language.Formula.iff

theorem isAtomic_graph (f : L.Functions n) : (graph f).IsAtomic :=
  BoundedFormula.IsAtomic.equal _ _
#align first_order.language.formula.is_atomic_graph FirstOrder.Language.Formula.isAtomic_graph

/-- A bijection sending formulas to sentences with constants. -/
def equivSentence : L.Formula α ≃ L[[α]].Sentence :=
  (BoundedFormula.constantsVarsEquiv.trans (BoundedFormula.relabelEquiv (Equiv.sumEmpty _ _))).symm
#align first_order.language.formula.equiv_sentence FirstOrder.Language.Formula.equivSentence

theorem equivSentence_not (φ : L.Formula α) : equivSentence φ.not = (equivSentence φ).not :=
  rfl
#align first_order.language.formula.equiv_sentence_not FirstOrder.Language.Formula.equivSentence_not

theorem equivSentence_inf (φ ψ : L.Formula α) :
    equivSentence (φ ⊓ ψ) = equivSentence φ ⊓ equivSentence ψ :=
  rfl
#align first_order.language.formula.equiv_sentence_inf FirstOrder.Language.Formula.equivSentence_inf

end Formula

namespace Relations

variable (r : L.Relations 2)

/-- The sentence indicating that a basic relation symbol is reflexive. -/
protected def reflexive : L.Sentence :=
  ∀'r.boundedFormula₂ (&0) &0
#align first_order.language.relations.reflexive FirstOrder.Language.Relations.reflexive

/-- The sentence indicating that a basic relation symbol is irreflexive. -/
protected def irreflexive : L.Sentence :=
  ∀'∼(r.boundedFormula₂ (&0) &0)
#align first_order.language.relations.irreflexive FirstOrder.Language.Relations.irreflexive

/-- The sentence indicating that a basic relation symbol is symmetric. -/
protected def symmetric : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0)
#align first_order.language.relations.symmetric FirstOrder.Language.Relations.symmetric

/-- The sentence indicating that a basic relation symbol is antisymmetric. -/
protected def antisymmetric : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0 ⟹ Term.bdEqual (&0) &1)
#align first_order.language.relations.antisymmetric FirstOrder.Language.Relations.antisymmetric

/-- The sentence indicating that a basic relation symbol is transitive. -/
protected def transitive : L.Sentence :=
  ∀'∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &2 ⟹ r.boundedFormula₂ (&0) &2)
#align first_order.language.relations.transitive FirstOrder.Language.Relations.transitive

/-- The sentence indicating that a basic relation symbol is total. -/
protected def total : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⊔ r.boundedFormula₂ (&1) &0)
#align first_order.language.relations.total FirstOrder.Language.Relations.total

end Relations

section Cardinality

variable (L)

/-- A sentence indicating that a structure has `n` distinct elements. -/
protected def Sentence.cardGe (n : ℕ) : L.Sentence :=
  ((((List.finRange n ×ˢ List.finRange n).filter fun ij : _ × _ => ij.1 ≠ ij.2).map
          fun ij : _ × _ => ∼((&ij.1).bdEqual &ij.2)).foldr
      (· ⊓ ·) ⊤).exs
#align first_order.language.sentence.card_ge FirstOrder.Language.Sentence.cardGe

/-- A theory indicating that a structure is infinite. -/
def infiniteTheory : L.Theory :=
  Set.range (Sentence.cardGe L)
#align first_order.language.infinite_theory FirstOrder.Language.infiniteTheory

/-- A theory that indicates a structure is nonempty. -/
def nonemptyTheory : L.Theory :=
  {Sentence.cardGe L 1}
#align first_order.language.nonempty_theory FirstOrder.Language.nonemptyTheory

/-- A theory indicating that each of a set of constants is distinct. -/
def distinctConstantsTheory (s : Set α) : L[[α]].Theory :=
  (fun ab : α × α => ((L.con ab.1).term.equal (L.con ab.2).term).not) ''
  (s ×ˢ s ∩ (Set.diagonal α)ᶜ)
#align first_order.language.distinct_constants_theory FirstOrder.Language.distinctConstantsTheory

variable {L}

open Set

theorem distinctConstantsTheory_mono {s t : Set α} (h : s ⊆ t) :
    L.distinctConstantsTheory s ⊆ L.distinctConstantsTheory t := by
  unfold distinctConstantsTheory; gcongr

theorem monotone_distinctConstantsTheory :
    Monotone (L.distinctConstantsTheory : Set α → L[[α]].Theory) := fun _s _t st =>
  L.distinctConstantsTheory_mono st
#align first_order.language.monotone_distinct_constants_theory FirstOrder.Language.monotone_distinctConstantsTheory

theorem directed_distinctConstantsTheory :
    Directed (· ⊆ ·) (L.distinctConstantsTheory : Set α → L[[α]].Theory) :=
  Monotone.directed_le monotone_distinctConstantsTheory
#align first_order.language.directed_distinct_constants_theory FirstOrder.Language.directed_distinctConstantsTheory

theorem distinctConstantsTheory_eq_iUnion (s : Set α) :
    L.distinctConstantsTheory s =
      ⋃ t : Finset s,
        L.distinctConstantsTheory (t.map (Function.Embedding.subtype fun x => x ∈ s)) := by
  classical
    simp only [distinctConstantsTheory]
    rw [← image_iUnion, ← iUnion_inter]
    refine congr(_ '' ($(?_) ∩ _))
    ext ⟨i, j⟩
    simp only [prod_mk_mem_set_prod_eq, Finset.coe_map, Function.Embedding.coe_subtype, mem_iUnion,
      mem_image, Finset.mem_coe, Subtype.exists, Subtype.coe_mk, exists_and_right, exists_eq_right]
    refine ⟨fun h => ⟨{⟨i, h.1⟩, ⟨j, h.2⟩}, ⟨h.1, ?_⟩, ⟨h.2, ?_⟩⟩, ?_⟩
    · simp
    · simp
    · rintro ⟨t, ⟨is, _⟩, ⟨js, _⟩⟩
      exact ⟨is, js⟩
#align first_order.language.distinct_constants_theory_eq_Union FirstOrder.Language.distinctConstantsTheory_eq_iUnion

end Cardinality

end Language

end FirstOrder
