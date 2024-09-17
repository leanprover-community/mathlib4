/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Metin Ersin Arıcan
-/
import Mathlib.ModelTheory.Equivalence

/-!
# Quantifier Complexity

This file defines quantifier complexity of first-order formulas, defines literals, and constructs
prenex normal forms.

## Main Definitions

- `FirstOrder.Language.BoundedFormula.IsAtomic` defines atomic formulas - those which are
  constructed only from terms and relations.
- `FirstOrder.Language.BoundedFormula.IsLiteral` defines literals - those which are `⊥`, `⊤`,
  atomic formulas or negation of atomic formulas.
- `FirstOrder.Language.BoundedFormula.IsConjunctive` defines conjunctive formulas - those which are
  constructed only from literals and conjunctions.
- `FirstOrder.Language.BoundedFormula.IsDisjunctive` defines disjunctive formulas - those which are
  constructed only from literals and disjunctions.
- `FirstOrder.Language.BoundedFormula.IsDNF` defines formulas in disjunctive normal form - those
  which are disjunctions of conjunctive formulas.
- `FirstOrder.Language.BoundedFormula.IsCNF` defines formulas in conjunctive normal form - those
  which are conjunctions of disjunctive formulas.
- `FirstOrder.Language.BoundedFormula.IsQF` defines quantifier-free formulas - those which are
  constructed only from atomic formulas and boolean operations.
- `FirstOrder.Language.BoundedFormula.toDNF` constructs a disjunctive normal form of a given
  quantifier-free formula.
- `FirstOrder.Language.BoundedFormula.toCNF` constructs a conjunctive normal form of a given
  quantifier-free formula.
- `FirstOrder.Language.BoundedFormula.IsPrenex` defines when a formula is in prenex normal form -
  when it consists of a series of quantifiers applied to a quantifier-free formula.
- `FirstOrder.Language.BoundedFormula.toPrenex` constructs a prenex normal form of a given formula.


## Main Results

- `FirstOrder.Language.BoundedFormula.toDNF_semanticallyEquivalent` shows that the disjunctive
  normal form of a formula is semantically equivalent to the original formula.
- `FirstOrder.Language.BoundedFormula.toCNF_semanticallyEquivalent` shows that the conjunctive
  normal form of a formula is semantically equivalent to the original formula.
- `FirstOrder.Language.BoundedFormula.realize_toPrenex` shows that the prenex normal form of a
  formula has the same realization as the original formula.

## TODO

- `FirstOrder.Language.BoundedFormula.IsDNF.components` which gives the literals of a DNF as
  a list of lists.
- `FirstOrder.Language.BoundedFormula.IsCNF.components` which gives the literals of a CNF as
  a list of lists.
-/

universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {L' : Language}
variable {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variable {α : Type u'} {β : Type v'} {γ : Type*}
variable {n l : ℕ} {φ ψ : L.BoundedFormula α l} {θ : L.BoundedFormula α l.succ}
variable {v : α → M} {xs : Fin l → M}

open FirstOrder Structure Fin

namespace BoundedFormula

/-- An auxilary definition to `FirstOrder.Language.BoundedFormula.simpleNot` and
  `FirstOrder.Language.BoundedFormula.simpleNot_semanticallyEquivalent_not`.-/
def simpleNotAux : {n : ℕ} → (φ : L.BoundedFormula α n) → {ψ : L.BoundedFormula α n // ψ ⇔[∅] ∼φ}
  | _, ⊥ => .mk ⊤ (by rfl)
  | _, equal t₁ t₂ => .mk ∼(equal t₁ t₂) (by rfl)
  | _, rel r tv => .mk ∼(rel r tv) (by rfl)

  | _, ⊤ => .mk ⊥ (by apply semanticallyEquivalent_not_not)
  | _, ∼(equal t₁ t₂) => .mk (equal t₁ t₂) (by apply semanticallyEquivalent_not_not)
  | _, ∼(rel r tv) => .mk (rel r tv) (by apply semanticallyEquivalent_not_not)

  | _, BoundedFormula.inf φ ψ =>
    .mk (φ.simpleNotAux ⊔ ψ.simpleNotAux) (by
      symm
      trans
      · exact not_inf_semanticallyEquivalent_sup_not φ ψ
      · exact Theory.SemanticallyEquivalent.sup φ.simpleNotAux.2.symm ψ.simpleNotAux.2.symm
    )
  | _, BoundedFormula.sup φ ψ =>
    .mk (φ.simpleNotAux ⊓ ψ.simpleNotAux) (by
      symm
      trans
      · exact not_sup_semanticallyEquivalent_inf_not φ ψ
      · exact Theory.SemanticallyEquivalent.inf φ.simpleNotAux.2.symm ψ.simpleNotAux.2.symm
    )

  | _, ∀' φ =>
    .mk (∃' φ.simpleNotAux) (by
      symm
      trans
      · exact not_all_semanticallyEquivalent_ex_not φ
      · exact Theory.SemanticallyEquivalent.ex φ.simpleNotAux.2.symm
    )
  | _, ∃' φ =>
    .mk (∀' φ.simpleNotAux) (by
      symm
      trans
      · exact not_ex_semanticallyEquivalent_all_not φ
      · exact Theory.SemanticallyEquivalent.all φ.simpleNotAux.2.symm
    )

  | _, φ => .mk ∼φ (by rfl)

/-- An auxilary operation which is semantically equivalent to
  `FirstOrder.Language.BoundedFormula.not`. It takes a bounded formula `φ`, assuming that any
  negation symbol inside `φ` occurs in front of an atomic formula or `⊥`, it applies negation to
  `φ`, pushes the negation inwards through `⊓`, `⊔`, `∀'`, `∃'`, and eliminates double negations.-/
def simpleNot (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  φ.simpleNotAux.1

theorem simpleNot_semanticallyEquivalent_not (φ : L.BoundedFormula α n) : simpleNot φ ⇔[∅] ∼φ :=
  φ.simpleNotAux.2

/-- An atomic formula is either equality or a relation symbol applied to terms.
Note that `⊥` and `⊤` are not considered atomic in this convention. -/
inductive IsAtomic : L.BoundedFormula α n → Prop
  | equal (t₁ t₂ : L.Term (α ⊕ (Fin n))) : IsAtomic (t₁.bdEqual t₂)
  | rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) :
    IsAtomic (R.boundedFormula ts)

theorem not_all_isAtomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsAtomic := fun con => by
  cases con

theorem not_ex_isAtomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsAtomic := fun con => by cases con

theorem IsAtomic.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsAtomic)
    (f : α → β ⊕ (Fin n)) : (φ.relabel f).IsAtomic :=
  IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

theorem IsAtomic.liftAt {k m : ℕ} (h : IsAtomic φ) : (φ.liftAt k m).IsAtomic :=
  IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

theorem IsAtomic.castLE {h : l ≤ n} (hφ : IsAtomic φ) : (φ.castLE h).IsAtomic :=
  IsAtomic.recOn hφ (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

protected theorem IsAtomic.simpleNot_eq_not {φ : L.BoundedFormula α n} (hφ : φ.IsAtomic) :
    φ.simpleNot = ∼φ := by
  induction hφ with
  | equal t₁ t₂ => rfl
  | rel R ts => rfl

protected theorem IsAtomic.simpleNot_of_not_eq {φ : L.BoundedFormula α n} (hφ : φ.IsAtomic) :
    φ.not.simpleNot = φ := by
  induction hφ with
  | equal t₁ t₂ => rfl
  | rel R ts => rfl

/-- A literal is either `⊥`, `⊤`, an atomic formula or the negation of an atomic formula. -/
inductive IsLiteral : L.BoundedFormula α n → Prop
  | falsum : IsLiteral BoundedFormula.falsum
  | of_isAtomic {φ : L.BoundedFormula α n} (h : φ.IsAtomic) : IsLiteral φ
  | not_falsum : IsLiteral BoundedFormula.falsum.not
  | of_not_of_isAtomic {φ : L.BoundedFormula α n} (h : φ.IsAtomic) : IsLiteral φ.not

theorem IsAtomic.isLiteral {φ : L.BoundedFormula α n} (hφ : φ.IsAtomic) : IsLiteral φ :=
  IsLiteral.of_isAtomic hφ

protected theorem IsLiteral.simpleNot {φ : L.BoundedFormula α n} (hφ : φ.IsLiteral) :
    φ.simpleNot.IsLiteral := by
  induction hφ with
  | falsum =>
    exact IsLiteral.not_falsum
  | of_isAtomic hφ =>
    rw [hφ.simpleNot_eq_not]
    exact IsLiteral.of_not_of_isAtomic hφ
  | not_falsum =>
    exact IsLiteral.falsum
  | of_not_of_isAtomic hφ =>
    rw [hφ.simpleNot_of_not_eq]
    exact hφ.isLiteral

/-- A conjunctive formula is a conjunction of literals. -/
inductive IsConjunctive : L.BoundedFormula α n → Prop
  | of_isLiteral {φ : L.BoundedFormula α n} (h : φ.IsLiteral) : IsConjunctive φ
  | inf {φ ψ : L.BoundedFormula α n} (hφ : IsConjunctive φ) (hψ : IsConjunctive ψ) :
    IsConjunctive (φ ⊓ ψ)

theorem IsLiteral.isConjunctive {φ : L.BoundedFormula α n} (hφ : φ.IsLiteral) : IsConjunctive φ :=
  IsConjunctive.of_isLiteral hφ

theorem IsAtomic.isConjunctive {φ : L.BoundedFormula α n} (hφ : φ.IsAtomic) : IsConjunctive φ :=
  IsLiteral.isConjunctive (IsAtomic.isLiteral hφ)

/-- A disjunctive formula is a disjunction of literals. -/
inductive IsDisjunctive : L.BoundedFormula α n → Prop
  | of_isLiteral {φ : L.BoundedFormula α n} (h : φ.IsLiteral) : IsDisjunctive φ
  | sup {φ ψ : L.BoundedFormula α n} (hφ : IsDisjunctive φ) (hψ : IsDisjunctive ψ) :
    IsDisjunctive (φ ⊔ ψ)

theorem IsLiteral.isDisjunctive {φ : L.BoundedFormula α n} (hφ : φ.IsLiteral) : IsDisjunctive φ :=
  IsDisjunctive.of_isLiteral hφ

theorem IsAtomic.isDisjunctive {φ : L.BoundedFormula α n} (hφ : φ.IsAtomic) : IsDisjunctive φ :=
  IsLiteral.isDisjunctive (IsAtomic.isLiteral hφ)

protected theorem IsConjunctive.simpleNot {φ : L.BoundedFormula α n} (hφ : φ.IsConjunctive) :
    φ.simpleNot.IsDisjunctive := by
  induction hφ with
  | of_isLiteral hφ =>
    apply IsDisjunctive.of_isLiteral
    exact IsLiteral.simpleNot hφ
  | inf hφ hψ hφ_ih hψ_ih =>
    dsimp only [simpleNot, simpleNotAux]
    exact IsDisjunctive.sup hφ_ih hψ_ih

protected theorem IsDisjunctive.simpleNot {φ : L.BoundedFormula α n} (hφ : φ.IsDisjunctive) :
    φ.simpleNot.IsConjunctive := by
  induction hφ with
  | of_isLiteral hφ =>
    apply IsConjunctive.of_isLiteral
    exact IsLiteral.simpleNot hφ
  | sup hφ hψ hφ_ih hψ_ih =>
    dsimp only [simpleNot, simpleNotAux]
    exact IsConjunctive.inf hφ_ih hψ_ih

/-- A DNF formula is a disjunction of conjunctive formulas i.e., it is a formula in disjunctive
  normal form. -/
inductive IsDNF : L.BoundedFormula α n → Prop
  | of_isConjunctive {φ : L.BoundedFormula α n} (h : φ.IsConjunctive) : IsDNF φ
  | sup {φ ψ : L.BoundedFormula α n} (hφ : IsDNF φ) (hψ : IsDNF ψ) : IsDNF (φ ⊔ ψ)

theorem IsConjunctive.isDNF {φ : L.BoundedFormula α n} (hφ : φ.IsConjunctive) : IsDNF φ :=
  IsDNF.of_isConjunctive hφ

/-- A CNF formula is a conjunction of disjunctive formulas i.e., it is a formula in conjunctive
  normal form. -/
inductive IsCNF : L.BoundedFormula α n → Prop
  | of_isDisjunctive {φ : L.BoundedFormula α n} (h : φ.IsDisjunctive) : IsCNF φ
  | inf {φ ψ : L.BoundedFormula α n} (hφ : IsCNF φ) (hψ : IsCNF ψ) : IsCNF (φ ⊓ ψ)

theorem IsDisjunctive.isCNF {φ : L.BoundedFormula α n} (hφ : φ.IsDisjunctive) : IsCNF φ :=
  IsCNF.of_isDisjunctive hφ

protected theorem IsDNF.simpleNot {φ : L.BoundedFormula α n} (hφ : φ.IsDNF) :
    φ.simpleNot.IsCNF := by
  induction hφ with
  | of_isConjunctive hφ =>
    apply IsCNF.of_isDisjunctive
    exact IsConjunctive.simpleNot hφ
  | sup hφ hψ hφ_ih hψ_ih =>
    dsimp only [simpleNot, simpleNotAux]
    exact IsCNF.inf hφ_ih hψ_ih

namespace IsCNF

protected theorem simpleNot {φ : L.BoundedFormula α n} (hφ : φ.IsCNF) : φ.simpleNot.IsDNF := by
  induction hφ with
  | of_isDisjunctive hφ =>
    apply IsDNF.of_isConjunctive
    exact IsDisjunctive.simpleNot hφ
  | inf hφ hψ hφ_ih hψ_ih =>
    dsimp only [simpleNot, simpleNotAux]
    exact IsDNF.sup hφ_ih hψ_ih

/-- An auxilary definition to `FirstOrder.Language.BoundedFormula.IsCNF.sup` and
  `FirstOrder.Language.BoundedFormula.IsCNF.sup_semanticallyEquivalent_sup`. -/
protected def supAux (φ ψ : L.BoundedFormula α n) : {χ : L.BoundedFormula α n // χ ⇔[∅] φ ⊔ ψ} :=
  match φ with
  | BoundedFormula.inf φ₁ φ₂ =>
    .mk ((IsCNF.supAux φ₁ ψ).1 ⊓ (IsCNF.supAux φ₂ ψ).1) (by
      trans; exact Theory.SemanticallyEquivalent.inf (IsCNF.supAux φ₁ ψ).2 (IsCNF.supAux φ₂ ψ).2
      dsimp only [Theory.SemanticallyEquivalent, Theory.ModelsBoundedFormula, BoundedFormula.inf]
      intros
      simp only [realize_iff, realize_not, realize_inf, realize_sup, realize_imp]
      tauto
    )
  | φ =>
    match ψ with
    | BoundedFormula.inf ψ₁ ψ₂ =>
      .mk ((IsCNF.supAux φ ψ₁).1 ⊓ (IsCNF.supAux φ ψ₂).1) (by
        trans; exact Theory.SemanticallyEquivalent.inf (IsCNF.supAux φ ψ₁).2 (IsCNF.supAux φ ψ₂).2
        dsimp only [Theory.SemanticallyEquivalent, Theory.ModelsBoundedFormula, BoundedFormula.inf]
        intros
        simp only [realize_iff, realize_not, realize_inf, realize_sup, realize_imp]
        tauto
      )
    | ψ => .mk (φ ⊔ ψ) (by rfl)

/-- An auxilary operation which is semantically equivalent to
  `FirstOrder.Language.BoundedFormula.sup`. It takes bounded formulas `φ` and `ψ`, assuming that any
  negation symbol inside them occurs in front of an atomic formula or `⊥`, it applies `⊔` and
  pushes it inwards by distributing it over `⊓`. -/
protected def sup (φ ψ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  (IsCNF.supAux φ ψ).1

protected theorem sup_semanticallyEquivalent_sup (φ ψ : L.BoundedFormula α n) :
    IsCNF.sup φ ψ ⇔[∅] φ ⊔ ψ :=
  (IsCNF.supAux φ ψ).2

protected lemma sup_of_isLiteral_eq {φ ψ : L.BoundedFormula α n} (hφ : φ.IsLiteral)
    (hψ : ψ.IsLiteral) : IsCNF.sup φ ψ = φ ⊔ ψ := by
  unfold IsCNF.sup IsCNF.supAux
  split
  · contradiction
  · split
    · contradiction
    · rfl

protected lemma sup_of_isDisjunctive_eq {φ ψ : L.BoundedFormula α n} (hφ : φ.IsDisjunctive)
    (hψ : ψ.IsDisjunctive) : IsCNF.sup φ ψ = φ ⊔ ψ := by
  unfold IsCNF.sup IsCNF.supAux
  split
  · contradiction
  · split
    · contradiction
    · rfl

/-- When `FirstOrder.Language.BoundedFormula.IsCNF.sup` is applied to formulas in CNF, the result
  is also a formula in CNF. -/
protected theorem sup_isCNF {φ ψ : L.BoundedFormula α n} (hφ : φ.IsCNF) (hψ : ψ.IsCNF) :
    (IsCNF.sup φ ψ).IsCNF := by
  induction hφ with
  | of_isDisjunctive hφ =>
      induction hψ with
      | of_isDisjunctive hψ =>
        rw [IsCNF.sup_of_isDisjunctive_eq hφ hψ]
        apply IsCNF.of_isDisjunctive
        exact IsDisjunctive.sup hφ hψ
      | inf _ _ hψ₁_ih hψ₂_ih =>
        unfold IsCNF.sup IsCNF.supAux
        split
        · contradiction
        · exact IsCNF.inf hψ₁_ih hψ₂_ih
  | inf _ _ hφ₁_ih hφ₂_ih =>
      unfold IsCNF.sup IsCNF.supAux
      exact IsCNF.inf hφ₁_ih hφ₂_ih

end IsCNF

/-- A quantifier-free formula is a formula defined without quantifiers. These are all equivalent
to boolean combinations of atomic formulas. -/
inductive IsQF : L.BoundedFormula α n → Prop
  | falsum : IsQF falsum
  | of_isAtomic {φ} (h : IsAtomic φ) : IsQF φ
  | imp {φ₁ φ₂} (h₁ : IsQF φ₁) (h₂ : IsQF φ₂) : IsQF (φ₁.imp φ₂)

theorem IsAtomic.isQF {φ : L.BoundedFormula α n} : IsAtomic φ → IsQF φ :=
  IsQF.of_isAtomic

theorem isQF_bot : IsQF (⊥ : L.BoundedFormula α n) :=
  IsQF.falsum

namespace IsQF

theorem not {φ : L.BoundedFormula α n} (h : IsQF φ) : IsQF φ.not :=
  h.imp isQF_bot

theorem top : IsQF (⊤ : L.BoundedFormula α n) := isQF_bot.not

theorem sup {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsQF ψ) : IsQF (φ ⊔ ψ) :=
  hφ.not.imp hψ

theorem inf {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsQF ψ) : IsQF (φ ⊓ ψ) :=
  (hφ.imp hψ.not).not

protected theorem relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsQF) (f : α → β ⊕ (Fin n)) :
    (φ.relabel f).IsQF :=
  IsQF.recOn h isQF_bot (fun h => (h.relabel f).isQF) fun _ _ h1 h2 => h1.imp h2

protected theorem liftAt {k m : ℕ} (h : IsQF φ) : (φ.liftAt k m).IsQF :=
  IsQF.recOn h isQF_bot (fun ih => ih.liftAt.isQF) fun _ _ ih1 ih2 => ih1.imp ih2

protected theorem castLE {h : l ≤ n} (hφ : IsQF φ) : (φ.castLE h).IsQF :=
  IsQF.recOn hφ isQF_bot (fun ih => ih.castLE.isQF) fun _ _ ih1 ih2 => ih1.imp ih2

end IsQF

mutual

/-- Given a quantifier free formula, it produces a semantically equivalent formula in DNF. -/
def toDNF (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  match φ with
  | φ ⟹ ψ /- ⇔[∅] ∼φ ⊔ ψ -/ => (toCNF φ).simpleNot ⊔ (toDNF ψ)
  | _ => φ

/-- Given a quantifier free formula, it produces a semantically equivalent formula in CNF. -/
def toCNF (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  match φ with
  | φ ⟹ ψ /- ⇔[∅] ∼φ ⊔ ψ ⇔[∅] ∼(φ ⊓ ∼ψ) -/ => IsCNF.sup (toDNF φ).simpleNot (toCNF ψ)
  | _ => φ

end

mutual

theorem toDNF_semanticallyEquivalent (φ : L.BoundedFormula α n) : toDNF φ ⇔[∅] φ := by
  match φ with
  | ⊥ => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | ∀' φ => rfl
  | φ₁ ⟹ φ₂ =>
    dsimp only [toDNF]
    symm
    trans; exact imp_semanticallyEquivalent_not_sup φ₁ φ₂
    apply Theory.SemanticallyEquivalent.sup
    · symm
      trans; exact simpleNot_semanticallyEquivalent_not _
      apply Theory.SemanticallyEquivalent.not
      exact toCNF_semanticallyEquivalent φ₁
    · symm
      exact toDNF_semanticallyEquivalent φ₂

theorem toCNF_semanticallyEquivalent (φ : L.BoundedFormula α n) : toCNF φ ⇔[∅] φ := by
  match φ with
  | ⊥ => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | ∀' φ => rfl
  | φ₁ ⟹ φ₂ =>
    dsimp only [toCNF]
    trans; exact IsCNF.sup_semanticallyEquivalent_sup _ _
    symm
    trans; exact imp_semanticallyEquivalent_not_sup φ₁ φ₂
    apply Theory.SemanticallyEquivalent.sup
    · symm
      trans; exact simpleNot_semanticallyEquivalent_not _
      apply Theory.SemanticallyEquivalent.not
      exact toDNF_semanticallyEquivalent φ₁
    · symm
      exact toCNF_semanticallyEquivalent φ₂

end

protected theorem IsAtomic.toDNF_eq {φ : L.BoundedFormula α n} (h : φ.IsAtomic) : toDNF φ = φ := by
  induction h with
  | equal t₁ t₂ => rfl
  | rel R ts => rfl

protected theorem IsAtomic.toCNF_eq {φ : L.BoundedFormula α n} (h : φ.IsAtomic) : toCNF φ = φ := by
  induction h with
  | equal t₁ t₂ => rfl
  | rel R ts => rfl

mutual

theorem IsQF.toDNF_isDNF {φ : L.BoundedFormula α n} (hφ : φ.IsQF) : φ.toDNF.IsDNF := by
  match hφ with
  | falsum =>
    dsimp only [toDNF]
    apply IsDNF.of_isConjunctive
    apply IsConjunctive.of_isLiteral
    exact IsLiteral.falsum
  | of_isAtomic hφ =>
    rw [IsAtomic.toDNF_eq hφ]
    apply IsDNF.of_isConjunctive
    apply IsConjunctive.of_isLiteral
    exact IsLiteral.of_isAtomic hφ
  | imp hφ hψ =>
    dsimp [toDNF]
    apply IsDNF.sup
    · apply IsCNF.simpleNot
      exact toCNF_isCNF hφ
    · exact toDNF_isDNF hψ

theorem IsQF.toCNF_isCNF {φ : L.BoundedFormula α n} (hφ : φ.IsQF) : φ.toCNF.IsCNF := by
  match hφ with
  | falsum =>
    dsimp only [toCNF]
    apply IsCNF.of_isDisjunctive
    apply IsDisjunctive.of_isLiteral
    exact IsLiteral.falsum
  | of_isAtomic hφ =>
    rw [IsAtomic.toCNF_eq hφ]
    apply IsCNF.of_isDisjunctive
    apply IsDisjunctive.of_isLiteral
    exact IsLiteral.of_isAtomic hφ
  | imp hφ hψ =>
    dsimp [toCNF]
    apply IsCNF.sup_isCNF
    · apply IsDNF.simpleNot
      exact toDNF_isDNF hφ
    · exact toCNF_isCNF hψ

end

theorem not_all_isQF (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsQF := fun con => by
  cases' con with _ con
  exact φ.not_all_isAtomic con

theorem not_ex_isQF (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsQF := fun con => by
  cases' con with _ con _ _ con
  · exact φ.not_ex_isAtomic con
  · exact not_all_isQF _ con

/-- Indicates that a bounded formula is in prenex normal form - that is, it consists of quantifiers
  applied to a quantifier-free formula. -/
inductive IsPrenex : ∀ {n}, L.BoundedFormula α n → Prop
  | of_isQF {n} {φ : L.BoundedFormula α n} (h : IsQF φ) : IsPrenex φ
  | all {n} {φ : L.BoundedFormula α (n + 1)} (h : IsPrenex φ) : IsPrenex φ.all
  | ex {n} {φ : L.BoundedFormula α (n + 1)} (h : IsPrenex φ) : IsPrenex φ.ex

theorem IsQF.isPrenex {φ : L.BoundedFormula α n} : IsQF φ → IsPrenex φ :=
  IsPrenex.of_isQF

theorem IsAtomic.isPrenex {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsPrenex φ :=
  h.isQF.isPrenex

theorem IsPrenex.induction_on_all_not {P : ∀ {n}, L.BoundedFormula α n → Prop}
    {φ : L.BoundedFormula α n} (h : IsPrenex φ)
    (hq : ∀ {m} {ψ : L.BoundedFormula α m}, ψ.IsQF → P ψ)
    (ha : ∀ {m} {ψ : L.BoundedFormula α (m + 1)}, P ψ → P ψ.all)
    (hn : ∀ {m} {ψ : L.BoundedFormula α m}, P ψ → P ψ.not) : P φ :=
  IsPrenex.recOn h hq (fun _ => ha) fun _ ih => hn (ha (hn ih))

theorem IsPrenex.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsPrenex)
    (f : α → β ⊕ (Fin n)) : (φ.relabel f).IsPrenex :=
  IsPrenex.recOn h (fun h => (h.relabel f).isPrenex) (fun _ h => by simp [h.all])
    fun _ h => by simp [h.ex]

theorem IsPrenex.castLE (hφ : IsPrenex φ) : ∀ {n} {h : l ≤ n}, (φ.castLE h).IsPrenex :=
  IsPrenex.recOn (motive := @fun l φ _ => ∀ (n : ℕ) (h : l ≤ n), (φ.castLE h).IsPrenex) hφ
    (@fun _ _ ih _ _ => ih.castLE.isPrenex)
    (@fun _ _ _ ih _ _ => (ih _ _).all)
    (@fun _ _ _ ih _ _ => (ih _ _).ex) _ _

theorem IsPrenex.liftAt {k m : ℕ} (h : IsPrenex φ) : (φ.liftAt k m).IsPrenex :=
  IsPrenex.recOn h (fun ih => ih.liftAt.isPrenex) (fun _ ih => ih.castLE.all)
    fun _ ih => ih.castLE.ex

-- Porting note: universes in different order
/-- An auxiliary operation to `FirstOrder.Language.BoundedFormula.toPrenex`.
  If `φ` is quantifier-free and `ψ` is in prenex normal form, then `φ.toPrenexImpRight ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def toPrenexImpRight : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n
  | n, φ, BoundedFormula.ex ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).ex
  | n, φ, all ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).all
  | _n, φ, ψ => φ.imp ψ

theorem IsQF.toPrenexImpRight {φ : L.BoundedFormula α n} :
    ∀ {ψ : L.BoundedFormula α n}, IsQF ψ → φ.toPrenexImpRight ψ = φ.imp ψ
  | _, IsQF.falsum => rfl
  | _, IsQF.of_isAtomic (IsAtomic.equal _ _) => rfl
  | _, IsQF.of_isAtomic (IsAtomic.rel _ _) => rfl
  | _, IsQF.imp IsQF.falsum _ => rfl
  | _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.equal _ _)) _ => rfl
  | _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.rel _ _)) _ => rfl
  | _, IsQF.imp (IsQF.imp _ _) _ => rfl

theorem isPrenex_toPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImpRight ψ) := by
  induction hψ with
  | of_isQF hψ => rw [hψ.toPrenexImpRight]; exact (hφ.imp hψ).isPrenex
  | all _ ih1 => exact (ih1 hφ.liftAt).all
  | ex _ ih2 => exact (ih2 hφ.liftAt).ex

-- Porting note: universes in different order
/-- An auxiliary operation to `FirstOrder.Language.BoundedFormula.toPrenex`.
  If `φ` and `ψ` are in prenex normal form, then `φ.toPrenexImp ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def toPrenexImp : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n
  | n, BoundedFormula.ex φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).all
  | n, all φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).ex
  | _, φ, ψ => φ.toPrenexImpRight ψ

theorem IsQF.toPrenexImp :
    ∀ {φ ψ : L.BoundedFormula α n}, φ.IsQF → φ.toPrenexImp ψ = φ.toPrenexImpRight ψ
  | _, _, IsQF.falsum => rfl
  | _, _, IsQF.of_isAtomic (IsAtomic.equal _ _) => rfl
  | _, _, IsQF.of_isAtomic (IsAtomic.rel _ _) => rfl
  | _, _, IsQF.imp IsQF.falsum _ => rfl
  | _, _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.equal _ _)) _ => rfl
  | _, _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.rel _ _)) _ => rfl
  | _, _, IsQF.imp (IsQF.imp _ _) _ => rfl

theorem isPrenex_toPrenexImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImp ψ) := by
  induction hφ with
  | of_isQF hφ => rw [hφ.toPrenexImp]; exact isPrenex_toPrenexImpRight hφ hψ
  | all _ ih1 => exact (ih1 hψ.liftAt).ex
  | ex _ ih2 => exact (ih2 hψ.liftAt).all

-- Porting note: universes in different order
/-- For any bounded formula `φ`, `φ.toPrenex` is a semantically-equivalent formula in prenex normal
  form. -/
def toPrenex : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n
  | _, falsum => ⊥
  | _, equal t₁ t₂ => t₁.bdEqual t₂
  | _, rel R ts => rel R ts
  | _, imp f₁ f₂ => f₁.toPrenex.toPrenexImp f₂.toPrenex
  | _, all f => f.toPrenex.all

theorem toPrenex_isPrenex (φ : L.BoundedFormula α n) : φ.toPrenex.IsPrenex :=
  BoundedFormula.recOn φ isQF_bot.isPrenex (fun _ _ => (IsAtomic.equal _ _).isPrenex)
    (fun _ _ => (IsAtomic.rel _ _).isPrenex) (fun _ _ h1 h2 => isPrenex_toPrenexImp h1 h2)
    fun _ => IsPrenex.all

variable [Nonempty M]

theorem realize_toPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ)
    {v : α → M} {xs : Fin n → M} :
    (φ.toPrenexImpRight ψ).Realize v xs ↔ (φ.imp ψ).Realize v xs := by
  induction hψ with
  | of_isQF hψ => rw [hψ.toPrenexImpRight]
  | all _ ih =>
    refine _root_.trans (forall_congr' fun _ => ih hφ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    exact ⟨fun h1 a h2 => h1 h2 a, fun h1 h2 a => h1 a h2⟩
  | ex _ ih =>
    unfold toPrenexImpRight
    rw [realize_ex]
    refine _root_.trans (exists_congr fun _ => ih hφ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_ex]
    refine ⟨?_, fun h' => ?_⟩
    · rintro ⟨a, ha⟩ h
      exact ⟨a, ha h⟩
    · by_cases h : φ.Realize v xs
      · obtain ⟨a, ha⟩ := h' h
        exact ⟨a, fun _ => ha⟩
      · inhabit M
        exact ⟨default, fun h'' => (h h'').elim⟩

theorem realize_toPrenexImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ)
    {v : α → M} {xs : Fin n → M} : (φ.toPrenexImp ψ).Realize v xs ↔ (φ.imp ψ).Realize v xs := by
  revert ψ
  induction hφ with
  | of_isQF hφ =>
    intro ψ hψ
    rw [hφ.toPrenexImp]
    exact realize_toPrenexImpRight hφ hψ
  | all _ ih =>
    intro ψ hψ
    unfold toPrenexImp
    rw [realize_ex]
    refine _root_.trans (exists_congr fun _ => ih hψ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    refine ⟨?_, fun h' => ?_⟩
    · rintro ⟨a, ha⟩ h
      exact ha (h a)
    · by_cases h : ψ.Realize v xs
      · inhabit M
        exact ⟨default, fun _h'' => h⟩
      · obtain ⟨a, ha⟩ := not_forall.1 (h ∘ h')
        exact ⟨a, fun h => (ha h).elim⟩
  | ex _ ih =>
    intro ψ hψ
    refine _root_.trans (forall_congr' fun _ => ih hψ.liftAt) ?_
    simp

@[simp]
theorem realize_toPrenex (φ : L.BoundedFormula α n) {v : α → M} :
    ∀ {xs : Fin n → M}, φ.toPrenex.Realize v xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp f1 f2 h1 h2 =>
    intros
    rw [toPrenex, realize_toPrenexImp f1.toPrenex_isPrenex f2.toPrenex_isPrenex, realize_imp,
      realize_imp, h1, h2]
  | all _ h =>
    intros
    rw [realize_all, toPrenex, realize_all]
    exact forall_congr' fun a => h

theorem IsQF.induction_on_sup_not {P : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : IsQF φ) (hf : P (⊥ : L.BoundedFormula α n))
    (ha : ∀ ψ : L.BoundedFormula α n, IsAtomic ψ → P ψ)
    (hsup : ∀ {φ₁ φ₂}, P φ₁ → P φ₂ → P (φ₁ ⊔ φ₂)) (hnot : ∀ {φ}, P φ → P φ.not)
    (hse :
      ∀ {φ₁ φ₂ : L.BoundedFormula α n}, (φ₁ ⇔[∅] φ₂) → (P φ₁ ↔ P φ₂)) :
    P φ :=
  IsQF.recOn h hf @(ha) fun {φ₁ φ₂} _ _ h1 h2 =>
    (hse (φ₁.imp_semanticallyEquivalent_not_sup φ₂)).2 (hsup (hnot h1) h2)

theorem IsQF.induction_on_inf_not {P : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : IsQF φ) (hf : P (⊥ : L.BoundedFormula α n))
    (ha : ∀ ψ : L.BoundedFormula α n, IsAtomic ψ → P ψ)
    (hinf : ∀ {φ₁ φ₂}, P φ₁ → P φ₂ → P (φ₁ ⊓ φ₂)) (hnot : ∀ {φ}, P φ → P φ.not)
    (hse :
      ∀ {φ₁ φ₂ : L.BoundedFormula α n}, (φ₁ ⇔[∅] φ₂) → (P φ₁ ↔ P φ₂)) :
    P φ :=
  h.induction_on_sup_not hf ha
    (fun {φ₁ φ₂} h1 h2 =>
      (hse (φ₁.sup_semanticallyEquivalent_not_inf_not φ₂)).2 (hnot (hinf (hnot h1) (hnot h2))))
    (fun {_} => hnot) fun {_ _} => hse

theorem semanticallyEquivalent_toPrenex (φ : L.BoundedFormula α n) :
    φ ⇔[∅] φ.toPrenex := fun M v xs => by
  rw [realize_iff, realize_toPrenex]

theorem induction_on_all_ex {P : ∀ {m}, L.BoundedFormula α m → Prop} (φ : L.BoundedFormula α n)
    (hqf : ∀ {m} {ψ : L.BoundedFormula α m}, IsQF ψ → P ψ)
    (hall : ∀ {m} {ψ : L.BoundedFormula α (m + 1)}, P ψ → P ψ.all)
    (hex : ∀ {m} {φ : L.BoundedFormula α (m + 1)}, P φ → P φ.ex)
    (hse : ∀ {m} {φ₁ φ₂ : L.BoundedFormula α m},
      (φ₁ ⇔[∅] φ₂) → (P φ₁ ↔ P φ₂)) :
    P φ := by
  suffices h' : ∀ {m} {φ : L.BoundedFormula α m}, φ.IsPrenex → P φ from
    (hse φ.semanticallyEquivalent_toPrenex).2 (h' φ.toPrenex_isPrenex)
  intro m φ hφ
  induction hφ with
  | of_isQF hφ => exact hqf hφ
  | all _ hφ => exact hall hφ
  | ex _ hφ => exact hex hφ

theorem induction_on_exists_not {P : ∀ {m}, L.BoundedFormula α m → Prop} (φ : L.BoundedFormula α n)
    (hqf : ∀ {m} {ψ : L.BoundedFormula α m}, IsQF ψ → P ψ)
    (hnot : ∀ {m} {φ : L.BoundedFormula α m}, P φ → P φ.not)
    (hex : ∀ {m} {φ : L.BoundedFormula α (m + 1)}, P φ → P φ.ex)
    (hse : ∀ {m} {φ₁ φ₂ : L.BoundedFormula α m},
      (φ₁ ⇔[∅] φ₂) → (P φ₁ ↔ P φ₂)) :
    P φ :=
  φ.induction_on_all_ex (fun {_ _} => hqf)
    (fun {_ φ} hφ => (hse φ.all_semanticallyEquivalent_not_ex_not).2 (hnot (hex (hnot hφ))))
    (fun {_ _} => hex) fun {_ _ _} => hse

/-- A universal formula is a formula defined by applying only universal quantifiers to a
quantifier-free formula. -/
inductive IsUniversal : ∀ {n}, L.BoundedFormula α n → Prop
  | of_isQF {n} {φ : L.BoundedFormula α n} (h : IsQF φ) : IsUniversal φ
  | all {n} {φ : L.BoundedFormula α (n + 1)} (h : IsUniversal φ) : IsUniversal φ.all

lemma IsQF.isUniversal {φ : L.BoundedFormula α n} : IsQF φ → IsUniversal φ :=
  IsUniversal.of_isQF

lemma IsAtomic.isUniversal {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsUniversal φ :=
  h.isQF.isUniversal

/-- An existential formula is a formula defined by applying only existential quantifiers to a
quantifier-free formula. -/
inductive IsExistential : ∀ {n}, L.BoundedFormula α n → Prop
  | of_isQF {n} {φ : L.BoundedFormula α n} (h : IsQF φ) : IsExistential φ
  | ex {n} {φ : L.BoundedFormula α (n + 1)} (h : IsExistential φ) : IsExistential φ.ex

lemma IsQF.isExistential {φ : L.BoundedFormula α n} : IsQF φ → IsExistential φ :=
  IsExistential.of_isQF

lemma IsAtomic.isExistential {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsExistential φ :=
  h.isQF.isExistential

section Preservation

variable {M : Type*} [L.Structure M] {N : Type*} [L.Structure N]
variable {F : Type*} [FunLike F M N]

lemma IsAtomic.realize_comp_of_injective {φ : L.BoundedFormula α n} (hA : φ.IsAtomic)
    [L.HomClass F M N] {f : F} (hInj : Function.Injective f) {v : α → M} {xs : Fin n → M} :
    φ.Realize v xs → φ.Realize (f ∘ v) (f ∘ xs) := by
  induction hA with
  | equal t₁ t₂ => simp only [realize_bdEqual, ← Sum.comp_elim, HomClass.realize_term, hInj.eq_iff,
    imp_self]
  | rel R ts =>
    simp only [realize_rel, ← Sum.comp_elim, HomClass.realize_term]
    exact HomClass.map_rel f R (fun i => Term.realize (Sum.elim v xs) (ts i))

lemma IsAtomic.realize_comp {φ : L.BoundedFormula α n} (hA : φ.IsAtomic)
    [EmbeddingLike F M N] [L.HomClass F M N] (f : F) {v : α → M} {xs : Fin n → M} :
    φ.Realize v xs → φ.Realize (f ∘ v) (f ∘ xs) :=
  hA.realize_comp_of_injective (EmbeddingLike.injective f)

variable [EmbeddingLike F M N] [L.StrongHomClass F M N]

lemma IsQF.realize_embedding {φ : L.BoundedFormula α n} (hQF : φ.IsQF)
    (f : F) {v : α → M} {xs : Fin n → M} :
    φ.Realize (f ∘ v) (f ∘ xs) ↔ φ.Realize v xs := by
  induction hQF with
  | falsum => rfl
  | of_isAtomic hA => induction hA with
    | equal t₁ t₂ => simp only [realize_bdEqual, ← Sum.comp_elim, HomClass.realize_term,
        (EmbeddingLike.injective f).eq_iff]
    | rel R ts =>
      simp only [realize_rel, ← Sum.comp_elim, HomClass.realize_term]
      exact StrongHomClass.map_rel f R (fun i => Term.realize (Sum.elim v xs) (ts i))
  | imp _ _ ihφ ihψ => simp only [realize_imp, ihφ, ihψ]

lemma IsUniversal.realize_embedding {φ : L.BoundedFormula α n} (hU : φ.IsUniversal)
    (f : F) {v : α → M} {xs : Fin n → M} :
    φ.Realize (f ∘ v) (f ∘ xs) → φ.Realize v xs := by
  induction hU with
  | of_isQF hQF => simp [hQF.realize_embedding]
  | all _ ih =>
    simp only [realize_all, Nat.succ_eq_add_one]
    refine fun h a => ih ?_
    rw [Fin.comp_snoc]
    exact h (f a)

lemma IsExistential.realize_embedding {φ : L.BoundedFormula α n} (hE : φ.IsExistential)
    (f : F) {v : α → M} {xs : Fin n → M} :
    φ.Realize v xs → φ.Realize (f ∘ v) (f ∘ xs) := by
  induction hE with
  | of_isQF hQF => simp [hQF.realize_embedding]
  | ex _ ih =>
    simp only [realize_ex, Nat.succ_eq_add_one]
    refine fun ⟨a, ha⟩ => ⟨f a, ?_⟩
    rw [← Fin.comp_snoc]
    exact ih ha

end Preservation

end BoundedFormula

/-- A theory is universal when it is comprised only of universal sentences - these theories apply
also to substructures. -/
class Theory.IsUniversal (T : L.Theory) : Prop where
  isUniversal_of_mem : ∀ ⦃φ⦄, φ ∈ T → φ.IsUniversal

lemma Theory.IsUniversal.models_of_embedding {T : L.Theory} [hT : T.IsUniversal]
    {N : Type*} [L.Structure N] [N ⊨ T] (f : M ↪[L] N) : M ⊨ T := by
  simp only [model_iff]
  refine fun φ hφ => (hT.isUniversal_of_mem hφ).realize_embedding f (?_)
  rw [Subsingleton.elim (f ∘ default) default, Subsingleton.elim (f ∘ default) default]
  exact Theory.realize_sentence_of_mem T hφ

instance Substructure.models_of_isUniversal
    (S : L.Substructure M) (T : L.Theory) [T.IsUniversal] [M ⊨ T] : S ⊨ T :=
  Theory.IsUniversal.models_of_embedding (Substructure.subtype S)

lemma Theory.IsUniversal.insert
    {T : L.Theory} [hT : T.IsUniversal] {φ : L.Sentence} (hφ : φ.IsUniversal) :
    (insert φ T).IsUniversal := ⟨by
  simp only [Set.mem_insert_iff, forall_eq_or_imp, hφ, true_and]
  exact hT.isUniversal_of_mem⟩

namespace Relations

open BoundedFormula

lemma isAtomic (r : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) :
    IsAtomic (r.boundedFormula ts) := IsAtomic.rel r ts

lemma isQF (r : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) :
    IsQF (r.boundedFormula ts) := (r.isAtomic ts).isQF

variable (r : L.Relations 2)

protected lemma isUniversal_reflexive : r.reflexive.IsUniversal :=
  (r.isQF _).isUniversal.all

protected lemma isUniversal_irreflexive : r.irreflexive.IsUniversal :=
  (r.isAtomic _).isQF.not.isUniversal.all

protected lemma isUniversal_symmetric : r.symmetric.IsUniversal :=
  ((r.isQF _).imp (r.isQF _)).isUniversal.all.all

protected lemma isUniversal_antisymmetric : r.antisymmetric.IsUniversal :=
  ((r.isQF _).imp ((r.isQF _).imp (IsAtomic.equal _ _).isQF)).isUniversal.all.all

protected lemma isUniversal_transitive : r.transitive.IsUniversal :=
  ((r.isQF _).imp ((r.isQF _).imp (r.isQF _))).isUniversal.all.all.all

protected lemma isUniversal_total : r.total.IsUniversal :=
  ((r.isQF _).sup (r.isQF _)).isUniversal.all.all

end Relations

theorem Formula.isAtomic_graph (f : L.Functions n) : (Formula.graph f).IsAtomic :=
  BoundedFormula.IsAtomic.equal _ _

end Language

end FirstOrder
