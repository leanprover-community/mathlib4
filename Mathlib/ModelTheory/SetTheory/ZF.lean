/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module

public import Mathlib.ModelTheory.Semantics
public import Mathlib.ModelTheory.SetTheory.Basic

/-!
# The First-Order Theory ZF

This file defines the Zermelo--Fraenkel axioms in the first-order language of set theory.
The Separation and Replacement schemes range over all formulas in that language, with finitely
many free variables.

## Main definitions

- `FirstOrder.SetTheory.ZFAxiom` indexes the finite axioms and the two axiom schemes.
- `FirstOrder.SetTheory.ZFAxiom.toSentence` is the sentence associated with a ZF axiom.
- `FirstOrder.SetTheory.ZFAxiom.toProp` gives the usual semantics of each axiom.
- `FirstOrder.Language.Theory.ZF` is the first-order theory of ZF.
-/

@[expose] public section

universe u

namespace FirstOrder.SetTheory

open Language Language.BoundedFormula Language.Structure
open scoped FirstOrder

/-- Universally close a formula whose free variables are indexed by `Fin n`. -/
def universalClosure {n : ℕ} (φ : Language.setTheory.Formula (Fin n)) :
    Language.setTheory.Sentence :=
  (BoundedFormula.relabel (β := Empty) Sum.inr φ).alls

/-! The following relabellings make the de Bruijn variable order in the two schemes explicit. -/

/-- Relabel `φ(params, x)` inside the Separation body, preserving the parameters. -/
def separationRelabel {n : ℕ} : Fin (n + 1) → Fin (n + 1) ⊕ Fin 2 :=
  Fin.lastCases (.inr (Fin.last 1)) fun i => .inl i.castSucc

private theorem comp_separationRelabel {M : Type*} {n : ℕ}
    (params : Fin n → M) (a b x : M) :
    (Sum.elim (Fin.snoc params a) (Fin.snoc (Fin.snoc default b) x) ∘
      separationRelabel) =
        Fin.snoc params x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Function.comp_apply, separationRelabel, Fin.lastCases_last, Sum.elim_inr,
      Fin.snoc_last]
  · simp only [Function.comp_apply, separationRelabel, Fin.lastCases_castSucc, Sum.elim_inl,
      Fin.snoc_castSucc]

/-- The Separation body associated with `φ(params, x)`. -/
def separationBody {n : ℕ} (φ : Language.setTheory.Formula (Fin (n + 1))) :
    Language.setTheory.Formula (Fin (n + 1)) :=
  ∃' ∀'
    ((&1).mem &0 ⇔
      ((&1).mem (Term.var (.inl (Fin.last n))) ⊓
        BoundedFormula.relabel
          separationRelabel φ))

/-- Relabel `φ(params, x, y)` after introducing the prospective value `y`. -/
def replacementWitnessRelabel {n : ℕ} : Fin (n + 2) → Fin (n + 1) ⊕ Fin 2 :=
  Fin.lastCases (.inr (Fin.last 1)) fun j =>
    Fin.lastCases (.inr (Fin.last 0).castSucc) (fun i => .inl i.castSucc) j

private theorem comp_replacementWitnessRelabel {M : Type*} {n : ℕ}
    (params : Fin n → M) (a x y : M) :
    (Sum.elim (Fin.snoc params a) (Fin.snoc (Fin.snoc default x) y) ∘
      replacementWitnessRelabel) =
          Fin.snoc (Fin.snoc params x) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Function.comp_apply, replacementWitnessRelabel, Fin.lastCases_last, Sum.elim_inr,
      Fin.snoc_last]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Function.comp_apply, replacementWitnessRelabel, Fin.lastCases_castSucc,
        Fin.lastCases_last, Sum.elim_inr, Fin.snoc_castSucc, Fin.snoc_last]
    · simp only [Function.comp_apply, replacementWitnessRelabel, Fin.lastCases_castSucc,
        Sum.elim_inl, Fin.snoc_castSucc]

/-- Relabel `φ(params, x, z)` when asserting uniqueness of a prospective value. -/
def replacementUniquenessRelabel {n : ℕ} : Fin (n + 2) → Fin (n + 1) ⊕ Fin 3 :=
  Fin.lastCases (.inr (Fin.last 2)) fun j =>
    Fin.lastCases (.inr (Fin.last 0).castSucc.castSucc) (fun i => .inl i.castSucc) j

private theorem comp_replacementUniquenessRelabel {M : Type*} {n : ℕ}
    (params : Fin n → M) (a x y z : M) :
    (Sum.elim (Fin.snoc params a) (Fin.snoc (Fin.snoc (Fin.snoc default x) y) z) ∘
      replacementUniquenessRelabel) =
          Fin.snoc (Fin.snoc params x) z := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Function.comp_apply, replacementUniquenessRelabel, Fin.lastCases_last,
      Sum.elim_inr, Fin.snoc_last]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Function.comp_apply, replacementUniquenessRelabel, Fin.lastCases_castSucc,
        Fin.lastCases_last, Sum.elim_inr, Fin.snoc_castSucc, Fin.snoc_last]
    · simp only [Function.comp_apply, replacementUniquenessRelabel, Fin.lastCases_castSucc,
        Sum.elim_inl, Fin.snoc_castSucc]

/-- Relabel `φ(params, x, y)` inside the exact-image conclusion of Replacement. -/
def replacementRangeRelabel {n : ℕ} : Fin (n + 2) → Fin (n + 1) ⊕ Fin 3 :=
  Fin.lastCases (.inr (Fin.last 1).castSucc) fun j =>
    Fin.lastCases (.inr (Fin.last 2)) (fun i => .inl i.castSucc) j

private theorem comp_replacementRangeRelabel {M : Type*} {n : ℕ}
    (params : Fin n → M) (a b y x : M) :
    (Sum.elim (Fin.snoc params a) (Fin.snoc (Fin.snoc (Fin.snoc default b) y) x) ∘
      replacementRangeRelabel) =
          Fin.snoc (Fin.snoc params x) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Function.comp_apply, replacementRangeRelabel, Fin.lastCases_last, Sum.elim_inr,
      Fin.snoc_castSucc, Fin.snoc_last]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Function.comp_apply, replacementRangeRelabel, Fin.lastCases_castSucc,
        Fin.lastCases_last, Sum.elim_inr, Fin.snoc_last, Fin.snoc_castSucc]
    · simp only [Function.comp_apply, replacementRangeRelabel, Fin.lastCases_castSucc,
        Sum.elim_inl, Fin.snoc_castSucc]

/-- Under `(params, a, x)`, assert that `φ(params, x, -)` has exactly one value. -/
def replacementUnique {n : ℕ} (φ : Language.setTheory.Formula (Fin (n + 2))) :
    Language.setTheory.BoundedFormula (Fin (n + 1)) 1 :=
  ∃'
    (BoundedFormula.relabel
        replacementWitnessRelabel φ ⊓
      ∀' (BoundedFormula.relabel
          replacementUniquenessRelabel φ ⟹
        (&2 =' &1)))

/-- The functional Replacement body associated with `φ(params, x, y)`. -/
def replacementBody {n : ℕ} (φ : Language.setTheory.Formula (Fin (n + 2))) :
    Language.setTheory.Formula (Fin (n + 1)) :=
  (∀' ((&0).mem (Term.var (.inl (Fin.last n))) ⟹ replacementUnique φ)) ⟹
    ∃' ∀'
      ((&1).mem &0 ⇔
        ∃' ((&2).mem (Term.var (.inl (Fin.last n))) ⊓
          BoundedFormula.relabel
            replacementRangeRelabel φ))

/-- Universal closure has the expected semantics. -/
@[simp]
theorem realize_universalClosure {M : Type u} [Language.setTheory.Structure M] {n : ℕ}
    (φ : Language.setTheory.Formula (Fin n)) :
    M ⊨ universalClosure φ ↔ ∀ v : Fin n → M, φ.Realize v := by
  simp only [Sentence.Realize, universalClosure, BoundedFormula.realize_alls]
  exact forall_congr' fun _ => Formula.realize_relabel_sumInr φ

/-- The Separation body has the usual semantics under an assignment of its parameters and set. -/
@[simp]
theorem realize_separationBody {M : Type u} [Language.setTheory.Structure M] {n : ℕ}
    (φ : Language.setTheory.Formula (Fin (n + 1))) (params : Fin n → M) (a : M) :
    (separationBody φ).Realize (Fin.snoc params a) ↔
      ∃ b : M, ∀ x : M,
        RelMap memRel ![x, b] ↔ RelMap memRel ![x, a] ∧ φ.Realize (Fin.snoc params x) := by
  have hzero (f : Fin 0 → M) : f = default := Subsingleton.elim _ _
  simp [separationBody, Formula.Realize, Term.mem, Fin.snoc, hzero,
    comp_separationRelabel]

/-- `replacementUnique` states that the scheme formula has exactly one value at `x`. -/
@[simp]
theorem realize_replacementUnique {M : Type u} [Language.setTheory.Structure M] {n : ℕ}
    (φ : Language.setTheory.Formula (Fin (n + 2))) (params : Fin n → M) (a x : M) :
    (replacementUnique φ).Realize (Fin.snoc params a) (Fin.snoc default x) ↔
      ∃! y : M, φ.Realize (Fin.snoc (Fin.snoc params x) y) := by
  have hzero (f : Fin 0 → M) : f = default := Subsingleton.elim _ _
  simp [replacementUnique, Formula.Realize, ExistsUnique, Fin.snoc, hzero,
    comp_replacementWitnessRelabel, comp_replacementUniquenessRelabel]

/-- Functional Replacement has the usual exact-image semantics. -/
@[simp]
theorem realize_replacementBody {M : Type u} [Language.setTheory.Structure M] {n : ℕ}
    (φ : Language.setTheory.Formula (Fin (n + 2))) (params : Fin n → M) (a : M) :
    (replacementBody φ).Realize (Fin.snoc params a) ↔
      ((∀ x : M, RelMap memRel ![x, a] →
          ∃! y : M, φ.Realize (Fin.snoc (Fin.snoc params x) y)) →
        ∃ b : M, ∀ y : M, RelMap memRel ![y, b] ↔
          ∃ x : M, RelMap memRel ![x, a] ∧ φ.Realize (Fin.snoc (Fin.snoc params x) y)) := by
  have hzero (f : Fin 0 → M) : f = default := Subsingleton.elim _ _
  simp [replacementBody, Formula.Realize, Term.mem, Fin.snoc, hzero,
    comp_replacementRangeRelabel]

/--
An index for each finite ZF axiom and each instance of Separation and Replacement.

In a Separation formula, the first `n` variables are parameters and the last variable is the
element being separated. In a Replacement formula, the final two variables are respectively the
argument and value of the relation.
-/
inductive ZFAxiom : Type
  | extensionality
  | emptySet
  | pairing
  | union
  | powerSet
  | infinity
  | foundation
  | separation (n : ℕ) (φ : Language.setTheory.Formula (Fin (n + 1)))
  | replacement (n : ℕ) (φ : Language.setTheory.Formula (Fin (n + 2)))

/-- The first-order sentence corresponding to a ZF axiom. -/
@[simp]
def ZFAxiom.toSentence : ZFAxiom → Language.setTheory.Sentence
  | .extensionality =>
      ∀' ∀' ((∀' ((&2).mem &0 ⇔ (&2).mem &1)) ⟹ (&0 =' &1))
  | .emptySet =>
      ∃' ∀' ∼((&1).mem &0)
  | .pairing =>
      ∀' ∀' ∃' ∀' ((&3).mem &2 ⇔ ((&3 =' &0) ⊔ (&3 =' &1)))
  | .union =>
      ∀' ∃' ∀' ((&2).mem &1 ⇔ ∃' ((&3).mem &0 ⊓ (&2).mem &3))
  | .powerSet =>
      ∀' ∃' ∀' ((&2).mem &1 ⇔ ∀' ((&3).mem &2 ⟹ (&3).mem &0))
  | .infinity =>
      ∃' ((∃' ((&1).mem &0 ⊓ ∀' ∼((&2).mem &1))) ⊓
        ∀' ((&1).mem &0 ⟹
          ∃' ((&2).mem &0 ⊓
            ∀' ((&3).mem &2 ⇔ ((&3).mem &1 ⊔ (&3 =' &1))))))
  | .foundation =>
      ∀' ((∃' (&1).mem &0) ⟹
        ∃' ((&1).mem &0 ⊓ ∀' ((&2).mem &0 ⟹ ∼((&2).mem &1))))
  | .separation _ φ => universalClosure (separationBody φ)
  | .replacement _ φ => universalClosure (replacementBody φ)

/-- The usual set-theoretic proposition corresponding to a ZF axiom. -/
@[simp]
def ZFAxiom.toProp (M : Type u) [Language.setTheory.Structure M] : ZFAxiom → Prop
  | .extensionality =>
      ∀ x y : M, (∀ z : M, RelMap memRel ![z, x] ↔ RelMap memRel ![z, y]) → x = y
  | .emptySet =>
      ∃ e : M, ∀ x : M, ¬RelMap memRel ![x, e]
  | .pairing =>
      ∀ x y : M, ∃ p : M, ∀ z : M, RelMap memRel ![z, p] ↔ z = x ∨ z = y
  | .union =>
      ∀ x : M, ∃ u : M, ∀ z : M,
        RelMap memRel ![z, u] ↔ ∃ y : M, RelMap memRel ![y, x] ∧ RelMap memRel ![z, y]
  | .powerSet =>
      ∀ x : M, ∃ p : M, ∀ y : M,
        RelMap memRel ![y, p] ↔ ∀ z : M, RelMap memRel ![z, y] → RelMap memRel ![z, x]
  | .infinity =>
      ∃ w : M,
        (∃ e : M, RelMap memRel ![e, w] ∧ ∀ z : M, ¬RelMap memRel ![z, e]) ∧
        ∀ x : M, RelMap memRel ![x, w] → ∃ y : M, RelMap memRel ![y, w] ∧
          ∀ z : M, RelMap memRel ![z, y] ↔ RelMap memRel ![z, x] ∨ z = x
  | .foundation =>
      ∀ x : M, (∃ y : M, RelMap memRel ![y, x]) →
        ∃ y : M, RelMap memRel ![y, x] ∧
          ∀ z : M, RelMap memRel ![z, x] → ¬RelMap memRel ![z, y]
  | .separation n φ =>
      ∀ (params : Fin n → M) (a : M), ∃ b : M, ∀ x : M,
        RelMap memRel ![x, b] ↔ RelMap memRel ![x, a] ∧ φ.Realize (Fin.snoc params x)
  | .replacement n φ =>
      ∀ (params : Fin n → M) (a : M),
        (∀ x : M, RelMap memRel ![x, a] →
          ∃! y : M, φ.Realize (Fin.snoc (Fin.snoc params x) y)) →
        ∃ b : M, ∀ y : M, RelMap memRel ![y, b] ↔
          ∃ x : M, RelMap memRel ![x, a] ∧ φ.Realize (Fin.snoc (Fin.snoc params x) y)

/-- A ZF axiom is realized exactly when its usual set-theoretic proposition holds. -/
theorem ZFAxiom.realize_toSentence_iff_toProp {M : Type u} [Language.setTheory.Structure M]
    (ax : ZFAxiom) : M ⊨ ax.toSentence ↔ ax.toProp M := by
  cases ax with
  | extensionality =>
      simp [ZFAxiom.toSentence, ZFAxiom.toProp, Sentence.Realize, Formula.Realize,
        Term.mem, Fin.snoc]
  | emptySet =>
      simp [ZFAxiom.toSentence, ZFAxiom.toProp, Sentence.Realize, Formula.Realize,
        Term.mem, Fin.snoc]
  | pairing =>
      simp [ZFAxiom.toSentence, ZFAxiom.toProp, Sentence.Realize, Formula.Realize,
        Term.mem, Fin.snoc]
  | union =>
      simp [ZFAxiom.toSentence, ZFAxiom.toProp, Sentence.Realize, Formula.Realize,
        Term.mem, Fin.snoc]
  | powerSet =>
      simp [ZFAxiom.toSentence, ZFAxiom.toProp, Sentence.Realize, Formula.Realize,
        Term.mem, Fin.snoc]
  | infinity =>
      simp [ZFAxiom.toSentence, ZFAxiom.toProp, Sentence.Realize, Formula.Realize,
        Term.mem, Fin.snoc]
  | foundation =>
      simp [ZFAxiom.toSentence, ZFAxiom.toProp, Sentence.Realize, Formula.Realize,
        Term.mem, Fin.snoc]
  | separation n φ =>
      rw [ZFAxiom.toSentence, ZFAxiom.toProp, realize_universalClosure]
      constructor
      · intro h params a
        exact (realize_separationBody φ params a).1 (h (Fin.snoc params a))
      · intro h v
        have hv := (realize_separationBody φ (Fin.init v) (v (Fin.last n))).2
          (h (Fin.init v) (v (Fin.last n)))
        simpa only [Fin.snoc_init_self] using hv
  | replacement n φ =>
      rw [ZFAxiom.toSentence, ZFAxiom.toProp, realize_universalClosure]
      constructor
      · intro h params a
        exact (realize_replacementBody φ params a).1 (h (Fin.snoc params a))
      · intro h v
        have hv := (realize_replacementBody φ (Fin.init v) (v (Fin.last n))).2
          (h (Fin.init v) (v (Fin.last n)))
        simpa only [Fin.snoc_init_self] using hv

/-- Zermelo--Fraenkel set theory with full Separation and functional Replacement. -/
def _root_.FirstOrder.Language.Theory.ZF : Language.setTheory.Theory :=
  Set.range ZFAxiom.toSentence

/-- Every indexed ZF axiom holds in a model of `Language.Theory.ZF`. -/
theorem ZFAxiom.toProp_of_model {M : Type u} [Language.setTheory.Structure M]
    [Language.Theory.ZF.Model M] (ax : ZFAxiom) : ax.toProp M :=
  (ZFAxiom.realize_toSentence_iff_toProp ax).1
    (Language.Theory.ZF.realize_sentence_of_mem ⟨ax, rfl⟩)

/-- A structure is a model of ZF exactly when it satisfies every indexed ZF axiom. -/
theorem _root_.FirstOrder.Language.Theory.model_ZF_iff {M : Type u}
    [Language.setTheory.Structure M] : M ⊨ Language.Theory.ZF ↔ ∀ ax : ZFAxiom, ax.toProp M := by
  rw [Language.Theory.model_iff]
  constructor
  · intro h ax
    exact (ax.realize_toSentence_iff_toProp).1 (h ax.toSentence ⟨ax, rfl⟩)
  · intro h φ hφ
    rcases hφ with ⟨ax, hax⟩
    subst φ
    exact ax.realize_toSentence_iff_toProp.2 (h ax)

end FirstOrder.SetTheory
