/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module

public import Mathlib.ModelTheory.SetTheory.ZF

/-!
# The First-Order Theory ZFC

This file extends the first-order theory `Language.Theory.ZF` by the Axiom of Choice. We use the
standard disjoint-family formulation: every pairwise disjoint family of nonempty sets has a set
meeting each member of the family in exactly one element.

## Main definitions

- `FirstOrder.SetTheory.choiceSentence` is the Axiom of Choice in the language of set theory.
- `FirstOrder.SetTheory.ModelsChoice` is its usual disjoint-family semantics.
- `FirstOrder.Language.Theory.ZFC` is ZF together with `choiceSentence`.
- `FirstOrder.Language.Theory.model_ZFC_iff` characterizes models of ZFC.
-/

@[expose] public section

universe u

namespace FirstOrder.SetTheory

open Language Language.BoundedFormula Language.Structure
open scoped FirstOrder

/-- Every member of `a` is nonempty in the membership structure on `M`. -/
def IsNonemptyFamily (M : Type u) [Language.setTheory.Structure M] (a : M) : Prop :=
  ∀ x : M, RelMap memRel ![x, a] → ∃ y : M, RelMap memRel ![y, x]

/-- Distinct members of `a` are disjoint in the membership structure on `M`. -/
def IsPairwiseDisjointFamily (M : Type u) [Language.setTheory.Structure M] (a : M) : Prop :=
  ∀ x : M, RelMap memRel ![x, a] →
    ∀ y : M, RelMap memRel ![y, a] → x ≠ y →
      ∀ z : M, RelMap memRel ![z, x] → ¬RelMap memRel ![z, y]

/-- `c` meets every member of `a` in exactly one element. -/
def IsChoiceSet (M : Type u) [Language.setTheory.Structure M] (a c : M) : Prop :=
  ∀ x : M, RelMap memRel ![x, a] →
    ∃ y : M, RelMap memRel ![y, x] ∧ RelMap memRel ![y, c] ∧
      ∀ z : M, RelMap memRel ![z, x] → RelMap memRel ![z, c] → z = y

/-- The disjoint-family semantic form of the Axiom of Choice. -/
def ModelsChoice (M : Type u) [Language.setTheory.Structure M] : Prop :=
  ∀ a : M, IsNonemptyFamily M a → IsPairwiseDisjointFamily M a →
    ∃ c : M, IsChoiceSet M a c

/--
The Axiom of Choice in the disjoint-family formulation.

The outermost variable is the family `a`, and the variable introduced in the conclusion is its
choice set `c`.
-/
def choiceSentence : Language.setTheory.Sentence :=
  ∀'
    (((∀' ((&1).mem &0 ⟹ ∃' ((&2).mem &1))) ⊓
        ∀' ((&1).mem &0 ⟹
          ∀' ((&2).mem &0 ⟹
            ∼(&1 =' &2) ⟹
              ∀' ((&3).mem &1 ⟹ ∼((&3).mem &2))))) ⟹
      ∃' ∀' ((&2).mem &0 ⟹
        ∃' ((&3).mem &2 ⊓
          ((&3).mem &1 ⊓
            ∀' ((&4).mem &2 ⟹ (&4).mem &1 ⟹ (&4 =' &3))))))

/-- `choiceSentence` has exactly the usual disjoint-family semantics. -/
@[simp]
theorem realize_choiceSentence_iff {M : Type u} [Language.setTheory.Structure M] :
    M ⊨ choiceSentence ↔ ModelsChoice M := by
  simp [choiceSentence, ModelsChoice, IsNonemptyFamily, IsPairwiseDisjointFamily,
    IsChoiceSet, Sentence.Realize, Formula.Realize, Term.mem, Fin.snoc]

/-- Zermelo--Fraenkel set theory together with the Axiom of Choice. -/
def _root_.FirstOrder.Language.Theory.ZFC : Language.setTheory.Theory :=
  Language.Theory.ZF ∪ {choiceSentence}

/-- A structure is a model of ZFC exactly when it models ZF and satisfies the Axiom of Choice. -/
theorem _root_.FirstOrder.Language.Theory.model_ZFC_iff {M : Type u}
    [Language.setTheory.Structure M] :
    M ⊨ Language.Theory.ZFC ↔
      M ⊨ Language.Theory.ZF ∧ ModelsChoice M := by
  simp only [Language.Theory.ZFC, Language.Theory.model_union_iff,
    Language.Theory.model_singleton_iff,
    realize_choiceSentence_iff]

/-- The axiom-by-axiom characterization of models of ZFC. -/
theorem _root_.FirstOrder.Language.Theory.model_ZFC_iff_axioms {M : Type u}
    [Language.setTheory.Structure M] :
    M ⊨ Language.Theory.ZFC ↔
      (∀ ax : ZFAxiom, ax.toProp M) ∧ ModelsChoice M := by
  rw [Language.Theory.model_ZFC_iff, Language.Theory.model_ZF_iff]

end FirstOrder.SetTheory
