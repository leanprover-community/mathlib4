/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module

public import Mathlib.ModelTheory.Syntax

/-!
# The First-Order Language of Set Theory

This file defines the first-order language with a single binary relation symbol
for membership. Equality is provided by first-order logic itself.

## Main Definitions

- `FirstOrder.Language.setTheory` is the first-order language of set theory.
- `FirstOrder.Language.Term.mem` is the atomic formula asserting membership between two terms.
- `FirstOrder.Language.setTheoryStructure` interprets membership as a binary relation.
-/

@[expose] public section

universe u v

namespace FirstOrder.Language

open Structure

variable {M : Type u} {α : Type v} {n : ℕ}

/-- The relation symbols of the first-order language of set theory. -/
inductive setTheoryRel : ℕ → Type
  | mem : setTheoryRel 2
  deriving DecidableEq

/-- The relational language with a single binary relation symbol for membership. -/
protected def setTheory : Language :=
  ⟨fun _ => Empty, setTheoryRel⟩
  deriving IsRelational

/-- The membership relation symbol in the first-order language of set theory. -/
abbrev memRel : Language.setTheory.Relations 2 := .mem

/-- The atomic formula asserting that `t₁` is a member of `t₂`. -/
def Term.mem (t₁ t₂ : Language.setTheory.Term (α ⊕ Fin n)) :
    Language.setTheory.BoundedFormula α n :=
  memRel.boundedFormula₂ t₁ t₂

/-- Interpret the first-order language of set theory using a binary relation. -/
@[implicit_reducible]
def setTheoryStructure (r : M → M → Prop) : Language.setTheory.Structure M where
  RelMap | .mem => fun x ↦ r (x 0) (x 1)

@[simp]
theorem setTheoryStructure_relMap (r : M → M → Prop) (x : Fin 2 → M) :
    @RelMap Language.setTheory M (setTheoryStructure r) 2 memRel x ↔ r (x 0) (x 1) :=
  Iff.rfl

end FirstOrder.Language
