/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module

public import Mathlib.ModelTheory.SetTheory.Basic
public import Mathlib.ModelTheory.Semantics

/-!
# Semantics for formulas in the language of set theory

This file provides relation-parametric term evaluation and formula realization
for Mathlib's first-order language of set theory.

The relation-parametric semantics below uses `BoundedFormula Empty n`: there are no
named free variables, and the `n` variables currently in scope are interpreted
by an assignment `Fin n -> A`.
-/

@[expose] public section

universe u

namespace Constructible

namespace Model

/-- Evaluate a term under an assignment in the membership structure induced by `E`. -/
def termValue {A : Type u} (E : A -> A -> Prop) {n : Nat}
    (t : FirstOrder.Language.setTheory.Term (Sum Empty (Fin n)))
    (s : Fin n -> A) : A :=
  letI : FirstOrder.Language.setTheory.Structure A :=
    FirstOrder.Language.setTheoryStructure E
  t.realize (Sum.elim Empty.elim s)

/-- Realization in the membership structure induced by `E`. -/
def realizes {A : Type u} (E : A -> A -> Prop) {n : Nat}
    (phi : FirstOrder.Language.setTheory.BoundedFormula Empty n)
    (s : Fin n -> A) : Prop :=
  letI : FirstOrder.Language.setTheory.Structure A :=
    FirstOrder.Language.setTheoryStructure E
  phi.Realize Empty.elim s

theorem realizes_falsum {A : Type u} {E : A -> A -> Prop}
    {n : Nat} {s : Fin n -> A} :
    realizes E (.falsum : FirstOrder.Language.setTheory.BoundedFormula Empty n) s <-> False := by
  rfl

theorem realizes_not {A : Type u} {E : A -> A -> Prop}
    {n : Nat} {phi : FirstOrder.Language.setTheory.BoundedFormula Empty n}
    {s : Fin n -> A} :
    realizes E phi.not s <-> Not (realizes E phi s) := by
  simp [realizes]

theorem realizes_and {A : Type u} {E : A -> A -> Prop}
    {n : Nat} {phi psi : FirstOrder.Language.setTheory.BoundedFormula Empty n}
    {s : Fin n -> A} :
    realizes E (phi ⊓ psi) s <-> realizes E phi s /\ realizes E psi s := by
  simp [realizes]

theorem realizes_imp {A : Type u} {E : A -> A -> Prop}
    {n : Nat} {phi psi : FirstOrder.Language.setTheory.BoundedFormula Empty n}
    {s : Fin n -> A} :
    realizes E (phi.imp psi) s <->
      (realizes E phi s -> realizes E psi s) := by
  rfl

theorem realizes_all {A : Type u} {E : A -> A -> Prop}
    {n : Nat} {phi : FirstOrder.Language.setTheory.BoundedFormula Empty (n + 1)}
    {s : Fin n -> A} :
    realizes E phi.all s <->
      forall x : A, realizes E phi (Fin.snoc s x) := by
  rfl

theorem realizes_ex {A : Type u} {E : A -> A -> Prop}
    {n : Nat} {phi : FirstOrder.Language.setTheory.BoundedFormula Empty (n + 1)}
    {s : Fin n -> A} :
    realizes E phi.ex s <->
      Exists fun x : A => realizes E phi (Fin.snoc s x) := by
  simp [realizes]

end Model

end Constructible
