/-
Copyright (c) 2025 Pierre Quinton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Quinton
-/
import Mathlib.Order.BooleanSigmaAlgebra.Defs

/-!
# Theory of Boolean σ-algebras

A Boolean σ-algebra is a Booleanalgebra in which every countable subset `s` has a least upper bound
and a greatest lower bound, denoted below by `sSup s` and `sInf s`. This provides a natural
generalization for σ-algebras.

The theory is very comparable to the theory of complete Boolean algebras, except that suitable
countability have to be added to most statements.

To differentiate the statements between complete Boolean algebras and Boolean σ-algebras, we prefix
`sInf` and `sSup` in the statements by `σ`, giving `σsInf` and `σsSup`.
For instance, `sInf_le` is a statement in complete lattices ensuring `sInf s ≤ x`,
while `σsInf_le` is the same statement in Boolean σ-algebras with an additional assumption that `s`
is countable.
-/


universe u v w w'

variable {α : Type u} {β : Type v} {ι : Sort w} {κ : ι → Sort w'}

section BooleanσAlgebra

variable [BooleanσAlgebra α] [Countable ι] {s : Set α}

lemma isLUB_σsSup (hs : s.Countable) : IsLUB s (sSup s) := by
  exact BooleanσAlgebra.isLUB_σsSup s hs

lemma isGLB_σsInf (hs : s.Countable) : IsGLB s (sInf s) := by
  exact BooleanσAlgebra.isGLB_σsInf s hs

lemma le_σsSup (a : α) (hs : s.Countable) (ha : a ∈ s) : a ≤ sSup s :=
  (isLUB_σsSup hs).left ha

lemma σsSup_le (a : α) (hs : s.Countable) (ha : a ∈ upperBounds s) : sSup s ≤ a :=
  (isLUB_σsSup hs).right ha

lemma σsInf_le (a : α) (hs : s.Countable) (ha : a ∈ s) : sInf s ≤ a :=
  (isGLB_σsInf hs).left ha

lemma le_σsInf (a : α) (hs : s.Countable) (ha : a ∈ lowerBounds s) : a ≤ sInf s :=
  (isGLB_σsInf hs).right ha

end BooleanσAlgebra
