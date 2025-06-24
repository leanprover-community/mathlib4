/-
Copyright (c) 2025 Pierre Quinton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Quinton
-/
import Mathlib.Order.BooleanSigmaAlgebra.Defs
import Mathlib.Order.Interval.Set.Defs

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

section BooleanSigmaAlgebra

variable [BooleanSigmaAlgebra α] [Countable ι] {s t : Set α} {a b : α}

lemma isLUB_σsSup (hs : s.Countable) : IsLUB s (sSup s) :=
  BooleanSigmaAlgebra.isLUB_σsSup s hs

lemma isGLB_σsInf (hs : s.Countable) : IsGLB s (sInf s) :=
  BooleanSigmaAlgebra.isGLB_σsInf s hs

lemma le_σsSup (hs : s.Countable) (ha : a ∈ s) : a ≤ sSup s :=
  (isLUB_σsSup hs).left ha

lemma σsSup_le (hs : s.Countable) (ha : a ∈ upperBounds s) : sSup s ≤ a :=
  (isLUB_σsSup hs).right ha

lemma σsInf_le (hs : s.Countable) (ha : a ∈ s) : sInf s ≤ a :=
  (isGLB_σsInf hs).left ha

lemma le_σsInf (hs : s.Countable) (ha : a ∈ lowerBounds s) : a ≤ sInf s :=
  (isGLB_σsInf hs).right ha

theorem le_σsSup_of_le (hs : s.Countable) (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (le_σsSup hs hb)

theorem σsInf_le_of_le (hs : s.Countable) (hb : b ∈ s) (h : b ≤ a) : sInf s ≤ a :=
  le_trans (σsInf_le hs hb) h

theorem σsSup_le_σsSup (ht : t.Countable) (hs : s.Countable) (h : s ⊆ t) : sSup s ≤ sSup t :=
  σsSup_le hs fun _ ha => le_σsSup ht (h ha)

theorem σsInf_le_σsInf (ht : t.Countable) (hs : s.Countable) (h : s ⊆ t) : sInf t ≤ sInf s :=
  le_σsInf hs fun _ ha => σsInf_le ht (h ha)

theorem le_σsSup_iff (hs : s.Countable) : a ≤ sSup s ↔ ∀ b ∈ upperBounds s, a ≤ b :=
  ⟨fun h _ hb => le_trans h (σsSup_le hs hb), fun hb => hb _ fun _ => le_σsSup hs⟩

theorem σsInf_le_iff (hs : s.Countable) : sInf s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  ⟨fun h _ hb => le_trans (le_σsInf hs hb) h, fun hb => hb _ fun _ => σsInf_le hs⟩

theorem IsLUB.σsSup_eq (h : IsLUB s a) (hs : s.Countable) : sSup s = a :=
  (isLUB_σsSup hs).unique h

theorem IsGLB.σsInf_eq (h : IsGLB s a) (hs : s.Countable) : sInf s = a :=
  (isGLB_σsInf hs).unique h

theorem subset_Icc_σsInf_σsSup (hs : s.Countable) : s ⊆ Set.Icc (sInf s) (sSup s) :=
  fun _ hx => ⟨σsInf_le hs hx, le_σsSup hs hx⟩

theorem σSup_le_iff (hs : s.Countable) : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_σsSup hs)

theorem le_σsInf_iff (hs : s.Countable) : a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (isGLB_σsInf hs)

theorem notMem_of_lt_σsInf {x : α} {s : Set α} (h : x < sInf s) (hs : s.Countable) : x ∉ s :=
  fun hx => lt_irrefl _ (h.trans_le (σsInf_le hs hx))

theorem notMem_of_σsSup_lt {x : α} {s : Set α} (h : sSup s < x) (hs : s.Countable) : x ∉ s :=
  notMem_of_lt_σsInf (α := αᵒᵈ) h hs

end BooleanSigmaAlgebra
