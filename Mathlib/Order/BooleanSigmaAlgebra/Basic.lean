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
countability assumptions have to be added.

To differentiate the statements between complete Boolean algebras and Boolean σ-algebras, we prefix
`sInf` and `sSup` in the statements by `σ`, giving `σsInf` and `σsSup`.
For instance, `sInf_le` is a statement in complete lattices ensuring `sInf s ≤ x`,
while `σsInf_le` is the same statement in Boolean σ-algebras with an additional assumption that `s`
is countable.
-/

variable {α : Type*}

section SigmaCompleteLattice

variable [SigmaCompleteLattice α] {s t : Set α} {a b : α}

lemma isLUB_σsSup (hs : s.Countable) : IsLUB s (sSup s) :=
  SigmaCompleteLattice.isLUB_σsSup s hs

lemma isGLB_σsInf (hs : s.Countable) : IsGLB s (sInf s) :=
  SigmaCompleteLattice.isGLB_σsInf s hs

lemma le_σsSup (hs : s.Countable) (ha : a ∈ s) : a ≤ sSup s :=
  (isLUB_σsSup hs).left ha

lemma σsInf_le (hs : s.Countable) (ha : a ∈ s) : sInf s ≤ a :=
  le_σsSup (α := αᵒᵈ) hs ha

lemma σsSup_le (hs : s.Countable) (ha : a ∈ upperBounds s) : sSup s ≤ a :=
  (isLUB_σsSup hs).right ha

lemma le_σsInf (hs : s.Countable) (ha : a ∈ lowerBounds s) : a ≤ sInf s :=
  σsSup_le (α := αᵒᵈ) hs ha

theorem le_σsSup_of_le (hs : s.Countable) (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (le_σsSup hs hb)

theorem σsInf_le_of_le (hs : s.Countable) (hb : b ∈ s) (h : b ≤ a) : sInf s ≤ a :=
  le_σsSup_of_le (α := αᵒᵈ) hs hb h

theorem σsSup_le_σsSup (ht : t.Countable) (h : s ⊆ t) : sSup s ≤ sSup t :=
  σsSup_le (ht.mono h) fun _ ha => le_σsSup ht (h ha)

theorem σsInf_le_σsInf (ht : t.Countable) (h : s ⊆ t) : sInf t ≤ sInf s :=
  σsSup_le_σsSup (α := αᵒᵈ) ht h

theorem le_σsSup_iff (hs : s.Countable) : a ≤ sSup s ↔ ∀ b ∈ upperBounds s, a ≤ b :=
  ⟨fun h _ hb => le_trans h (σsSup_le hs hb), fun hb => hb _ fun _ => le_σsSup hs⟩

theorem σsInf_le_iff (hs : s.Countable) : sInf s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  le_σsSup_iff (α := αᵒᵈ) hs

theorem IsLUB.σsSup_eq (h : IsLUB s a) (hs : s.Countable) : sSup s = a :=
  (isLUB_σsSup hs).unique h

theorem IsGLB.σsInf_eq (h : IsGLB s a) (hs : s.Countable) : sInf s = a :=
  IsLUB.σsSup_eq (α := αᵒᵈ) h hs

theorem subset_Icc_σsInf_σsSup (hs : s.Countable) : s ⊆ Set.Icc (sInf s) (sSup s) :=
  fun _ hx => ⟨σsInf_le hs hx, le_σsSup hs hx⟩

theorem σsSup_le_iff (hs : s.Countable) : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_σsSup hs)

theorem le_σsInf_iff (hs : s.Countable) : a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b :=
  σsSup_le_iff (α := αᵒᵈ) hs

theorem notMem_of_lt_σsInf (h : a < sInf s) (hs : s.Countable) : a ∉ s :=
  fun hx => lt_irrefl _ (h.trans_le (σsInf_le hs hx))

theorem notMem_of_σsSup_lt (h : sSup s < a) (hs : s.Countable) : a ∉ s :=
  notMem_of_lt_σsInf (α := αᵒᵈ) h hs

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `sSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem σsSup_eq_of_forall_le_of_forall_lt_exists_gt (hs : s.Countable) (h₁ : ∀ a ∈ s, a ≤ b)
    (h₂ : ∀ w, w < b → ∃ a ∈ s, w < a) : sSup s = b :=
  (eq_of_le_of_not_lt (σsSup_le hs h₁)) fun hb =>
    let ⟨_, ha, ha'⟩ := h₂ _ hb
    lt_irrefl _ <| ha'.trans_le <| le_σsSup hs ha

/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `sInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem σsInf_eq_of_forall_ge_of_forall_gt_exists_lt (hs : s.Countable) (h₁ : ∀ a ∈ s, b ≤ a)
    (h₂ : ∀ w, b < w → ∃ a ∈ s, a < w) : sInf s = b :=
  σsSup_eq_of_forall_le_of_forall_lt_exists_gt (α := αᵒᵈ) hs h₁ h₂

theorem lt_σsSup_of_lt (hs : s.Countable) (ha : a ∈ s) (h : b < a) : b < sSup s :=
  lt_of_lt_of_le h (le_σsSup hs ha)

theorem σsInf_lt_of_lt (hs : s.Countable) (ha : a ∈ s) (h : a < b) : sInf s < b :=
  lt_σsSup_of_lt (α := αᵒᵈ) hs ha h

@[simp]
theorem σsSup_singleton : sSup {a} = a :=
  IsLUB.σsSup_eq isLUB_singleton (Set.countable_singleton a)

@[simp]
theorem σsInf_singleton : sInf {a} = a :=
  σsSup_singleton (α := αᵒᵈ)

theorem σsSup_pair (a b : α) : sSup {a, b} = a ⊔ b :=
  (@isLUB_pair _ _ a b).σsSup_eq <| by simp

theorem σsInf_pair (a b : α) : sInf {a, b} = a ⊓ b :=
  σsSup_pair (α := αᵒᵈ) a b

/-- If a set is countable, and non-empty, its infimum is less than or equal to its supremum. -/
theorem σsInf_le_σsSup (hs : s.Countable) (ne : s.Nonempty) : sInf s ≤ sSup s :=
  isGLB_le_isLUB (isGLB_σsInf hs) (isLUB_σsSup hs) ne

/-- The `sSup` of a union of two sets is the max of the suprema of each subset, under the
assumptions that all sets are countable. -/
theorem σsSup_union (hs : s.Countable) (ht : t.Countable) :
    sSup (s ∪ t) = sSup s ⊔ sSup t :=
  ((isLUB_σsSup hs).union (isLUB_σsSup ht)).σsSup_eq (hs.union ht)

/-- The `sInf` of a union of two sets is the min of the infima of each subset, under the
assumptions that all sets are countable. -/
theorem σsInf_union (hs : s.Countable) (ht : t.Countable) :
    sInf (s ∪ t) = sInf s ⊓ sInf t :=
  σsSup_union (α := αᵒᵈ) hs ht

/-- The supremum of an intersection of two sets is bounded above by the minimum of the suprema of
each set, under the assumptions that all sets are countable. -/
theorem σsSup_inter_le (hs : s.Countable) (ht : t.Countable) : sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  σsSup_le (hs.mono Set.inter_subset_left) fun _ hx => le_inf (le_σsSup hs hx.1) (le_σsSup ht hx.2)

/-- The infimum of an intersection of two sets is bounded below by the maximum of the infima of
each set, under the assumptions that all sets are countable. -/
theorem le_σsInf_inter (hs : s.Countable) (ht : t.Countable) : sInf s ⊔ sInf t ≤ sInf (s ∩ t) :=
  σsSup_inter_le (α := αᵒᵈ) hs ht

/-- The supremum of `insert a s` is the maximum of `a` and the supremum of `s`, if `s` is
nonempty and bounded above. -/
@[simp]
theorem σsSup_insert (hs : s.Countable) : sSup (insert a s) = a ⊔ sSup s :=
  ((isLUB_σsSup hs).insert a).σsSup_eq <| hs.insert a

/-- The infimum of `insert a s` is the minimum of `a` and the infimum of `s`, if `s` is
nonempty and bounded below. -/
@[simp]
theorem σsInf_insert (hs : s.Countable) : sInf (insert a s) = a ⊓ sInf s :=
  σsSup_insert (α := αᵒᵈ) hs

theorem σsSup_le_σsSup_of_forall_exists_le (hs : s.Countable) (ht : t.Countable)
    (h : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) : sSup s ≤ sSup t :=
  (le_σsSup_iff ht).2 fun _ hb =>
    σsSup_le hs fun a ha =>
      let ⟨_, hct, hac⟩ := h a ha
      hac.trans (hb hct)

theorem σsInf_le_σsInf_of_forall_exists_le (hs : s.Countable) (ht : t.Countable)
    (h : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) : sInf t ≤ sInf s :=
  σsSup_le_σsSup_of_forall_exists_le (α := αᵒᵈ) hs ht h

@[simp]
theorem σsSup_empty [OrderBot α] : sSup ∅ = (⊥ : α) :=
  (@isLUB_empty α _ _).σsSup_eq Set.countable_empty

@[simp]
theorem σsInf_empty [OrderTop α] : sInf ∅ = (⊤ : α) :=
  σsSup_empty (α := αᵒᵈ)

theorem σsSup_le_σsSup_of_subset_insert_bot [OrderBot α] (ht : t.Countable) (h : s ⊆ insert ⊥ t) :
    sSup s ≤ sSup t :=
  (σsSup_le_σsSup (ht.insert ⊥) h).trans_eq ((σsSup_insert ht).trans (bot_sup_eq _))

theorem σsInf_le_σsInf_of_subset_insert_top [OrderTop α] (ht : t.Countable) (h : s ⊆ insert ⊤ t) :
    sInf t ≤ sInf s :=
  σsSup_le_σsSup_of_subset_insert_bot (α := αᵒᵈ) ht h

@[simp]
theorem σsSup_diff_singleton_bot [OrderBot α] (hs : s.Countable) : sSup (s \ {⊥}) = sSup s :=
  (σsSup_le_σsSup hs Set.diff_subset).antisymm <|
    σsSup_le_σsSup_of_subset_insert_bot (hs.mono Set.diff_subset) <|
      Set.subset_insert_diff_singleton _ _

@[simp]
theorem σsInf_diff_singleton_top [OrderTop α] (hs : s.Countable) : sInf (s \ {⊤}) = sInf s :=
  σsSup_diff_singleton_bot (α := αᵒᵈ) hs

end SigmaCompleteLattice
