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

variable {α β : Type*} {ι ι' : Sort*} {κ κ' : ι → Sort*}

section SigmaCompleteLattice

variable [SigmaCompleteLattice α] {s t : Set α} {a b : α}
  [Countable ι] [Countable ι'] [∀ j, Countable (κ j)] [∀ j, Countable (κ' j)] {f g : ι → α} {i : ι}

lemma isLUB_σsSup (hs : s.Countable) : IsLUB s (sSup s) :=
  SigmaCompleteLattice.isLUB_σsSup s hs

lemma isGLB_σsInf (hs : s.Countable) : IsGLB s (sInf s) :=
  SigmaCompleteLattice.isGLB_σsInf s hs

lemma isLUB_σiSup : IsLUB (Set.range f) (iSup f) :=
  isLUB_σsSup (Set.countable_range f)

lemma isGLB_σiInf : IsGLB (Set.range f) (iInf f) :=
  isLUB_σiSup (α := αᵒᵈ)

lemma le_σsSup (hs : s.Countable) (ha : a ∈ s) : a ≤ sSup s :=
  (isLUB_σsSup hs).left ha

lemma σsInf_le (hs : s.Countable) (ha : a ∈ s) : sInf s ≤ a :=
  le_σsSup (α := αᵒᵈ) hs ha

theorem le_σiSup (f : ι → α) (i : ι) : f i ≤ ⨆ j : ι, f j := by
  rw [iSup]
  exact le_σsSup (Set.countable_range f) (Set.mem_range_self i)

theorem σiInf_le (f : ι → α) (i : ι) : ⨅ j : ι, f j ≤ f i :=
  le_σiSup (α := αᵒᵈ) f i

lemma σsSup_le (hs : s.Countable) (ha : ∀ b ∈ s, b ≤ a) : sSup s ≤ a :=
  (isLUB_σsSup hs).right ha

lemma le_σsInf (hs : s.Countable) (ha : ∀ b ∈ s, a ≤ b) : a ≤ sInf s :=
  σsSup_le (α := αᵒᵈ) hs ha

lemma σiSup_le (h : ∀ (i : ι), f i ≤ a) : iSup f ≤ a :=
  σsSup_le (Set.countable_range f) fun _ ⟨i, Eq⟩ => Eq ▸ h i

lemma le_σiInf  (h : ∀ (i : ι), a ≤ f i) : a ≤ iInf f :=
  σiSup_le (α := αᵒᵈ) h

theorem σiSup₂_le {f : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ a) : ⨆ (i) (j), f i j ≤ a :=
  σiSup_le fun i => σiSup_le <| h i

theorem le_σiInf₂ {f : ∀ i, κ i → α} (h : ∀ i j, a ≤ f i j) : a ≤ ⨅ (i) (j), f i j :=
  σiSup₂_le (α := αᵒᵈ) h

theorem σiSup₂_le_σiSup (f : ι → α) : ⨆ (i) (_ : κ i), f i ≤ ⨆ i, f i :=
  σiSup₂_le fun i _ => le_σiSup f i

theorem σiInf_le_σiInf₂ (f : ι → α) : ⨅ i, f i ≤ ⨅ (i) (_ : κ i), f i :=
  σiSup₂_le_σiSup (α := αᵒᵈ) f

theorem le_σsSup_of_le (hs : s.Countable) (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (le_σsSup hs hb)

theorem σsInf_le_of_le (hs : s.Countable) (hb : b ∈ s) (h : b ≤ a) : sInf s ≤ a :=
  le_σsSup_of_le (α := αᵒᵈ) hs hb h

theorem le_σiSup_of_le (i : ι) (h : a ≤ f i) : a ≤ iSup f :=
  le_trans h (le_σiSup f i)

theorem σiInf_le_of_le (h : f i ≤ a) : iInf f ≤ a :=
  le_σiSup_of_le (α := αᵒᵈ) i h

theorem le_σiSup₂ {f : ∀ i, κ i → α} (i : ι) (j : κ i) : f i j ≤ ⨆ (i) (j), f i j :=
  le_σiSup_of_le i <| le_σiSup (f i) j

theorem σiInf₂_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) : ⨅ (i) (j), f i j ≤ f i j :=
  le_σiSup₂ (α := αᵒᵈ) i j

theorem le_σiSup₂_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : a ≤ f i j) :
    a ≤ ⨆ (i) (j), f i j :=
  h.trans <| le_σiSup₂ i j

theorem σiInf₂_le_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : f i j ≤ a) :
    ⨅ (i) (j), f i j ≤ a :=
  le_σiSup₂_of_le (α := αᵒᵈ) i j h

theorem σsSup_le_σsSup (ht : t.Countable) (h : s ⊆ t) : sSup s ≤ sSup t :=
  σsSup_le (ht.mono h) fun _ ha => le_σsSup ht (h ha)

theorem σsInf_le_σsInf (ht : t.Countable) (h : s ⊆ t) : sInf t ≤ sInf s :=
  σsSup_le_σsSup (α := αᵒᵈ) ht h

theorem le_σsSup_iff (hs : s.Countable) : a ≤ sSup s ↔ ∀ b ∈ upperBounds s, a ≤ b :=
  ⟨fun h _ hb => le_trans h (σsSup_le hs hb), fun hb => hb _ fun _ => le_σsSup hs⟩

theorem σsInf_le_iff (hs : s.Countable) : sInf s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  le_σsSup_iff (α := αᵒᵈ) hs

theorem le_σiSup_iff : a ≤ iSup f ↔ ∀ b, (∀ i, f i ≤ b) → a ≤ b := by
  simp [iSup, le_σsSup_iff (Set.countable_range f), upperBounds]

theorem σiInf_le_iff : iInf f ≤ a ↔ ∀ b, (∀ i, b ≤ f i) → b ≤ a :=
  le_σiSup_iff (α := αᵒᵈ)

theorem IsLUB.σsSup_eq (h : IsLUB s a) (hs : s.Countable) : sSup s = a :=
  (isLUB_σsSup hs).unique h

theorem IsGLB.σsInf_eq (h : IsGLB s a) (hs : s.Countable) : sInf s = a :=
  IsLUB.σsSup_eq (α := αᵒᵈ) h hs

theorem IsLUB.σiSup_eq (h : IsLUB (Set.range f) a) : ⨆ j, f j = a :=
  h.σsSup_eq (Set.countable_range f)

theorem IsGLB.σiInf_eq (h : IsGLB (Set.range f) a) : ⨅ j, f j = a :=
  IsLUB.σiSup_eq (α := αᵒᵈ) h

theorem subset_Icc_σsInf_σsSup (hs : s.Countable) : s ⊆ Set.Icc (sInf s) (sSup s) :=
  fun _ hx => ⟨σsInf_le hs hx, le_σsSup hs hx⟩

theorem σsSup_le_iff (hs : s.Countable) : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_σsSup hs)

theorem le_σsInf_iff (hs : s.Countable) : a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b :=
  σsSup_le_iff (α := αᵒᵈ) hs

@[simp]
theorem σiSup_le_iff : iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff isLUB_σiSup).trans Set.forall_mem_range

@[simp]
theorem le_σiInf_iff : a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  σiSup_le_iff (α := αᵒᵈ)

theorem σiSup₂_le_iff {f : ∀ i, κ i → α} : ⨆ (i) (j), f i j ≤ a ↔ ∀ i j, f i j ≤ a := by
  simp_rw [σiSup_le_iff]

theorem σle_iInf₂_iff {f : ∀ i, κ i → α} : (a ≤ ⨅ (i) (j), f i j) ↔ ∀ i j, a ≤ f i j :=
  σiSup₂_le_iff (α := αᵒᵈ)

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

theorem σiSup_const [Nonempty ι] : ⨆ (_ : ι), a = a := by
  rw [iSup, Set.range_const, σsSup_singleton]

theorem σiInf_const [Nonempty ι] : ⨅ (_ : ι), a = a :=
  σiSup_const (α := αᵒᵈ)

/-- If a set is countable, and non-empty, its infimum is less than or equal to its supremum. -/
theorem σsInf_le_σsSup (hs : s.Countable) (ne : s.Nonempty) : sInf s ≤ sSup s :=
  isGLB_le_isLUB (isGLB_σsInf hs) (isLUB_σsSup hs) ne

theorem σiInf_le_σiSup [Nonempty ι] : ⨅ i, f i ≤ ⨆ i, f i :=
  (σiInf_le _ (Classical.arbitrary _)).trans <| le_σiSup _ (Classical.arbitrary _)

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
theorem σsSup_empty : sSup ∅ = (⊥ : α) :=
  (@isLUB_empty α _ _).σsSup_eq Set.countable_empty

@[simp]
theorem σsInf_empty : sInf ∅ = (⊤ : α) :=
  σsSup_empty (α := αᵒᵈ)

theorem σiSup_empty [IsEmpty ι] : ⨆ i, f i = ⊥ := by
  simp [iSup, Set.range_eq_empty]

theorem σiInf_empty [IsEmpty ι] : ⨅ i, f i = ⊤ :=
  σiSup_empty (α := αᵒᵈ)

theorem σiSup_const_mem : ⨆ (_ : ι), a ∈ ({⊥, a} : Set α) := by
  cases isEmpty_or_nonempty ι with
  | inl h_empty => simp [σiSup_empty]
  | inr h_non_empty => simp

theorem σiInf_const_mem : ⨅ (_ : ι), a ∈ ({⊤, a} : Set α) :=
  σiSup_const_mem (α := αᵒᵈ)

theorem σsSup_le_σsSup_of_subset_insert_bot (ht : t.Countable) (h : s ⊆ insert ⊥ t) :
    sSup s ≤ sSup t :=
  (σsSup_le_σsSup (ht.insert ⊥) h).trans_eq ((σsSup_insert ht).trans (bot_sup_eq _))

theorem σsInf_le_σsInf_of_subset_insert_top (ht : t.Countable) (h : s ⊆ insert ⊤ t) :
    sInf t ≤ sInf s :=
  σsSup_le_σsSup_of_subset_insert_bot (α := αᵒᵈ) ht h

@[simp]
theorem σsSup_diff_singleton_bot (hs : s.Countable) : sSup (s \ {⊥}) = sSup s :=
  (σsSup_le_σsSup hs Set.diff_subset).antisymm <|
    σsSup_le_σsSup_of_subset_insert_bot (hs.mono Set.diff_subset) <|
      Set.subset_insert_diff_singleton _ _

@[simp]
theorem σsInf_diff_singleton_top (hs : s.Countable) : sInf (s \ {⊤}) = sInf s :=
  σsSup_diff_singleton_bot (α := αᵒᵈ) hs

@[simp]
theorem σsSup_eq_bot (hs : s.Countable) : sSup s = ⊥ ↔ ∀ a ∈ s, a = ⊥ :=
  ⟨fun h _ ha => bot_unique <| h ▸ le_σsSup hs ha, fun h =>
    bot_unique <| σsSup_le hs fun a ha => le_bot_iff.2 <| h a ha⟩

@[simp]
theorem σsInf_eq_top (hs : s.Countable) : sInf s = ⊤ ↔ ∀ a ∈ s, a = ⊤ :=
  σsSup_eq_bot (α := αᵒᵈ) hs

lemma σsSup_eq_bot' (hs : s.Countable) : sSup s = ⊥ ↔ s = ∅ ∨ s = {⊥} := by
  rw [σsSup_eq_bot hs, ← Set.subset_singleton_iff_eq, Set.subset_singleton_iff]

lemma σsInf_eq_bot' (hs : s.Countable) : sInf s = ⊤ ↔ s = ∅ ∨ s = {⊤} :=
  σsSup_eq_bot' (α := αᵒᵈ) hs

theorem eq_singleton_bot_of_σsSup_eq_bot_of_nonempty (hs : s.Countable)
    (h_sup : sSup s = ⊥) (hne : s.Nonempty) : s = {⊥} := by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [σsSup_eq_bot hs] at h_sup
  exact ⟨hne, h_sup⟩

theorem eq_singleton_top_of_σsInf_eq_top_of_nonempty (hs : s.Countable)
    (h_inf : sInf s = ⊤) (hne : s.Nonempty) : s = {⊤} :=
  eq_singleton_bot_of_σsSup_eq_bot_of_nonempty (α := αᵒᵈ) hs h_inf hne

@[gcongr]
theorem σiSup_mono (h : ∀ i, f i ≤ g i) : iSup f ≤ iSup g :=
  σiSup_le fun i => le_σiSup_of_le i <| h i

@[gcongr]
theorem σiInf_mono (h : ∀ i, f i ≤ g i) : iInf f ≤ iInf g :=
  σiSup_mono (α := αᵒᵈ) h

theorem σiSup₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    ⨆ (i) (j), f i j ≤ ⨆ (i) (j), g i j :=
  σiSup_mono fun i => σiSup_mono <| h i

theorem σiInf₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    ⨅ (i) (j), f i j ≤ ⨅ (i) (j), g i j :=
  σiSup₂_mono (α := αᵒᵈ) h

theorem σiSup_mono' {g : ι' → α} (h : ∀ i, ∃ i', f i ≤ g i') : iSup f ≤ iSup g :=
  σiSup_le fun i => Exists.elim (h i) le_σiSup_of_le

theorem σiInf_mono' {g : ι' → α} (h : ∀ i', ∃ i, f i ≤ g i') : iInf f ≤ iInf g :=
  σiSup_mono' (α := αᵒᵈ) h

theorem σiSup₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α}
    (h : ∀ i j, ∃ i' j', f i j ≤ g i' j') : ⨆ (i) (j), f i j ≤ ⨆ (i) (j), g i j :=
  σiSup₂_le fun i j =>
    let ⟨i', j', h⟩ := h i j
    le_σiSup₂_of_le i' j' h

theorem σiInf₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α}
    (h : ∀ i j, ∃ i' j', f i' j' ≤ g i j) : ⨅ (i) (j), f i j ≤ ⨅ (i) (j), g i j :=
  σiSup₂_mono' (α := αᵒᵈ) h

theorem σiSup_const_mono (h : ι → ι') : ⨆ _ : ι, a ≤ ⨆ _ : ι', a :=
  σiSup_le <| le_σiSup _ ∘ h

theorem σiInf_const_mono (h : ι' → ι) : ⨅ _ : ι, a ≤ ⨅ _ : ι', a :=
  σiSup_const_mono (α := αᵒᵈ) h

theorem σiSup_σiInf_le_σiInf_σiSup (f : ι → ι' → α) : ⨆ i, ⨅ j, f i j ≤ ⨅ j, ⨆ i, f i j :=
  σiSup_le fun i => σiInf_mono fun j => le_σiSup (fun i => f i j) i

theorem bσiSup_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    ⨆ (i) (_ : p i), f i ≤ ⨆ (i) (_ : q i), f i :=
  σiSup_mono fun i => σiSup_const_mono (hpq i)

theorem bσiInf_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    ⨅ (i) (_ : q i), f i ≤ ⨅ (i) (_ : p i), f i :=
  σiInf_mono fun i => σiInf_const_mono (hpq i)

theorem σiSup_lt_iff : iSup f < a ↔ ∃ b, b < a ∧ ∀ i, f i ≤ b :=
  ⟨fun h => ⟨iSup f, h, le_σiSup f⟩, fun ⟨_, h, hb⟩ => (σiSup_le hb).trans_lt h⟩

theorem σlt_iInf_iff : a < iInf f ↔ ∃ b, a < b ∧ ∀ i, b ≤ f i :=
  σiSup_lt_iff (α := αᵒᵈ)

end SigmaCompleteLattice
