/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Gabriel Ebner, Yury Kudryashov
-/
import Mathlib.Data.Set.Accumulate
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Conditionally complete linear order structure on `ℕ`

In this file we

* define a `ConditionallyCompleteLinearOrderBot` structure on `ℕ`;
* prove a few lemmas about `iSup`/`iInf`/`Set.iUnion`/`Set.iInter` and natural numbers.
-/

assert_not_exists MonoidWithZero

open Set

namespace Nat

open scoped Classical in
noncomputable instance : InfSet ℕ :=
  ⟨fun s ↦ if h : ∃ n, n ∈ s then @Nat.find (fun n ↦ n ∈ s) _ h else 0⟩

open scoped Classical in
noncomputable instance : SupSet ℕ :=
  ⟨fun s ↦ if h : ∃ n, ∀ a ∈ s, a ≤ n then @Nat.find (fun n ↦ ∀ a ∈ s, a ≤ n) _ h else 0⟩

open scoped Classical in
theorem sInf_def {s : Set ℕ} (h : s.Nonempty) : sInf s = @Nat.find (fun n ↦ n ∈ s) _ h :=
  dif_pos _

open scoped Classical in
theorem sSup_def {s : Set ℕ} (h : ∃ n, ∀ a ∈ s, a ≤ n) :
    sSup s = @Nat.find (fun n ↦ ∀ a ∈ s, a ≤ n) _ h :=
  dif_pos _

theorem _root_.Set.Infinite.Nat.sSup_eq_zero {s : Set ℕ} (h : s.Infinite) : sSup s = 0 :=
  dif_neg fun ⟨n, hn⟩ ↦
    let ⟨k, hks, hk⟩ := h.exists_gt n
    (hn k hks).not_gt hk

@[simp]
theorem sInf_eq_zero {s : Set ℕ} : sInf s = 0 ↔ 0 ∈ s ∨ s = ∅ := by
  cases eq_empty_or_nonempty s with
  | inl h => subst h
             simp only [or_true, InfSet.sInf,
                        mem_empty_iff_false, exists_false, dif_neg, not_false_iff]
  | inr h => simp only [h.ne_empty, or_false, Nat.sInf_def, h, Nat.find_eq_zero]

@[simp]
theorem sInf_empty : sInf ∅ = 0 := by
  rw [sInf_eq_zero]
  right
  rfl

@[simp]
theorem iInf_of_empty {ι : Sort*} [IsEmpty ι] (f : ι → ℕ) : iInf f = 0 := by
  rw [iInf_of_isEmpty, sInf_empty]

/-- This combines `Nat.iInf_of_empty` with `ciInf_const`. -/
@[simp]
lemma iInf_const_zero {ι : Sort*} : ⨅ _ : ι, 0 = 0 :=
  (isEmpty_or_nonempty ι).elim (fun h ↦ by simp) fun h ↦ sInf_eq_zero.2 <| by simp

theorem sInf_mem {s : Set ℕ} (h : s.Nonempty) : sInf s ∈ s := by
  classical
  rw [Nat.sInf_def h]
  exact Nat.find_spec h

theorem notMem_of_lt_sInf {s : Set ℕ} {m : ℕ} (hm : m < sInf s) : m ∉ s := by
  classical
  cases eq_empty_or_nonempty s with
  | inl h => subst h; apply notMem_empty
  | inr h => rw [Nat.sInf_def h] at hm; exact Nat.find_min h hm

@[deprecated (since := "2025-05-23")] alias not_mem_of_lt_sInf := notMem_of_lt_sInf

protected theorem sInf_le {s : Set ℕ} {m : ℕ} (hm : m ∈ s) : sInf s ≤ m := by
  classical
  rw [Nat.sInf_def ⟨m, hm⟩]
  exact Nat.find_min' ⟨m, hm⟩ hm

theorem nonempty_of_pos_sInf {s : Set ℕ} (h : 0 < sInf s) : s.Nonempty := by
  by_contra contra
  rw [Set.not_nonempty_iff_eq_empty] at contra
  have h' : sInf s ≠ 0 := ne_of_gt h
  apply h'
  rw [Nat.sInf_eq_zero]
  right
  assumption

theorem nonempty_of_sInf_eq_succ {s : Set ℕ} {k : ℕ} (h : sInf s = k + 1) : s.Nonempty :=
  nonempty_of_pos_sInf (h.symm ▸ succ_pos k : sInf s > 0)

theorem eq_Ici_of_nonempty_of_upward_closed {s : Set ℕ} (hs : s.Nonempty)
    (hs' : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s) : s = Ici (sInf s) :=
  ext fun n ↦ ⟨fun H ↦ Nat.sInf_le H, fun H ↦ hs' (sInf s) n H (sInf_mem hs)⟩

theorem sInf_upward_closed_eq_succ_iff {s : Set ℕ} (hs : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s)
    (k : ℕ) : sInf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s := by
  classical
  constructor
  · intro H
    rw [eq_Ici_of_nonempty_of_upward_closed (nonempty_of_sInf_eq_succ _) hs, H, mem_Ici, mem_Ici]
    · exact ⟨le_rfl, k.not_succ_le_self⟩
    · exact k
    · assumption
  · rintro ⟨H, H'⟩
    rw [sInf_def (⟨_, H⟩ : s.Nonempty), find_eq_iff]
    exact ⟨H, fun n hnk hns ↦ H' <| hs n k (Nat.lt_succ_iff.mp hnk) hns⟩

/-- This instance is necessary, otherwise the lattice operations would be derived via
`ConditionallyCompleteLinearOrderBot` and marked as noncomputable. -/
instance : Lattice ℕ :=
  LinearOrder.toLattice

open scoped Classical in
noncomputable instance : ConditionallyCompleteLinearOrderBot ℕ :=
  { (inferInstance : OrderBot ℕ), (LinearOrder.toLattice : Lattice ℕ),
    (inferInstance : LinearOrder ℕ) with
    le_csSup := fun s a hb ha ↦ by rw [sSup_def hb]; revert a ha; exact @Nat.find_spec _ _ hb
    csSup_le := fun s a _ ha ↦ by rw [sSup_def ⟨a, ha⟩]; exact Nat.find_min' _ ha
    le_csInf := fun s a hs hb ↦ by
      rw [sInf_def hs]; exact hb (@Nat.find_spec (fun n ↦ n ∈ s) _ _)
    csInf_le := fun s a _ ha ↦ by rw [sInf_def ⟨a, ha⟩]; exact Nat.find_min' _ ha
    csSup_empty := by
      simp only [sSup_def, Set.mem_empty_iff_false, forall_const, forall_prop_of_false,
        not_false_iff, exists_const]
      apply bot_unique (Nat.find_min' _ _)
      trivial
    csSup_of_not_bddAbove := by
      intro s hs
      simp only [sSup,
        mem_empty_iff_false, IsEmpty.forall_iff, forall_const, exists_const, dite_true]
      rw [dif_neg]
      · exact le_antisymm (zero_le _) (find_le trivial)
      · exact hs
    csInf_of_not_bddBelow := fun s hs ↦ by simp at hs }

theorem sSup_mem {s : Set ℕ} (h₁ : s.Nonempty) (h₂ : BddAbove s) : sSup s ∈ s :=
  let ⟨k, hk⟩ := h₂
  h₁.csSup_mem ((finite_le_nat k).subset hk)

theorem sInf_add {n : ℕ} {p : ℕ → Prop} (hn : n ≤ sInf { m | p m }) :
    sInf { m | p (m + n) } + n = sInf { m | p m } := by
  classical
  obtain h | ⟨m, hm⟩ := { m | p (m + n) }.eq_empty_or_nonempty
  · rw [h, Nat.sInf_empty, zero_add]
    obtain hnp | hnp := hn.eq_or_lt
    · exact hnp
    suffices hp : p (sInf { m | p m } - n + n) from (h.subset hp).elim
    rw [Nat.sub_add_cancel hn]
    exact csInf_mem (nonempty_of_pos_sInf <| n.zero_le.trans_lt hnp)
  · have hp : ∃ n, n ∈ { m | p m } := ⟨_, hm⟩
    rw [Nat.sInf_def ⟨m, hm⟩, Nat.sInf_def hp]
    rw [Nat.sInf_def hp] at hn
    exact find_add hn

theorem sInf_add' {n : ℕ} {p : ℕ → Prop} (h : 0 < sInf { m | p m }) :
    sInf { m | p m } + n = sInf { m | p (m - n) } := by
  suffices h₁ : n ≤ sInf {m | p (m - n)} by
    convert sInf_add h₁
    simp_rw [Nat.add_sub_cancel_right]
  obtain ⟨m, hm⟩ := nonempty_of_pos_sInf h
  refine
    le_csInf ⟨m + n, ?_⟩ fun b hb ↦
      le_of_not_gt fun hbn ↦
        ne_of_mem_of_not_mem ?_ (notMem_of_lt_sInf h) (Nat.sub_eq_zero_of_le hbn.le)
  · dsimp
    rwa [Nat.add_sub_cancel_right]
  · exact hb

section

variable {α : Type*} [CompleteLattice α]

theorem iSup_lt_succ (u : ℕ → α) (n : ℕ) : ⨆ k < n + 1, u k = (⨆ k < n, u k) ⊔ u n := by
  simp_rw [Nat.lt_add_one_iff, biSup_le_eq_sup]

theorem iSup_lt_succ' (u : ℕ → α) (n : ℕ) : ⨆ k < n + 1, u k = u 0 ⊔ ⨆ k < n, u (k + 1) := by
  rw [← sup_iSup_nat_succ]
  simp

theorem iInf_lt_succ (u : ℕ → α) (n : ℕ) : ⨅ k < n + 1, u k = (⨅ k < n, u k) ⊓ u n :=
  @iSup_lt_succ αᵒᵈ _ _ _

theorem iInf_lt_succ' (u : ℕ → α) (n : ℕ) : ⨅ k < n + 1, u k = u 0 ⊓ ⨅ k < n, u (k + 1) :=
  @iSup_lt_succ' αᵒᵈ _ _ _

theorem iSup_le_succ (u : ℕ → α) (n : ℕ) : ⨆ k ≤ n + 1, u k = (⨆ k ≤ n, u k) ⊔ u (n + 1) := by
  simp_rw [← Nat.lt_succ_iff, iSup_lt_succ]

theorem iSup_le_succ' (u : ℕ → α) (n : ℕ) : ⨆ k ≤ n + 1, u k = u 0 ⊔ ⨆ k ≤ n, u (k + 1) := by
  simp_rw [← Nat.lt_succ_iff, iSup_lt_succ']

theorem iInf_le_succ (u : ℕ → α) (n : ℕ) : ⨅ k ≤ n + 1, u k = (⨅ k ≤ n, u k) ⊓ u (n + 1) :=
  @iSup_le_succ αᵒᵈ _ _ _

theorem iInf_le_succ' (u : ℕ → α) (n : ℕ) : ⨅ k ≤ n + 1, u k = u 0 ⊓ ⨅ k ≤ n, u (k + 1) :=
  @iSup_le_succ' αᵒᵈ _ _ _

end

end Nat

namespace Set

variable {α : Type*}

theorem biUnion_lt_succ (u : ℕ → Set α) (n : ℕ) : ⋃ k < n + 1, u k = (⋃ k < n, u k) ∪ u n :=
  Nat.iSup_lt_succ u n

theorem biUnion_lt_succ' (u : ℕ → Set α) (n : ℕ) : ⋃ k < n + 1, u k = u 0 ∪ ⋃ k < n, u (k + 1) :=
  Nat.iSup_lt_succ' u n

theorem biInter_lt_succ (u : ℕ → Set α) (n : ℕ) : ⋂ k < n + 1, u k = (⋂ k < n, u k) ∩ u n :=
  Nat.iInf_lt_succ u n

theorem biInter_lt_succ' (u : ℕ → Set α) (n : ℕ) : ⋂ k < n + 1, u k = u 0 ∩ ⋂ k < n, u (k + 1) :=
  Nat.iInf_lt_succ' u n

theorem biUnion_le_succ (u : ℕ → Set α) (n : ℕ) : ⋃ k ≤ n + 1, u k = (⋃ k ≤ n, u k) ∪ u (n + 1) :=
  Nat.iSup_le_succ u n

theorem biUnion_le_succ' (u : ℕ → Set α) (n : ℕ) : ⋃ k ≤ n + 1, u k = u 0 ∪ ⋃ k ≤ n, u (k + 1) :=
  Nat.iSup_le_succ' u n

theorem biInter_le_succ (u : ℕ → Set α) (n : ℕ) : ⋂ k ≤ n + 1, u k = (⋂ k ≤ n, u k) ∩ u (n + 1) :=
  Nat.iInf_le_succ u n

theorem biInter_le_succ' (u : ℕ → Set α) (n : ℕ) : ⋂ k ≤ n + 1, u k = u 0 ∩ ⋂ k ≤ n, u (k + 1) :=
  Nat.iInf_le_succ' u n

theorem accumulate_succ (u : ℕ → Set α) (n : ℕ) :
    Accumulate u (n + 1) = Accumulate u n ∪ u (n + 1) := biUnion_le_succ u n

end Set
