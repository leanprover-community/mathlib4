/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Gabriel Ebner, Yury Kudryashov

! This file was ported from Lean 3 source module data.nat.lattice
! leanprover-community/mathlib commit 52fa514ec337dd970d71d8de8d0fd68b455a1e54
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Nat.Interval
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Conditionally complete linear order structure on `ℕ`

In this file we

* define a `ConditionallyCcompleteLinearOrderBot` structure on `ℕ`;
* prove a few lemmas about `supᵢ`/`infᵢ`/`Set.unionᵢ`/`Set.interᵢ` and natural numbers.
-/


open Set

namespace Nat

open Classical

noncomputable instance : InfSet ℕ :=
  ⟨fun s ↦ if h : ∃ n, n ∈ s then @Nat.find (fun n ↦ n ∈ s) _ h else 0⟩

noncomputable instance : SupSet ℕ :=
  ⟨fun s ↦ if h : ∃ n, ∀ a ∈ s, a ≤ n then @Nat.find (fun n ↦ ∀ a ∈ s, a ≤ n) _ h else 0⟩

theorem infₛ_def {s : Set ℕ} (h : s.Nonempty) : infₛ s = @Nat.find (fun n ↦ n ∈ s) _ h :=
  dif_pos _
#align nat.Inf_def Nat.infₛ_def

theorem supₛ_def {s : Set ℕ} (h : ∃ n, ∀ a ∈ s, a ≤ n) :
    supₛ s = @Nat.find (fun n ↦ ∀ a ∈ s, a ≤ n) _ h :=
  dif_pos _
#align nat.Sup_def Nat.supₛ_def

theorem _root_.Set.Infinite.Nat.supₛ_eq_zero {s : Set ℕ} (h : s.Infinite) : supₛ s = 0 :=
  dif_neg fun ⟨n, hn⟩ ↦
    let ⟨k, hks, hk⟩ := h.exists_gt n
    (hn k hks).not_lt hk
#align set.infinite.nat.Sup_eq_zero Set.Infinite.Nat.supₛ_eq_zero

@[simp]
theorem infₛ_eq_zero {s : Set ℕ} : infₛ s = 0 ↔ 0 ∈ s ∨ s = ∅ := by
  cases eq_empty_or_nonempty s with
  | inl h => subst h
             simp only [or_true_iff, eq_self_iff_true, iff_true_iff, infᵢ, InfSet.infₛ,
                        mem_empty_iff_false, exists_false, dif_neg, not_false_iff]
  | inr h => simp only [h.ne_empty, or_false_iff, Nat.infₛ_def, h, Nat.find_eq_zero]
#align nat.Inf_eq_zero Nat.infₛ_eq_zero

@[simp]
theorem infₛ_empty : infₛ ∅ = 0 := by
  rw [infₛ_eq_zero]
  right
  rfl
#align nat.Inf_empty Nat.infₛ_empty

@[simp]
theorem infᵢ_of_empty {ι : Sort _} [IsEmpty ι] (f : ι → ℕ) : infᵢ f = 0 := by
  rw [infᵢ_of_empty', infₛ_empty]
#align nat.infi_of_empty Nat.infᵢ_of_empty

theorem infₛ_mem {s : Set ℕ} (h : s.Nonempty) : infₛ s ∈ s := by
  rw [Nat.infₛ_def h]
  exact Nat.find_spec h
#align nat.Inf_mem Nat.infₛ_mem

theorem not_mem_of_lt_infₛ {s : Set ℕ} {m : ℕ} (hm : m < infₛ s) : m ∉ s := by
  cases eq_empty_or_nonempty s with
  | inl h => subst h; apply not_mem_empty
  | inr h => rw [Nat.infₛ_def h] at hm; exact Nat.find_min h hm
#align nat.not_mem_of_lt_Inf Nat.not_mem_of_lt_infₛ

protected theorem infₛ_le {s : Set ℕ} {m : ℕ} (hm : m ∈ s) : infₛ s ≤ m := by
  rw [Nat.infₛ_def ⟨m, hm⟩]
  exact Nat.find_min' ⟨m, hm⟩ hm
#align nat.Inf_le Nat.infₛ_le

theorem nonempty_of_pos_infₛ {s : Set ℕ} (h : 0 < infₛ s) : s.Nonempty := by
  by_contra contra
  rw [Set.not_nonempty_iff_eq_empty] at contra
  have h' : infₛ s ≠ 0 := ne_of_gt h
  apply h'
  rw [Nat.infₛ_eq_zero]
  right
  assumption
#align nat.nonempty_of_pos_Inf Nat.nonempty_of_pos_infₛ

theorem nonempty_of_infₛ_eq_succ {s : Set ℕ} {k : ℕ} (h : infₛ s = k + 1) : s.Nonempty :=
  nonempty_of_pos_infₛ (h.symm ▸ succ_pos k : infₛ s > 0)
#align nat.nonempty_of_Inf_eq_succ Nat.nonempty_of_infₛ_eq_succ

theorem eq_Ici_of_nonempty_of_upward_closed {s : Set ℕ} (hs : s.Nonempty)
    (hs' : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s) : s = Ici (infₛ s) :=
  ext fun n ↦ ⟨fun H ↦ Nat.infₛ_le H, fun H ↦ hs' (infₛ s) n H (infₛ_mem hs)⟩
#align nat.eq_Ici_of_nonempty_of_upward_closed Nat.eq_Ici_of_nonempty_of_upward_closed

theorem infₛ_upward_closed_eq_succ_iff {s : Set ℕ} (hs : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s)
    (k : ℕ) : infₛ s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s := by
  constructor
  · intro H
    rw [eq_Ici_of_nonempty_of_upward_closed (nonempty_of_infₛ_eq_succ _) hs, H, mem_Ici, mem_Ici]
    exact ⟨le_rfl, k.not_succ_le_self⟩;
    exact k; assumption
  · rintro ⟨H, H'⟩
    rw [infₛ_def (⟨_, H⟩ : s.Nonempty), find_eq_iff]
    exact ⟨H, fun n hnk hns ↦ H' <| hs n k (lt_succ_iff.mp hnk) hns⟩
#align nat.Inf_upward_closed_eq_succ_iff Nat.infₛ_upward_closed_eq_succ_iff

/-- This instance is necessary, otherwise the lattice operations would be derived via
`ConditionallyCompleteLinearOrderBot` and marked as noncomputable. -/
instance : Lattice ℕ :=
  LinearOrder.toLattice

noncomputable instance : ConditionallyCompleteLinearOrderBot ℕ :=
  { (inferInstance : OrderBot ℕ), (LinearOrder.toLattice : Lattice ℕ),
    (inferInstance : LinearOrder ℕ) with
    -- sup := supₛ -- Porting note: removed, unecessary?
    -- inf := infₛ -- Porting note: removed, unecessary?
    le_csupₛ := fun s a hb ha ↦ by rw [supₛ_def hb] ; revert a ha ; exact @Nat.find_spec _ _ hb
    csupₛ_le := fun s a _ ha ↦ by rw [supₛ_def ⟨a, ha⟩] ; exact Nat.find_min' _ ha
    le_cinfₛ := fun s a hs hb ↦ by
      rw [infₛ_def hs] ; exact hb (@Nat.find_spec (fun n ↦ n ∈ s) _ _)
    cinfₛ_le := fun s a _ ha ↦ by rw [infₛ_def ⟨a, ha⟩] ; exact Nat.find_min' _ ha
    csupₛ_empty := by
      simp only [supₛ_def, Set.mem_empty_iff_false, forall_const, forall_prop_of_false,
        not_false_iff, exists_const]
      apply bot_unique (Nat.find_min' _ _)
      trivial }

theorem supₛ_mem {s : Set ℕ} (h₁ : s.Nonempty) (h₂ : BddAbove s) : supₛ s ∈ s :=
  let ⟨k, hk⟩ := h₂
  h₁.cSup_mem ((finite_le_nat k).subset hk)
#align nat.Sup_mem Nat.supₛ_mem

theorem infₛ_add {n : ℕ} {p : ℕ → Prop} (hn : n ≤ infₛ { m | p m }) :
    infₛ { m | p (m + n) } + n = infₛ { m | p m } := by
  obtain h | ⟨m, hm⟩ := { m | p (m + n) }.eq_empty_or_nonempty
  · rw [h, Nat.infₛ_empty, zero_add]
    obtain hnp | hnp := hn.eq_or_lt
    · exact hnp
    suffices hp : p (infₛ { m | p m } - n + n)
    · exact (h.subset hp).elim
    rw [tsub_add_cancel_of_le hn]
    exact cinfₛ_mem (nonempty_of_pos_infₛ <| n.zero_le.trans_lt hnp)
  · have hp : ∃ n, n ∈ { m | p m } := ⟨_, hm⟩
    rw [Nat.infₛ_def ⟨m, hm⟩, Nat.infₛ_def hp]
    rw [Nat.infₛ_def hp] at hn
    exact find_add hn
#align nat.Inf_add Nat.infₛ_add

theorem infₛ_add' {n : ℕ} {p : ℕ → Prop} (h : 0 < infₛ { m | p m }) :
    infₛ { m | p m } + n = infₛ { m | p (m - n) } := by
  suffices h₁ : n ≤ infₛ {m | p (m - n)}
  convert infₛ_add h₁
  · simp_rw [add_tsub_cancel_right]
  obtain ⟨m, hm⟩ := nonempty_of_pos_infₛ h
  refine'
    le_cinfₛ ⟨m + n, _⟩ fun b hb ↦
      le_of_not_lt fun hbn ↦
        ne_of_mem_of_not_mem _ (not_mem_of_lt_infₛ h) (tsub_eq_zero_of_le hbn.le)
  · dsimp
    rwa [add_tsub_cancel_right]
  · exact hb
#align nat.Inf_add' Nat.infₛ_add'

section

variable {α : Type _} [CompleteLattice α]

theorem supᵢ_lt_succ (u : ℕ → α) (n : ℕ) : (⨆ k < n + 1, u k) = (⨆ k < n, u k) ⊔ u n := by
  simp [Nat.lt_succ_iff_lt_or_eq, supᵢ_or, supᵢ_sup_eq]
#align nat.supr_lt_succ Nat.supᵢ_lt_succ

theorem supᵢ_lt_succ' (u : ℕ → α) (n : ℕ) : (⨆ k < n + 1, u k) = u 0 ⊔ ⨆ k < n, u (k + 1) := by
  rw [← sup_supᵢ_nat_succ]
  simp
#align nat.supr_lt_succ' Nat.supᵢ_lt_succ'

theorem infᵢ_lt_succ (u : ℕ → α) (n : ℕ) : (⨅ k < n + 1, u k) = (⨅ k < n, u k) ⊓ u n :=
  @supᵢ_lt_succ αᵒᵈ _ _ _
#align nat.infi_lt_succ Nat.infᵢ_lt_succ

theorem infᵢ_lt_succ' (u : ℕ → α) (n : ℕ) : (⨅ k < n + 1, u k) = u 0 ⊓ ⨅ k < n, u (k + 1) :=
  @supᵢ_lt_succ' αᵒᵈ _ _ _
#align nat.infi_lt_succ' Nat.infᵢ_lt_succ'

end

end Nat

namespace Set

variable {α : Type _}

theorem bunionᵢ_lt_succ (u : ℕ → Set α) (n : ℕ) : (⋃ k < n + 1, u k) = (⋃ k < n, u k) ∪ u n :=
  Nat.supᵢ_lt_succ u n
#align set.bUnion_lt_succ Set.bunionᵢ_lt_succ

theorem bunionᵢ_lt_succ' (u : ℕ → Set α) (n : ℕ) : (⋃ k < n + 1, u k) = u 0 ∪ ⋃ k < n, u (k + 1) :=
  Nat.supᵢ_lt_succ' u n
#align set.bUnion_lt_succ' Set.bunionᵢ_lt_succ'

theorem binterᵢ_lt_succ (u : ℕ → Set α) (n : ℕ) : (⋂ k < n + 1, u k) = (⋂ k < n, u k) ∩ u n :=
  Nat.infᵢ_lt_succ u n
#align set.bInter_lt_succ Set.binterᵢ_lt_succ

theorem binterᵢ_lt_succ' (u : ℕ → Set α) (n : ℕ) : (⋂ k < n + 1, u k) = u 0 ∩ ⋂ k < n, u (k + 1) :=
  Nat.infᵢ_lt_succ' u n
#align set.bInter_lt_succ' Set.binterᵢ_lt_succ'

end Set
