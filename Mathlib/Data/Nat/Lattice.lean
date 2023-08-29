/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Gabriel Ebner, Yury Kudryashov
-/
import Mathlib.Data.Nat.Interval
import Mathlib.Order.ConditionallyCompleteLattice.Finset

#align_import data.nat.lattice from "leanprover-community/mathlib"@"52fa514ec337dd970d71d8de8d0fd68b455a1e54"

/-!
# Conditionally complete linear order structure on `ℕ`

In this file we

* define a `ConditionallyCompleteLinearOrderBot` structure on `ℕ`;
* prove a few lemmas about `iSup`/`iInf`/`Set.iUnion`/`Set.iInter` and natural numbers.
-/


open Set

namespace Nat

open Classical

noncomputable instance : InfSet ℕ :=
  ⟨fun s ↦ if h : ∃ n, n ∈ s then @Nat.find (fun n ↦ n ∈ s) _ h else 0⟩

noncomputable instance : SupSet ℕ :=
  ⟨fun s ↦ if h : ∃ n, ∀ a ∈ s, a ≤ n then @Nat.find (fun n ↦ ∀ a ∈ s, a ≤ n) _ h else 0⟩

theorem sInf_def {s : Set ℕ} (h : s.Nonempty) : sInf s = @Nat.find (fun n ↦ n ∈ s) _ h :=
  dif_pos _
#align nat.Inf_def Nat.sInf_def

theorem sSup_def {s : Set ℕ} (h : ∃ n, ∀ a ∈ s, a ≤ n) :
    sSup s = @Nat.find (fun n ↦ ∀ a ∈ s, a ≤ n) _ h :=
  dif_pos _
#align nat.Sup_def Nat.sSup_def

theorem _root_.Set.Infinite.Nat.sSup_eq_zero {s : Set ℕ} (h : s.Infinite) : sSup s = 0 :=
  dif_neg fun ⟨n, hn⟩ ↦
    let ⟨k, hks, hk⟩ := h.exists_gt n
    (hn k hks).not_lt hk
#align set.infinite.nat.Sup_eq_zero Set.Infinite.Nat.sSup_eq_zero

@[simp]
theorem sInf_eq_zero {s : Set ℕ} : sInf s = 0 ↔ 0 ∈ s ∨ s = ∅ := by
  cases eq_empty_or_nonempty s with
  | inl h => subst h
             simp only [or_true_iff, eq_self_iff_true, iff_true_iff, iInf, InfSet.sInf,
                        mem_empty_iff_false, exists_false, dif_neg, not_false_iff]
  | inr h => simp only [h.ne_empty, or_false_iff, Nat.sInf_def, h, Nat.find_eq_zero]
#align nat.Inf_eq_zero Nat.sInf_eq_zero

@[simp]
theorem sInf_empty : sInf ∅ = 0 := by
  rw [sInf_eq_zero]
  -- ⊢ 0 ∈ ∅ ∨ ∅ = ∅
  right
  -- ⊢ ∅ = ∅
  rfl
  -- 🎉 no goals
#align nat.Inf_empty Nat.sInf_empty

@[simp]
theorem iInf_of_empty {ι : Sort*} [IsEmpty ι] (f : ι → ℕ) : iInf f = 0 := by
  rw [iInf_of_empty', sInf_empty]
  -- 🎉 no goals
#align nat.infi_of_empty Nat.iInf_of_empty

theorem sInf_mem {s : Set ℕ} (h : s.Nonempty) : sInf s ∈ s := by
  rw [Nat.sInf_def h]
  -- ⊢ Nat.find h ∈ s
  exact Nat.find_spec h
  -- 🎉 no goals
#align nat.Inf_mem Nat.sInf_mem

theorem not_mem_of_lt_sInf {s : Set ℕ} {m : ℕ} (hm : m < sInf s) : m ∉ s := by
  cases eq_empty_or_nonempty s with
  | inl h => subst h; apply not_mem_empty
  | inr h => rw [Nat.sInf_def h] at hm; exact Nat.find_min h hm
#align nat.not_mem_of_lt_Inf Nat.not_mem_of_lt_sInf

protected theorem sInf_le {s : Set ℕ} {m : ℕ} (hm : m ∈ s) : sInf s ≤ m := by
  rw [Nat.sInf_def ⟨m, hm⟩]
  -- ⊢ Nat.find (_ : ∃ x, x ∈ s) ≤ m
  exact Nat.find_min' ⟨m, hm⟩ hm
  -- 🎉 no goals
#align nat.Inf_le Nat.sInf_le

theorem nonempty_of_pos_sInf {s : Set ℕ} (h : 0 < sInf s) : s.Nonempty := by
  by_contra contra
  -- ⊢ False
  rw [Set.not_nonempty_iff_eq_empty] at contra
  -- ⊢ False
  have h' : sInf s ≠ 0 := ne_of_gt h
  -- ⊢ False
  apply h'
  -- ⊢ sInf s = 0
  rw [Nat.sInf_eq_zero]
  -- ⊢ 0 ∈ s ∨ s = ∅
  right
  -- ⊢ s = ∅
  assumption
  -- 🎉 no goals
#align nat.nonempty_of_pos_Inf Nat.nonempty_of_pos_sInf

theorem nonempty_of_sInf_eq_succ {s : Set ℕ} {k : ℕ} (h : sInf s = k + 1) : s.Nonempty :=
  nonempty_of_pos_sInf (h.symm ▸ succ_pos k : sInf s > 0)
#align nat.nonempty_of_Inf_eq_succ Nat.nonempty_of_sInf_eq_succ

theorem eq_Ici_of_nonempty_of_upward_closed {s : Set ℕ} (hs : s.Nonempty)
    (hs' : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s) : s = Ici (sInf s) :=
  ext fun n ↦ ⟨fun H ↦ Nat.sInf_le H, fun H ↦ hs' (sInf s) n H (sInf_mem hs)⟩
#align nat.eq_Ici_of_nonempty_of_upward_closed Nat.eq_Ici_of_nonempty_of_upward_closed

theorem sInf_upward_closed_eq_succ_iff {s : Set ℕ} (hs : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s)
    (k : ℕ) : sInf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s := by
  constructor
  -- ⊢ sInf s = k + 1 → k + 1 ∈ s ∧ ¬k ∈ s
  · intro H
    -- ⊢ k + 1 ∈ s ∧ ¬k ∈ s
    rw [eq_Ici_of_nonempty_of_upward_closed (nonempty_of_sInf_eq_succ _) hs, H, mem_Ici, mem_Ici]
    exact ⟨le_rfl, k.not_succ_le_self⟩;
    -- ⊢ ℕ
    exact k; assumption
    -- ⊢ sInf s = k + 1
             -- 🎉 no goals
  · rintro ⟨H, H'⟩
    -- ⊢ sInf s = k + 1
    rw [sInf_def (⟨_, H⟩ : s.Nonempty), find_eq_iff]
    -- ⊢ k + 1 ∈ s ∧ ∀ (n : ℕ), n < k + 1 → ¬n ∈ s
    exact ⟨H, fun n hnk hns ↦ H' <| hs n k (lt_succ_iff.mp hnk) hns⟩
    -- 🎉 no goals
#align nat.Inf_upward_closed_eq_succ_iff Nat.sInf_upward_closed_eq_succ_iff

/-- This instance is necessary, otherwise the lattice operations would be derived via
`ConditionallyCompleteLinearOrderBot` and marked as noncomputable. -/
instance : Lattice ℕ :=
  LinearOrder.toLattice

noncomputable instance : ConditionallyCompleteLinearOrderBot ℕ :=
  { (inferInstance : OrderBot ℕ), (LinearOrder.toLattice : Lattice ℕ),
    (inferInstance : LinearOrder ℕ) with
    -- sup := sSup -- Porting note: removed, unnecessary?
    -- inf := sInf -- Porting note: removed, unnecessary?
    le_csSup := fun s a hb ha ↦ by rw [sSup_def hb]; revert a ha; exact @Nat.find_spec _ _ hb
                                   -- ⊢ a ≤ Nat.find hb
                                                     -- ⊢ ∀ (a : ℕ), a ∈ s → a ≤ Nat.find hb
                                                                  -- 🎉 no goals
    csSup_le := fun s a _ ha ↦ by rw [sSup_def ⟨a, ha⟩]; exact Nat.find_min' _ ha
                                  -- ⊢ Nat.find (_ : ∃ n, ∀ (a : ℕ), a ∈ s → a ≤ n) ≤ a
                                                         -- 🎉 no goals
    le_csInf := fun s a hs hb ↦ by
      rw [sInf_def hs]; exact hb (@Nat.find_spec (fun n ↦ n ∈ s) _ _)
      -- ⊢ a ≤ Nat.find hs
                                  -- ⊢ Nat.find (_ : ∃ x, x ∈ s) ≤ a
                                                         -- 🎉 no goals
                        -- 🎉 no goals
    csInf_le := fun s a _ ha ↦ by rw [sInf_def ⟨a, ha⟩]; exact Nat.find_min' _ ha
    csSup_empty := by
      simp only [sSup_def, Set.mem_empty_iff_false, forall_const, forall_prop_of_false,
        not_false_iff, exists_const]
      apply bot_unique (Nat.find_min' _ _)
      -- ⊢ True
      trivial
      -- 🎉 no goals
      -- ⊢ sSup s = sSup univ
    csSup_of_not_bddAbove := by
      -- ⊢ (if h : ∃ n, ∀ (a : ℕ), a ∈ s → a ≤ n then Nat.find h else 0) = if h : ∃ n,  …
      intro s hs
      -- ⊢ ¬∃ n, ∀ (a : ℕ), a ≤ n
      simp only [mem_univ, forall_true_left, sSup]
        -- ⊢ ∀ (x : ℕ), ∃ x_1, x < x_1
      rw [dif_neg, dif_neg]
        -- 🎉 no goals
      · simp only [not_exists, not_forall, not_le]
        -- 🎉 no goals
        exact fun n ↦ ⟨n+1, lt.base n⟩
                                           -- 🎉 no goals
      · exact hs
    csInf_of_not_bddBelow := fun s hs ↦ by simp at hs }

theorem sSup_mem {s : Set ℕ} (h₁ : s.Nonempty) (h₂ : BddAbove s) : sSup s ∈ s :=
  let ⟨k, hk⟩ := h₂
  h₁.cSup_mem ((finite_le_nat k).subset hk)
#align nat.Sup_mem Nat.sSup_mem

theorem sInf_add {n : ℕ} {p : ℕ → Prop} (hn : n ≤ sInf { m | p m }) :
    sInf { m | p (m + n) } + n = sInf { m | p m } := by
  obtain h | ⟨m, hm⟩ := { m | p (m + n) }.eq_empty_or_nonempty
  -- ⊢ sInf {m | p (m + n)} + n = sInf {m | p m}
  · rw [h, Nat.sInf_empty, zero_add]
    -- ⊢ n = sInf {m | p m}
    obtain hnp | hnp := hn.eq_or_lt
    -- ⊢ n = sInf {m | p m}
    · exact hnp
      -- 🎉 no goals
    suffices hp : p (sInf { m | p m } - n + n)
    -- ⊢ n = sInf {m | p m}
    · exact (h.subset hp).elim
      -- 🎉 no goals
    rw [tsub_add_cancel_of_le hn]
    -- ⊢ p (sInf {m | p m})
    exact csInf_mem (nonempty_of_pos_sInf <| n.zero_le.trans_lt hnp)
    -- 🎉 no goals
  · have hp : ∃ n, n ∈ { m | p m } := ⟨_, hm⟩
    -- ⊢ sInf {m | p (m + n)} + n = sInf {m | p m}
    rw [Nat.sInf_def ⟨m, hm⟩, Nat.sInf_def hp]
    -- ⊢ Nat.find (_ : ∃ x, x ∈ {m | p (m + n)}) + n = Nat.find hp
    rw [Nat.sInf_def hp] at hn
    -- ⊢ Nat.find (_ : ∃ x, x ∈ {m | p (m + n)}) + n = Nat.find hp
    exact find_add hn
    -- 🎉 no goals
#align nat.Inf_add Nat.sInf_add

theorem sInf_add' {n : ℕ} {p : ℕ → Prop} (h : 0 < sInf { m | p m }) :
    sInf { m | p m } + n = sInf { m | p (m - n) } := by
  suffices h₁ : n ≤ sInf {m | p (m - n)}
  -- ⊢ sInf {m | p m} + n = sInf {m | p (m - n)}
  convert sInf_add h₁
  -- ⊢ x✝ = x✝ + n - n
  · simp_rw [add_tsub_cancel_right]
    -- 🎉 no goals
  obtain ⟨m, hm⟩ := nonempty_of_pos_sInf h
  -- ⊢ n ≤ sInf {m | p (m - n)}
  refine'
    le_csInf ⟨m + n, _⟩ fun b hb ↦
      le_of_not_lt fun hbn ↦
        ne_of_mem_of_not_mem _ (not_mem_of_lt_sInf h) (tsub_eq_zero_of_le hbn.le)
  · dsimp
    -- ⊢ p (m + n - n)
    rwa [add_tsub_cancel_right]
    -- 🎉 no goals
  · exact hb
    -- 🎉 no goals
#align nat.Inf_add' Nat.sInf_add'

section

variable {α : Type*} [CompleteLattice α]

theorem iSup_lt_succ (u : ℕ → α) (n : ℕ) : ⨆ k < n + 1, u k = (⨆ k < n, u k) ⊔ u n := by
  simp [Nat.lt_succ_iff_lt_or_eq, iSup_or, iSup_sup_eq]
  -- 🎉 no goals
#align nat.supr_lt_succ Nat.iSup_lt_succ

theorem iSup_lt_succ' (u : ℕ → α) (n : ℕ) : ⨆ k < n + 1, u k = u 0 ⊔ ⨆ k < n, u (k + 1) := by
  rw [← sup_iSup_nat_succ]
  -- ⊢ (⨆ (_ : 0 < n + 1), u 0) ⊔ ⨆ (i : ℕ) (_ : i + 1 < n + 1), u (i + 1) = u 0 ⊔  …
  simp
  -- 🎉 no goals
#align nat.supr_lt_succ' Nat.iSup_lt_succ'

theorem iInf_lt_succ (u : ℕ → α) (n : ℕ) : ⨅ k < n + 1, u k = (⨅ k < n, u k) ⊓ u n :=
  @iSup_lt_succ αᵒᵈ _ _ _
#align nat.infi_lt_succ Nat.iInf_lt_succ

theorem iInf_lt_succ' (u : ℕ → α) (n : ℕ) : ⨅ k < n + 1, u k = u 0 ⊓ ⨅ k < n, u (k + 1) :=
  @iSup_lt_succ' αᵒᵈ _ _ _
#align nat.infi_lt_succ' Nat.iInf_lt_succ'

end

end Nat

namespace Set

variable {α : Type*}

theorem biUnion_lt_succ (u : ℕ → Set α) (n : ℕ) : ⋃ k < n + 1, u k = (⋃ k < n, u k) ∪ u n :=
  Nat.iSup_lt_succ u n
#align set.bUnion_lt_succ Set.biUnion_lt_succ

theorem biUnion_lt_succ' (u : ℕ → Set α) (n : ℕ) : ⋃ k < n + 1, u k = u 0 ∪ ⋃ k < n, u (k + 1) :=
  Nat.iSup_lt_succ' u n
#align set.bUnion_lt_succ' Set.biUnion_lt_succ'

theorem biInter_lt_succ (u : ℕ → Set α) (n : ℕ) : ⋂ k < n + 1, u k = (⋂ k < n, u k) ∩ u n :=
  Nat.iInf_lt_succ u n
#align set.bInter_lt_succ Set.biInter_lt_succ

theorem biInter_lt_succ' (u : ℕ → Set α) (n : ℕ) : ⋂ k < n + 1, u k = u 0 ∩ ⋂ k < n, u (k + 1) :=
  Nat.iInf_lt_succ' u n
#align set.bInter_lt_succ' Set.biInter_lt_succ'

end Set
