/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Kevin Buzzard, Bhavik Mehta, Oliver Nash
-/
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.SuccPred

/-!
# Characterisation of the closed interval

In this file we provide a characterisation of the closed interval for locally-finite conditionally
complete linear orders, together with convenience specialisations for use with types such as
`ℕ`, `ℤ`, `Fin n`.

## Main results:
 * `Set.Nonempty.eq_Icc_of_Ioo_subseteq_compl_empty`: a characterisation of closed intervals for
   locally-finite conditionally complete linear orders.
 * `Set.Nonempty.eq_Icc_of_Ioo_subseteq_compl_empty'`: characterisation of closed intervals for
   locally-finite conditionally complete linear orders (convenient for `Fin n`).
 * `Set.Finite.eq_Icc_of_Ioo_subseteq_compl_empty_nat`: characterisation of closed intervals
   for `ℕ`.
 * `Set.Finite.eq_Icc_of_Ioo_subseteq_compl_empty_int`: characterisation of closed intervals
   for `ℤ`.
-/

variable {α : Type*} {I : Set α}

lemma Set.Finite.ordConnected_of_Ioo_subseteq_compl_empty [LinearOrder α]
    (h₁ : I.Finite)
    (h₂ : ∀ᵉ (x ∈ I) (y ∈ I), Ioo x y ⊆ Iᶜ → Ioo x y = ∅) :
    I.OrdConnected := by
  refine ordConnected_of_Ioo fun x hx y hy hxy z hz ↦ ?_
  by_contra hz'
  obtain ⟨x', hx', hx''⟩ := (h₁.inter_of_left (Iic z)).exists_le_maximal ⟨hx, hz.1.le⟩
  have hxz : x' < z := lt_of_le_of_ne hx''.1.2 (ne_of_mem_of_not_mem hx''.1.1 hz')
  obtain ⟨y', hy', hy''⟩ := (h₁.inter_of_left (Ici z)).exists_minimal_le ⟨hy, hz.2.le⟩
  have hzy : z < y' := lt_of_le_of_ne' hy''.1.2 (ne_of_mem_of_not_mem hy''.1.1 hz')
  have h₃ : Ioc x' z ⊆ Iᶜ := fun t ht ht' ↦ hx''.not_gt (by simp_all) ht.1
  have h₄ : Ico z y' ⊆ Iᶜ := fun t ht ht' ↦ hy''.not_lt (by simp_all) ht.2
  have h₅ : Ioo x' y' ⊆ Iᶜ := by
    simp only [← Ioc_union_Ico_eq_Ioo hxz hzy, union_subset_iff, and_true, h₃, h₄]
  exact eq_empty_iff_forall_not_mem.1 (h₂ x' hx''.prop.1 y' hy''.prop.1 h₅) z ⟨hxz, hzy⟩

lemma Set.Nonempty.eq_Icc_of_Ioo_subseteq_compl_empty
    [ConditionallyCompleteLinearOrder α] [LocallyFiniteOrder α]
    (h₀ : I.Nonempty) (h₁ : BddBelow I) (h₂ : BddAbove I)
    (h₃ : ∀ᵉ (x ∈ I) (y ∈ I), Ioo x y ⊆ Iᶜ → Ioo x y = ∅) :
    I = Icc (sInf I) (sSup I) :=
  have h₄ : I.Finite := h₁.finite_of_bddAbove h₂
  have _i : OrdConnected I := h₄.ordConnected_of_Ioo_subseteq_compl_empty h₃
  le_antisymm (subset_Icc_csInf_csSup h₁ h₂) (I.Icc_subset (h₀.csInf_mem h₄) (h₀.csSup_mem h₄))

/-- A version of `Set.Nonempty.eq_Icc_of_Ioo_subseteq_compl_empty` for complete linear orders such
as `Fin n` in which the explicit boundedness hypotheses are not necessary. -/
lemma Set.Nonempty.eq_Icc_of_Ioo_subseteq_compl_empty'
    [CompleteLinearOrder α] [LocallyFiniteOrder α]
    (h₀ : I.Nonempty)
    (h₃ : ∀ᵉ (x ∈ I) (y ∈ I), Ioo x y ⊆ Iᶜ → Ioo x y = ∅) :
    I = Icc (sInf I) (sSup I) :=
  h₀.eq_Icc_of_Ioo_subseteq_compl_empty (OrderBot.bddBelow I) (OrderTop.bddAbove I) h₃

lemma Set.Nonempty.eq_Icc_of_Ioo_subseteq_compl_empty_nat {I : Set ℕ}
    (h₀ : I.Nonempty) (h₂ : BddAbove I)
    (h₃ : ∀ᵉ (x ∈ I) (y ∈ I), Ioo x y ⊆ Iᶜ → y ≤ x + 1) :
    I = Icc (sInf I) (sSup I) :=
  h₀.eq_Icc_of_Ioo_subseteq_compl_empty (OrderBot.bddBelow I) h₂
    fun x hx y hy hxy ↦ Order.Ioo_eq_empty_iff_le_succ.mpr <| h₃ x hx y hy hxy

lemma Set.Nonempty.eq_Icc_of_Ioo_subseteq_compl_empty_int {I : Set ℤ}
    (h₀ : I.Nonempty) (h₁ : BddBelow I) (h₂ : BddAbove I)
    (h₃ : ∀ᵉ (x ∈ I) (y ∈ I), Ioo x y ⊆ Iᶜ → y ≤ x + 1) :
    I = Icc (sInf I) (sSup I) :=
  h₀.eq_Icc_of_Ioo_subseteq_compl_empty h₁ h₂
    fun x hx y hy hxy ↦ Order.Ioo_eq_empty_iff_le_succ.mpr <| h₃ x hx y hy hxy
