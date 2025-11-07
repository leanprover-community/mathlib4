/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bhavik Mehta, Oliver Nash
-/
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.SuccPred

/-!
# Order-connected subsets of linear orders

In this file we provide some results about order-connected subsets of linear orders, together with
some convenience lemmas for characterising closed intervals in certain concrete types such as `ℤ`,
`ℕ`, and `Fin n`.

## Main results:
* `Set.ordConnected_iff_disjoint_Ioo_empty`: a characterisation of `Set.OrdConnected` for
  locally-finite linear orders.
* `Set.Nonempty.ordConnected_iff_of_bdd`: a characterisation of closed intervals for locally-finite
  conditionally complete linear orders.
* `Set.Nonempty.ordConnected_iff_of_bdd'`: a characterisation of closed intervals for
  locally-finite complete linear orders (convenient for `Fin n`).
* `Set.Nonempty.eq_Icc_iff_nat`: characterisation of closed intervals for `ℕ`.
* `Set.Nonempty.eq_Icc_iff_int`: characterisation of closed intervals for `ℤ`.
-/

variable {α : Type*} {I : Set α}

lemma Set.Nonempty.ordConnected_iff_of_bdd
    [ConditionallyCompleteLinearOrder α] [LocallyFiniteOrder α]
    (h₀ : I.Nonempty) (h₁ : BddBelow I) (h₂ : BddAbove I) :
    I.OrdConnected ↔ I = Icc (sInf I) (sSup I) :=
  have h₄ : I.Finite := h₁.finite_of_bddAbove h₂
  ⟨fun _ ↦ le_antisymm (subset_Icc_csInf_csSup h₁ h₂)
    (I.Icc_subset (h₀.csInf_mem h₄) (h₀.csSup_mem h₄)), fun h₃ ↦ h₃ ▸ ordConnected_Icc⟩

/-- A version of `Set.Nonempty.ordConnected_iff_of_bdd` for complete linear orders, such as `Fin n`,
in which the explicit boundedness hypotheses are not necessary. -/
lemma Set.Nonempty.ordConnected_iff_of_bdd' [ConditionallyCompleteLinearOrder α]
    [OrderTop α] [OrderBot α] [LocallyFiniteOrder α]
    (h₀ : I.Nonempty) :
    I.OrdConnected ↔ I = Icc (sInf I) (sSup I) :=
  h₀.ordConnected_iff_of_bdd (OrderBot.bddBelow I) (OrderTop.bddAbove I)

/- TODO The `LocallyFiniteOrder` assumption here is probably too strong (e.g., it rules out `ℝ`
for which this result holds). However at the time of writing it is not clear what weaker
assumption(s) should replace it. -/
lemma Set.ordConnected_iff_disjoint_Ioo_empty [LinearOrder α] [LocallyFiniteOrder α] :
    I.OrdConnected ↔ ∀ᵉ (x ∈ I) (y ∈ I), Disjoint (Ioo x y) I → Ioo x y = ∅ := by
  simp_rw [← Set.subset_compl_iff_disjoint_right]
  refine ⟨fun h' x hx y hy hxy ↦ ?_, fun h' ↦ ordConnected_of_Ioo fun x hx y hy hxy z hz ↦ ?_⟩
  · suffices ∀ z, x < z → y ≤ z by ext z; simpa using this z
    intro z hz
    suffices z ∉ Ioo x y by simp_all
    exact fun contra ↦ hxy contra <| h'.out hx hy <| mem_Icc_of_Ioo contra
  · by_contra hz'
    obtain ⟨x', hx', hx''⟩ :=
      ((finite_Icc x z).inter_of_right I).exists_le_maximal ⟨hx, le_refl _, hz.1.le⟩
    have hxz : x' < z := lt_of_le_of_ne hx''.1.2.2 (ne_of_mem_of_not_mem hx''.1.1 hz')
    obtain ⟨y', hy', hy''⟩ :=
      ((finite_Icc z y).inter_of_right I).exists_le_minimal ⟨hy, hz.2.le, le_refl _⟩
    have hzy : z < y' := lt_of_le_of_ne' hy''.1.2.1 (ne_of_mem_of_not_mem hy''.1.1 hz')
    have h₃ : Ioc x' z ⊆ Iᶜ := fun t ht ht' ↦ hx''.not_gt (⟨ht', le_trans hx' ht.1.le, ht.2⟩) ht.1
    have h₄ : Ico z y' ⊆ Iᶜ := fun t ht ht' ↦ hy''.not_lt (⟨ht', ht.1, le_trans ht.2.le hy'⟩) ht.2
    have h₅ : Ioo x' y' ⊆ Iᶜ := by
      simp only [← Ioc_union_Ico_eq_Ioo hxz hzy, union_subset_iff, and_true, h₃, h₄]
    exact eq_empty_iff_forall_notMem.1 (h' x' hx''.prop.1 y' hy''.prop.1 h₅) z ⟨hxz, hzy⟩

lemma Set.Nonempty.eq_Icc_iff_nat {I : Set ℕ}
    (h₀ : I.Nonempty) (h₂ : BddAbove I) :
    I = Icc (sInf I) (sSup I) ↔ ∀ᵉ (x ∈ I) (y ∈ I), Disjoint (Ioo x y) I → y ≤ x + 1 := by
  simp [← h₀.ordConnected_iff_of_bdd (OrderBot.bddBelow I) h₂, ordConnected_iff_disjoint_Ioo_empty]

lemma Set.Nonempty.eq_Icc_iff_int {I : Set ℤ}
    (h₀ : I.Nonempty) (h₁ : BddBelow I) (h₂ : BddAbove I) :
    I = Icc (sInf I) (sSup I) ↔ ∀ᵉ (x ∈ I) (y ∈ I), Disjoint (Ioo x y) I → y ≤ x + 1 := by
  simp [← h₀.ordConnected_iff_of_bdd h₁ h₂, ordConnected_iff_disjoint_Ioo_empty, Int.succ]
