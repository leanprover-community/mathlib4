/-
Copyright (c) 2024 Wang Haocheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ma Jiajun, Wang Haocheng
-/
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Real.Basic

/-!
# Auction Theory

This file formalizes core concepts and results in auction theory. It includes the definitions of
first-price and second-price auctions, as well as several fundamental results and helping lemmas.

## Main Definitions

- `Auction`: Defines an auction with bidders and their valuations.
- `maxb`: Function that computes the highest bid given a bidding function.
- `winner`: Identifies the winner of the auction as the bidder with the highest bid.
- `B`: Function that computes the highest bid excluding a given participant.
- `secondprice`: Computes the second highest bid in the auction.
- `utility`: Computes the utility of each bidder based on the outcome of the auction.
- `dominant`: Establishes whether a strategy is dominant for a bidder.
- `utility.FirstPrice`: Computes the utility for a first price auction.
- `dominant`: Defines a dominant strategy in the context of a first price auction.

## Main Results

- `utility_nneg`: utility is non-negative if the bid equals the valuation.
- `valuation_is_dominant`: Bidding one's valuation is a dominant strategy.
- `first_price_has_no_dominant_strategy`: There is no dominant strategy in a first price auction.

## Helping Lemmas

- `gt_wins`: If `i`'s bid is higher than all other bids, then `i` wins.
- `exists_max`: There exists a participant whose bid matches the highest bid
- `winner_take_max`: The winner's bid is the highest.
- `b_winner`: The winner's bid is at least the second highest bid.
- `utility_winner`: If `i` wins, utility is the valuation minus the second highest bid.
- `utility_loser`: If `i` does not win, their utility is 0.
- `b_winner_max`: The winner's bid is greater than or equal to all other bids.
- `b_loser_max`: If `i` does not win, the highest bid excluding `i` matches the highest bid.
- `utility_first_price_winner`: If `i` wins in a first price auction utility is valuation minus bid.
- `utility_first_price_loser`: If `i` does not win in a first price auction, utility is 0.

## Notations

- `|b|`: Represents a bidding function.
- `maxb(b)`: The highest bid in the function `b`.
- `B i`: The maximal bid of all participants but `i`.

## Implementation Notes

The structure and functions assume the existence of multiple bidders to allow for meaningful
auction dynamics. Definitions like `winner` and `maxb` make use of Lean's `Finset` and `Classical`
logic to handle potential non-constructive cases effectively.
## References

* [T. Roughgarden, *Twenty lectures on Algorithmic Game Theory*][roughgarden2016]

## Tags

auction, game theory, economics, bidding, valuation
-/

open Classical

/-!### Structure Definition -/

/-- The Auction structure is set with components including: -/
structure Auction where
   /-- A set of participants.-/
   I : Type*
   /-- A `Fintype` instance. -/
   hF : Fintype I
   /-- An `Inhabited` instance. -/
   hI : Nontrivial I
   /-- A function mapping each participant to their valuation. -/
   v : I → ℝ

attribute [instance] Auction.hF Auction.hI

namespace Auction

variable {a : Auction} (b : a.I → ℝ)

/-!### Helper Functions and Definitions -/
/-- Computes the highest bid given a bidding function `b`. -/
@[simp]
def maxb : ℝ := Finset.sup' Finset.univ Finset.univ_nonempty b

/-- A strategy is dominant if bidding `bi` ensures that
`i`'s utility is maximized relative to any other bids `b'` where `b i = bi`. -/
def dominant (utility : (a.I → ℝ) → a.I → ℝ) (i : a.I) (bi : ℝ) : Prop := ∀ b b' : a.I → ℝ,
  (b i = bi) → (∀ j : a.I, j ≠ i → b j = b' j)
   → utility b' i ≤ utility b i

/-- `hole` represents a bidding function by setting the bid of participant `i` to `bi`, while other
bids unchanged. -/
noncomputable abbrev hole (i : a.I) (bi : ℝ) (b : a.I → ℝ) : a.I → ℝ :=
  fun j => if j=i then bi else b j

/-- There exists a participant `i` whose bid equals the highest bid. -/
lemma exists_max : ∃ i : a.I, b i = a.maxb b := by
   obtain ⟨i, _, h2⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty b
   exact ⟨i, symm h2⟩

/-- winner: The participant with the highest bid. -/
noncomputable def winner : a.I := Classical.choose (exists_max b)

/-- The bid of the winner equals the highest bid. -/
lemma winner_take_max : b (winner b) = maxb b := Classical.choose_spec (exists_max b)

/-!  ## Finset Nontriviality Lemmas -/

/--  Relates the nontriviality of type `α` with its universal finite set, implying the universal set
has at least two distinct elements if `α` does. -/
lemma Finset.univ_nontrivial_iff {α : Type*} [Fintype α] :
    (Finset.univ : Finset α).Nontrivial ↔ Nontrivial α := by
  rw [Finset.Nontrivial, Finset.coe_univ, Set.nontrivial_univ_iff]

/-- Asserts that the universal set of a nontrivial type `α` is nontrivial. -/
lemma Finset.univ_nontrivial {α : Type*} [Fintype α] [h : Nontrivial α] :
    (Finset.univ : Finset α).Nontrivial :=
  Finset.univ_nontrivial_iff.mpr h

/-- Proves that the universal set contains distinct elements for any nontrivial type `α`. -/
lemma Finset.Nontrivial.univ {α} [Fintype α] [Nontrivial α] :
    Finset.Nontrivial (Finset.univ : Finset α) := by
  let ⟨a, b, h⟩ := exists_pair_ne α
  exact ⟨a, Finset.mem_univ _, b, Finset.mem_univ _, h⟩

/-- `B i` is the maximal bid of all participants but `i`. -/
noncomputable def B (i : a.I) : ℝ := Finset.sup' (Finset.erase Finset.univ i)
(Finset.Nontrivial.erase_nonempty (Finset.univ_nontrivial)) b

/--The second highest bid: the highest bid excluding the winner’s bid.-/
noncomputable def secondPrice : ℝ := B b (winner b)

/-- The bid of the winner is always greater than or equal to the bids of all other participants.-/
lemma b_winner_max (j : a.I) : b j ≤ b (winner b) := by
  rw [winner_take_max b]
  exact Finset.le_sup' b (Finset.mem_univ j)

/-- If `i`'s bid is higher than all other bids, then `i` is the winner. -/
lemma gt_wins (i : a.I) (H : ∀ j , i ≠ j → b j < b i) : i = winner b := by
  contrapose! H
  exact ⟨winner b, H, b_winner_max b i⟩

/-- The bid of the winner is always greater than or equal to the second highest bid. -/
lemma b_winner : secondPrice b ≤ b (winner b) := by
  rw [winner_take_max b]
  exact Finset.sup'_mono b (Finset.subset_univ _)
    (Finset.Nontrivial.erase_nonempty (Finset.univ_nontrivial))

/-- If `i` is not the winner, then the highest bid excluding `i` is equal to the highest bid. -/
lemma b_loser_max {i : a.I} (H : i ≠ winner b) : B b i = maxb b := by
  have H1: B b i ≤ maxb b := by
    apply Finset.sup'_le
    intro i _
    apply Finset.le_sup'
    simp only [Finset.mem_univ]
  have H2: maxb b ≤ B b i := by
    rw [← winner_take_max b]
    apply Finset.le_sup'
    simp only [Finset.mem_univ, Finset.mem_erase, and_true]
    exact (H.symm)
  exact Real.partialOrder.proof_4 (B b i) (Finset.sup' Finset.univ maxb.proof_1 b) H1 H2

namespace secondPrice

/-- Defines the utility of participant `i`,
which is their valuation minus the second highest bid if `i` is the winner, otherwise, it's 0. -/
noncomputable def utility (i : a.I) : ℝ := if i = winner b then a.v i - secondPrice b else 0

/-! ### Proofs and Lemmas -/
variable {i : a.I}
/-- If `i` is the winner, then their utility is their valuation minus the second highest bid. -/
lemma utility_winner (H: i = winner b) : utility b i = a.v i - secondPrice b:= by
  rw [utility]; simp only [ite_true, H]

/-- If `i` is not the winner, then their utility is 0. -/
lemma utility_loser (i : a.I) (H : i≠ winner b) : utility b i = 0 := by
  rw [utility]; simp only [ite_false, H]

/-- utility is non-negative if the bid equals the valuation. -/
lemma utility_nneg (i : a.I) (H : b i = a.v i) : 0 ≤ utility b i := by
  by_cases H2: i = winner b
  · rw [utility]
    simp only [H2]
    rw [← H2, ← H, H2]
    rw [winner_take_max b]
    apply sub_nonneg.mpr
    rw [secondPrice]
    apply Finset.sup'_le
    simp only [Finset.mem_univ, Finset.mem_erase, and_true]
    intro j _
    rw [maxb]
    simp only [Finset.le_sup'_iff, Finset.mem_univ, true_and]
    use j
  · rw[utility, if_neg H2]

/-- Proves that the strategy of bidding one's valuation is a dominant strategy for `i`. -/
theorem valuation_is_dominant (i : a.I) : dominant utility i (a.v i) := by
  intro b b' hb hb'
  by_cases H : i = winner b'
  · by_cases H1 : B b' i < a.v i
    · have h_winner_b : i = winner b := gt_wins b i (λ j hj => by
      rw [hb, hb']
      have HBi: b' j ≤ B b' i := by
        rw [B]
        simp only [Finset.mem_univ, not_true, ge_iff_le, Finset.le_sup'_iff,
                  Finset.mem_erase, ne_eq, and_true]
        use j
        simp only [le_refl, and_true]
        rw [← ne_eq,ne_comm]
        exact hj
      exact gt_of_gt_of_ge H1 HBi
      exact id (hj.symm))
      rw [utility_winner _ h_winner_b, utility_winner _ H]
      have h_secondprice_eq : secondPrice b = secondPrice b' := by
        repeat rw [secondPrice]
        rw[← h_winner_b, ← H]
        repeat rw [B]
        apply Finset.sup'_congr (Finset.Nontrivial.erase_nonempty (Finset.univ_nontrivial)) (rfl)
        intro j hj
        rw [Finset.mem_erase] at hj
        exact hb' j hj.1
      · rw [h_secondprice_eq]
    · rw [utility,← H]
      simp only [ite_true, ge_iff_le, tsub_le_iff_right]
      simp only [gt_iff_lt, not_lt] at H1
      rw [secondPrice, ← H]
      have := utility_nneg b i hb
      exact le_add_of_nonneg_of_le this H1
  · have := utility_nneg b i hb
    convert this
    simp [utility, H]

end secondPrice

namespace firstPrice

/-- Computes the utility for a first price auction where the winner pays their bid. -/
noncomputable def utility (i : a.I) : ℝ := if i = winner b then a.v i - b i else 0

/-- If `i` is the winner in a first price auction, utility is their valuation minus their bid. -/
lemma utility_winner (i : a.I) (H : i = winner b) : utility b i = a.v i - b i := by
  rw [H]
  simp only [utility, if_true]

/-- If `i` is not the winner in a first price auction, their utility is 0. -/
lemma utility_loser (i : a.I) (H : i ≠ winner b) : utility b i = 0 := by
  rw [utility]
  simp only [H, if_false]

/-- Defines a dominant strategy in the context of a first price auction. -/
def dominant (i : a.I) (bi : ℝ) : Prop :=
  ∀ b b' : a.I → ℝ, (b i = bi) → (∀ j: a.I, j ≠ i → b j = b' j)
  → utility b' i ≤ utility b i

/-- Shows that there is no dominant strategy in a first price auction for any `i` and bid `bi`. -/
theorem first_price_has_no_dominant_strategy (i : a.I) (bi : ℝ) : ¬ dominant i bi := by
  simp only [dominant, not_forall]
  let b := fun j => if j = i then bi else bi - 2
  let b' := fun j => if j = i then bi - 1 else bi - 2
  use b, b'
  simp only [exists_prop, ite_true, exists_const, true_and, b]
  constructor
  · intro j hj
    simp only [if_false, hj]
    exact (if_neg hj).symm
  · have winner_b : i = winner b := by
      apply gt_wins b i
      intro j hj
      simp [hj.symm, b]
    have winner_b' : i = winner b' := by
      apply gt_wins b' i
      intro j hj
      simp only [b, b', ite_true, hj.symm, ite_false, gt_iff_lt, sub_lt_sub_iff_left]
      exact one_lt_two
    have h1 := utility_winner b i winner_b
    have h2 := utility_winner b' i winner_b'
    simp [h1, h2, b, b']

end firstPrice

end Auction
