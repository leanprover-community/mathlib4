/-
Copyright (c) 2024 Wang Haocheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ma Jiajun, Wang Haocheng
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Real.Basic

/-!
# Auction Theory

This file formalizes core concepts and results in auction theory. It includes the definitions of
first-price and second-price auctions, as well as several fundamental results and helping lemmas.

## Main Definitions

- `Auction`: Defines an auction with bidders and their valuations.
- `maxBid`: Function that computes the highest bid given a bidding function.
- `winner`: Identifies the winner of the auction as the bidder with the highest bid.
- `maxBidExcluding`: Function that computes the highest bid excluding a given participant.
- `dominant`: Defines a dominant strategy in the context of a auction.
- `Secondprice`: Computes the second highest bid in the auction.
- `Secondprice.utility`: Computes the utility of each bidder based on the outcome of the auction.
- `Firstprice.utility`: Computes the utility for a first price auction.

## Main Results

- `utility_nneg`: Utility is non-negative if the bid equals the valuation in second price auction.
- `valuation_is_dominant`: Bidding one's valuation is a dominant strategy in second price auction.
- `first_price_has_no_dominant_strategy`: There is no dominant strategy in first price auction.

## Helping Lemmas

- `eq_winner_of_bid_gt`: If `i`'s bid is higher than all other bids, then `i` wins.
- `exists_maxBid`: There exists a participant whose bid matches the highest bid
- `bid_winner_eq_maxBid`: The winner's bid is the highest.
- `winnerbid_ge_second`: The winner's bid is at least the second highest bid.
- `Secondprice.utility_winner`: If `i` wins, utility is the valuation minus the second highest bid.
- `Secondprice.utility_loser`: If `i` does not win, their utility is 0.
- `bid_le_bid_winner`: The winner's bid is greater than or equal to all other bids.
- `maxBidExcluding_eq_maxBid_if_loser`: If `i` does not win, the highest bid excluding `i` equals
   the highest bid.
- `Firstprice.utility_winner`: If `i` wins in a first price auction utility is valuation minus bid.
- `Firstprice.utility_loser`: If `i` does not win in a first price auction, utility is 0.

## Implementation Notes

The structure and functions assume the existence of multiple bidders to allow for meaningful
auction dynamics. Definitions like `winner` and `maxBid` make use of Lean's `Finset` and `Classical`
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
   /-- An `Nontrivial` instance. -/
   hI : Nontrivial I
   /-- A function mapping each participant to their valuation. -/
   v : I → ℝ

attribute [instance] Auction.hF Auction.hI

namespace Auction

variable {a : Auction} (b : a.I → ℝ)

/-!### Helper Functions and Definitions -/
/-- Computes the highest bid given a bidding function `b`. -/
@[simp]
def maxBid : ℝ := Finset.sup' Finset.univ Finset.univ_nonempty b

/-- There exists a participant `i` whose bid equals the highest bid. -/
lemma exists_maxBid : ∃ i : a.I, b i = a.maxBid b := by
   obtain ⟨i, _, h2⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty b
   exact ⟨i, symm h2⟩

/-- winner: The participant with the highest bid. -/
noncomputable def winner : a.I := Classical.choose (exists_maxBid b)

/-- The bid of the winner equals the highest bid. -/
lemma bid_winner_eq_maxBid : b (winner b) = maxBid b := Classical.choose_spec (exists_maxBid b)

/-- The bid of the winner is always greater than or equal to the bids of all others.-/
lemma bid_le_bid_winner (j : a.I) : b j ≤ b (winner b) := by
  rw [bid_winner_eq_maxBid b]
  exact Finset.le_sup' b (Finset.mem_univ j)

/-- If `i`'s bid is higher than all other bids, then `i` is the winner. -/
lemma eq_winner_of_bid_gt (i : a.I) (H : ∀ j , j ≠ i → b j < b i) : i = winner b := by
  contrapose! H
  exact ⟨winner b, H.symm, bid_le_bid_winner b i⟩

/-- A strategy is dominant if bidding `bi` ensures that
`i`'s utility is maximized relative to any other bids `b'` where `b i = bi`. -/
def dominant (utility : (a.I → ℝ) → a.I → ℝ) (i : a.I) (bi : ℝ) : Prop :=
  ∀ b, utility b i ≤ utility (Function.update b i bi) i

/-! ### Proofs and Lemmas -/

namespace Firstprice

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

/-- Shows that there is no dominant strategy in a first price auction for any `i` and bid `bi`. -/
theorem firstprice_auction_has_no_dominant_strategy (i : a.I) (bi : ℝ) :
    ¬ dominant utility i bi := by
  rw [dominant, not_forall]
  use Function.update (fun _ ↦ (bi - 2)) i (bi - 1)
  rw [utility, utility, if_pos (eq_winner_of_bid_gt _ i _), if_pos (eq_winner_of_bid_gt _ i _)]
  <;> intros <;> simp [*]

end Firstprice

/-- `maxBidExcluding i` is the maximal bid of all participants but `i`. -/
noncomputable def maxBidExcluding (i : a.I) : ℝ := Finset.sup' (Finset.erase Finset.univ i)
(Finset.Nontrivial.erase_nonempty (Finset.univ_nontrivial)) b

/--The second highest bid: the highest bid excluding the winner’s bid.-/
noncomputable def Secondprice : ℝ := maxBidExcluding b (winner b)

namespace Secondprice

/-- The bid of the winner is always greater than or equal to the second highest bid. -/
lemma winnerbid_ge_second : Secondprice b ≤ b (winner b) := by
  rw [bid_winner_eq_maxBid b]
  exact Finset.sup'_mono b (Finset.subset_univ _)
    (Finset.Nontrivial.erase_nonempty (Finset.univ_nontrivial))

/-- The bid of the winner is always greater than or equal to the second highest bid. -/
lemma maxBidExcluding_le_maxBid {i : a.I}(b : a.I → ℝ): maxBidExcluding b i ≤ maxBid b := by
  apply Finset.sup'_mono
  exact Finset.subset_univ (Finset.erase Finset.univ i)

/-- If `i` is not the winner, then the highest bid excluding `i` is equal to the highest bid. -/
lemma maxBidExcluding_eq_maxBid_if_loser {i : a.I} (H : i ≠ winner b) :
    maxBidExcluding b i = maxBid b := by
  apply le_antisymm
  · exact maxBidExcluding_le_maxBid b
  · rw [← bid_winner_eq_maxBid b]
    apply Finset.le_sup'
    exact Finset.mem_erase_of_ne_of_mem H.symm (Finset.mem_univ (winner b))

/-- Defines the utility of participant `i`,
which is their valuation minus the second highest bid if `i` is the winner, otherwise, it's 0. -/
noncomputable def utility (i : a.I) : ℝ := if i = winner b then a.v i - Secondprice b else 0

variable {i : a.I}
/-- If `i` is the winner, then their utility is their valuation minus the second highest bid. -/
lemma utility_winner (H: i = winner b) : utility b i = a.v i - Secondprice b:= by
  rw [utility]; simp only [ite_true, H]

/-- If `i` is not the winner, then their utility is 0. -/
lemma utility_loser (H : i≠ winner b) : utility b i = 0 := by
  rw [utility]; simp only [ite_false, H]

/-- utility is non-negative if the bid equals the valuation. -/
lemma utility_nneg (i : a.I) (H : b i = a.v i) : 0 ≤ utility b i := by
  rcases eq_or_ne i (winner b) with rfl | H2
  · rw [utility, if_pos rfl, ← H, bid_winner_eq_maxBid b, sub_nonneg, Secondprice]
    exact maxBidExcluding_le_maxBid b
  · rw [utility, if_neg H2]

/-- Proves that the strategy of bidding one's valuation is a dominant strategy for `i`. -/
theorem valuation_is_dominant (i : a.I) : dominant utility i (a.v i) := by
  intro b
  have key : maxBidExcluding (Function.update b i (a.v i)) i = maxBidExcluding b i :=
    (Finset.sup'_congr _ rfl fun j hj ↦ dif_neg (Finset.ne_of_mem_erase hj))
  by_cases h1 : i = winner b
  · rw [utility_winner b h1, Secondprice, ← h1, ← key]
    by_cases h2 : i = winner (Function.update b i (a.v i))
    · rw [utility_winner _ h2, sub_le_sub_iff_left, Secondprice, ← h2]
    · rw [utility_loser _ h2, sub_nonpos, maxBidExcluding_eq_maxBid_if_loser _ h2]
      conv_lhs => rw [← Function.update_same i (a.v i) b]
      exact Finset.le_sup' _ (Finset.mem_univ i)
  · rw [utility_loser b h1]
    apply utility_nneg
    apply Function.update_same

end Secondprice

end Auction
