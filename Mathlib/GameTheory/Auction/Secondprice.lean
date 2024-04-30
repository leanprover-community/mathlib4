/-
Copyright (c) 2024 Wang Haocheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wang Haocheng.
-/

import Mathlib.Data.Real.EReal
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice

/-!
# Auction Theory

This file formalizes core concepts and results in auction theory.

## Main Definitions

- `Auction`: Defines an auction with bidders and their valuations.
- `maxb`: Function that computes the highest bid given a bidding function.
- `winner`: Identifies the winner of the auction as the bidder with the highest bid.
- `utility`: Computes the utility of each bidder based on the outcome of the auction.
- `dominant`: Establishes whether a strategy is dominant for a bidder.

## Main Results

- `exists_max`: There exists a participant whose bid matches the highest bid.
- `winner_take_max`: The winner's bid is the highest.
- `b_winner`: The winner's bid is at least the second highest bid.
- `valuation_is_dominant`: Bidding one's valuation is a dominant strategy.

## Notations

- `|b|`: Represents a bidding function.
- `maxb(b)`: The highest bid in the function `b`.
- `B i` is the maximal bid of all participants but `i`.

## Implementation Notes

The structure and functions assume the existence of multiple bidders to allow for meaningful
auction dynamics. Definitions like `winner` and `maxb` make use of Lean's `Finset` and `Classical`
logic to handle
potential non-constructive cases effectively.

## References

- Theoretical foundations can be linked back to classical auction theory texts and papers,
  adapting general proofs to the formalized environment of Lean.

## Tags

auction, game theory, economics, bidding, valuation

-/

open Classical

lemma two_different_elements {I : Type*} (h : ∃ (i j : I), i≠ j) : ∀ (i:I), ∃ j, i≠ j := by
   obtain ⟨ i0 , j0 , hij ⟩  := h
   intro i
   by_cases H : i=i0
   . use j0 ; simp [ H , hij ]
   . use i0


/-!###   Structure Definition  -/

structure Auction where
   I : Type*
   hF : Fintype I
   hI: Inhabited I
   hP : ∃ i j : I , i ≠ j
   hP' :  ∀ i : I , ∃ j, i ≠  j := two_different_elements hP
   v : I → ℝ -- The value of each clients

namespace Auction

variable {a : Auction} (b : a.I → ℝ )

instance : Fintype a.I := a.hF


/-!###  Helper Functions and Definitions -/

/-- Computes the highest bid given a bidding function `b`. -/
@[simp]
def maxb : ℝ  := Finset.sup' Finset.univ (⟨ a.hI.default ,  (Finset.mem_univ _)⟩ ) b

/-- There exists a participant `i` whose bid equals the highest bid. -/
lemma exists_max : ∃ i: a.I, b i = a.maxb b := by
   obtain ⟨  i , _ ,h2⟩ := Finset.exists_mem_eq_sup' (⟨ a.hI.default, (Finset.mem_univ _)⟩ ) b
   exact ⟨ i, symm h2⟩

/-- winner: The participant with the highest bid. -/
noncomputable def winner : a.I := Classical.choose (exists_max b)

/-- The bid of the winner equals the highest bid. -/
lemma winner_take_max : b (winner b) = maxb b:= Classical.choose_spec (exists_max b)

/-- Removing a participant `i` from all participants still leaves a non-empty set. -/
lemma delete_i_nonempty (i:a.I) :Finset.Nonempty (Finset.erase  Finset.univ i ) := by
  obtain ⟨ i , hi ⟩  := a.hP' i
  use i
  simp only [Finset.mem_univ, not_true, Finset.mem_erase, and_true]
  rw [ne_comm]
  exact hi

/-- `B i` is the maximal bid of all participants but `i`. -/
noncomputable def B (i: a.I) : ℝ  := Finset.sup' (Finset.erase Finset.univ i)
(delete_i_nonempty i) b

/--The second highest bid: the highest bid excluding the winner’s bid.-/
noncomputable def secondprice : ℝ  := B b (winner b)

/-- Defines the utility of participant `i`,
which is their valuation minus the second highest bid if `i` is the winner, otherwise, it's 0. -/
noncomputable def utility  (i : a.I) : ℝ := if i = winner b then a.v i - secondprice b else 0


/-! ### Proofs and Lemmas -/
variable {i: a.I}
/-- If `i` is the winner, then their utility is their valuation minus the second highest bid. -/
lemma utility_winner  (H: i = winner b) : utility b i = a.v i - secondprice b:= by
  rw [utility]; simp only [ite_true, H]

/-- If `i` is not the winner, then their utility is 0. -/
lemma utility_loser (i: a.I) (H : i≠ winner b) : utility b i = 0 := by
  rw [utility]; simp only [ite_false, H]

/-- A strategy is dominant if bidding `bi` ensures that
`i`'s utility is maximized relative to any other bids `b'` where `b i = bi`. -/
def dominant (i : a.I) (bi : ℝ) : Prop :=
  ∀ b b': a.I → ℝ , (b i = bi) → (∀ j: a.I, j≠ i→ b j = b' j)
   →  utility  b i ≥ utility b' i

/-- If `i`'s bid is higher than all other bids, then `i` is the winner. -/
lemma gt_wins (i : a.I) (H: ∀ j , i ≠j →  b i > b j) : i = winner b := by
   have HH : ∀ j, i = j ↔  b j = maxb b:= by
      have imax : b i = maxb b := by
         have H1 : b i ≤  maxb b := by
            apply Finset.le_sup'
            simp only [Finset.mem_univ]
         have H2 : maxb b ≤ b i := by
            apply Finset.sup'_le
            intro j _
            by_cases hji : i=j
            . rw [hji]
            .  have hji' := H j ( by rw [ne_eq] ; exact hji)
               linarith
         linarith
      intro j
      constructor
      .  intro hji
         rw [<-hji]
         exact imax
      .  intro hbj
         by_contra hji
         have hji' := H j (by rw [ne_eq];exact hji)
         rw [hbj] at hji'
         linarith
   rw [HH]
   rw [<-winner_take_max]

/-- The bid of the winner is always greater than or equal to the bids of all other participants.-/
lemma b_winner_max (H: i = winner b) : ∀ j: a.I, b i ≥ b j := by
  intro j
  have H_max: b (winner b) = maxb b := winner_take_max b
  rw [<-H] at H_max
  have H_sup: b j ≤ maxb b := by
    apply Finset.le_sup'; simp only [Finset.mem_univ]
  rw [<-H_max] at H_sup
  exact H_sup


/-- The bid of the winner is always greater than or equal to the second highest bid. -/
lemma b_winner (H: i = winner b) : b i ≥ secondprice b := by
  have Hmax := winner_take_max b
  rw [<-H] at Hmax
  rw [Hmax]
  apply Finset.sup'_le
  apply delete_i_nonempty
  intro j _
  apply Finset.le_sup'
  simp only [Finset.mem_erase, Finset.mem_univ]

/-- If `i` is not the winner, then the highest bid excluding `i` is equal to the highest bid. -/
lemma b_loser_max (H: i ≠ winner b) : B b i = maxb b := by
  have H1: B b i ≤ maxb b := by
    apply Finset.sup'_le
    intro i _
    apply Finset.le_sup'
    simp only [Finset.mem_univ]
  have H2: maxb b ≤ B b i := by
    rw [<-winner_take_max b]
    apply Finset.le_sup'
    simp only [Finset.mem_univ, Finset.mem_erase, and_true]
    exact (Ne.symm H)
  linarith



/-- Utility is non-negative if the bid equals the valuation. -/
lemma utility_nneg (i: a.I) : (b i = a.v i) → utility b i ≥ 0 := by
  intro H
  by_cases H2: i = winner b
  rw [utility]
  simp only [H2]
  rw [<-H2]
  rw [<-H]
  rw [H2]
  rw [winner_take_max b]
  apply sub_nonneg.mpr
  rw [secondprice]
  apply Finset.sup'_le
  simp only [Finset.mem_univ, Finset.mem_erase, and_true]
  intro j _
  rw [maxb]
  simp only [Finset.le_sup'_iff, Finset.mem_univ, true_and]
  use j
  rw[utility]
  rw [if_neg H2]




/-- Proves that the strategy of bidding one's valuation is a dominant strategy for `i`. -/
theorem valuation_is_dominant (i : a.I ) : dominant i (a.v i) := by
   intro b b' hb hb'
   by_cases H : i = winner b'
   .  by_cases H1 : a.v i >  B b' i
      .  have h_winner_b : i = winner b := gt_wins b i (λ j hj => by
         rw[hb]
         rw[hb']
         have HBi: B b' i ≥  b' j := by
            rw [B]
            simp only [Finset.mem_univ, not_true, ge_iff_le, Finset.le_sup'_iff,
                      Finset.mem_erase, ne_eq, and_true]
            use j
            simp only [le_refl, and_true]
            rw [<-ne_eq,ne_comm]
            exact hj
         exact gt_of_gt_of_ge H1 HBi
         exact id (Ne.symm hj))
         rw [utility_winner _ h_winner_b]
         rw [utility_winner _ H]
         have h_secondprice_eq : secondprice b = secondprice b' := by
            repeat rw [secondprice]
            rw[<-h_winner_b,<-H]
            repeat rw [B]
            apply Finset.sup'_congr (delete_i_nonempty i) (rfl)
            intro j hj
            rw [Finset.mem_erase] at hj
            exact hb' j hj.1
         . rw [h_secondprice_eq]
      .  rw [ge_iff_le,utility,<-H]
         simp only [ite_true, ge_iff_le, tsub_le_iff_right]
         simp only [gt_iff_lt, not_lt] at H1
         rw [secondprice,<-H]
         have := utility_nneg b i hb
         linarith
   .  have := utility_nneg b i hb
      convert this
      simp [utility,H]

#check valuation_is_dominant

/-- Computes the utility for a first price auction where the winner pays their bid. -/
noncomputable def Utility.FirstPrice (i : a.I) : ℝ := if i = winner b then a.v i - b i else 0

/-- If `i` is the winner in a first price auction, utility is their valuation minus their bid. -/
lemma utility_first_price_winner (i :a.I) (H :i = winner b) :
Utility.FirstPrice b i = a.v i - b i := by
   rw[H]
   simp only [Utility.FirstPrice]
   simp only [if_true]

/-- If `i` is not the winner in a first price auction, their utility is 0. -/
lemma utility_first_price_loser(i :a.I) (H : i ≠ winner b) : Utility.FirstPrice b i = 0 := by
   rw[Utility.FirstPrice]
   simp only [H]
   simp only [if_false]

/-- Defines a dominant strategy in the context of a first price auction. -/
def Dominant.FirstPrice (i : a.I) (bi : ℝ) : Prop :=
    ∀ b b': a.I → ℝ, (b i = bi) → (∀ j : a.I, j ≠ i → b j = b' j)
    → Utility.FirstPrice b i  ≥ Utility.FirstPrice b' i

/-- Shows that there is no dominant strategy in a first price auction for any `i` and bid `bi`. -/
theorem first_price_has_no_dominant_strategy (i : a.I) (bi :  ℝ) : ¬ (Dominant.FirstPrice i bi):=
 by
   simp only [Dominant.FirstPrice, not_forall]
   let b := fun j => if j = i then (bi:ℝ) else bi-2
   let b' := fun j => if j = i then (bi-1:ℝ) else bi-2
   use b, b'
   simp only [ne_eq, exists_prop, ite_true, exists_const, true_and,b,b']
   constructor
   intro j hj
   simp only [if_false, hj]
   have winner_b : i = winner b := by
      apply gt_wins b i
      intro j hj
      simp [Ne.symm hj,b]
   have winner_b' : i = winner b' := by
      apply gt_wins b' i
      intro j hj
      simp only [b,b',ite_true, Ne.symm hj, ite_false, gt_iff_lt, sub_lt_sub_iff_left]
      linarith
   have h1 := utility_first_price_winner b i winner_b
   have h2 := utility_first_price_winner b' i winner_b'
   simp [h1,h2,b,b']

end Auction
