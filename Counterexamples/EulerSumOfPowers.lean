/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi, Michael Stoll
-/
import Mathlib.NumberTheory.FLT.Three

/-!
# Euler's sum of powers conjecture

Euler's sum of powers conjecture says that at least n nth powers of positive integers
are required to sum to an nth power of a positive integer.

This was an attempt to generalize Fermat's Last Theorem,
which is the special case of summing 2 nth powers.

We demonstrate the connection with FLT, prove that it's true for `n ≤ 3`,
and provide counterexamples for `n = 4` and `n = 5`.
The status of the conjecture for `n ≥ 6` is unknown.

https://en.wikipedia.org/wiki/Euler%27s_sum_of_powers_conjecture
http://euler.free.fr/

## TODO

* Formalize Elkies's construction of infinitely many coprime counterexamples for `n = 4`
  https://www.ams.org/journals/mcom/1988-51-184/S0025-5718-1988-0930224-9/S0025-5718-1988-0930224-9.pdf
-/


namespace Counterexample

/-- Euler's sum of powers conjecture over a given semiring with a specific exponent. -/
abbrev SumOfPowersConjectureWith (R : Type*) [Semiring R] (n : ℕ) : Prop :=
  ∀ (a : List R) (b : R), 2 ≤ a.length → 0 ∉ a → b ≠ 0 →
  (a.map (· ^ n)).sum = b ^ n → n ≤ a.length

/-- Euler's sum of powers conjecture over the naturals for a given exponent. -/
abbrev SumOfPowersConjectureFor (n : ℕ) : Prop := SumOfPowersConjectureWith ℕ n

/-- Euler's sum of powers conjecture over the naturals. -/
abbrev SumOfPowersConjecture : Prop := ∀ n, SumOfPowersConjectureFor n

/-- Euler's sum of powers conjecture over a given semiring with a specific exponent implies FLT. -/
theorem fermatLastTheoremWith_of_sumOfPowersConjectureWith (R : Type*) [Semiring R] :
    ∀ n ≥ 3, SumOfPowersConjectureWith R n → FermatLastTheoremWith R n := by
  intro n hn conj a b c ha hb hc hsum
  have : n ≤ 2 := conj [a, b] c (by simp) (by simp [ha.symm, hb.symm]) hc (by simpa)
  cutsat

/-- Euler's sum of powers conjecture over the naturals implies FLT. -/
theorem fermatLastTheorem_of_sumOfPowersConjecture : SumOfPowersConjecture → FermatLastTheorem :=
  fun conj n hn ↦ fermatLastTheoremWith_of_sumOfPowersConjectureWith ℕ n hn <| conj n

/-- For `n = 3`, Euler's sum of powers conjecture over a given semiring is equivalent to FLT. -/
theorem sumOfPowersConjectureWith_three_iff_fermatLastTheoremWith_three (R : Type*) [Semiring R] :
    SumOfPowersConjectureWith R 3 ↔ FermatLastTheoremWith R 3 := by
  refine ⟨fermatLastTheoremWith_of_sumOfPowersConjectureWith R 3 (by rfl), ?_⟩
  intro FLT a b ha ha₀ hb₀ hsum
  contrapose! hsum
  have ⟨x, y, hxy⟩ := a.length_eq_two.mp <| by cutsat
  simp [hxy, FLT x y b (by grind) (by grind) hb₀]

/-- Euler's sum of powers conjecture over the naturals is true for `n ≤ 3`. -/
theorem sumOfPowersConjectureFor_le_three : ∀ n ≤ 3, SumOfPowersConjectureFor n := by
  intro n hn
  by_cases h3 : n = 3
  · exact h3 ▸ (sumOfPowersConjectureWith_three_iff_fermatLastTheoremWith_three _).mpr
      fermatLastTheoremThree
  cutsat

/-- Given a ring homomorphism from `R` to `S` with no nontrivial zeros,
the conjecture over `S` implies the conjecture over `R`. -/
lemma sumOfPowersConjecture_of_ringHom {R S : Type*} [Semiring R] [Semiring S] {f : R →+* S}
    (hf : ∀ x, f x = 0 → x = 0) {n : ℕ} (conj : SumOfPowersConjectureWith S n) :
    SumOfPowersConjectureWith R n := by
  intro a b ha ha₀ hb hsum
  have h : (· ^ n) ∘ f = f ∘ (· ^ n) := by ext; simp
  convert conj (a.map f) (f b) ?_ ?_ ?_ (by simp [h, hsum, List.sum_map_hom]) <;> grind

/-- Given an injective ring homomorphism from `R` to `S`,
the conjecture over `S` implies the conjecture over `R`. -/
lemma sumOfPowersConjecture_of_injective {R S : Type*} [Semiring R] [Semiring S] {f : R →+* S}
    (hf : Function.Injective f) {n : ℕ} (h : SumOfPowersConjectureWith S n) :
    SumOfPowersConjectureWith R n :=
  sumOfPowersConjecture_of_ringHom (fun _ _ ↦ hf <| by rwa [map_zero]) h

/--
The first counterexample was found by Leon J. Lander and Thomas R. Parkin in 1966
through a computer search, disproving the conjecture.
https://www.ams.org/journals/bull/1966-72-06/S0002-9904-1966-11654-3/S0002-9904-1966-11654-3.pdf
This is also the smallest counterexample for `n = 5`.
-/
theorem sumOfPowersConjectureFor_five_false : ¬SumOfPowersConjectureFor 5 := by
  intro conj
  let a := [27, 84, 110, 133]
  let b := 144
  have : 5 ≤ 4 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  cutsat

/--
The first counterexample for `n = 4` was found by Noam D. Elkies in October 1988:
`a := [2_682_440, 15_365_639, 18_796_760]`, `b := 20_615_673`
https://www.ams.org/journals/mcom/1988-51-184/S0025-5718-1988-0930224-9/S0025-5718-1988-0930224-9.pdf
In this paper, Elkies constructs infinitely many solutions to `a^4 + b^4 + c^4 = d^4` for coprime
`a, b, c, d`, which provide infinitely many coprime counterexamples for the case `n = 4`.
Here we use the smallest counterexample for `n = 4`, which was found a month later by Roger E. Frye
https://ieeexplore.ieee.org/document/74138
-/
theorem sumOfPowersConjectureFor_four_false : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let a := [95_800, 217_519, 414_560]
  let b := 422_481
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  cutsat

/--
For all `(k, m, n)` we define the Diophantine equation `∑ x_i ^ k = ∑ y_i ^ k`
where `x` and `y` are disjoint with length `m` and `n` respectively.
This is a generalization of the diophantine equation of Euler's sum of powers conjecture.
-/
abbrev ExistsEqualSumsOfLikePowersFor (R : Type*) [Semiring R] (k m n : ℕ) : Prop :=
  ∃ (x y : List R), (x.length = m) ∧ (y.length = n) ∧ (0 ∉ x) ∧ (0 ∉ y) ∧ (List.Disjoint x y) ∧
  (x.map (· ^ k)).sum = (y.map (· ^ k)).sum

/-- Euler's sum of powers conjecture for `k` restricts solutions for `(k, m, 1)`. -/
theorem existsEqualSumsOfLikePowersFor_of_sumOfPowersConjectureWith (R : Type*) [Semiring R]
    (k m : ℕ) (hm : 2 ≤ m) :
    SumOfPowersConjectureWith R k → ExistsEqualSumsOfLikePowersFor R k m 1 → k ≤ m := by
  intro conj ⟨x, y, hx, hy, hx₀, hy₀, hdisj, hsum⟩
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.eq_cons_of_length_one hy] at hsum
  exact hx ▸ conj x (y.get ⟨0, _⟩) (by cutsat) hx₀ (by grind) hsum

/--
After the first counterexample was found, Leon J. Lander, Thomas R. Parkin, and John Selfridge
made a similar conjecture that is not amenable to the counterexamples found so far.
The status of this conjecture is unknown.
https://en.wikipedia.org/wiki/Lander,_Parkin,_and_Selfridge_conjecture
https://www.ams.org/journals/mcom/1967-21-099/S0025-5718-1967-0222008-0/S0025-5718-1967-0222008-0.pdf
-/
abbrev LanderParkinSelfridgeConjecture (R : Type*) [Semiring R] (k m n : ℕ) : Prop :=
  ExistsEqualSumsOfLikePowersFor R k m n → k ≤ m + n

/-- Euler's sum of powers conjecture for `k` implies the Lander, Parkin, and Selfridge conjecture
for `(k, m, 1)`. -/
theorem LanderParkinSelfridgeConjecture_of_sumOfPowersConjectureWith (R : Type*) [Semiring R]
    (k m : ℕ) (hm : 2 ≤ m) :
    SumOfPowersConjectureWith R k → LanderParkinSelfridgeConjecture R k m 1 := by
  intro conj hsum
  have := existsEqualSumsOfLikePowersFor_of_sumOfPowersConjectureWith R k m hm conj hsum
  cutsat

end Counterexample
