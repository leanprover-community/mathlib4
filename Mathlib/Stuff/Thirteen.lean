import Mathlib.Stuff.Inertia
import Mathlib.NumberTheory.Cyclotomic.Embeddings
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.Tactic
import Mathlib.Stuff.Factorization
import Mathlib.Stuff.Cyclotomic
import Mathlib.Stuff.OrderOf

set_option linter.style.header false

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

theorem Nat.prime_thirteen : Nat.Prime 13 := by
  norm_num

instance Nat.fact_prime_thirteen : Fact (Nat.Prime 13) :=
  ⟨prime_thirteen⟩

lemma crazy13 : ⌊(4 / π) ^ 6 * (12! / 12 ^ 12 * √1792160394037)⌋₊ = 306 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      _ ≥ (4 / 3.14159265358979323847) ^ 6 * (12! / 12 ^ 12 * √1792160394037) := by
        gcongr; exact pi_lt_d20.le
      _ ≥ (4 / 3.14159265358979323847) ^ 6 * (12! / 12 ^ 12 * 1338715) := by
        gcongr; exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      _ ≥ 306 := by norm_num
  · calc
      _ < (4 / 3.14159265358979323846) ^ 6 * (12! / 12 ^ 12 * √1792160394037) := by
        gcongr; exact pi_gt_d20
      _ ≤ (4 / 3.14159265358979323846) ^ 6 * (12! / 12 ^ 12 * 1338716) := by
        gcongr; exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ ≤ _ := by norm_num

variable [IsCyclotomicExtension {13} ℚ K]

theorem M13 : ⌊(M K)⌋₊ = 306 := by
  rw [absdiscr_prime 13 K, IsCyclotomicExtension.finrank (n := 13) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 13, totient_prime
      Nat.prime_thirteen]
  simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg, Int.reducePow,
    reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact crazy13

theorem cyclotomic_13 : cyclotomic 13 ℤ =
    X^12 + X^11 + X^10 + X^9 + X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1 := by
  simp [cyclotomic_prime, sum_range_succ]
  ring

set_option linter.style.maxHeartbeats false in
set_option linter.style.longLine false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem pid13 : IsPrincipalIdealRing (𝓞 K) := by
  apply IsCyclotomicExtension.Rat.pid6 13
  rw [M13, cyclotomic_13]
  intro p hple hp hpn
  fin_cases hple; any_goals norm_num at hp
  on_goal 6 => simp at hpn
  on_goal 2 =>
    right
    let P : ℤ[X] := X^3 + 2*X + 2; let d := 3
    let Q : ℤ[X] := X^9 + X^8 + 2*X^7 + X^5 + 2*X^3 + 2*X^2 + 2
    let A : ℤ[X] := -X^10 - X^9 - 2*X^8 - X^7 - X^6 - X^5 - X^4 - 3*X^3 - X^2 - X - 1
    use P, Q, A
    use X^8 + X^6 + X, -X^11 - 2*X^10 - X^9 - X^6 - X^4 - X^3 - X^2 - 2*X - 2, X^7 + X^6 - X^3 - X + 3
    use -X^11 - X^10 + X^8 - X^4 - X^3 - X^2 - 2*X - 1, X^7 - X^4 - X^2 + X + 2
    use X^5 - X^3 - 2*X^2 + 2*X + 6, -5*X - 4
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · simp
      refine ⟨?_, ?_, ?_⟩ <;> ring
  on_goal 14 =>
    right
    let P : ℤ[X] := X + 4; let d := 1
    let Q : ℤ[X] := X^11 + 50*X^10 + 13*X^9 + 2*X^8 + 46*X^7 + 29*X^6 + 44*X^5 + 37*X^4 + 12*X^3 + 6*X^2 + 30*X + 40
    let A : ℤ[X] := -X^11 - 4*X^10 - X^9 - X^8 - 4*X^7 - 3*X^6 - 4*X^5 - 3*X^4 - X^3 - X^2 - 3*X - 3
    use P, Q, A
    use X^11 - X^9 + X^5 + 1, 22*X^11 - 13*X^10 - 32*X^9 - 9*X^8 + 5*X^7 + 2*X^6 - 39*X^5 - 34*X^4 - X^3 + 26*X^2 - 29*X - 21, -22*X^10 + 35*X^9 + 41*X^8 - 58*X^7 - 33*X^6 + 26*X^5 + 33*X^4 + 27*X^3 - 55*X^2 - 45*X + 74
    use X^11 - 2*X^10 - 3*X^9 - X^8 - X^6 - 4*X^5 - 3*X^4 + X^2 - 3*X - 2, -X^10 + 3*X^9 + 2*X^8 - 5*X^7 - 2*X^6 + 3*X^5 + 3*X^4 + X^3 - 5*X^2 - 2*X + 6
    use X^10 - 4*X^9 + 15*X^8 - 60*X^7 + 240*X^6 - 960*X^5 + 3841*X^4 - 15364*X^3 + 61456*X^2 - 245824*X + 983296, -74211
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · simp
      refine ⟨?_, ?_, ?_⟩ <;> ring
  on_goal 19 =>
    right
    let P : ℤ[X] := X + 12; let d := 1
    let Q : ℤ[X] := X^11 + 68*X^10 + 54*X^9 + 64*X^8 + 23*X^7 + 41*X^6 + 62*X^5 + 47*X^4 + 69*X^3 + 42*X^2 + 50*X + 33
    let A : ℤ[X] := -X^11 - 11*X^10 - 9*X^9 - 10*X^8 - 4*X^7 - 7*X^6 - 10*X^5 - 8*X^4 - 11*X^3 - 7*X^2 - 8*X - 5
    use P, Q, A
    use X^10 + X^5 + X^2 + X, X^11 - 11*X^10 - 25*X^9 - 15*X^8 - 56*X^7 - 38*X^6 - 17*X^5 - 32*X^4 - 10*X^3 - 37*X^2 - 29*X - 46, -X^9 + 12*X^8 + 14*X^7 - 10*X^6 + 41*X^5 - 19*X^4 - 9*X^3 + 29*X^2 - 33*X + 79
    use -2*X^10 - 4*X^9 - 3*X^8 - 9*X^7 - 6*X^6 - 3*X^5 - 5*X^4 - 2*X^3 - 6*X^2 - 5*X - 7, 2*X^8 + 2*X^7 - X^6 + 6*X^5 - 3*X^4 - X^3 + 4*X^2 - 4*X + 12
    use X^9 - 12*X^8 + 144*X^7 - 1728*X^6 + 20736*X^5 - 248831*X^4 + 2985972*X^3 - 35831664*X^2 + 429979969*X - 5159759627, 783760956
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · simp
      refine ⟨?_, ?_, ?_⟩ <;> ring
  on_goal 28 =>
    right
    let P : ℤ[X] := X + 18; let d := 1
    let Q : ℤ[X] := X^11 + 114*X^10 + 45*X^9 + 108*X^8 + 22*X^7 + 129*X^6 + 37*X^5 + 121*X^4 + 50*X^3 + 18*X^2 + 70*X + 51
    let A : ℤ[X] := -X^11 - 16*X^10 - 7*X^9 - 15*X^8 - 4*X^7 - 18*X^6 - 6*X^5 - 17*X^4 - 7*X^3 - 3*X^2 - 10*X - 7
    use P, Q, A
    use X^11 + X^10 + X^7 + X^6 + X^3 + X^2 + X - 1, -61*X^11 - 11*X^10 + 6*X^9 - 38*X^8 - 32*X^7 - 9*X^6 - 30*X^5 - 45*X^4 - 37*X^3 - 50*X^2 - 78*X - 98, 61*X^10 + 11*X^9 - 67*X^8 + 27*X^7 + 99*X^6 - 18*X^5 - 69*X^4 + 63*X^3 + 106*X^2 - 13*X + 33
    use -8*X^11 - X^10 + X^9 - 5*X^8 - 4*X^7 - X^6 - 4*X^5 - 6*X^4 - 5*X^3 - 7*X^2 - 11*X - 13, 8*X^10 + X^9 - 9*X^8 + 4*X^7 + 13*X^6 - 3*X^5 - 9*X^4 + 9*X^3 + 14*X^2 - 2*X + 5
    use X^10 - 17*X^9 + 306*X^8 - 5508*X^7 + 99145*X^6 - 1784609*X^5 + 32122962*X^4 - 578213316*X^3 + 10407839689*X^2 - 187341114401*X + 3372140059219, -463347489053
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · simp
      refine ⟨?_, ?_, ?_⟩ <;> ring
  on_goal 32 =>
    right
    let P : ℤ[X] := X + 4; let d := 1
    let Q : ℤ[X] := X^11 + 154*X^10 + 13*X^9 + 106*X^8 + 48*X^7 + 123*X^6 + 137*X^5 + 81*X^4 + 148*X^3 + 37*X^2 + 10*X + 118
    let A : ℤ[X] := -X^11 - 4*X^10 - X^9 - 3*X^8 - 2*X^7 - 4*X^6 - 4*X^5 - 3*X^4 - 4*X^3 - X^2 - X - 3
    use P, Q, A
    use X^11 + X^7 + X^3 + X^2 + X, -90*X^11 - 44*X^10 - 71*X^9 - 120*X^8 - 81*X^7 - 80*X^6 - 84*X^5 - 68*X^4 - 132*X^3 - 33*X^2 - 115*X - 101, 90*X^10 - 46*X^9 + 27*X^8 + 49*X^7 + 51*X^6 - 47*X^5 + 31*X^4 + 33*X^3 + 115*X^2 - 56*X + 157
    use -2*X^11 - X^10 - 2*X^9 - 3*X^8 - 2*X^7 - 2*X^6 - 2*X^5 - 2*X^4 - 3*X^3 - X^2 - 3*X - 2, 2*X^10 - X^9 + X^8 + X^7 + X^6 - X^5 + X^4 + X^3 + 2*X^2 - X + 4
    use X^10 - 4*X^9 + 16*X^8 - 64*X^7 + 257*X^6 - 1028*X^5 + 4112*X^4 - 16448*X^3 + 65793*X^2 - 263171*X + 1052685, -26820
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · simp
      refine ⟨?_, ?_, ?_⟩ <;> ring
  all_goals {
    left; simp; norm_num; refine orderOf_lt_of (by norm_num) (fun i hi hipos ↦ ?_)
    have := Finset.mem_Icc.mpr ⟨hipos, hi⟩; fin_cases this <;> norm_num }
