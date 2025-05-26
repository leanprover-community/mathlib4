import Mathlib.Stuff.Inertia
import Mathlib.NumberTheory.Cyclotomic.Embeddings
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.Tactic
import Mathlib.Stuff.Factorization
import Mathlib.Stuff.Cyclotomic

set_option linter.style.header false

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

theorem PNat.prime_eleven : (11 : ℕ+).Prime :=
  Nat.prime_eleven

instance Nat.fact_prime_eleven : Fact (Nat.Prime 11) :=
  ⟨prime_eleven⟩

instance PNat.fact_prime_seven : Fact (11 : ℕ+).Prime :=
  ⟨prime_eleven⟩

lemma crazy11 : ⌊(4 / π) ^ 5 * (10! / 10 ^ 10 * √2357947691)⌋₊ = 58 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      _ ≥ (4 / 3.14159265358979323847) ^ 5 * (10! / 10 ^ 10 * √2357947691) := by
        gcongr; exact pi_lt_d20.le
      _ ≥ (4 / 3.14159265358979323847) ^ 5 * (10! / 10 ^ 10 * 48558) := by
        gcongr; exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      _ ≥ 58 := by norm_num
  · calc
      _ < (4 / 3.14159265358979323846) ^ 5 * (10! / 10 ^ 10 * √2357947691) := by
        gcongr; exact pi_gt_d20
      _ ≤ (4 / 3.14159265358979323846) ^ 5 * (10! / 10 ^ 10 * 48559) := by
        gcongr; exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ ≤ 58 + 1 := by norm_num

variable [IsCyclotomicExtension {11} ℚ K]

theorem M11 : ⌊(M K)⌋₊ = 58 := by
  rw [absdiscr_prime 11 K, IsCyclotomicExtension.finrank (n := 11) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 11, totient_prime
      PNat.prime_eleven]
  simp only [PNat.val_ofNat, Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg,
    Int.reducePow, reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact crazy11

theorem cyclotomic_11 : cyclotomic ((11 : ℕ+) : ℕ) ℤ =
    X^10 + X^9 + X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1 := by
  simp [cyclotomic_prime, sum_range_succ]
  ring

set_option maxHeartbeats 0 in
set_option linter.style.maxHeartbeats false in
set_option linter.style.longLine false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
theorem pid11 : IsPrincipalIdealRing (𝓞 K) := by
  apply IsCyclotomicExtension.Rat.pid4 11
  rw [M11, cyclotomic_11]
  intro p hple hp hpn
  fin_cases hple; any_goals norm_num at hp
  on_goal 5 => simp at hpn
  · let P : ℤ[X] := X^10 + X^9 + X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1; let d := 10
    let Q : ℤ[X] := 1
    let A : ℤ[X] := 0
    use P, Q, A
    use 0, 0, 0
    use 0, 0
    use 0, 0
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · left
      norm_num
  · let P : ℤ[X] := X^5 + 2*X^3 + X^2 + 2*X + 2; let d := 5
    let Q : ℤ[X] := X^5 + X^4 + 2*X^3 + X^2 + 2
    let A : ℤ[X] := -X^8 - X^7 - 2*X^6 - 3*X^5 - 2*X^4 - 3*X^3 - X^2 - X - 1
    use P, Q, A
    use 0, 0, 0
    use 0, 0
    use 0, 0
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · left
      norm_num
  · let P : ℤ[X] := X^5 + 2*X^4 + 4*X^3 + X^2 + X + 4; let d := 5
    let Q : ℤ[X] := X^5 + 4*X^4 + 4*X^3 + X^2 + 3*X + 4
    let A : ℤ[X] := -X^9 - 3*X^8 - 5*X^7 - 5*X^6 - 5*X^5 - 8*X^4 - 7*X^3 - 2*X^2 - 3*X - 3
    use P, Q, A
    use 0, 0, 0
    use 0, 0
    use 0, 0
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · left
      norm_num
  · let P : ℤ[X] := X^10 + X^9 + X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1; let d := 10
    let Q : ℤ[X] := 1
    let A : ℤ[X] := 0
    use P, Q, A
    use 0, 0, 0
    use 0, 0
    use 0, 0
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · left
      norm_num
  · let P : ℤ[X] := X^10 + X^9 + X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1; let d := 10
    let Q : ℤ[X] := 1
    let A : ℤ[X] := 0
    use P, Q, A
    use 0, 0, 0
    use 0, 0
    use 0, 0
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · left
      norm_num
  · let P : ℤ[X] := X^10 + X^9 + X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1; let d := 10
    let Q : ℤ[X] := 1
    let A : ℤ[X] := 0
    use P, Q, A
    use 0, 0, 0
    use 0, 0
    use 0, 0
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · left
      norm_num
  · let P : ℤ[X] := X^10 + X^9 + X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1; let d := 10
    let Q : ℤ[X] := 1
    let A : ℤ[X] := 0
    use P, Q, A
    use 0, 0, 0
    use 0, 0
    use 0, 0
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · left
      norm_num
  · let P : ℤ[X] := X + 5; let d := 1
    let Q : ℤ[X] := X^9 + 19*X^8 + 21*X^7 + 11*X^6 + 15*X^5 + 18*X^4 + 3*X^3 + 9*X^2 + 2*X + 14
    let A : ℤ[X] := -X^9 - 5*X^8 - 5*X^7 - 3*X^6 - 4*X^5 - 4*X^4 - X^3 - 2*X^2 - X - 3
    use P, Q, A
    use -X^8 - X^7 - X^6 - X^5 - X^4 - X^3 - X - 1, 17*X^9 + X^8 + 12*X^7 + 3*X^6 + 2*X^5 + 7*X^4 + 5*X^3 + 15*X^2 + 11*X + 8, 17*X^7 + X^6 + 12*X^5 + 3*X^4 + 2*X^3 + 7*X^2 - 12*X + 31
    use 3*X^9 + 2*X^7 + X^4 + X^3 + 3*X^2 + 2*X + 1, 3*X^7 + 2*X^5 + X^2 - 2*X + 6
    use -X^7 + 4*X^6 - 21*X^5 + 104*X^4 - 521*X^3 + 2604*X^2 - 13020*X + 65099, -14152
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · right
      simp
      refine ⟨?_, ?_, ?_⟩ <;> ring
  · let P : ℤ[X] := X^10 + X^9 + X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1; let d := 10
    let Q : ℤ[X] := 1
    let A : ℤ[X] := 0
    use P, Q, A
    use 0, 0, 0
    use 0, 0
    use 0, 0
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · left
      norm_num
  · let P : ℤ[X] := X^5 + 10*X^4 + 30*X^3 + X^2 + 9*X + 30; let d := 5
    let Q : ℤ[X] := X^5 + 22*X^4 + 30*X^3 + X^2 + 21*X + 30
    let A : ℤ[X] := -X^9 - 9*X^8 - 31*X^7 - 31*X^6 - 17*X^5 - 60*X^4 - 59*X^3 - 8*X^2 - 29*X - 29
    use P, Q, A
    use 0, 0, 0
    use 0, 0
    use 0, 0
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · left
      norm_num
  · let P : ℤ[X] := X^5 + 14*X^4 + 36*X^3 + X^2 + 13*X + 36; let d := 5
    let Q : ℤ[X] := X^5 + 24*X^4 + 36*X^3 + X^2 + 23*X + 36
    let A : ℤ[X] := -X^9 - 11*X^8 - 37*X^7 - 37*X^6 - 21*X^5 - 72*X^4 - 71*X^3 - 10*X^2 - 35*X - 35
    use P, Q, A
    use 0, 0, 0
    use 0, 0
    use 0, 0
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · left
      norm_num
  · let P : ℤ[X] := X^10 + X^9 + X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1; let d := 10
    let Q : ℤ[X] := 1
    let A : ℤ[X] := 0
    use P, Q, A
    use 0, 0, 0
    use 0, 0
    use 0, 0
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · left
      norm_num
  · let P : ℤ[X] := X^2 + 7*X + 1; let d := 2
    let Q : ℤ[X] := X^8 + 37*X^7 + 42*X^6 + 14*X^5 + 33*X^4 + 14*X^3 + 42*X^2 + 37*X + 1
    let A : ℤ[X] := -X^9 - 7*X^8 - 8*X^7 - 4*X^6 - 6*X^5 - 4*X^4 - 8*X^3 - 7*X^2 - X
    use P, Q, A
    use 0, 0, 0
    use 0, 0
    use 0, 0
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · left
      norm_num
  · let P : ℤ[X] := X^5 + 21*X^4 + 46*X^3 + X^2 + 20*X + 46; let d := 5
    let Q : ℤ[X] := X^5 + 27*X^4 + 46*X^3 + X^2 + 26*X + 46
    let A : ℤ[X] := -X^9 - 14*X^8 - 47*X^7 - 47*X^6 - 27*X^5 - 92*X^4 - 91*X^3 - 13*X^2 - 45*X - 45
    use P, Q, A
    use 0, 0, 0
    use 0, 0
    use 0, 0
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · left
      norm_num
  · let P : ℤ[X] := X^5 + 13*X^4 + 52*X^3 + X^2 + 12*X + 52; let d := 5
    let Q : ℤ[X] := X^5 + 41*X^4 + 52*X^3 + X^2 + 40*X + 52
    let A : ℤ[X] := -X^9 - 12*X^8 - 53*X^7 - 53*X^6 - 23*X^5 - 104*X^4 - 103*X^3 - 11*X^2 - 51*X - 51
    use P, Q, A
    use 0, 0, 0
    use 0, 0
    use 0, 0
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp
      ring
    · left
      norm_num
