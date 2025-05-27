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

theorem PNat.prime_seven : (7 : ℕ+).Prime :=
  Nat.prime_seven

instance Nat.fact_prime_seven : Fact (Nat.Prime 7) :=
  ⟨prime_seven⟩

instance PNat.fact_prime_seven : Fact (7 : ℕ+).Prime :=
  ⟨prime_seven⟩

lemma crazy7 : ⌊(4 / π) ^ 3 * (6! / 6 ^ 6 * √16807)⌋₊ = 4 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      _ ≥ (4 / 3.14159265358979323847) ^ 3 * (6! / 6 ^ 6 * √16807) := by
        gcongr; exact pi_lt_d20.le
      _ ≥ (4 / 3.14159265358979323847) ^ 3 * (6! / 6 ^ 6 * 129) := by
        gcongr; exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      _ ≥ 4 := by norm_num
  · calc
      _ < (4 / 3.14159265358979323846) ^ 3 * (6! / 6 ^ 6 * √16807) := by
        gcongr; exact pi_gt_d20
      _ ≤ (4 / 3.14159265358979323846) ^ 3 * (6! / 6 ^ 6 * 130) := by
        gcongr; exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ ≤ _ := by norm_num

variable [IsCyclotomicExtension {7} ℚ K]

theorem M7 : ⌊(M K)⌋₊ = 4 := by
  rw [absdiscr_prime 7 K, IsCyclotomicExtension.finrank (n := 7) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 7, totient_prime
      PNat.prime_seven]
  simp only [PNat.val_ofNat, Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg,
    Int.reducePow, reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact crazy7

theorem cyclotomic_7 : cyclotomic ((7 : ℕ+) : ℕ) ℤ =
    X^6 + X^5 + X^4 + X^3 + X^2 + X + 1 := by
  simp [cyclotomic_prime, sum_range_succ]
  ring

example : Nat.log 2 8 = 3 := by
  norm_num

theorem pid7 : IsPrincipalIdealRing (𝓞 K) := by
  apply IsCyclotomicExtension.Rat.pid6 7
  rw [M7, cyclotomic_7]
  intro p hple hp hpn
  fin_cases hple; any_goals norm_num at hp
  · left; simp; norm_num; refine orderOf_lt_of (by norm_num) (fun i hi hipos ↦ ?_)
    have := Finset.mem_Icc.mpr ⟨hipos, hi⟩; fin_cases this <;> norm_num
  · left; simp; norm_num; refine orderOf_lt_of (by norm_num) (fun i hi hipos ↦ ?_)
    have := Finset.mem_Icc.mpr ⟨hipos, hi⟩; fin_cases this <;> norm_num
