/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Fabrizio Barroero, Laura Capuano, Nirvana Coppola,
María Inés de Frutos-Fernández, Sam van Gool, Silvain Rideau-Kikuchi, Amos Turchet,
Francesco Veneziano
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.NumberTheory.Padics.PadicNorm

/-!
# Ostrowski’s Theorem

Ostrowski's Theorem for the field `ℚ`: every absolute value on `ℚ` is equivalent to either a
`p`-adic absolute value or to the standard Archimedean (Euclidean) absolute value.

## Main results

- `Rat.AbsoluteValue.equiv_real_or_padic`: given an absolute value on `ℚ`, it is equivalent
to the standard Archimedean (Euclidean) absolute value `Rat.AbsoluteValue.real` or to a `p`-adic
absolute value `Rat.AbsoluteValue.padic p` for some prime number `p`.

## TODO

Extend to arbitrary number fields.

## References

* [K. Conrad, *Ostrowski's Theorem for Q*][conradQ]
* [K. Conrad, *Ostrowski for number fields*][conradnumbfield]
* [J. W. S. Cassels, *Local fields*][cassels1986local]

## Tags

ring norm, ostrowski
-/

/-!
### API for AbsoluteValue (from MulRingNorm)
-/

section API

namespace AbsoluteValue

variable {R : Type*} [Semiring R]

/-- Triangle inequality for `AbsoluteValue` applied to a list. -/
lemma listSum_le {S : Type*} [OrderedSemiring S] (l : List R) (f : AbsoluteValue R S) :
    f l.sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons head tail ih => exact (f.add_le' ..).trans <| add_le_add_left ih (f head)

/-- Two absolute values `f, g` on `R` with values in `ℝ` are *equivalent* if there exists
a positive constant `c` such that for all `x ∈ R`, `(f x)^c = g x`. -/
def equiv (f g : AbsoluteValue R ℝ) :=
  ∃ c : ℝ, 0 < c ∧ (f · ^ c) = g

/-- Equivalence of absolute values is reflexive. -/
lemma equiv_refl (f : AbsoluteValue R ℝ) : equiv f f :=
  ⟨1, Real.zero_lt_one, funext fun x ↦ Real.rpow_one (f x)⟩

/-- Equivalence of absolute values is symmetric. -/
lemma equiv_symm {f g : AbsoluteValue R ℝ} (hfg : equiv f g) : equiv g f := by
  rcases hfg with ⟨c, hcpos, h⟩
  refine ⟨1 / c, one_div_pos.mpr hcpos, ?_⟩
  simp [← h, Real.rpow_rpow_inv (apply_nonneg f _) (ne_of_lt hcpos).symm]

/-- Equivalence of absolute values is transitive. -/
lemma equiv_trans {f g k : AbsoluteValue R ℝ} (hfg : equiv f g) (hgk : equiv g k) :
    equiv f k := by
  rcases hfg with ⟨c, hcPos, hfg⟩
  rcases hgk with ⟨d, hdPos, hgk⟩
  refine ⟨c * d, mul_pos hcPos hdPos, ?_⟩
  simp [← hgk, ← hfg, Real.rpow_mul (apply_nonneg f _)]

/-- The *trivial* absolute value takes the value `1` on all nonzero elements. -/
protected
def trivial [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R] {S : Type*} [OrderedSemiring S]
    [Nontrivial S] :
    AbsoluteValue R S where
  toFun x := if x = 0 then 0 else 1
  map_mul' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    simp [hx, hy]
  nonneg' x := by rcases eq_or_ne x 0 with hx | hx <;> simp [hx]
  eq_zero' x := by rcases eq_or_ne x 0 with hx | hx <;> simp [hx]
  add_le' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    simp only [hx, ↓reduceIte, hy, show (1 : S) + 1 = 2 by norm_num]
    rcases eq_or_ne (x + y) 0 with hxy | hxy <;> simp [hxy, one_le_two]

@[simp]
lemma trivial_apply [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R] {S : Type*}
    [OrderedSemiring S] [Nontrivial S] {x : R} (hx : x ≠ 0) :
    AbsoluteValue.trivial (S := S) x = 1 :=
  if_neg hx

/-- An absolute value that is equivalent to the trivial one is already trivial. -/
lemma eq_trivial_of_equiv_trivial [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R] {S : Type*}
    [OrderedSemiring S] [Nontrivial S] (f : AbsoluteValue R ℝ) :
    f.equiv .trivial ↔ f = .trivial := by
  refine ⟨fun ⟨c, hc₀, hc⟩ ↦ ext fun x ↦ ?_, fun H ↦ H ▸ equiv_refl f⟩
  apply_fun (· x) at hc
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp only [ne_eq, hx, not_false_eq_true, trivial_apply] at hc ⊢
    exact (Real.rpow_left_inj (f.nonneg x) zero_le_one hc₀.ne').mp <| (Real.one_rpow c).symm ▸ hc

/-- An absolute value satisfies `f n ≤ n` for every `n : ℕ`. -/
lemma apply_nat_le_self {S : Type*} [OrderedRing S] [IsDomain S] (n : ℕ) (f : AbsoluteValue R S) :
    f n ≤ n := by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.eq_zero (n : R)]
  induction n with
  | zero => simp
  | succ n hn =>
    simp only [Nat.cast_succ]
    calc
      f (n + 1) ≤ f n + f 1 := f.add_le' ..
      _ = f n + 1 := congrArg (f n + ·) f.map_one
      _ ≤ n + 1 := add_le_add_right hn 1

open Int in
/-- An absolute value composed with the absolute value on integers equals
the absolute value itself. -/
lemma apply_natAbs_eq {R S : Type*} [Ring R] [OrderedCommRing S] [NoZeroDivisors S] (x : ℤ)
    (f : AbsoluteValue R S) :
    f (natAbs x) = f x := by
  obtain ⟨_, rfl | rfl⟩ := eq_nat_or_neg x <;> simp

end AbsoluteValue

end API

/-! ### Preliminary lemmas on limits and lists -/


open Filter Nat Real Topology

-- For any `C > 0`, the limit of `C ^ (1/k)` is 1 as `k → ∞`
private lemma tendsto_const_rpow_inv {C : ℝ} (hC : 0 < C) :
    Tendsto (fun k : ℕ ↦ C ^ (k : ℝ)⁻¹) atTop (𝓝 1) :=
  ((continuous_iff_continuousAt.mpr fun _ ↦ continuousAt_const_rpow hC.ne').tendsto'
    0 1 (rpow_zero C)).comp <| tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

--extends the lemma `tendsto_rpow_div` when the function has natural input
private lemma tendsto_nat_rpow_inv :
    Tendsto (fun k : ℕ ↦ (k : ℝ) ^ (k : ℝ)⁻¹) atTop (𝓝 1) := by
  simp_rw [← one_div]
  exact Tendsto.comp tendsto_rpow_div tendsto_natCast_atTop_atTop

-- Multiplication by a constant moves in a List.sum
private lemma list_mul_sum {R : Type*} [CommSemiring R] {T : Type*} (l : List T) (y : R) (x : R) :
    (l.mapIdx fun i _ => x * y ^ i).sum = x * (l.mapIdx fun i _ => y ^ i).sum := by
  simp_rw [← smul_eq_mul, List.smul_sum, List.mapIdx_eq_enum_map]
  congr 1
  simp

-- Geometric sum for lists
private lemma list_geom {T : Type*} {F : Type*} [Field F] (l : List T) {y : F} (hy : y ≠ 1) :
    (l.mapIdx fun i _ => y ^ i).sum = (y ^ l.length - 1) / (y - 1) := by
  rw [← geom_sum_eq hy l.length, List.mapIdx_eq_enum_map, Finset.sum_range, ← Fin.sum_univ_get']
  simp only [List.getElem_enum, Function.uncurry_apply_pair]
  let e : Fin l.enum.length ≃ Fin l.length := finCongr List.enum_length
  exact Fintype.sum_bijective e e.bijective _ _ fun _ ↦ rfl

namespace Rat.AbsoluteValue

open Int AbsoluteValue

variable {f g : AbsoluteValue ℚ ℝ}

/-- Values of an absolute value on the rationals coincide on `ℕ` if and only if they coincide
on `ℤ`. -/
lemma eq_on_nat_iff_eq_on_Int : (∀ n : ℕ , f n = g n) ↔ ∀ n : ℤ , f n = g n := by
  refine ⟨fun h z ↦ ?_, fun a n ↦ a n⟩
  obtain ⟨n , rfl | rfl⟩ := eq_nat_or_neg z <;> simp [h n]

/-- Values of an absolute value on the rationals are determined by the values on the natural
numbers. -/
lemma eq_on_nat_iff_eq : (∀ n : ℕ , f n = g n) ↔ f = g := by
  refine ⟨fun h ↦ ?_, fun h n ↦ congrFun (congrArg DFunLike.coe h) ↑n⟩
  ext1 z
  rw [← Rat.num_div_den z, map_div₀, map_div₀, h, eq_on_nat_iff_eq_on_Int.mp h]

/-- The equivalence class of an absolute value on the rationals is determined by its values on
the natural numbers. -/
lemma equiv_on_nat_iff_equiv : (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ , f n ^ c = g n) ↔ f.equiv g := by
  refine ⟨fun ⟨c, hc, h⟩ ↦ ⟨c, hc, ?_⟩, fun ⟨c, hc, h⟩ ↦ ⟨c, hc, (congrFun h ·)⟩⟩
  ext1 x
  rw [← Rat.num_div_den x, map_div₀, map_div₀, div_rpow (by positivity) (by positivity), h x.den,
    ← AbsoluteValue.apply_natAbs_eq,← AbsoluteValue.apply_natAbs_eq, h (natAbs x.num)]

section Non_archimedean

/-!
### The non-archimedean case

Every bounded absolute value is equivalent to a `p`-adic absolute value
-/

/-- The real-valued `AbsoluteValue` corresponding to the p-adic norm on `ℚ`. -/
def padic (p : ℕ) [Fact p.Prime] : AbsoluteValue ℚ ℝ where
  toFun x := (padicNorm p x : ℝ)
  map_mul' := by simp only [padicNorm.mul, Rat.cast_mul, forall_const]
  nonneg' x := cast_nonneg.mpr <| padicNorm.nonneg x
  eq_zero' x :=
    ⟨fun H ↦ padicNorm.zero_of_padicNorm_eq_zero <| cast_eq_zero.mp H,
      fun H ↦ cast_eq_zero.mpr <| H ▸ padicNorm.zero (p := p)⟩
  add_le' x y := by simp only; exact_mod_cast padicNorm.triangle_ineq x y

@[simp] lemma padic_eq_padicNorm (p : ℕ) [Fact p.Prime] (r : ℚ) :
    padic p r = padicNorm p r := rfl

-- ## Step 1: define `p = minimal n s. t. 0 < f n < 1`

variable (hf_nontriv : f ≠ AbsoluteValue.trivial) (bdd : ∀ n : ℕ, f n ≤ 1)

include hf_nontriv bdd in
/-- There exists a minimal positive integer with absolute value smaller than 1. -/
lemma exists_minimal_nat_zero_lt_and_lt_one :
    ∃ p : ℕ, (0 < f p ∧ f p < 1) ∧ ∀ m : ℕ, 0 < f m ∧ f m < 1 → p ≤ m := by
  -- There is a positive integer with absolute value different from one.
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, n ≠ 0 ∧ f n ≠ 1 := by
    contrapose! hf_nontriv
    rw [AbsoluteValue.trivial, ← eq_on_nat_iff_eq]
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · simp [hn0, hf_nontriv n hn0]
  set P := {m : ℕ | 0 < f ↑m ∧ f ↑m < 1} -- p is going to be the minimum of this set.
  have hP : P.Nonempty :=
    ⟨n, map_pos_of_ne_zero f (Nat.cast_ne_zero.mpr hn1), lt_of_le_of_ne (bdd n) hn2⟩
  exact ⟨sInf P, Nat.sInf_mem hP, fun m hm ↦ Nat.sInf_le hm⟩

-- ## Step 2: p is prime

variable {p : ℕ} (hp0 : 0 < f p) (hp1 : f p < 1) (hmin : ∀ m : ℕ, 0 < f m ∧ f m < 1 → p ≤ m)

include hp0 hp1 hmin in
/-- The minimal positive integer with absolute value smaller than 1 is a prime number.-/
lemma is_prime_of_minimal_nat_zero_lt_and_lt_one : p.Prime := by
  rw [← Nat.irreducible_iff_nat_prime]
  constructor -- Two goals: p is not a unit and any product giving p must contain a unit.
  · rw [Nat.isUnit_iff]
    rintro rfl
    simp only [Nat.cast_one, map_one, lt_self_iff_false] at hp1
  · rintro a b rfl
    rw [Nat.isUnit_iff, Nat.isUnit_iff]
    by_contra! con
    obtain ⟨ha₁, hb₁⟩ := con
    obtain ⟨ha₀, hb₀⟩ : a ≠ 0 ∧ b ≠ 0 := by
      refine mul_ne_zero_iff.mp fun h ↦ ?_
      rwa [h, Nat.cast_zero, map_zero, lt_self_iff_false] at hp0
    have hap : a < a * b := lt_mul_of_one_lt_right (by omega) (by omega)
    have hbp : b < a * b := lt_mul_of_one_lt_left (by omega) (by omega)
    have ha :=
      le_of_not_lt <| not_and.mp ((hmin a).mt hap.not_le) (map_pos_of_ne_zero f (mod_cast ha₀))
    have hb :=
      le_of_not_lt <| not_and.mp ((hmin b).mt hbp.not_le) (map_pos_of_ne_zero f (mod_cast hb₀))
    rw [Nat.cast_mul, map_mul] at hp1
    exact ((one_le_mul_of_one_le_of_one_le ha hb).trans_lt hp1).false

-- ## Step 3: if p does not divide m, then f m = 1

open Real

include hp0 hp1 hmin bdd in
/-- A natural number not divible by `p` has absolute value 1. -/
lemma eq_one_of_not_dvd {m : ℕ} (hpm : ¬ p ∣ m) : f m = 1 := by
  apply le_antisymm (bdd m)
  by_contra! hm
  set M := f p ⊔ f m with hM
  set k := Nat.ceil (M.logb (1 / 2)) + 1 with hk
  obtain ⟨a, b, bezout⟩ : IsCoprime (p ^ k : ℤ) (m ^ k) :=
    is_prime_of_minimal_nat_zero_lt_and_lt_one hp0 hp1 hmin
      |>.coprime_iff_not_dvd |>.mpr hpm |>.isCoprime |>.pow
  have le_half {x} (hx0 : 0 < x) (hx1 : x < 1) (hxM : x ≤ M) : x ^ k < 1 / 2 := by
    calc
    x ^ k = x ^ (k : ℝ) := (rpow_natCast x k).symm
    _ < x ^ M.logb (1 / 2) := by
      apply rpow_lt_rpow_of_exponent_gt hx0 hx1
      rw [hk]
      push_cast
      exact lt_add_of_le_of_pos (Nat.le_ceil _) zero_lt_one
    _ ≤ x ^ x.logb (1 / 2) := by
      apply rpow_le_rpow_of_exponent_ge hx0 hx1.le
      simp only [one_div, ← log_div_log, log_inv, neg_div, ← div_neg, hM]
      gcongr
      simp only [Left.neg_pos_iff]
      exact log_neg (lt_sup_iff.mpr <| .inl hp0) (sup_lt_iff.mpr ⟨hp1, hm⟩)
    _ = 1 / 2 := rpow_logb hx0 hx1.ne one_half_pos
  apply lt_irrefl (1 : ℝ)
  calc
  1 = f 1 := (map_one f).symm
  _ = f (a * p ^ k + b * m ^ k) := by rw_mod_cast [bezout]; norm_cast
  _ ≤ f (a * p ^ k) + f (b * m ^ k) := f.add_le' ..
  _ ≤ 1 * (f p) ^ k + 1 * (f m) ^ k := by
    simp only [map_mul, map_pow]
    gcongr
    all_goals rw [← AbsoluteValue.apply_natAbs_eq]; apply bdd
  _ = (f p) ^ k + (f m) ^ k := by simp only [one_mul]
  _ < 1 := by
    have hm₀ : 0 < f m := f.pos <| Nat.cast_ne_zero.mpr fun H ↦ hpm <| H ▸ dvd_zero p
    linarith only [le_half hp0 hp1 le_sup_left, le_half hm₀ hm le_sup_right]

-- ## Step 4: f p = p ^ (-t) for some positive real t

include hp0 hp1 hmin in
/-- The absolute value of `p` is `p ^ (-t)` for some positive real number `t`. -/
lemma exists_pos_eq_pow_neg : ∃ t : ℝ, 0 < t ∧ f p = p ^ (-t) := by
  have pprime := is_prime_of_minimal_nat_zero_lt_and_lt_one hp0 hp1 hmin
  refine ⟨- logb p (f p), Left.neg_pos_iff.mpr <| logb_neg (mod_cast pprime.one_lt) hp0 hp1, ?_⟩
  rw [neg_neg]
  exact (rpow_logb (mod_cast pprime.pos) (mod_cast pprime.ne_one) hp0).symm

-- ## Non-archimedean case: end goal

include hf_nontriv bdd in
/-- If `f` is bounded and not trivial, then it is equivalent to a p-adic absolute value. -/
theorem equiv_padic_of_bounded :
    ∃! p, ∃ (_ : Fact p.Prime), f.equiv (padic p) := by
  obtain ⟨p, hfp, hmin⟩ := exists_minimal_nat_zero_lt_and_lt_one hf_nontriv bdd
  have hprime := is_prime_of_minimal_nat_zero_lt_and_lt_one hfp.1 hfp.2 hmin
  have hprime_fact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨t, h⟩ := exists_pos_eq_pow_neg hfp.1 hfp.2 hmin
  simp_rw [← equiv_on_nat_iff_equiv]
  refine ⟨p, ⟨hprime_fact, t⁻¹, inv_pos_of_pos h.1, fun n ↦ ?_⟩, fun q ⟨hq_prime, h_equiv⟩ ↦ ?_⟩
  · have ht : t⁻¹ ≠ 0 := inv_ne_zero h.1.ne'
    rcases eq_or_ne n 0 with rfl | hn -- Separate cases n = 0 and n ≠ 0
    · simp [ht]
    · /- Any natural number can be written as a power of p times a natural number not divisible
      by p  -/
      rcases Nat.exists_eq_pow_mul_and_not_dvd hn p hprime.ne_one with ⟨e, m, hpm, rfl⟩
      simp only [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, h.2,
        eq_one_of_not_dvd bdd hfp.1 hfp.2 hmin hpm, padic_eq_padicNorm,
        padicNorm.padicNorm_p_of_prime, cast_inv, cast_natCast, inv_pow]
      rw [← padicNorm.nat_eq_one_iff] at hpm
      simp only [← rpow_natCast, p.cast_nonneg, ← rpow_mul, neg_mul, mul_one, ← rpow_neg, hpm,
        cast_one]
      congr
      field_simp [h.1.ne']
  · by_contra! hne
    apply hq_prime.elim.prime.ne_one
    rw [ne_comm, ← Nat.coprime_primes hprime hq_prime.elim, hprime.coprime_iff_not_dvd] at hne
    rcases h_equiv with ⟨c, _, h_eq⟩
    have h_eq' := h_eq q
    simp only [eq_one_of_not_dvd bdd hfp.1 hfp.2 hmin hne, one_rpow, padic_eq_padicNorm,
      padicNorm.padicNorm_p_of_prime, cast_inv, cast_natCast, eq_comm, inv_eq_one] at h_eq'
    exact_mod_cast h_eq'

end Non_archimedean

section Archimedean

/-! ## Archimedean case

Every unbounded absolute value is equivalent to the standard absolute value
-/

/-- The usual absolute value on `ℚ`. -/
def real : AbsoluteValue ℚ ℝ where
  toFun x := |x|
  map_mul' x y := by simpa using abs_mul (x : ℝ) (y : ℝ)
  nonneg' x := by simp
  eq_zero' x := by simp
  add_le' x y := by simpa using abs_add_le (x : ℝ) (y : ℝ)

@[simp] lemma real_eq_abs (r : ℚ) : real r = |r| := by
  simp [real]

-- ## Preliminary result

/-- Given an two integers `n`, `m` with `m > 1`, the absolute value of `n` is bounded by
`m + m * f m + m * (f m) ^ 2 + ... + m * (f m) ^ d` where `d` is the number of digits of the
expansion of `n` in base `m`. -/
lemma apply_le_sum_digits (n : ℕ) {m : ℕ} (hm : 1 < m) :
    f n ≤ ((Nat.digits m n).mapIdx fun i _ ↦ m * (f m) ^ i).sum := by
  set L := Nat.digits m n
  set L' : List ℚ := List.map Nat.cast (L.mapIdx fun i a ↦ (a * m ^ i)) with hL'
  -- If `c` is a digit in the expansion of `n` in base `m`, then `f c` is less than `m`.
  have hcoef {c : ℕ} (hc : c ∈ Nat.digits m n) : f c < m :=
    lt_of_le_of_lt (f.apply_nat_le_self c) (mod_cast Nat.digits_lt_base hm hc)
  calc
  f n = f ((Nat.ofDigits m L : ℕ) : ℚ) := by rw [Nat.ofDigits_digits m n]
    _ = f (L'.sum) := by rw [Nat.ofDigits_eq_sum_mapIdx]; norm_cast
    _ ≤ (L'.map f).sum := AbsoluteValue.listSum_le L' f
    _ ≤ (L.mapIdx fun i _ ↦ m * (f m) ^ i).sum := ?_
  simp only [hL', List.mapIdx_eq_enum_map, List.map_map]
  apply List.sum_le_sum
  rintro ⟨i, a⟩ hia
  dsimp [Function.uncurry]
  replace hia := List.mem_enumFrom hia
  push_cast
  rw [map_mul, map_pow]
  gcongr
  simp only [zero_le, zero_add, tsub_zero, true_and] at hia
  exact (hcoef (List.mem_iff_get.mpr ⟨⟨i, hia.1⟩, hia.2.symm⟩)).le

-- ## Step 1: if f is an AbsoluteValue and f n > 1 for some natural n, then f n > 1 for all n ≥ 2

/-- If `f n > 1` for some `n` then `f n > 1` for all `n ≥ 2` -/
lemma one_lt_of_not_bounded (notbdd : ¬ ∀ n : ℕ, f n ≤ 1) {n₀ : ℕ} (hn₀ : 1 < n₀) : 1 < f n₀ := by
  contrapose! notbdd with h
  intro n
  have h_ineq1 {m : ℕ} (hm : 1 ≤ m) : f m ≤ n₀ * (logb n₀ m + 1) := by
    /- L is the string of digits of `n` in the base `n₀`-/
    set L := Nat.digits n₀ m
    calc
    f m ≤ (L.mapIdx fun i _ ↦ n₀ * f n₀ ^ i).sum := apply_le_sum_digits m hn₀
    _ ≤ (L.mapIdx fun _ _ ↦ (n₀ : ℝ)).sum := by
      simp only [List.mapIdx_eq_enum_map, List.map_map]
      apply List.sum_le_sum
      rintro ⟨i, a⟩ _
      simp only [Function.comp_apply, Function.uncurry_apply_pair]
      exact mul_le_of_le_of_le_one' (mod_cast le_refl n₀) (pow_le_one₀ (by positivity) h)
        (by positivity) (by positivity)
    _ = n₀ * (Nat.log n₀ m + 1) := by
      rw [List.mapIdx_eq_enum_map, List.eq_replicate_of_mem (a := (n₀ : ℝ))
        (l := List.map (Function.uncurry fun _ _ ↦ n₀) (List.enum L)),
        List.sum_replicate, List.length_map, List.enum_length, nsmul_eq_mul, mul_comm,
        Nat.digits_len n₀ m hn₀ (not_eq_zero_of_lt hm), Nat.cast_add_one]
      simp +contextual
    _ ≤ n₀ * (logb n₀ m + 1) := by gcongr; exact natLog_le_logb ..
  -- For h_ineq2 we need to exclude the case n = 0.
  rcases eq_or_ne n 0 with rfl | h₀
  · simp
  have h_ineq2 (k : ℕ) (hk : 0 < k) :
      f n ≤ (n₀ * (logb n₀ n + 1)) ^ (k : ℝ)⁻¹ * k ^ (k : ℝ)⁻¹ := by
    have : 0 ≤ logb n₀ n := logb_nonneg (one_lt_cast.mpr hn₀) (mod_cast Nat.one_le_of_lt h₀.bot_lt)
    calc
    f n = (f ↑(n ^ k)) ^ (k : ℝ)⁻¹ := by
      rw [Nat.cast_pow, map_pow, ← rpow_natCast, rpow_rpow_inv (by positivity) (by positivity)]
    _  ≤ (n₀ * (logb n₀ ↑(n ^ k) + 1)) ^ (k : ℝ)⁻¹ := by
      gcongr
      exact h_ineq1 <| one_le_pow₀ (one_le_iff_ne_zero.mpr h₀)
    _  = (n₀ * (k * logb n₀ n + 1)) ^ (k : ℝ)⁻¹ := by
      rw [Nat.cast_pow, logb_pow]
    _  ≤ (n₀ * (k * logb n₀ n + k)) ^ (k : ℝ)⁻¹ := by
      gcongr
      exact one_le_cast.mpr hk
    _ = (n₀ * (logb n₀ n + 1)) ^ (k : ℝ)⁻¹ * k ^ (k : ℝ)⁻¹ := by
      rw [← mul_rpow (by positivity) (by positivity), mul_assoc, add_mul, one_mul,
        mul_comm _ (k : ℝ)]
-- For 0 < logb n₀ n below we also need to exclude n = 1.
  rcases eq_or_ne n 1 with rfl | h₁
  · simp
  refine le_of_tendsto_of_tendsto tendsto_const_nhds ?_ (eventually_atTop.mpr ⟨1, h_ineq2⟩)
  nth_rw 2 [← mul_one 1]
  have : 0 < logb n₀ n := logb_pos (mod_cast hn₀) (by norm_cast; omega)
  exact Tendsto.mul (tendsto_const_rpow_inv (by positivity)) tendsto_nat_rpow_inv

-- ## Step 2: given m,n ≥ 2 and |m|=m^s, |n|=n^t for s,t > 0, we have t ≤ s

variable {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (notbdd : ¬ ∀ (n : ℕ), f n ≤ 1)

include hm notbdd in
private lemma expr_pos : 0 < m * f m / (f m - 1) := by
  apply div_pos (mul_pos (mod_cast zero_lt_of_lt hm)
    (map_pos_of_ne_zero f (mod_cast ne_zero_of_lt hm)))
  linarith only [one_lt_of_not_bounded notbdd hm]

include hn hm notbdd in
private lemma param_upperbound {k : ℕ} (hk : k ≠ 0) :
    f n ≤ (m * f m / (f m - 1)) ^ (k : ℝ)⁻¹ * f m ^ logb m n := by
  have h_ineq1 {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
      f n ≤ (m * f m / (f m - 1)) * f m ^ logb m n := by
    let d := Nat.log m n
    calc
    f n ≤ ((Nat.digits m n).mapIdx fun i _ ↦ m * f m ^ i).sum :=
      apply_le_sum_digits n hm
    _ = m * ((Nat.digits m n).mapIdx fun i _ ↦ f m ^ i).sum := list_mul_sum (m.digits n) (f m) m
    _ = m * ((f m ^ (d + 1) - 1) / (f m - 1)) := by
      rw [list_geom _ (ne_of_gt (one_lt_of_not_bounded notbdd hm)),
        (Nat.digits_len m n hm (not_eq_zero_of_lt hn)).symm]
    _ ≤ m * ((f m ^ (d + 1)) / (f m - 1)) := by
      gcongr
      · linarith only [one_lt_of_not_bounded notbdd hm]
      · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le_one]
    _ = ↑m * f ↑m / (f ↑m - 1) * f ↑m ^ d := by ring
    _ ≤ ↑m * f ↑m / (f ↑m - 1) * f ↑m ^ logb ↑m ↑n := by
      gcongr
      · exact (expr_pos hm notbdd).le
      · rw [← rpow_natCast, rpow_le_rpow_left_iff (one_lt_of_not_bounded notbdd hm)]
        exact natLog_le_logb n m
  apply le_of_pow_le_pow_left₀ hk <| mul_nonneg (rpow_nonneg (expr_pos hm notbdd).le _)
    (rpow_nonneg (apply_nonneg f ↑m) _)
  nth_rewrite 2 [← rpow_natCast]
  rw [mul_rpow (rpow_nonneg (expr_pos hm notbdd).le _) (rpow_nonneg (apply_nonneg f ↑m) _),
    ← rpow_mul (expr_pos hm notbdd).le, ← rpow_mul (apply_nonneg f ↑m),
    inv_mul_cancel₀ (mod_cast hk), rpow_one, mul_comm (logb ..)]
  calc
    (f n) ^ k = f ↑(n ^ k) := by simp
    _ ≤ (m * f m / (f m - 1)) * f m ^ logb m ↑(n ^ k) := h_ineq1 hm (Nat.one_lt_pow hk hn)
    _ = (m * f m / (f m - 1)) * f m ^ (k * logb m n) := by
      rw [Nat.cast_pow, logb_pow]

include hm hn notbdd in
/-- Given two natural numbers `n, m` greater than 1 we have `f n ≤ f m ^ logb m n`. -/
lemma le_pow_log : f n ≤ f m ^ logb m n := by
  have : Tendsto (fun k : ℕ ↦ (m * f m / (f m - 1)) ^ (k : ℝ)⁻¹ * f m ^ logb m n)
      atTop (𝓝 (f m ^ logb m n)) := by
    nth_rw 2 [← one_mul (f ↑m ^ logb ↑m ↑n)]
    exact (tendsto_const_rpow_inv (expr_pos hm notbdd)).mul_const _
  exact le_of_tendsto_of_tendsto (tendsto_const_nhds (x:= f ↑n)) this <|
    eventually_atTop.mpr ⟨2, fun b hb ↦ param_upperbound hm hn notbdd (not_eq_zero_of_lt hb)⟩

include hm hn notbdd in
/-- Given `m, n ≥ 2` and `f m = m ^ s`, `f n = n ^ t` for `s, t > 0`, we have `t ≤ s`. -/
lemma le_of_eq_pow {s t : ℝ} (hfm : f m = m ^ s) (hfn : f n = n ^ t)  : t ≤ s := by
  rw [← rpow_le_rpow_left_iff (x := n) (mod_cast hn), ← hfn]
  apply le_trans <| le_pow_log hm hn notbdd
  rw [hfm, ← rpow_mul (Nat.cast_nonneg m), mul_comm, rpow_mul (Nat.cast_nonneg m),
    rpow_logb (mod_cast zero_lt_of_lt hm) (mod_cast hm.ne') (mod_cast zero_lt_of_lt hn)]

include hm hn notbdd in
private lemma symmetric_roles {s t : ℝ} (hfm : f m = m ^ s) (hfn : f n = n ^ t) : s = t :=
  le_antisymm (le_of_eq_pow hn hm notbdd hfn hfm) (le_of_eq_pow hm hn notbdd hfm hfn)

-- ## Archimedean case: end goal

include notbdd in
/-- If `f` is not bounded and not trivial, then it is equivalent to the standard absolute value on
`ℚ`. -/
theorem equiv_real_of_unbounded : f.equiv real := by
  obtain ⟨m, hm⟩ := Classical.exists_not_of_not_forall notbdd
  have oneltm : 1 < m := by
    contrapose! hm
    rcases le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl <;> simp
  rw [← equiv_on_nat_iff_equiv]
  set s := logb m (f m) with hs
  refine ⟨s⁻¹,
    inv_pos.mpr (logb_pos (Nat.one_lt_cast.mpr oneltm) (one_lt_of_not_bounded notbdd oneltm)),
    fun n ↦ ?_⟩
  rcases lt_trichotomy n 1 with h | rfl | h
  · obtain rfl : n = 0 := by omega
    have : (logb (↑m) (f ↑m))⁻¹ ≠ 0 := by
      simp only [ne_eq, inv_eq_zero, logb_eq_zero, Nat.cast_eq_zero, Nat.cast_eq_one, map_eq_zero,
        not_or]
      exact ⟨not_eq_zero_of_lt oneltm, oneltm.ne', by norm_cast,
        not_eq_zero_of_lt oneltm, ne_of_not_le hm, by linarith only [apply_nonneg f ↑m]⟩
    simp [hs, this]
  · simp
  · simp only [real_eq_abs, abs_cast, Rat.cast_natCast]
    rw [rpow_inv_eq (apply_nonneg f ↑n) (Nat.cast_nonneg n)
      (logb_ne_zero_of_pos_of_ne_one (one_lt_cast.mpr oneltm) (by linarith only [hm])
      (by linarith only [hm]))]
    have hfm : f m = m ^ s := by
      rw [rpow_logb (mod_cast zero_lt_of_lt oneltm) (mod_cast oneltm.ne') (by linarith only [hm])]
    have hfn : f n = n ^ logb n (f n) := by
      rw [rpow_logb (mod_cast zero_lt_of_lt h) (mod_cast h.ne')
      (by apply map_pos_of_ne_zero; exact_mod_cast not_eq_zero_of_lt h)]
    rwa [← hs, symmetric_roles oneltm h notbdd hfm hfn]

end Archimedean

/-- **Ostrowski's Theorem**: every absolute value (with values in `ℝ`) on `ℚ` is equivalent
to either the standard absolute value or a `p`-adic absolute value for a prime `p`. -/
theorem equiv_real_or_padic (f : AbsoluteValue ℚ ℝ) (hf_nontriv : f ≠ .trivial) :
    f.equiv real ∨ ∃! p, ∃ (_ : Fact p.Prime), f.equiv (padic p) := by
  by_cases bdd : ∀ n : ℕ, f n ≤ 1
  · exact .inr <| equiv_padic_of_bounded hf_nontriv bdd
  · exact .inl <| equiv_real_of_unbounded bdd

/-- The standard absolute value on `ℚ` is not equivalent to any `p`-adic absolute value. -/
lemma not_real_equiv_padic (p : ℕ) [Fact p.Prime] : ¬ real.equiv (padic p) := by
  have hp : p.Prime := Fact.out
  rintro ⟨c, hc₀, hc⟩
  apply_fun (· 2) at hc
  simp only [real_eq_abs, abs_ofNat, cast_ofNat, padic_eq_padicNorm, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, padicNorm.eq_zpow_of_nonzero, zpow_neg, cast_inv, cast_zpow,
    cast_natCast] at hc
  -- hc : 2 ^ c = (↑p ^ padicValRat p 2)⁻¹
  exact (((inv_le_one₀ <| zpow_pos (mod_cast hp.pos) _).mpr <| mod_cast NeZero.one_le).trans_lt <|
    one_lt_rpow one_lt_two hc₀).ne' hc

end Rat.AbsoluteValue
