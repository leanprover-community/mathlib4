/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.RingTheory.HahnSeries.HEval
public import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# Binomial expansions of powers of Hahn Series
We introduce binomial expansions using `embDomain`.

## Main Definitions
  * `HahnSeries.binomialFamily`

## Main results
  * coefficients of powers of binomials

-/

@[expose] public section

noncomputable section

namespace HahnSeries

variable {Γ R A : Type*}

variable [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
  [BinomialRing R]

namespace SummableFamily

variable [CommRing A] [Algebra R A]

/-- A summable family of Hahn series, whose `n`th term is `Ring.choose r n • (x - 1) ^ n` when
`x` is close to `1` (more precisely, when `0 < (x - 1).orderTop`), and `0 ^ n` otherwise. These
terms give a formal expansion of `x ^ r` as `(1 + (x - 1)) ^ r`. -/
def binomialFamily (x : A⟦Γ⟧) (r : R) :
    SummableFamily Γ A ℕ :=
  powerSeriesFamily (x - 1) (PowerSeries.binomialSeries A r)

@[simp]
theorem binomialFamily_apply {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) (n : ℕ) :
    binomialFamily x r n = Ring.choose r n • (x - 1) ^ n := by
  simp [hx, binomialFamily]

@[simp]
theorem binomialFamily_apply_of_orderTop_nonpos {x : A⟦Γ⟧} (hx : ¬ 0 < (x - 1).orderTop)
    (r : R) (n : ℕ) :
    binomialFamily x r n = 0 ^ n := by
  rw [binomialFamily, powerSeriesFamily_of_not_orderTop_pos hx]
  by_cases hn : n = 0 <;> simp [hn]

theorem binomialFamily_orderTop_pos {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) {n : ℕ}
    (hn : 0 < n) :
    0 < (binomialFamily x r n).orderTop := by
  simp only [binomialFamily, smulFamily_toFun, PowerSeries.binomialSeries_coeff, powers_toFun, hx,
    ↓reduceIte, smul_assoc, one_smul]
  have : n ≠ 0 := by exact Nat.ne_zero_of_lt hn
  calc
    0 < n • (x - 1).orderTop := (nsmul_pos_iff (Nat.ne_zero_of_lt hn)).mpr hx
    _ ≤ ((x - 1) ^ n).orderTop := orderTop_nsmul_le_orderTop_pow
    _ ≤ ((Ring.choose r n) • ((x - 1) ^ n)).orderTop :=
      orderTop_le_orderTop_smul (Ring.choose r n) ((x - 1) ^ n)

theorem binomialFamily_mem_support {x : A⟦Γ⟧}
    (hx : 0 < (x - 1).orderTop) (r : R) (n : ℕ) {g : Γ}
    (hg : g ∈ (binomialFamily x r n).support) : 0 ≤ g := by
  by_cases hn : n = 0; · simp_all
  exact le_of_lt (WithTop.coe_pos.mp (lt_of_lt_of_le (binomialFamily_orderTop_pos hx r
    (Nat.pos_of_ne_zero hn)) (orderTop_le_of_coeff_ne_zero hg)))

theorem orderTop_hsum_binomialFamily_pos {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop)
    (r : R) : (0 : WithTop Γ) < (SummableFamily.hsum (binomialFamily x r) - 1).orderTop := by
  obtain (_|_) := subsingleton_or_nontrivial A
  · simp [Subsingleton.eq_zero ((binomialFamily x r).hsum - 1)]
  · refine (orderTop_self_sub_one_pos_iff (binomialFamily x r).hsum).mpr ?_
    constructor
    · exact hsum_orderTop_of_le (by simp [hx]) (fun b g hg => binomialFamily_mem_support
        hx r b hg) fun b hb => coeff_eq_zero_of_lt_orderTop <| binomialFamily_orderTop_pos hx r <|
        Nat.zero_lt_of_ne_zero hb
    · have : (binomialFamily x r 0).coeff 0 = 1 := by simp [hx]
      rw [← this]
      refine hsum_leadingCoeff_of_le (g := 0) (a := 0) (by simp [hx]) ?_ ?_
      · intro b g' hg'
        exact binomialFamily_mem_support hx r b hg'
      · intro b hb
        exact coeff_eq_zero_of_lt_orderTop <| binomialFamily_orderTop_pos hx r <|
        Nat.zero_lt_of_ne_zero hb

end SummableFamily

open SummableFamily

instance : Pow (orderTopSubOnePos Γ R) R where
  pow x r := toOrderTopSubOnePos (orderTop_hsum_binomialFamily_pos x.2 r)

@[simp]
theorem binomial_power {x : orderTopSubOnePos Γ R} {r : R} :
    x ^ r = toOrderTopSubOnePos (orderTop_hsum_binomialFamily_pos x.2 r) :=
  rfl

theorem pow_add {x : orderTopSubOnePos Γ R} {r s : R} : x ^ (r + s) = x ^ r * x ^ s := by
  suffices (x ^ (r + s)).val = (x ^ r * x ^ s).val by exact SetLike.coe_eq_coe.mp this
  suffices (x ^ (r + s)).val.val = (x ^ r * x ^ s).val.val by exact Units.val_inj.mp this
  simp [binomialFamily, hsum_powerSeriesFamily_mul, hsum_mul]

theorem coeff_toOrderTopSubOnePos_pow {g : Γ} (hg : 0 < g) (r s : R) (k : ℕ) :
    HahnSeries.coeff (toOrderTopSubOnePos (orderTop_sub_pos hg r) ^ s).val (k • g) =
      Ring.choose s k • r ^ k := by
  simp only [val_toOrderTopSubOnePos_coe, binomial_power, coeff_hsum, smul_eq_mul]
  rw [finsum_eq_single _ k, binomialFamily_apply (orderTop_sub_pos hg r), add_sub_cancel_left,
    single_pow, coeff_smul, coeff_single_same (k • g) (r ^ k), smul_eq_mul]
  intro n hn
  rw [binomialFamily_apply, add_sub_cancel_left, coeff_smul, single_pow, coeff_single_of_ne,
    smul_zero]
  · contrapose! hn
    apply (StrictMono.injective (nsmul_left_strictMono hg)) hn.symm
  · by_cases hr : r = 0 <;> simp [hr, hg]

end HahnSeries
