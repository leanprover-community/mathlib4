/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.HEval
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# Binomial expansions of powers of Hahn Series
We introduce binomial expansions using `embDomain`.

## Main Definitions
  * `HahnSeries.orderTopSubOnePos` is the group of invertible Hahn series close to 1, i.e., those
  series such that subtracting one yields a series with strictly positive `orderTop`.
  * `HahnSeries.binomialFamily`
## Main results
  * coefficients of powers of binomials


-/

open Finset Function

open BigOperators Pointwise

namespace HahnSeries

suppress_compilation

variable {Γ R A : Type*}

theorem orderTop_self_sub_one_pos_iff [LinearOrder Γ] [Zero Γ] [NonAssocRing R] [Nontrivial R]
    (x : HahnSeries Γ R) :
    0 < (x - 1).orderTop ↔ x.orderTop = 0 ∧ x.leadingCoeff = 1 := by
  constructor
  · intro hx
    constructor
    · rw [← sub_add_cancel x 1, add_comm, ← orderTop_one (R := R)]
      exact orderTop_add_eq_left (Γ := Γ) (R := R) (orderTop_one (R := R) (Γ := Γ) ▸ hx)
    · rw [← sub_add_cancel x 1, add_comm, ← leadingCoeff_one (Γ := Γ) (R := R)]
      exact leadingCoeff_add_eq_left (Γ := Γ) (R := R) (orderTop_one (R := R) (Γ := Γ) ▸ hx)
  · intro h
    refine lt_of_le_of_ne (le_of_eq_of_le (by simp_all)
      (min_orderTop_le_orderTop_sub (Γ := Γ) (R := R))) <| Ne.symm <|
      orderTop_sub_ne h.1 orderTop_one ?_
    rw [h.2, leadingCoeff_one]
--#find_home! orderTop_self_sub_one_pos_iff --[Mathlib.RingTheory.HahnSeries.Multiplication]

variable [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]

namespace SummableFamily

variable [BinomialRing R] [CommRing A] [Algebra R A]

/-- A summable family of Hahn series, whose `n`th term is `Ring.choose r n • (x - 1) ^ n` when
`x` is close to `1` (more precisely, when `0 < (x - 1).orderTop`), and `0 ^ n` otherwise. These
terms give a formal expansion of `x^r` as `(1 + (x-1))^r`. -/
def binomialFamily (x : HahnSeries Γ A) (r : R) :
    SummableFamily Γ A ℕ :=
  SummableFamily.powerSeriesFamily (x - 1) (PowerSeries.mk (fun n => Ring.choose r n))

@[simp]
theorem binomialFamily_apply {x : HahnSeries Γ A} (hx : 0 < (x - 1).orderTop) (r : R) (n : ℕ) :
    binomialFamily x r n = Ring.choose r n • (x - 1) ^ n := by
  simp [hx, binomialFamily]

@[simp]
theorem binomialFamily_apply_of_orderTop_nonpos {x : HahnSeries Γ A} (hx : ¬ 0 < (x - 1).orderTop)
    (r : R) (n : ℕ) :
    binomialFamily x r n = 0 ^ n := by
  rw [binomialFamily, powerSeriesFamily_of_not_orderTop_pos hx]
  by_cases hn : n = 0 <;> simp [hn]

theorem binomialFamily_orderTop_pos {x : HahnSeries Γ A} (hx : 0 < (x - 1).orderTop) (r : R) {n : ℕ}
    (hn : 0 < n) :
    0 < (binomialFamily x r n).orderTop := by
  simp only [binomialFamily, smulFamily_toFun, PowerSeries.coeff_mk, powers_toFun, hx, ↓reduceIte]
  have : n ≠ 0 := by exact Nat.ne_zero_of_lt hn
  calc
    0 < n • (x - 1).orderTop := (nsmul_pos_iff (Nat.ne_zero_of_lt hn)).mpr hx
    n • (x - 1).orderTop ≤ ((x - 1) ^ n).orderTop := orderTop_nsmul_le_orderTop_pow
    ((x - 1) ^ n).orderTop ≤ ((Ring.choose r n) • ((x - 1) ^ n)).orderTop :=
      orderTop_le_orderTop_smul (Ring.choose r n) ((x - 1) ^ n)

theorem binomialFamily_mem_support {x : HahnSeries Γ A}
    (hx : 0 < (x - 1).orderTop) (r : R) (n : ℕ) {g : Γ}
    (hg : g ∈ (binomialFamily x r n).support) : 0 ≤ g := by
  by_cases hn : n = 0; · simp_all
  exact le_of_lt (WithTop.coe_pos.mp (lt_of_lt_of_le (binomialFamily_orderTop_pos hx r
    (Nat.pos_of_ne_zero hn)) (orderTop_le_of_coeff_ne_zero hg)))

theorem orderTop_hsum_binomialFamily_pos {x : HahnSeries Γ A} (hx : 0 < (x - 1).orderTop)
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


theorem isUnit_of_orderTop_pos {x : HahnSeries Γ R} (h : 0 < (x - 1).orderTop) :
    IsUnit x := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact isUnit_of_subsingleton x
  · refine isUnit_of_isUnit_leadingCoeff_AddUnitOrder ?_ ?_
    · rw [(x.orderTop_self_sub_one_pos_iff.mp h).2]
      exact isUnit_one
    · have := (x.orderTop_self_sub_one_pos_iff.mp h).1
      rw [← order_eq_orderTop_of_ne_zero
        (fun h ↦ WithTop.top_ne_zero (orderTop_eq_top.mpr h ▸ this)), WithTop.coe_eq_zero] at this
      rw [this]
      exact isAddUnit_zero

/-- The group of invertible Hahn series close to 1, i.e., those series such that subtracting 1
  yields a series with strictly positive `orderTop`. -/
@[simps]
def orderTopSubOnePos (Γ) (R) [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [CommRing R] :
    Subgroup (HahnSeries Γ R)ˣ where
  carrier := { x : (HahnSeries Γ R)ˣ | 0 < (x.val - 1).orderTop}
  mul_mem' := by
    intro x y hx hy
    obtain (_|_) := subsingleton_or_nontrivial R
    · simp
    · simp_all only [Set.mem_setOf_eq, orderTop_self_sub_one_pos_iff]
      have h1 : x.val.leadingCoeff * y.val.leadingCoeff = 1 := by rw [hx.2, hy.2, mul_one]
      constructor
      · rw [Units.val_mul, orderTop_mul_of_nonzero (by simp [h1]), hx.1, hy.1, add_zero]
      · rw [Units.val_mul, leadingCoeff_mul_of_nonzero (h1 ▸ one_ne_zero), h1]
  one_mem' := by simp
  inv_mem' {y} h := by
    suffices 0 < (y.inv - 1).orderTop by exact this
    obtain (_|_) := subsingleton_or_nontrivial R
    · simp
    · have : 0 < (y.val - 1).orderTop := h
      rw [orderTop_self_sub_one_pos_iff] at this
      have nz : y.val.leadingCoeff * y.inv.leadingCoeff ≠ 0 := by
        rw [this.2, one_mul]
        exact leadingCoeff_ne_zero.mpr (by simp)
      refine y.inv.orderTop_self_sub_one_pos_iff.mpr ⟨?_, ?_⟩
      · simpa [this.1, y.val_inv] using (orderTop_mul_of_nonzero nz).symm
      · simpa [this.2, y.val_inv] using (leadingCoeff_mul_of_nonzero nz).symm

@[simp]
theorem mem_orderTopSubOnePos_iff (x : (HahnSeries Γ R)ˣ) :
    x ∈ orderTopSubOnePos Γ R ↔ 0 < (x.val - 1).orderTop := by
  exact Eq.to_iff rfl

/-- Make an element of `orderTopSubOnePos` -/
@[simps]
def toOrderTopSubOnePos {x : HahnSeries Γ R} (h : 0 < (x - 1).orderTop) :
    orderTopSubOnePos Γ R where
  val := ⟨x, (isUnit_of_orderTop_pos h).unit.inv, IsUnit.mul_val_inv (isUnit_of_orderTop_pos h),
    IsUnit.val_inv_mul (isUnit_of_orderTop_pos h)⟩
  property := h

omit [IsOrderedCancelAddMonoid Γ] in
theorem orderTop_sub_pos {g : Γ} (hg : 0 < g) (r : R) :
    0 < ((1 + single g r) - 1).orderTop := by
  by_cases hr : r = 0 <;> simp [hr, hg]
--#find_home! orderTop_sub_pos --[Mathlib.RingTheory.HahnSeries.Multiplication]

theorem one_plus_single_mem_orderTopSubOnePos {g : Γ} (hg : 0 < g) (r : R) :
    (toOrderTopSubOnePos (orderTop_sub_pos hg r)).val ∈ orderTopSubOnePos Γ R :=
  (mem_orderTopSubOnePos_iff (toOrderTopSubOnePos (orderTop_sub_pos hg r)).val).mpr
    (orderTop_sub_pos hg r)

open SummableFamily

instance [BinomialRing R] :
    HPow (orderTopSubOnePos Γ R) R (orderTopSubOnePos Γ R) where
  hPow x r := toOrderTopSubOnePos (orderTop_hsum_binomialFamily_pos x.2 r)

@[simp]
theorem binomial_power [BinomialRing R] {x : orderTopSubOnePos Γ R} {r : R} :
    HPow.hPow x r = toOrderTopSubOnePos (orderTop_hsum_binomialFamily_pos x.2 r) :=
  rfl

theorem binomialFamily_coeff [BinomialRing R] {g : Γ} (hg : 0 < g) (r s : R) (k : ℕ) :
    HahnSeries.coeff ((toOrderTopSubOnePos
      (one_plus_single_mem_orderTopSubOnePos hg r)) ^ s).val (k • g) = Ring.choose s k • r ^ k := by
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
