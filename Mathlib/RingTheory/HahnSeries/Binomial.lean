/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.HahnSeries.HEval
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# Hahn Series
We introduce binomial expansions using `embDomain`.

## Main Definitions
  * `UnitBinomial` describes an invertible binomial, i.e., one with invertible leading coefficient.
  * `HahnSeries.binomialFamily`
## Main results

  * coefficients of powers of binomials

## To do
  * Use RingTheory.PowerSeries.Binomial
  * coefficients of negative powers.
  * Change API to use `R`-algebra hom `R[[X]] →ₐ[R] HahnSeries Γ R` given by substitution.  Then we
    can use the power series API for expansion of `1/(u-x)`.
  * Allow "arbitrary" powers of `1 - single g r`, where arbitrary means coming from a binomial ring
    over which `R` is an algebra?

-/

open Finset Function

open BigOperators Pointwise

suppress_compilation

variable {Γ R A : Type*}

namespace MonoidAlgebra

variable [Ring R]

/-- A unit monomial minus a unit monomial. -/
def single_sub_single (g g' : Γ) : MonoidAlgebra R Γ := single g 1 - single g' 1

@[simp]
theorem single_sub_single_of_subsingleton [Subsingleton R] (g g' : Γ) :
    single_sub_single g g' = (0 : MonoidAlgebra R Γ) :=
  Subsingleton.eq_zero (single_sub_single g g')

@[simp]
theorem single_sub_single_eq_zero_iff [Nontrivial R] (g g' : Γ) :
    single_sub_single g g' = (0 : MonoidAlgebra R Γ) ↔ g = g' := by
  refine ⟨?_, fun h ↦ (by simp [single_sub_single, h])⟩
  intro h
  by_contra hgg'
  rw [single_sub_single, sub_eq_zero, MonoidAlgebra.ext_iff] at h
  specialize h g
  classical
  rw [single_apply, single_apply] at h
  simp [Ne.symm hgg'] at h

theorem single_sub_single_neg (g g' : Γ) :
    - single_sub_single g g' (R := R) = single_sub_single g' g := by
  simp [single_sub_single]

theorem single_sub_single_pow [CommMonoid Γ] (g g' : Γ) (n : ℕ) :
    (single_sub_single g g' (R := R)) ^ n = ∑ i ∈ antidiagonal n,
      Int.negOnePow (i.2) • n.choose (i.1) • single (g ^ (i.1) * g' ^ i.2) 1 := by
  rw [single_sub_single, Ring.sub_eq_add_neg, Commute.add_pow]
  · rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine sum_congr rfl ?_
    intro i hi
    rw [neg_pow']
    simp only [single_pow, one_pow, smul_single, nsmul_eq_mul, mul_one]
    rw [← mul_assoc, single_mul_single, one_mul, Int.negOnePow_def, uzpow_natCast]
    have : Commute (single (g ^ i * g' ^ (n - i)) 1) ((-1 : MonoidAlgebra R Γ) ^ (n - i)) :=
      single_commute (fun a' ↦ Commute.all (g ^ i * g' ^ (n - i)) a') (fun b' ↦ Commute.one_left b')
        ((-1) ^ (n - i))
    rw [this, ← Nat.cast_comm,
      show (-1 : MonoidAlgebra R Γ) ^ (n - i) = ((-1) ^  (n - i) : ℤ) by norm_cast]
    rw [← zsmul_eq_mul, ← nsmul_eq_mul, smul_single, smul_single]
    congr 1
    rw [nsmul_eq_mul, Nat.cast_comm, smul_one_mul]
    congr
  · exact Commute.neg_right (single_commute_single (Commute.all g g') rfl)

end MonoidAlgebra

namespace HahnSeries

section BinomialPow

variable [LinearOrderedAddCommGroup Γ] [CommRing R] [BinomialRing R] [Module R Γ]
[CommRing A] [Algebra R A]

theorem pos_orderTop_single_sub {g g' : Γ} (h : g < g') (a : A) :
    0 < (single (g' - g) a).orderTop := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [orderTop_single ha, WithTop.coe_pos]
    exact sub_pos.mpr h
--#find_home! pos_orderTop_single_sub --[Mathlib.RingTheory.HahnSeries.Multiplication]

/-- A Hahn series formally expanding `(X g - X g') ^ r` where `r` is an element of a binomial ring.
-/
def binomialPow (g g' : Γ) (r : R) : HahnSeries Γ A :=
  single (r • g) (1 : A) *
    (PowerSeries.heval ((single (g' - g)) (-1 : A)) (PowerSeries.binomialSeries A r))

@[simp]
theorem binomialPow_apply (g g' : Γ) (r : R) :
    binomialPow g g' r = single (r • g) 1 *
      (PowerSeries.heval ((single (g' - g)) (-1 : A)) (PowerSeries.binomialSeries A r)) :=
  rfl

theorem binomialPow_apply_of_not_gt {g g' : Γ} (h : ¬ g < g') (r : R) :
    binomialPow g g' r = single (r • g) (1 : A) := by
  cases subsingleton_or_nontrivial A
  · have _ : Subsingleton (HahnSeries Γ A) := instSubsingleton
    exact Subsingleton.elim _ _
  · have : ¬ 0 < (single (g' - g) (-1 : A)).orderTop := by
      rw [orderTop_single (neg_ne_zero.mpr one_ne_zero), WithTop.coe_pos, sub_pos]
      exact h
    rw [binomialPow_apply, PowerSeries.heval_of_orderTop_not_pos _ this]
    simp

theorem binomialPow_add {g g' : Γ} (r r' : R) :
    binomialPow (A := A) g g' r * binomialPow g g' r' =
      binomialPow g g' (r + r') := by
  simp only [binomialPow, PowerSeries.binomialSeries_add, PowerSeries.heval_mul, add_smul]
  rw [mul_left_comm, ← mul_assoc, ← mul_assoc, single_mul_single, mul_one, add_comm, ← mul_assoc]

theorem binomialPow_nat {g g' : Γ} (h : g < g') (n : ℕ) :
    binomialPow g g' (n : R) = ((single g (1 : A)) - single g' 1) ^ n := by
  induction n with
  | zero => simp [PowerSeries.binomialSeries_zero, map_one]
  | succ n ih =>
    rw [Nat.cast_add, ← binomialPow_add, pow_add, ih]
    have : binomialPow g g' (Nat.cast (R := R) 1) = ((single g) (1 : A) - (single g') 1) := by
      simp only [Nat.cast_one, binomialPow_apply, one_smul]
      rw [← Nat.cast_one (R := R), PowerSeries.binomialSeries_nat 1, pow_one, map_add,
        PowerSeries.heval_X, ← RingHom.map_one (f := PowerSeries.C A), PowerSeries.heval_C,
        one_smul, mul_add, mul_one, single_mul_single, one_mul, single_neg, add_sub_cancel,
        sub_eq_add_neg]
      · exact pos_orderTop_single_sub h (-1)
      · exact pos_orderTop_single_sub h (-1)
    rw [this, pow_one]

end BinomialPow

/-! We consider integral powers of binomials with invertible leading term.  Also, we consider more
binomial ring powers of binomials with leading term 1, when the coefficient ring is an algebra over
the binomial ring in question.  Question: how to approach switching to consider locality in vertex
algebras?  -/

section Binomial

theorem pos_addUnit_neg_add [AddMonoid Γ] [LT Γ]
    [CovariantClass Γ Γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x < x_1]
    [ContravariantClass Γ Γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x < x_1] {g g' : Γ} (hg : IsAddUnit g)
    (hgg' : g < g') : 0 < hg.addUnit.neg + g' := by
  refine (lt_add_iff_pos_right g).mp ?_
  rw [← add_assoc, AddUnits.neg_eq_val_neg, IsAddUnit.add_val_neg, zero_add]
  exact hgg'

--#find_home pos_addUnit_neg_add --Mathlib.Algebra.Order.Group.Units

theorem one_sub_single_sub_one_orderTop_pos [OrderedCancelAddCommMonoid Γ] [CommRing R]
    {g : Γ} (hg : 0 < g) (r : R) : 0 < ((1 - single g r) - 1).orderTop := by
  refine lt_of_lt_of_le (WithTop.coe_pos.mpr hg) ?_
  simp only [sub_sub_cancel_left, orderTop_neg, orderTop_single_le]

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R]

theorem minus_one_orderTop_pos [Nontrivial R] (x : HahnSeries Γ R) :
    0 < (x - 1).orderTop ↔ x.orderTop = 0 ∧ x.leadingCoeff = 1 := by
  constructor
  · intro hx
    rw [show x = (x - 1) + 1 by exact Eq.symm (sub_add_cancel x 1), add_comm,
      ← orderTop_one (R := R) (Γ := Γ), ← leadingCoeff_one (R := R) (Γ := Γ)]
    constructor
    · exact orderTop_add_eq_left (Γ := Γ) (R := R) (orderTop_one (R := R) (Γ := Γ) ▸ hx)
    · exact leadingCoeff_add_eq_left (Γ := Γ) (R := R) (orderTop_one (R := R) (Γ := Γ) ▸ hx)
  · intro h
    refine lt_of_le_of_ne (le_of_eq_of_le (by simp_all)
      (min_orderTop_le_orderTop_sub (Γ := Γ) (R := R))) <| Ne.symm <|
      sub_orderTop_ne_of_leadingCoeff_eq h.1 orderTop_one ?_
    rw [h.2, leadingCoeff_one]

/-- The monoid of elements close to 1, i.e., subtracting 1 yields positive `orderTop`. -/
@[simps]
def onePlusPosOrderTop (Γ) (R) [LinearOrderedCancelAddCommMonoid Γ] [CommRing R] :
    Submonoid (HahnSeries Γ R) where
  carrier := { x : HahnSeries Γ R | 0 < (x - 1).orderTop}
  mul_mem' := by
    intro x y hx hy
    obtain (_|_) := subsingleton_or_nontrivial R
    · simp
    · simp_all only [Set.mem_setOf_eq, minus_one_orderTop_pos]
      have h1 : x.leadingCoeff * y.leadingCoeff = 1 := by rw [hx.2, hy.2, mul_one]
      constructor
      · rw [orderTop_mul_of_nonzero (h1 ▸ one_ne_zero), hx.1, hy.1, add_zero]
      · rw [leadingCoeff_mul_of_nonzero (h1 ▸ one_ne_zero), h1]
  one_mem' := by simp

@[simp]
theorem mem_onePlusPosOrderTop_iff (x : HahnSeries Γ R) :
    x ∈ onePlusPosOrderTop Γ R ↔ 0 < (x - 1).orderTop := by
  exact Eq.to_iff rfl

theorem one_plus_single_mem_onePlusPosOrderTop {g : Γ} (hg : 0 < g) (r : R) :
    1 + single g r ∈ onePlusPosOrderTop Γ R := by
  refine (mem_onePlusPosOrderTop_iff _).mpr ?_
  rw [add_sub_cancel_left]
  exact lt_of_lt_of_le (WithTop.coe_pos.mpr hg) orderTop_single_le

namespace SummableFamily
open HahnSeries

/-- A summable family of Hahn series, whose `n`th term is `Ring.choose r n • (x-1)^n`. These terms
give a formal expansion of `x^r` as `(1 + (x-1))^r`. -/
def binomialFamily [BinomialRing R] [CommRing A] [Algebra R A] (x : HahnSeries Γ A) (r : R) :
    SummableFamily Γ A ℕ :=
  SummableFamily.powerSeriesFamily (x - 1) (PowerSeries.mk (fun n => Ring.choose r n))

@[simp]
theorem binomialFamily_toFun [BinomialRing R] [CommRing A] [Algebra R A] {x : HahnSeries Γ A}
    (hx : x ∈ onePlusPosOrderTop Γ A) (r : R) (n : ℕ) :
    binomialFamily x r n = Ring.choose r n • (x - 1) ^ n := by
  simp only [mem_onePlusPosOrderTop_iff] at hx
  simp [hx, binomialFamily]

/-!
theorem binomialFamily_orderTop_pos [BinomialRing R] [CommRing A] [Algebra R A] {x : HahnSeries Γ A}
    (hx : x ∈ onePlusPosOrderTop Γ A) (r : R) {n : ℕ} (hn : 0 < n) :
  0 < (binomialFamily x r n).orderTop := by
  rw [mem_onePlusPosOrderTop_iff] at hx
  simp only [hx, binomialFamily]
  calc
    0 < n • (x - 1).orderTop := (nsmul_pos_iff (Nat.not_eq_zero_of_lt hn)).mpr hx
    n • (x - 1).orderTop ≤ ((x - 1) ^ n).orderTop := orderTop_nsmul_le_orderTop_pow
    ((x - 1) ^ n).orderTop ≤ ((Ring.choose r n) • ((x - 1) ^ n)).orderTop :=
      orderTop_le_orderTop_smul (Ring.choose r n) ((x - 1) ^ n)


theorem binomialFamily_mem_support [BinomialRing R] [CommRing A] [Algebra R A] {x : HahnSeries Γ A}
    (hx : x ∈ onePlusPosOrderTop Γ A) (r : R) (n : ℕ) {g : Γ}
    (hg : g ∈ (binomialFamily hx r n).support) : 0 ≤ g := by
  by_cases hn : n = 0; · simp_all
  exact le_of_lt (WithTop.coe_pos.mp (lt_of_lt_of_le (binomialFamily_orderTop_pos hx r
    (Nat.pos_of_ne_zero hn)) (orderTop_le_of_coeff_ne_zero hg)))

theorem binomialFamily_hsum_in_onePlusPosOrderTop [BinomialRing R] (x : onePlusPosOrderTop Γ R)
    (r : R) : (0 : Γ) < (SummableFamily.hsum (binomialFamily x.2 r) - 1).orderTop := by
  obtain (_|_) := subsingleton_or_nontrivial R
  · simp
  · refine (minus_one_orderTop_pos (binomialFamily x.2 r).hsum).mpr ?_
    constructor
    · exact SummableFamily.hsum_orderTop_of_le (by simp) (fun b g hg => binomialFamily_mem_support
        x.2 r b hg) fun b hb => coeff_eq_zero_of_lt_orderTop <| binomialFamily_orderTop_pos x.2 r <|
        Nat.zero_lt_of_ne_zero hb
    · have : (binomialFamily x.2 r 0).coeff 0 = 1 := by simp
      rw [← this]
      refine SummableFamily.hsum_leadingCoeff_of_le (g := 0) (a := 0) (by simp) ?_ ?_
      · intro b g' hg'
        exact binomialFamily_mem_support x.property r b hg'
      · intro b hb
        exact coeff_eq_zero_of_lt_orderTop <| binomialFamily_orderTop_pos x.2 r <|
        Nat.zero_lt_of_ne_zero hb

instance [LinearOrderedCancelAddCommMonoid Γ] [CommRing R] [BinomialRing R] :
    HPow (onePlusPosOrderTop Γ R) R (onePlusPosOrderTop Γ R) where
  hPow x r := ⟨(binomialFamily x.2 r).hsum, binomialFamily_hsum_in_onePlusPosOrderTop x r⟩

@[simp]
theorem binomial_power [BinomialRing R] {x : onePlusPosOrderTop Γ R} {r : R} :
    HPow.hPow x r = (binomialFamily x.2 r).hsum :=
  rfl

theorem binomialFamily_coeff [BinomialRing R] {g : Γ} (hg : 0 < g) (r s : R) (k : ℕ) :
    HahnSeries.coeff ((⟨(1 + single g r), one_plus_single_mem_onePlusPosOrderTop hg r⟩ :
      onePlusPosOrderTop Γ R) ^ s) (k • g) = Ring.choose s k • r ^ k := by
  simp only [binomial_power, SummableFamily.coeff_hsum, binomialFamily_toFun, add_sub_cancel_left,
    single_pow, coeff_smul, smul_eq_mul]
  rw [finsum_eq_single _ k, coeff_single_same (k • g) (r ^ k)]
  intro n hn
  rw [coeff_single_of_ne, mul_zero]
  exact (Injective.ne_iff (f := fun (k : ℕ) => k • g) <| StrictMono.injective <|
    nsmul_left_strictMono hg).mpr hn.symm
-/
end SummableFamily

theorem isUnit_one_sub_single {g : Γ} (hg : 0 < g) (r : R) : IsUnit (1 - single g r) := by
  rw [← meval_X hg, ← RingHom.map_one (meval hg r), ← RingHom.map_sub]
  refine RingHom.isUnit_map (meval hg r) ?_
  rw [← pow_one (1 - PowerSeries.X)]
  rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow R 1]
  exact Units.isUnit (PowerSeries.invOneSubPow R 1)⁻¹

theorem one_sub_single_npow_coeff {g : Γ} (hg : 0 < g) (r : R) (n k : ℕ) :
    ((1 - single g r) ^ n).coeff (k • g) = (-1) ^ k • Nat.choose n k • r ^ k := by
  rw [← meval_X hg, ← RingHom.map_one (meval hg r), ← RingHom.map_sub, ← RingHom.map_pow]
  by_cases hn : n = 0
  · by_cases hk : k = 0
    · simp [hn, hk]
    · rw [hn, Nat.choose_eq_zero_of_lt (Nat.zero_lt_of_ne_zero hk)]
      have hkg : k • g ≠ 0 • g := fun h => hk (StrictMono.injective (nsmul_left_strictMono hg) h)
      simp_all [hk, hkg]
  · have hm : (1 : PowerSeries R) - PowerSeries.X = PowerSeries.rescale (-1 : R)
        ((1 : PowerSeries R) + PowerSeries.X) := by
      simp [Mathlib.Tactic.RingNF.add_neg]
    rw [meval_apply_coeff, hm, ← RingHom.map_pow, PowerSeries.coeff_rescale, show 1 +
      PowerSeries.X = Polynomial.coeToPowerSeries.ringHom ((1 : Polynomial R) + Polynomial.X) by
      simp, ← RingHom.map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe,
      Polynomial.coeff_one_add_X_pow R n k, mul_rotate']
    simp

/-!
theorem one_sub_single_negSuccPow_coeff {g : Γ} (hg : 0 < g) (r : R) (n k : ℕ) :
    ((isUnit_one_sub_single hg r).unit ^ (Int.negSucc n)).val.coeff (k • g) =
      Nat.choose (n + k) k • r ^ k := by
  have hm : ((isUnit_one_sub_single hg r).unit ^ (Int.negSucc n)).val =
      (meval hg r) (PowerSeries.invOneSubPow n).val := by
    rw [@zpow_negSucc]

    sorry
  sorry
-/
-- theorem one_sub_single_npow_coeff_notin_range

/-- An invertible binomial, i.e., one with invertible leading term. -/
def UnitBinomial {g g' : Γ} (hg : IsAddUnit g) (hgg' : g < g') {a : R} (ha : IsUnit a) (b : R) :
    (HahnSeries Γ R)ˣ :=
  (UnitSingle hg ha) *
    IsUnit.unit (isUnit_one_sub_single (pos_addUnit_neg_add hg hgg') (ha.unit.inv * -b))

theorem unitBinomial_eq_single_add_single {g g' : Γ} {hg : IsAddUnit g} {hgg' : g < g'} {a : R}
    {ha : IsUnit a} {b : R} : UnitBinomial hg hgg' ha b = single g a + single g' b := by
  simp only [UnitBinomial, AddUnits.neg_eq_val_neg, Units.inv_eq_val_inv, Units.val_mul,
    val_UnitSingle, IsUnit.unit_spec, mul_sub, mul_one, single_mul_single, sub_right_inj]
  rw [← add_assoc, IsAddUnit.add_val_neg, zero_add, ← mul_assoc, IsUnit.mul_val_inv, one_mul,
    sub_eq_iff_eq_add, add_assoc, ← single_add, add_neg_cancel, single_eq_zero, add_zero]

theorem orderTop_unitBinomial [Nontrivial R] {g g' : Γ} (hg : IsAddUnit g) (hgg' : g < g') {a : R}
    (ha : IsUnit a) (b : R) : (UnitBinomial hg hgg' ha b).val.orderTop = g := by
  rw [unitBinomial_eq_single_add_single, orderTop_add_eq_left, orderTop_single (IsUnit.ne_zero ha)]
  · refine lt_of_lt_of_le ?_ orderTop_single_le
    rw [(orderTop_single (IsUnit.ne_zero ha))]
    exact WithTop.coe_lt_coe.mpr hgg'

theorem order_unitBinomial [Nontrivial R] {g g' : Γ} (hg : IsAddUnit g) (hgg' : g < g') {a : R}
    (ha : IsUnit a) (b : R) : (UnitBinomial hg hgg' ha b).val.order = g := by
  rw [← WithTop.coe_eq_coe, order_eq_orderTop_of_ne (Units.ne_zero (UnitBinomial hg hgg' ha b))]
  exact orderTop_unitBinomial hg hgg' ha b

theorem leadingCoeff_unitBinomial [Nontrivial R] {g g' : Γ} (hg : IsAddUnit g) (hgg' : g < g')
    {a : R} (ha : IsUnit a) (b : R) : (UnitBinomial hg hgg' ha b).val.leadingCoeff = a := by
  rw [leadingCoeff_eq, order_unitBinomial, unitBinomial_eq_single_add_single, coeff_add,
    coeff_single_same, coeff_single_of_ne (ne_of_lt hgg'), add_zero]

--theorem unitBinomial_npow_coeff

-- coefficients of powers - use embDomain_coeff and embDomain_notin_range from Basic

theorem orderTop_single_add_single {g g' : Γ} (hgg' : g < g') {a : R} (ha : a ≠ 0) (b : R) :
    (single g a + single g' b).orderTop = g := by
  rw [← orderTop_single ha]
  exact orderTop_add_eq_left (lt_of_eq_of_lt (orderTop_single ha)
    (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hgg') orderTop_single_le))

theorem coeff_single_add_single {g g' : Γ} (hgg' : g < g') {a b : R} :
    (single g a + single g' b).coeff g = a := by
  simp_all [ne_of_lt hgg']

theorem single_add_single_ne {g g' : Γ} (hgg' : g < g') {a : R} (ha : a ≠ 0) (b : R) :
    single g a + single g' b ≠ 0 :=
  ne_zero_of_coeff_ne_zero (ne_of_eq_of_ne (coeff_single_add_single hgg') ha)

-- Do I need this?
theorem single_add_single_support {g g' : Γ} {a b : R} :
    (single g a + single g' b).support ⊆ {g} ∪ {g'} := by
  refine support_add_subset.trans ?_
  simp_all only [Set.union_singleton, Set.union_subset_iff]
  refine { left := fun _ hk => Set.mem_insert_of_mem g' (support_single_subset hk), right := ?_ }
  rw [Set.pair_comm]
  exact fun k hk => Equiv.Set.union.proof_1 k <| Set.mem_insert_of_mem g (support_single_subset hk)

theorem leadingCoeff_single_add_single {g g' : Γ} (hgg' : g < g') {a b : R} (ha : a ≠ 0) :
    (single g a + single g' b).leadingCoeff = a := by
  have hn := single_add_single_ne hgg' ha b
  have ho := orderTop_single_add_single hgg' ha b
  rw [orderTop_of_ne hn, WithTop.coe_eq_coe] at ho
  rw [leadingCoeff_of_ne hn, ho, coeff_single_add_single hgg']

theorem order_single_add_single {g g' : Γ} (hgg' : g < g') {a b : R} (ha : a ≠ 0) :
    (single g a + single g' b).order = g := by
  refine WithTop.coe_eq_coe.mp ?_
  rw [order_eq_orderTop_of_ne (single_add_single_ne hgg' ha b), orderTop_single_add_single hgg' ha]

theorem isUnit_single_add_single {g g' : Γ} (hg : IsAddUnit g) (hgg' : g < g') (a : Units R)
    (b : R) : IsUnit (single g a.val + single g' b) := by
  by_cases ha : a.val = 0
  · have hz : (0 : R) = 1 :=
      isUnit_zero_iff.mp (Eq.mpr (congrArg (fun h ↦ IsUnit h) ha.symm) a.isUnit)
    rw [← MulAction.one_smul (α := R) ((single g) a.val + (single g') b), ← hz, zero_smul,
      isUnit_zero_iff, ← single_zero_one, ← hz, single_eq_zero]
  · refine isUnit_of_isUnit_leadingCoeff_AddUnitOrder (R := R) ?_ ?_
    · rw [leadingCoeff_single_add_single hgg' ha]
      exact Units.isUnit a
    · rw [order_single_add_single hgg' ha]
      exact hg

/-- A binomial Hahn series with unit leading coefficient -/
abbrev UnitBinomial' {g g' : Γ} (hg : IsAddUnit g) (hgg' : g < g') {a : R} (ha : IsUnit a) (b : R) :
    (HahnSeries Γ R)ˣ :=
  IsUnit.unit (isUnit_single_add_single hg hgg' (IsUnit.unit ha) b)

theorem UnitBinomial_val {g g' : Γ} (hg : IsAddUnit g) (hgg' : g < g') {a : R} (ha : IsUnit a)
    (b : R) : (UnitBinomial' hg hgg' ha b).val = single g (IsUnit.unit ha).val + single g' b :=
  rfl
/-!
theorem UnitBinimial_inv_coeff {g g' : Γ} (hg : IsAddUnit g) (hgg' : g < g') {a : R} (ha : IsUnit a)
    (b : R) : (UnitBinomial hg hgg' ha b).inv = sorry := --hsum
  sorry -- induction, telescoping.
-/
/-- A function for describing coefficients of powers of invertible binomials. -/
def UnitBinomialPow_coeff_aux {a : R} (ha : IsUnit a) (b : R) (n : ℤ) :
    ℕ → R := fun k => (IsUnit.unit ha) ^ (n - k) • b ^ k • Ring.choose n k

end Binomial

section OneSubSingle -- may be superfluous

--theorem xxx [CommRing R] : IsUnit (1 : R) := by exact isUnit_one

-- if k ∈ Monoid.closure g, then ... else 0

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R]

theorem supp_one_sub_single {g : Γ} (r : R) :
    (1 - single g r).support ⊆ {0, g} := by
  refine support_add_subset.trans ?_
  simp_all only [support_neg, Set.union_subset_iff]
  constructor
  · by_cases h : Nontrivial R
    · rw [support_one]
      exact Set.singleton_subset_iff.mpr (Set.mem_insert 0 {g})
    · rw [not_nontrivial_iff_subsingleton, subsingleton_iff] at h
      exact Set.compl_subset_compl.mp fun ⦃a⦄ _ a_2 ↦ a_2 (h (coeff 1 a) 0)
  · exact support_single_subset.trans (Set.subset_insert 0 {g})

theorem orderTop_one_sub_single [Nontrivial R] {g : Γ} (hg : 0 < g) (r : R) :
    (1 - single g r).orderTop = 0 := by
  rw [orderTop_sub, orderTop_one]
  rw [orderTop_one]
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hg) orderTop_single_le

theorem leadingCoeff_one_sub_single {g : Γ} (hg : 0 < g) (r : R) :
    (1 - single g r).leadingCoeff = 1 := by
  by_cases h : Nontrivial R
  · rw [leadingCoeff_sub, leadingCoeff_one]
    rw [orderTop_one]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hg) orderTop_single_le
  · rw [not_nontrivial_iff_subsingleton] at h
    exact Subsingleton.eq_one (leadingCoeff (1 - (single g) r))

theorem coeff_mul_one_sub_single {x : HahnSeries Γ R} {g g' : Γ} {r : R} :
    (x * (1 - single g r)).coeff (g + g') = x.coeff (g + g') - r * x.coeff g' := by
  rw [mul_one_sub, coeff_sub, Pi.sub_apply, sub_right_inj, add_comm, coeff_mul_single_add, mul_comm]

/-!
theorem support_one_sub_single_npow_zero {g : Γ} {r : R} {n : ℕ} :
    ((1 - single g r) ^ n).support ⊆ AddSubmonoid.closure {0, g} :=
  (support_pow_subset_closure (1 - (single g) r) n).trans
    (AddSubmonoid.closure_mono (supp_one_sub_single r))

theorem support_one_sub_single_npow (g : Γ) (r : R) {n : ℕ} :
    ((1 - single g r) ^ n).support ⊆ AddSubmonoid.closure {g} :=
  support_one_sub_single_npow_zero.trans AddSubmonoid.closure_insert_zero
-/

theorem _root_.AddSubmonoid.neg_not_in_closure {Γ} [OrderedAddCommMonoid Γ] {g g' : Γ} (hg : 0 ≤ g)
    (hg' : g' < 0) : ¬ g' ∈ AddSubmonoid.closure {g} := by
  rw [AddSubmonoid.mem_closure_singleton, not_exists]
  intro k hk
  have hgk : 0 ≤ k • g :=
    nsmul_nonneg hg k
  rw [hk] at hgk
  exact (lt_self_iff_false 0).mp (lt_of_le_of_lt hgk hg')
--#find_home AddSubmonoid.neg_not_in_closure --[Mathlib.GroupTheory.Submonoid.Membership]

/-!
theorem coeff_one_sub_single_pow_of_neg {g g' : Γ} (hg : 0 ≤ g) (hg' : g' < 0) {r : R} {n : ℕ} :
    ((1 - single g r) ^ n).coeff g' = 0 := by
  by_contra h
  rw [← ne_eq, ← mem_support] at h
  apply (AddSubmonoid.neg_not_in_closure hg hg')
    (Set.mem_of_subset_of_mem (support_one_sub_single_npow g r) h)

theorem coeff_one_sub_single_pow_of_add_eq_zero {g g' : Γ} (hg : 0 < g) (hgg' : g + g' = 0) {r : R}
    {n : ℕ} : ((1 - single g r) ^ n).coeff g' = 0 := by
  have hg' : g' < 0 := by
    rw [← hgg']
    exact (lt_add_iff_pos_left g').mpr hg
  exact coeff_one_sub_single_pow_of_neg (le_of_lt hg) hg'
-/
theorem coeff_single_mul_of_no_add {x : HahnSeries Γ R} {a b : Γ} {r : R} (hab : ¬∃c, c + a = b) :
    (x * single a r).coeff b = 0 := by
  rw [coeff_mul]
  trans Finset.sum ∅ fun (ij : Γ × Γ) => x.coeff ij.fst * (single a r).coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp_all [mem_addAntidiagonal, coeff_single]
  · exact rfl
--#find_home! coeff_single_mul_of_no_add --[Mathlib.RingTheory.HahnSeries.Multiplication]
/-!
theorem coeff_zero_one_sub_single_npow {g : Γ} (hg : 0 < g) {r : R} {n : ℕ} :
    ((1 - single g r) ^ n).coeff 0 = 1 := by
  by_cases hr : r = 0; · rw [hr, single_eq_zero, sub_zero, one_pow, one_coeff, if_pos rfl]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    by_cases hg' : ∃ g' : Γ, g + g' = 0
    · rw [← hg'.choose_spec, coeff_mul_one_sub_single, hg'.choose_spec, ih, sub_eq_self,
        coeff_one_sub_single_pow_of_add_eq_zero hg hg'.choose_spec, mul_zero]
    · rw [mul_one_sub, coeff_sub, Pi.sub_apply, ih, sub_eq_self, coeff_single_mul_of_no_add]
      simp_all [add_comm]

theorem coeff_one_sub_single_npow {g : Γ} (hg : 0 < g) (r : R) {k n : ℕ}:
    ((1 - single g r) ^ n).coeff (k • g) = (-1) ^ k • (Nat.choose n k) • (r ^ k) := by
  induction' n with n ihn generalizing k
  · simp only [Nat.zero_eq, zero_smul, Int.reduceNeg, pow_zero, Nat.choose_zero_right, one_smul]
    induction' k with k
    · simp
    · simp only [Nat.zero_eq, pow_zero, one_coeff, Int.reduceNeg, Nat.choose_zero_succ, zero_smul,
      smul_zero, ite_eq_right_iff]
      have hkg : ¬ Nat.succ k • g = 0 :=
        ne_comm.mp <| ne_of_lt <| (nsmul_pos_iff (Nat.succ_ne_zero k)).mpr hg
      simp_all only [Nat.zero_eq, pow_zero, one_coeff, nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow,
        Int.cast_neg, Int.cast_one, IsEmpty.forall_iff]
  · induction' k with k
    · simp only [Nat.zero_eq, zero_smul, Int.reduceNeg, pow_zero, Nat.choose_zero_right, one_smul]
      exact coeff_zero_one_sub_single_npow hg
    · have hkg : Nat.succ k • g = g + k • g := by
        rw [← Nat.add_one, add_smul, one_smul, add_comm _ g]
      rw [pow_succ, hkg, coeff_mul_one_sub_single, ← hkg, ihn, ihn, Nat.choose_succ_succ,
        sub_eq_add_neg, neg_mul_eq_mul_neg, pow_succ', pow_succ']
      simp only [Int.reduceNeg, neg_mul, one_mul, nsmul_eq_mul, neg_smul, zsmul_eq_mul,
        Int.cast_pow, Int.cast_neg, Int.cast_one, mul_neg, Nat.cast_add]
      ring_nf

--redundant
theorem zero_lt_orderTop_single {g : Γ} (hg : 0 < g) (r : R) : 0 < (single g r).orderTop :=
  lt_orderTop_single hg

theorem one_sub_single_inv_eq_powers {g : Γ} (hg : 0 < g) {r : R} :
    (IsUnit.unit (isUnit_one_sub_single hg r)).inv =
    (SummableFamily.powers (zero_lt_orderTop_single hg r)).hsum := by
  rw [Units.inv_eq_val_inv, ← Units.mul_eq_one_iff_inv_eq, IsUnit.unit_spec]
  exact SummableFamily.one_sub_self_mul_hsum_powers (zero_lt_orderTop_single hg r)

theorem coeff_one_sub_single_inv {g : Γ} (hg : 0 < g) {r : R} {k : ℕ} :
    (IsUnit.unit (isUnit_one_sub_single hg r)).inv.coeff (k • g) = r ^ k := by
  rw [one_sub_single_inv_eq_powers hg, SummableFamily.coeff_hsum, SummableFamily.coe_powers,
    finsum_eq_single (fun i => ((single g) r ^ i).coeff (k • g)) k]
  · simp only [single_pow, coeff_single_same]
  intro i hi
  rw [single_pow, coeff_single_of_ne]
  rw [ne_iff_lt_or_gt] at hi
  cases hi with
  | inl hik => exact Ne.symm (ne_of_lt (nsmul_lt_nsmul_left hg hik))
  | inr hki => exact ne_of_lt (nsmul_lt_nsmul_left hg hki)

theorem coeff_one_sub_single_neg_pow {g : Γ} (hg : 0 < g) {r : R} {n k : ℕ} :
    ((IsUnit.unit (isUnit_one_sub_single hg r)) ^ (-n : ℤ)).val.coeff (k • g) =
    Nat.choose (n + k - 1) k • (-r) ^ k := by
  induction' n with n ihn generalizing k
  · simp only [Nat.zero_eq, Nat.cast_zero, neg_zero, zpow_zero, Units.val_one, one_coeff,
      nsmul_eq_mul]
    induction' k with k ihk
    · simp
    · simp only [zero_add, Nat.succ_sub_succ_eq_sub, tsub_zero, Nat.choose_succ_self,
      Nat.cast_zero, zero_mul, ite_eq_right_iff]
      intro hkg
      have h : 0 < Nat.succ k • g := nsmul_pos hg (Ne.symm (NeZero.ne' (Nat.succ k)))
      simp_all
  · simp_all only [nsmul_eq_mul, neg_add_rev, Nat.succ_add_sub_one]
    sorry

-- change this to cases, do induction in separate results?
theorem coeff_one_sub_single_zpow {g : Γ} (hg : 0 < g) {r : R} {n : ℤ} : ∀(k : ℕ),
    ((IsUnit.unit (isUnit_one_sub_single hg r)) ^ n).val.coeff (k • g) =
      (-r) ^ k • Ring.choose n k := by
  refine Int.induction_on n ?_ ?_ ?_
  · exact fun k => by
      rw [zpow_zero]
      by_cases hk : k = 0
      · simp [hk]
      · simp [Ring.choose_zero_pos ℤ k (Nat.pos_iff_ne_zero.mpr hk)]
        have hkg : 0 < k • g := (nsmul_pos_iff hk).mpr hg
        have hkg' : ¬ k • g = 0 := fun h => by simp_all only [lt_self_iff_false]
        exact fun a ↦ (hkg' a).elim
  · intro n h k
    norm_cast
    simp only [zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    rw [coeff_one_sub_single_npow hg, Ring.choose_eq_Nat_choose, smul_algebra_smul_comm,
      ← smul_pow, smul_eq_mul, mul_comm]
    simp
  · intro n h
    simp_all only [zpow_neg, zpow_natCast, smul_eq_mul]

    sorry
-/

end OneSubSingle

end HahnSeries
