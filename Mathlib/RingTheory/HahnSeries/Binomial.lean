/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.RingTheory.HahnSeries.HEval
public import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# Hahn Series expansions of powers of binomials
We introduce generalized powers of certain binomials in Hahn series. Recall that
Hahn series are formal power series `Γ → A` where the exponent set `Γ` is partially ordered, and the
support is partially well-ordered. In this file, we consider the case where one has an action of a
binomial ring `R` on both `Γ` and `A`. Here, a binomial ring is a ring `R` that admits a uniquely
defined notion of binomial coefficient `Ring.choose r n` for all `r` in `R` and natural numbers `n`.
Using a binomial series expansion, this allows us to define generalized powers of the
form `(x - y)^r`, where `x` and `y` are Hahn series with singleton support.
One application of these binomial powers is to the theory of vertex algebras, where one often
encounters expressions in the abbreviated form `(x-y)^n A(x)B(y)`, where `n` is an integer,
`A : V → V((x))` and `B : V → V((y))` are linear maps to Laurent series spaces. This is expanded
as a linear map `V → V((x))((y))` once `(x-y)^n` is rewritten as `x^n(1 - y/x)^n` and `A(x)` is
extended to a map `V((y)) → V((x))((y))` by operating on coefficients.
## Main Definitions
  * `HahnSeries.binomialFamily` is a summable family whose formal sum is an expansion of `x ^ r` as
  `(1 + (x - 1)) ^ r`, when `x - 1` has strictly positive order.
  * `HahnSeries.binomialPow` describes powers of a binomial of the form `single g 1 - single g' 1`,
  where the powers take values in a binomial ring.
## Main results
  * `HahnSeries.binomialPow_add` asserts that adding exponents amounts to multiplying the
  corresponding formal powers of binomial series.
  * `HahnSeries.binomialPow_nat` asserts that natural number powers are given by the usual iterated
  multiplication of Hahn series.
## TODO
  * `HahnSeries.coeff_binomialPow_smul_add` :
    `(binomialPow A g g' a r).coeff (r • g + n • (g' - g)) = Int.negOnePow n • Ring.choose r n • 1`
    (proved in a WIP PR)
-/

@[expose] public section

noncomputable section

namespace HahnSeries

open Finset BigOperators

variable {Γ R A : Type*}

section orderTopOneSubPos

variable [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
  [BinomialRing R]

namespace SummableFamily

variable [CommRing A] [Algebra R A]

/-- A summable family of Hahn series, whose `n`th term is `Ring.choose r n • (x - 1) ^ n` when
`x` is close to `1` (more precisely, when `0 < (x - 1).orderTop`), and `0 ^ n` otherwise. These
terms give a formal expansion of `x ^ r` as `(1 + (x - 1)) ^ r`. -/
def binomialFamily (x : HahnSeries Γ A) (r : R) :
    SummableFamily Γ A ℕ :=
  powerSeriesFamily (x - 1) (PowerSeries.binomialSeries A r)

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
  simp only [binomialFamily, smulFamily_toFun, PowerSeries.binomialSeries_coeff, powers_toFun, hx,
    ↓reduceIte, smul_assoc, one_smul]
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

end orderTopOneSubPos

section BinomialPow

variable [LinearOrder Γ] [AddCommGroup Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R] [BinomialRing R]
[Module R Γ] [CommRing A] [Algebra R A]

/-- A Hahn series formally expanding `(X g + a X g') ^ r` where `r` is an element of a binomial ring
`R` and `a` is an element of an `R`-algebra. We require `g` and `g'` to lie in an ordered
`R`-module. -/
def binomialPow (g g' : Γ) (a : A) (r : R) : HahnSeries Γ A :=
  single (r • g) (1 : A) *
    (PowerSeries.heval ((single (g' - g)) (a : A)) (PowerSeries.binomialSeries A r))

theorem binomialPow_apply (g g' : Γ) (a : A) (r : R) :
    binomialPow g g' a r = single (r • g) 1 *
      (PowerSeries.heval ((single (g' - g)) (a : A)) (PowerSeries.binomialSeries A r)) :=
  rfl

theorem binomialPow_apply_of_not_gt {g g' : Γ} (h : ¬ g < g') (a : A) (r : R) :
    binomialPow g g' a r = single (r • g) (1 : A) := by
  by_cases ha : a = 0
  · simp [ha, binomialPow_apply]
  · have : ¬ 0 < (single (g' - g) (a : A)).orderTop := by
      rwa [orderTop_single ha, WithTop.coe_pos, sub_pos]
    simp [binomialPow_apply, PowerSeries.heval_of_orderTop_not_pos _ this]

@[simp]
theorem binomialPow_zero {g g' : Γ} (a : A) :
    binomialPow g g' a (0 : R) = single 0 (1 : A) := by
  by_cases h : g < g'
  · simp [binomialPow_apply, OneHomClass.map_one]
  · simp [binomialPow_apply_of_not_gt h a (0 : R)]

theorem binomialPow_add {g g' : Γ} (a : A) (r r' : R) :
    binomialPow g g' a r * binomialPow g g' a r' =
      binomialPow g g' a (r + r') := by
  simp only [binomialPow, PowerSeries.binomialSeries_add, PowerSeries.heval_mul, add_smul]
  rw [mul_left_comm, ← mul_assoc, ← mul_assoc, single_mul_single, mul_one, add_comm, ← mul_assoc]

theorem binomialPow_one {g g' : Γ} (h : g < g') (a : A) :
    binomialPow g g' a (Nat.cast (R := R) 1) = ((single g) (1 : A) + (single g') a) := by
  rw [binomialPow_apply, PowerSeries.binomialSeries_nat 1, pow_one, map_add,
    PowerSeries.heval_X _ (pos_orderTop_single_sub h a), ← RingHom.map_one PowerSeries.C,
    PowerSeries.heval_C _, one_smul, mul_add, mul_one, single_mul_single, one_mul,
    Nat.cast_one, one_smul, add_sub_cancel]

theorem binomialPow_nat {g g' : Γ} (h : g < g') (a : A) (n : ℕ) :
    binomialPow g g' a (n : R) = ((single g (1 : A)) + single g' a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, ← binomialPow_add, _root_.pow_add, ih, binomialPow_one h, pow_one]

theorem binomialPow_one_sub {g₀ g₁ g₂ : Γ} (h₀₁ : g₀ < g₁) (h₁₂ : g₁ < g₂) (a : A) :
    binomialPow g₀ g₁ (a : A) (Nat.cast (R := R) 1) + (-a) •
      binomialPow g₁ g₂ a (Nat.cast (R := R) 1) =
      binomialPow g₀ g₂ (-a * a) (Nat.cast (R := R) 1) := by
  rw [binomialPow_one h₀₁, binomialPow_one h₁₂, binomialPow_one (h₀₁.trans h₁₂), add_assoc,
    smul_add, ← add_assoc (single g₁ a), smul_single, ← single_add]
  simp

theorem binomialPow_coeff_eq {g g' : Γ} (h : g < g') (a : A) (r : R) (n : ℕ) :
    (binomialPow g g' a r).coeff (r • g + n • (g' - g)) =
      a ^ n • Ring.choose r n • 1 := by
  simp only [binomialPow_apply, PowerSeries.heval_apply]
  rw [add_comm, HahnSeries.coeff_single_mul_add, one_mul]
  simp only [SummableFamily.coeff_hsum, SummableFamily.smulFamily_toFun,
    PowerSeries.binomialSeries_coeff, smul_eq_mul, coeff_smul]
  rw [finsum_eq_single _ n, SummableFamily.powers_of_orderTop_pos
    (pos_orderTop_single_sub h a) n, single_pow, coeff_single_same, mul_comm]
  · intro m hmn
    rw [SummableFamily.powers_of_orderTop_pos (pos_orderTop_single_sub h a) m, single_pow,
      coeff_single_of_ne, mul_zero]
    obtain h' | h' | h' := lt_trichotomy m n
    · exact ne_of_gt <| nsmul_lt_nsmul_left (sub_pos.mpr h) h'
    · exact (hmn h').elim
    · exact ne_of_lt <| nsmul_lt_nsmul_left (sub_pos.mpr h) h'

theorem binomialPow_coeff_eq_zero {g g' g'' : Γ} (h : g < g') (a : A) (r : R)
    (hg'' : ∀ (n : ℕ), ¬r • g + n • (g' - g) = g'') :
    (binomialPow g g' a r).coeff g'' = 0 := by
  simp only [binomialPow_apply, PowerSeries.heval_apply]
  rw [← sub_add_cancel g'' (r • g), HahnSeries.coeff_single_mul_add, one_mul]
  simp only [SummableFamily.coeff_hsum, SummableFamily.smulFamily_toFun,
    PowerSeries.binomialSeries_coeff, smul_assoc, one_smul, coeff_smul]
  rw [finsum_eq_zero_of_forall_eq_zero]
  intro m
  refine smul_eq_zero_of_right (Ring.choose r m) ?_
  rw [SummableFamily.powers_of_orderTop_pos (pos_orderTop_single_sub h a) m, single_pow,
    coeff_single_of_ne]
  contrapose! hg''
  use m
  rw [sub_eq_iff_eq_add'] at hg''
  rw [hg'']

end BinomialPow

end HahnSeries
