/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
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

--@[simp]
theorem binomial_power {x : orderTopSubOnePos Γ R} {r : R} :
    x ^ r = toOrderTopSubOnePos (orderTop_hsum_binomialFamily_pos x.2 r) :=
  rfl

theorem pow_add {x : orderTopSubOnePos Γ R} {r s : R} : x ^ (r + s) = x ^ r * x ^ s := by
  suffices (x ^ (r + s)).val = (x ^ r * x ^ s).val by exact SetLike.coe_eq_coe.mp this
  suffices (x ^ (r + s)).val.val = (x ^ r * x ^ s).val.val by exact Units.val_inj.mp this
  simp [binomialFamily, binomial_power, hsum_powerSeriesFamily_mul, hsum_mul]

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

/- These don't seem to be necessary.
omit [BinomialRing R] in
theorem support_toOrderTopSubOnePos_orderTopSubOnePos {g : Γ} (hg : 0 < g) (r : R) :
     ((toOrderTopSubOnePos (orderTop_sub_pos hg r)).val.val).support ⊆ {0, g} := by
  simp only [val_toOrderTopSubOnePos_coe]
  refine (support_add_subset (x := (1 : R⟦Γ⟧))).trans ?_
  refine Set.union_subset ?_ (support_single_subset.trans (Set.subset_insert 0 {g}))
  obtain (_| h ) := subsingleton_or_nontrivial R
  · simp [(Subsingleton.eq_one (0 : R⟦Γ⟧)).symm]
  · simp

omit [BinomialRing R] in
theorem support_toOrderTopSubOnePos_orderTopSubOnePos_pow {g : Γ} (hg : 0 < g) (r : R) (n : ℕ) :
    ((toOrderTopSubOnePos (orderTop_sub_pos hg r)).val.val ^ n).support ⊆
      AddSubmonoid.closure {g} := by
    refine (support_pow_subset_closure (toOrderTopSubOnePos (orderTop_sub_pos hg r)).val.val
      n).trans ?_
    rw [SetLike.coe_subset_coe, val_toOrderTopSubOnePos_coe, AddSubmonoid.closure_le]
    exact (support_toOrderTopSubOnePos_orderTopSubOnePos hg r).trans
      (Set.pair_subset (zero_mem (AddSubmonoid.closure {g}))
      (SetLike.mem_coe.mpr (AddSubmonoid.mem_closure_of_mem rfl)))
-/

theorem coeff_toOrderTopSubOnePos_pow_not_nsmul {g g' : Γ} (hg : 0 < g) (r s : R)
    (hgg' : ¬ ∃ n : ℕ, g' = n • g) :
    HahnSeries.coeff ((toOrderTopSubOnePos (orderTop_sub_pos hg r)) ^ s).val g' = (0 : R) := by
  rw [binomial_power, val_toOrderTopSubOnePos_coe, val_toOrderTopSubOnePos_coe, coeff_hsum,
    finsum_eq_zero_of_forall_eq_zero]
  intro i
  rw [binomialFamily_apply (orderTop_sub_pos hg r), coeff_smul, add_sub_cancel_left, single_pow]
  rw [not_exists] at hgg'
  exact smul_eq_zero_of_right (Ring.choose s i) (coeff_single_of_ne (hgg' i))

theorem heval_single_binomialSeries {g : Γ} (hg : 0 < g) (r s : R) :
    PowerSeries.heval (single g r) (PowerSeries.binomialSeries R s) =
    ((toOrderTopSubOnePos (orderTop_sub_pos hg r)) ^ s).val := by
  ext g'
  simp only [PowerSeries.heval_apply, coeff_hsum, smulFamily_toFun,
    PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one, powers_toFun, ite_pow, single_pow,
    smul_ite, smul_single]
  by_cases h : ∃ k : ℕ, g' = k • g
  · obtain ⟨k, hk⟩ := h
    rw [hk, coeff_toOrderTopSubOnePos_pow hg r s k]
    have : (0 : WithTop Γ) < (single g r).orderTop := lt_orderTop_single hg
    simp only [this, ↓reduceIte, coeff_single, smul_eq_mul]
    rw [finsum_eq_single _ k]
    · simp
    · intro i hi
      contrapose! hi
      simp only [ne_eq, ite_eq_right_iff, Classical.not_imp] at hi
      exact Nat.le_antisymm ((smul_le_smul_iff_of_pos_right hg).mp (ge_of_eq hi.1))
        ((smul_le_smul_iff_of_pos_right hg).mp (le_of_eq hi.1)) -- missing API?
  · rw [finsum_eq_zero_of_forall_eq_zero, coeff_toOrderTopSubOnePos_pow_not_nsmul hg r s h]
    intro i
    simp only [lt_of_lt_of_le (WithTop.coe_pos.mpr hg) orderTop_single_le, ↓reduceIte]
    rw [not_exists] at h
    refine coeff_single_of_ne (h i)

/-
(xy-1)^n = ((x-1)(y-1) + (x-1) + (y-1))^n
  = ∑(i+j+k=n) trinomial{n}{i,j,k} (x-1)^(i+j) (y-1)^(i+k)
Have:
∑(n) binom{r}{n} ∑(i+j+k=n) trinomial{n}{i,j,k} (x-1)^(i+j) (y-1)^(i+k)
  = ∑(i,j,k) binom{r}{i+j+k} trinomial{i+j+k}{i,j,k} (x-1)^(i+j) (y-1)^(i+k)
  = ∑(j) (x-1)^j ∑(k) (y-1)^k ∑(i ≤ min(j,k)) binom{r}{j+k-i} trinomial{j+k-i}{i,j-i,k-i}
  = ∑(i) binom{r}{i} (x-1)^i * ∑(j) binom{r}{j} (y-1)^j
Assuming :
  ∑(i ≤ min(j,k)) binom{r}{j+k-i} trinomial{j+k-i}{i,j-i,k-i} = binom{r}{j} binom{r}{k}
WLoG j ≤ k.
Induct on j?
j=0 i=0 : binom{r}{k} = binom{r}{k}
descPochhammer r k/(j+1)!(k-j-1)! + ∑(i ≤ min(j,k)) descPochhammer r (j+1+k-i) / i! (j+1-i)!(k-i)! -
  descPochhammer r (j+k-i) / i! (j-i)!(k-i)! =
  (binom{r}{j+1} - binom{r}{j}) binom{r}{k}
descPochhammer r (j+1+k-i) / i! (j+1-i)!(k-i)! - descPochhammer r (j+k-i) / i! (j-i)!(k-i)! =


Induct on k?
k=0 : 1 = 1
show: ∑(i ≤ j) binom{r}{j+k+1-i} trinomial{j+k+1-i}{i,j-i,k-i+1} -
  binom{r}{j+k-i} trinomial{j+k-i}{i,j-i,k-i} = binom{r}{j} (binom{r}{k+1} - binom{r}{k})

r!/(r-j-k-1+i)!i!(j-i)!(k-i+1)! - r!/(r-j-k+i)!i!(j-i)!(k-i)! =
  ((r-j-k+i)/(k-i+1) - 1)r!/(r-j-k+i)!i!(j-i)!(k-i)! =
  ((r-j-2k+2i-1)/(k-i+1))(r!/(r-j)!j!)(r-j)!j!/(r-j-k+i)!i!(j-i)!(k-i)! =
  binom{r}{j} binom{j}{i} binom{r-j}{k-i} (r-j-2k+2i-1)/(k-i+1)

Elliot's argument: These identities hold for natural number powers, and the coefficients
of (x - 1)^n in x^r are integer-valued polynomials in r. Therefore, identities follow from the fact
that integer-valued polynomials are uniquely determined by their evaluations at natural numbers.

theorem mul_pow {x y : orderTopSubOnePos Γ R} {r : R} : (x * y) ^ r = x ^ r * y ^ r := by
  suffices ((x * y) ^ r).val = (x ^ r * y ^ r).val by exact SetLike.coe_eq_coe.mp this
  suffices ((x * y) ^ r).val.val = (x ^ r * y ^ r).val.val by exact Units.val_inj.mp this
  have hx : 0 < (x.val.val - 1).orderTop := (mem_orderTopSubOnePos_iff x.val).mp (SetLike.coe_mem x)
  have hy : 0 < (y.val.val - 1).orderTop := (mem_orderTopSubOnePos_iff y.val).mp (SetLike.coe_mem y)
  have hxy : 0 < (x.val.val * y.val.val - 1).orderTop := by
    rw [← Units.val_mul, ← Subgroup.coe_mul]
    exact (mem_orderTopSubOnePos_iff (x * y).val).mp (SetLike.coe_mem (x * y))
  simp only [binomial_power, binomialFamily, Subgroup.coe_mul, Units.val_mul,
    val_toOrderTopSubOnePos_coe]
  simp only [powerSeriesFamily, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
  rw [← hsum_mul]
  simp [smulFamily, hx, hy, hxy]

  have hxysub : x.val.val * y.val.val - 1 =
      (x.val.val - 1) * (y.val.val - 1) + (x.val.val - 1) + (y.val.val - 1) := by ring
  simp_rw [hxysub]

  sorry

theorem pow_mul {x : orderTopSubOnePos Γ R} {r s : R} : x ^ (r * s) = (x ^ r) ^ s := by
  suffices (x ^ (r * s)).val = ((x ^ r) ^ s).val by exact SetLike.coe_eq_coe.mp this
  suffices (x ^ (r * s)).val.val = ((x ^ r) ^ s).val.val by exact Units.val_inj.mp this
  simp only [binomial_power, binomialFamily, val_toOrderTopSubOnePos_coe]
  sorry
 -/

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
