/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.SmoothNumbers

/-!
# Euler Products

The main result in this file is `EulerProduct.eulerProduct_hasProd`, which says that
if `f : ℕ → R` is norm-summable, where `R` is a complete normed commutative ring and `f` is
multiplicative on coprime arguments with `f 0 = 0`, then
`∏' p : Primes, ∑' e : ℕ, f (p^e)` converges to `∑' n, f n`.

`ArithmeticFunction.IsMultiplicative.eulerProduct_hasProd` is a version
for multiplicative arithmetic functions in the sense of
`ArithmeticFunction.IsMultiplicative`.

There is also a version `EulerProduct.eulerProduct_completely_multiplicative_hasProd`,
which states that `∏' p : Primes, (1 - f p)⁻¹` converges to `∑' n, f n`
when `f` is completely multiplicative with values in a complete normed field `F`
(implemented as `f : ℕ →*₀ F`).

There are variants stating the equality of the infinite product and the infinite sum
(`EulerProduct.eulerProduct_tprod`, `ArithmeticFunction.IsMultiplicative.eulerProduct_tprod`,
`EulerProduct.eulerProduct_completely_multiplicative_tprod`) and also variants stating
the convergence of the sequence of partial products over primes `< n`
(`EulerProduct.eulerProduct`, `ArithmeticFunction.IsMultiplicative.eulerProduct`,
`EulerProduct.eulerProduct_completely_multiplicative`.)

An intermediate step is `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum`
(and its variant `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric`),
which relates the finite product over primes `p ∈ s` to the sum of `f n` over `s`-factored `n`,
for `s : Finset ℕ`.

## Tags

Euler product, multiplicative function
-/
set_option backward.defeqAttrib.useBackward true

public section

/-- If `f` is multiplicative and summable, then its values at natural numbers `> 1`
have norm strictly less than `1`. -/
lemma Summable.norm_lt_one {F : Type*} [NormedDivisionRing F] [CompleteSpace F] {f : ℕ →* F}
    (hsum : Summable f) {p : ℕ} (hp : 1 < p) :
    ‖f p‖ < 1 := by
  refine summable_geometric_iff_norm_lt_one.mp ?_
  simp_rw [← map_pow]
  exact hsum.comp_injective <| Nat.pow_right_injective hp

open scoped Topology

open Nat Finset

section General

/-!
### General Euler Products

In this section we consider multiplicative (on coprime arguments) functions `f : ℕ → R`,
where `R` is a complete normed commutative ring. The main result is `EulerProduct.eulerProduct`.
-/

variable {R : Type*} [NormedCommRing R] {f : ℕ → R}

-- local instance to speed up typeclass search
@[local instance] private lemma instT0Space : T0Space R := MetricSpace.instT0Space

variable [CompleteSpace R]

namespace EulerProduct

variable (hf₁ : f 1 = 1) (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)

include hf₁ hmul in
/-- We relate a finite product over primes in `s` to an infinite sum over `s`-factored numbers. -/
lemma summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ ↦ ‖f (p ^ n)‖)) (s : Finset ℕ) :
    Summable (fun m : factoredNumbers s ↦ ‖f m‖) ∧
      HasSum (fun m : factoredNumbers s ↦ f m)
        (∏ p ∈ s with p.Prime, ∑' n : ℕ, f (p ^ n)) := by
  induction s using Finset.induction with
  | empty =>
    rw [factoredNumbers_empty]
    simp only [notMem_empty, IsEmpty.forall_iff, forall_const, filter_true_of_mem, prod_empty]
    exact ⟨(Set.finite_singleton 1).summable (‖f ·‖), hf₁ ▸ hasSum_singleton 1 f⟩
  | insert p s hp ih =>
    rw [filter_insert]
    split_ifs with hpp
    · constructor
      · simp only [← (equivProdNatFactoredNumbers hpp hp).summable_iff, Function.comp_def,
          equivProdNatFactoredNumbers_apply', factoredNumbers.map_prime_pow_mul hmul hpp hp]
        refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_mul_le ..) ?_
        apply Summable.mul_of_nonneg (hsum hpp) ih.1 <;> exact fun n ↦ norm_nonneg _
      · have hp' : p ∉ {p ∈ s | p.Prime} := mt (mem_of_mem_filter p) hp
        rw [prod_insert hp', ← (equivProdNatFactoredNumbers hpp hp).hasSum_iff, Function.comp_def]
        conv =>
          enter [1, x]
          rw [equivProdNatFactoredNumbers_apply', factoredNumbers.map_prime_pow_mul hmul hpp hp]
        have : T3Space R := instT3Space -- speeds up the following
        apply (hsum hpp).of_norm.hasSum.mul ih.2
        -- `exact summable_mul_of_summable_norm (hsum hpp) ih.1` gives a time-out
        apply summable_mul_of_summable_norm (hsum hpp) ih.1
    · rwa [factoredNumbers_insert s hpp]

include hf₁ hmul in
/-- A version of `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum`
in terms of the value of the series. -/
lemma prod_filter_prime_tsum_eq_tsum_factoredNumbers (hsum : Summable (‖f ·‖)) (s : Finset ℕ) :
    ∏ p ∈ s with p.Prime, ∑' n : ℕ, f (p ^ n) = ∑' m : factoredNumbers s, f m :=
  (summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf₁ hmul
    (fun hp ↦ hsum.comp_injective <| Nat.pow_right_injective hp.one_lt) _).2.tsum_eq.symm

/-- The following statement says that summing over `s`-factored numbers such that
`s` contains `primesBelow N` for large enough `N` gets us arbitrarily close to the sum
over all natural numbers (assuming `f` is summable and `f 0 = 0`; the latter since
`0` is not `s`-factored). -/
lemma norm_tsum_factoredNumbers_sub_tsum_lt (hsum : Summable f) (hf₀ : f 0 = 0) {ε : ℝ}
    (εpos : 0 < ε) :
    ∃ N : ℕ, ∀ s : Finset ℕ, primesBelow N ≤ s →
      ‖(∑' m : ℕ, f m) - ∑' m : factoredNumbers s, f m‖ < ε := by
  obtain ⟨N, hN⟩ :=
    summable_iff_nat_tsum_vanishing.mp hsum (Metric.ball 0 ε) <| Metric.ball_mem_nhds 0 εpos
  simp_rw [mem_ball_zero_iff] at hN
  refine ⟨N, fun s hs ↦ ?_⟩
  have := hN _ <| factoredNumbers_compl hs
  rwa [← hsum.tsum_subtype_add_tsum_subtype_compl (factoredNumbers s),
    add_sub_cancel_left, tsum_eq_tsum_diff_singleton (factoredNumbers s)ᶜ hf₀]

-- Versions of the three lemmas above for `smoothNumbers N`

include hf₁ hmul in
/-- We relate a finite product over primes to an infinite sum over smooth numbers. -/
lemma summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ ↦ ‖f (p ^ n)‖)) (N : ℕ) :
    Summable (fun m : N.smoothNumbers ↦ ‖f m‖) ∧
      HasSum (fun m : N.smoothNumbers ↦ f m) (∏ p ∈ N.primesBelow, ∑' n : ℕ, f (p ^ n)) := by
  rw [smoothNumbers_eq_factoredNumbers, primesBelow]
  exact summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf₁ hmul hsum _

include hf₁ hmul in
/-- A version of `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum`
in terms of the value of the series. -/
lemma prod_primesBelow_tsum_eq_tsum_smoothNumbers (hsum : Summable (‖f ·‖)) (N : ℕ) :
    ∏ p ∈ N.primesBelow, ∑' n : ℕ, f (p ^ n) = ∑' m : N.smoothNumbers, f m :=
  (summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf₁ hmul
    (fun hp ↦ hsum.comp_injective <| Nat.pow_right_injective hp.one_lt) _).2.tsum_eq.symm

/-- The following statement says that summing over `N`-smooth numbers
for large enough `N` gets us arbitrarily close to the sum over all natural numbers
(assuming `f` is norm-summable and `f 0 = 0`; the latter since `0` is not smooth). -/
lemma norm_tsum_smoothNumbers_sub_tsum_lt (hsum : Summable f) (hf₀ : f 0 = 0)
    {ε : ℝ} (εpos : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ‖(∑' m : ℕ, f m) - ∑' m : N.smoothNumbers, f m‖ < ε := by
  conv => enter [1, N₀, N]; rw [smoothNumbers_eq_factoredNumbers]
  obtain ⟨N₀, hN₀⟩ := norm_tsum_factoredNumbers_sub_tsum_lt hsum hf₀ εpos
  refine ⟨N₀, fun N hN ↦ hN₀ (range N) fun p hp ↦ ?_⟩
  exact mem_range.mpr <| (lt_of_mem_primesBelow hp).trans_le hN


include hf₁ hmul in
/-- The *Euler Product* for multiplicative (on coprime arguments) functions.

If `f : ℕ → R`, where `R` is a complete normed commutative ring, `f 0 = 0`, `f 1 = 1`, `f` is
multiplicative on coprime arguments, and `‖f ·‖` is summable, then
`∏' p : Nat.Primes, ∑' e, f (p ^ e) = ∑' n, f n`. This version is stated using `HasProd`. -/
theorem eulerProduct_hasProd (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    HasProd (fun p : Primes ↦ ∑' e, f (p ^ e)) (∑' n, f n) := by
  let F : ℕ → R := fun n ↦ ∑' e, f (n ^ e)
  change HasProd (F ∘ Subtype.val (p := (· ∈ {x | Nat.Prime x}))) _
  rw [hasProd_subtype_iff_mulIndicator, HasProd, SummationFilter.unconditional,
    Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := norm_tsum_factoredNumbers_sub_tsum_lt hsum.of_norm hf₀ hε
  refine ⟨range N₀, fun s hs ↦ ?_⟩
  have : ∏ p ∈ s, {p | Nat.Prime p}.mulIndicator F p = ∏ p ∈ s with p.Prime, F p :=
    prod_mulIndicator_eq_prod_filter s (fun _ ↦ F) _ id
  rw [this, dist_eq_norm, prod_filter_prime_tsum_eq_tsum_factoredNumbers hf₁ hmul hsum,
    norm_sub_rev]
  exact hN₀ s fun p hp ↦ hs <| mem_range.mpr <| lt_of_mem_primesBelow hp

include hf₁ hmul in
/-- The *Euler Product* for multiplicative (on coprime arguments) functions.

If `f : ℕ → R`, where `R` is a complete normed commutative ring, `f 0 = 0`, `f 1 = 1`, `f` is
multiplicative on coprime arguments, and `‖f ·‖` is summable, then
`∏' p : ℕ, if p.Prime then ∑' e, f (p ^ e) else 1 = ∑' n, f n`.
This version is stated using `HasProd` and `Set.mulIndicator`. -/
theorem eulerProduct_hasProd_mulIndicator (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    HasProd (Set.mulIndicator {p | Nat.Prime p} fun p ↦ ∑' e, f (p ^ e)) (∑' n, f n) := by
  rw [← hasProd_subtype_iff_mulIndicator]
  exact eulerProduct_hasProd hf₁ hmul hsum hf₀

open Filter in
include hf₁ hmul in
/-- The *Euler Product* for multiplicative (on coprime arguments) functions.

If `f : ℕ → R`, where `R` is a complete normed commutative ring, `f 0 = 0`, `f 1 = 1`, `f` is
multiplicative on coprime arguments, and `‖f ·‖` is summable, then
`∏' p : {p : ℕ | p.Prime}, ∑' e, f (p ^ e) = ∑' n, f n`.
This is a version using convergence of finite partial products. -/
theorem eulerProduct (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, ∑' e, f (p ^ e)) atTop (𝓝 (∑' n, f n)) := by
  have := (eulerProduct_hasProd_mulIndicator hf₁ hmul hsum hf₀).tendsto_prod_nat
  let F : ℕ → R := fun p ↦ ∑' (e : ℕ), f (p ^ e)
  have H (n : ℕ) : ∏ i ∈ range n, Set.mulIndicator {p | Nat.Prime p} F i =
                     ∏ p ∈ primesBelow n, ∑' (e : ℕ), f (p ^ e) :=
    prod_mulIndicator_eq_prod_filter (range n) (fun _ ↦ F) (fun _ ↦ {p | Nat.Prime p}) id
  simpa only [F, H]

include hf₁ hmul in
/-- The *Euler Product* for multiplicative (on coprime arguments) functions.

If `f : ℕ → R`, where `R` is a complete normed commutative ring, `f 0 = 0`, `f 1 = 1`, `f` is
multiplicative on coprime arguments, and `‖f ·‖` is summable, then
`∏' p : {p : ℕ | p.Prime}, ∑' e, f (p ^ e) = ∑' n, f n`. -/
theorem eulerProduct_tprod (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    ∏' p : Primes, ∑' e, f (p ^ e) = ∑' n, f n :=
  (eulerProduct_hasProd hf₁ hmul hsum hf₀).tprod_eq

end EulerProduct

/-!
### Versions for arithmetic functions
-/

namespace ArithmeticFunction

open EulerProduct

/-- The *Euler Product* for a multiplicative arithmetic function `f` with values in a
complete normed commutative ring `R`: if `‖f ·‖` is summable, then
`∏' p : Nat.Primes, ∑' e, f (p ^ e) = ∑' n, f n`.
This version is stated in terms of `HasProd`. -/
nonrec theorem IsMultiplicative.eulerProduct_hasProd {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (hsum : Summable (‖f ·‖)) :
    HasProd (fun p : Primes ↦ ∑' e, f (p ^ e)) (∑' n, f n) :=
  eulerProduct_hasProd hf.1 hf.2 hsum f.map_zero

open Filter in
/-- The *Euler Product* for a multiplicative arithmetic function `f` with values in a
complete normed commutative ring `R`: if `‖f ·‖` is summable, then
`∏' p : Nat.Primes, ∑' e, f (p ^ e) = ∑' n, f n`.
This version is stated in the form of convergence of finite partial products. -/
nonrec theorem IsMultiplicative.eulerProduct {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hsum : Summable (‖f ·‖)) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, ∑' e, f (p ^ e)) atTop (𝓝 (∑' n, f n)) :=
  eulerProduct hf.1 hf.2 hsum f.map_zero

/-- The *Euler Product* for a multiplicative arithmetic function `f` with values in a
complete normed commutative ring `R`: if `‖f ·‖` is summable, then
`∏' p : Nat.Primes, ∑' e, f (p ^ e) = ∑' n, f n`. -/
nonrec theorem IsMultiplicative.eulerProduct_tprod {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (hsum : Summable (‖f ·‖)) :
    ∏' p : Primes, ∑' e, f (p ^ e) = ∑' n, f n :=
  eulerProduct_tprod hf.1 hf.2 hsum f.map_zero

end ArithmeticFunction

end General

section CompletelyMultiplicative

/-!
### Euler Products for completely multiplicative functions

We now assume that `f` is completely multiplicative and has values in a complete normed field `F`.
Then we can use the formula for geometric series to simplify the statement. This leads to
`EulerProduct.eulerProduct_completely_multiplicative_hasProd` and variants.
-/

variable {F : Type*} [NormedField F] [CompleteSpace F]

namespace EulerProduct

-- a helper lemma that is useful below
lemma one_sub_inv_eq_geometric_of_summable_norm {f : ℕ →*₀ F} {p : ℕ} (hp : p.Prime)
    (hsum : Summable fun x ↦ ‖f x‖) :
    (1 - f p)⁻¹ = ∑' (e : ℕ), f (p ^ e) := by
  simp only [map_pow]
  refine (tsum_geometric_of_norm_lt_one <| summable_geometric_iff_norm_lt_one.mp ?_).symm
  refine Summable.of_norm ?_
  simpa only [Function.comp_def, map_pow]
    using hsum.comp_injective <| Nat.pow_right_injective hp.one_lt

/-- Given a (completely) multiplicative function `f : ℕ → F`, where `F` is a normed field,
such that `‖f p‖ < 1` for all primes `p`, we can express the sum of `f n` over all `s`-factored
positive integers `n` as a product of `(1 - f p)⁻¹` over the primes `p ∈ s`. At the same time,
we show that the sum involved converges absolutely. -/
lemma summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric {f : ℕ →* F}
    (h : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1) (s : Finset ℕ) :
    Summable (fun m : factoredNumbers s ↦ ‖f m‖) ∧
      HasSum (fun m : factoredNumbers s ↦ f m) (∏ p ∈ s with p.Prime, (1 - f p)⁻¹) := by
  have hmul {m n} (_ : Nat.Coprime m n) := f.map_mul m n
  have H₁ :
      ∏ p ∈ s with p.Prime, ∑' n : ℕ, f (p ^ n) = ∏ p ∈ s with p.Prime, (1 - f p)⁻¹ := by
    refine prod_congr rfl fun p hp ↦ ?_
    simp only [map_pow]
    exact tsum_geometric_of_norm_lt_one <| h (mem_filter.mp hp).2
  have H₂ : ∀ {p : ℕ}, p.Prime → Summable fun n ↦ ‖f (p ^ n)‖ := by
    intro p hp
    simp only [map_pow]
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_pow_le ..) ?_
    exact summable_geometric_iff_norm_lt_one.mpr <| (norm_norm (f p)).symm ▸ h hp
  exact H₁ ▸ summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum f.map_one hmul H₂ s

/-- A version of `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric`
in terms of the value of the series. -/
lemma prod_filter_prime_geometric_eq_tsum_factoredNumbers {f : ℕ →* F} (hsum : Summable f)
    (s : Finset ℕ) :
    ∏ p ∈ s with p.Prime, (1 - f p)⁻¹ = ∑' m : factoredNumbers s, f m := by
  refine (summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric ?_ s).2.tsum_eq.symm
  exact fun {_} hp ↦ hsum.norm_lt_one hp.one_lt

/-- Given a (completely) multiplicative function `f : ℕ → F`, where `F` is a normed field,
such that `‖f p‖ < 1` for all primes `p`, we can express the sum of `f n` over all `N`-smooth
positive integers `n` as a product of `(1 - f p)⁻¹` over the primes `p < N`. At the same time,
we show that the sum involved converges absolutely. -/
lemma summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric {f : ℕ →* F}
    (h : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1) (N : ℕ) :
    Summable (fun m : N.smoothNumbers ↦ ‖f m‖) ∧
      HasSum (fun m : N.smoothNumbers ↦ f m) (∏ p ∈ N.primesBelow, (1 - f p)⁻¹) := by
  rw [smoothNumbers_eq_factoredNumbers, primesBelow]
  exact summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric h _

/-- A version of `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric`
in terms of the value of the series. -/
lemma prod_primesBelow_geometric_eq_tsum_smoothNumbers {f : ℕ →* F} (hsum : Summable f) (N : ℕ) :
    ∏ p ∈ N.primesBelow, (1 - f p)⁻¹ = ∑' m : N.smoothNumbers, f m := by
  rw [smoothNumbers_eq_factoredNumbers, primesBelow]
  exact prod_filter_prime_geometric_eq_tsum_factoredNumbers hsum _

/-- The *Euler Product* for completely multiplicative functions.

If `f : ℕ →*₀ F`, where `F` is a complete normed field and `‖f ·‖` is summable, then
`∏' p : Nat.Primes, (1 - f p)⁻¹ = ∑' n, f n`.
This version is stated in terms of `HasProd`. -/
theorem eulerProduct_completely_multiplicative_hasProd {f : ℕ →*₀ F} (hsum : Summable (‖f ·‖)) :
    HasProd (fun p : Primes ↦ (1 - f p)⁻¹) (∑' n, f n) := by
  have H : (fun p : Primes ↦ (1 - f p)⁻¹) = fun p : Primes ↦ ∑' (e : ℕ), f (p ^ e) :=
    funext <| fun p ↦ one_sub_inv_eq_geometric_of_summable_norm p.prop hsum
  simpa only [map_pow, H]
    using eulerProduct_hasProd f.map_one (fun {m n} _ ↦ f.map_mul m n) hsum f.map_zero

/-- The *Euler Product* for completely multiplicative functions.

If `f : ℕ →*₀ F`, where `F` is a complete normed field and `‖f ·‖` is summable, then
`∏' p : Nat.Primes, (1 - f p)⁻¹ = ∑' n, f n`. -/
theorem eulerProduct_completely_multiplicative_tprod {f : ℕ →*₀ F} (hsum : Summable (‖f ·‖)) :
    ∏' p : Primes, (1 - f p)⁻¹ = ∑' n, f n :=
  (eulerProduct_completely_multiplicative_hasProd hsum).tprod_eq

open Filter in
/-- The *Euler Product* for completely multiplicative functions.

If `f : ℕ →*₀ F`, where `F` is a complete normed field and `‖f ·‖` is summable, then
`∏' p : Nat.Primes, (1 - f p)⁻¹ = ∑' n, f n`.
This version is stated in the form of convergence of finite partial products. -/
theorem eulerProduct_completely_multiplicative {f : ℕ →*₀ F} (hsum : Summable (‖f ·‖)) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - f p)⁻¹) atTop (𝓝 (∑' n, f n)) := by
  have hmul {m n} (_ : Nat.Coprime m n) := f.map_mul m n
  have := (eulerProduct_hasProd_mulIndicator f.map_one hmul hsum f.map_zero).tendsto_prod_nat
  have H (n : ℕ) : ∏ p ∈ range n, {p | Nat.Prime p}.mulIndicator (fun p ↦ (1 - f p)⁻¹) p =
                     ∏ p ∈ primesBelow n, (1 - f p)⁻¹ :=
    prod_mulIndicator_eq_prod_filter
      (range n) (fun _ ↦ fun p ↦ (1 - f p)⁻¹) (fun _ ↦ {p | Nat.Prime p}) id
  have H' : {p | Nat.Prime p}.mulIndicator (fun p ↦ (1 - f p)⁻¹) =
              {p | Nat.Prime p}.mulIndicator (fun p ↦ ∑' e : ℕ, f (p ^ e)) :=
    Set.mulIndicator_congr fun p hp ↦ one_sub_inv_eq_geometric_of_summable_norm hp hsum
  simpa only [← H, H'] using this

end EulerProduct

end CompletelyMultiplicative
