/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.Convergence

/-!
# Dirichlet convolution of sequences and products of L-series

We define the *Dirichlet convolution* `f ⍟ g` of two sequences `f g : ℕ → R` with values in a
semiring `R` by `(f ⍟ g) n = ∑ (k * m = n), f k * g m` when `n ≠ 0` and `(f ⍟ g) 0 = 0`.
Technically, this is done by transporting the existing definition for `ArithmeticFunction R`;
see `LSeries.convolution`. We show that these definitions agree (`LSeries.convolution_def`).

We then consider the case `R = ℂ` and show that `L (f ⍟ g) = L f * L g` on the common domain
of convergence of the L-series `L f`  and `L g` of `f` and `g`; see `LSeries_convolution`
and `LSeries_convolution'`.
-/

open scoped LSeries.notation

open Complex LSeries

/-!
### Dirichlet convolution of two functions
-/

open Nat

/-- We turn any function `ℕ → R` into an `ArithmeticFunction R` by setting its value at `0`
to be zero. -/
def toArithmeticFunction {R : Type*} [Zero R] (f : ℕ → R) : ArithmeticFunction R where
  toFun n := if n = 0 then 0 else f n
  map_zero' := rfl

lemma toArithmeticFunction_congr {R : Type*} [Zero R] {f f' : ℕ → R}
    (h : ∀ {n}, n ≠ 0 → f n = f' n) :
    toArithmeticFunction f = toArithmeticFunction f' := by
  ext
  simp_all [toArithmeticFunction]

/-- If we consider an arithmetic function just as a function and turn it back into an
arithmetic function, it is the same as before. -/
@[simp]
lemma ArithmeticFunction.toArithmeticFunction_eq_self {R : Type*} [Zero R]
    (f : ArithmeticFunction R) :
    toArithmeticFunction f = f := by
  ext n
  simp +contextual [toArithmeticFunction]

/-- Dirichlet convolution of two sequences.

We define this in terms of the already existing definition for arithmetic functions. -/
noncomputable def LSeries.convolution {R : Type*} [Semiring R] (f g : ℕ → R) : ℕ → R :=
  ⇑(toArithmeticFunction f * toArithmeticFunction g)

@[inherit_doc]
scoped[LSeries.notation] infixl:70 " ⍟ " => LSeries.convolution

lemma LSeries.convolution_congr {R : Type*} [Semiring R] {f f' g g' : ℕ → R}
    (hf : ∀ {n}, n ≠ 0 → f n = f' n) (hg : ∀ {n}, n ≠ 0 → g n = g' n) :
    f ⍟ g = f' ⍟ g' := by
  simp [convolution, toArithmeticFunction_congr hf, toArithmeticFunction_congr hg]

/-- The product of two arithmetic functions defines the same function as the Dirichlet convolution
of the functions defined by them. -/
lemma ArithmeticFunction.coe_mul {R : Type*} [Semiring R] (f g : ArithmeticFunction R) :
    f ⍟ g = ⇑(f * g) := by
  simp [convolution]

namespace LSeries

lemma convolution_def {R : Type*} [Semiring R] (f g : ℕ → R) :
    f ⍟ g = fun n ↦ ∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2 := by
  ext n
  simpa [convolution, toArithmeticFunction] using
    Finset.sum_congr rfl fun p hp ↦ by simp [ne_zero_of_mem_divisorsAntidiagonal hp]

@[simp]
lemma convolution_map_zero {R : Type*} [Semiring R] (f g : ℕ → R) : (f ⍟ g) 0 = 0 := by
  simp [convolution_def]


/-!
### Multiplication of L-series
-/

/-- We give an expression of the `LSeries.term` of the convolution of two functions
in terms of a sum over `Nat.divisorsAntidiagonal`. -/
lemma term_convolution (f g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term (f ⍟ g) s n = ∑ p ∈ n.divisorsAntidiagonal, term f s p.1 * term g s p.2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  -- now `n ≠ 0`
  rw [term_of_ne_zero hn, convolution_def, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have ⟨hp₁, hp₂⟩ := ne_zero_of_mem_divisorsAntidiagonal hp
  rw [term_of_ne_zero hp₁, term_of_ne_zero hp₂, mul_comm_div, div_div, ← mul_div_assoc,
    ← natCast_mul_natCast_cpow, ← cast_mul, mul_comm p.2, (mem_divisorsAntidiagonal.mp hp).1]

open Set in
/-- We give an expression of the `LSeries.term` of the convolution of two functions
in terms of an a priori infinite sum over all pairs `(k, m)` with `k * m = n`
(the set we sum over is infinite when `n = 0`). This is the version needed for the
proof that `L (f ⍟ g) = L f * L g`. -/
lemma term_convolution' (f g : ℕ → ℂ) (s : ℂ) :
    term (f ⍟ g) s = fun n ↦
      ∑' (b : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n}), term f s b.val.1 * term g s b.val.2 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · -- show that both sides vanish when `n = 0`; this is the hardest part of the proof!
    refine (term_zero ..).trans ?_
    -- the right hand sum is over the union below, but in each term, one factor is always zero
    have hS : (fun p ↦ p.1 * p.2) ⁻¹' {0} = {0} ×ˢ univ ∪ univ ×ˢ {0} := by
      ext
      simp [Nat.mul_eq_zero]
    have : ∀ p : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {0}, term f s p.val.1 * term g s p.val.2 = 0 := by
      rintro ⟨⟨_, _⟩, hp⟩
      rcases hS ▸ hp with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> simp
    simp [this]
  -- now `n ≠ 0`
  rw [show (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n} = n.divisorsAntidiagonal by ext; simp [hn],
    Finset.tsum_subtype' n.divisorsAntidiagonal fun p ↦ term f s p.1 * term g s p.2,
    term_convolution f g s n]

end LSeries

open Set in
/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
lemma LSeriesHasSum.convolution {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
    (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f ⍟ g) s (a * b) := by
  have hsum := summable_mul_of_summable_norm hf.summable.norm hg.summable.norm
  -- NB: this `simpa` is quite slow if un-squeezed
  simpa only [LSeriesHasSum, term_convolution'] using (hf.mul hg hsum).tsum_fiberwise _

/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
lemma LSeries_convolution' {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeries (f ⍟ g) s = LSeries f s * LSeries g s :=
  (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeries_eq

/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
equals the product of their L-series in their common half-plane of absolute convergence. -/
lemma LSeries_convolution {f g : ℕ → ℂ} {s : ℂ}
    (hf : abscissaOfAbsConv f < s.re) (hg : abscissaOfAbsConv g < s.re) :
    LSeries (f ⍟ g) s = LSeries f s * LSeries g s :=
  LSeries_convolution' (LSeriesSummable_of_abscissaOfAbsConv_lt_re hf)
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re hg)

/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
is summable when both L-series are summable. -/
lemma LSeriesSummable.convolution {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f ⍟ g) s :=
  (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeriesSummable

/-- The abscissa of absolute convergence of `f ⍟ g` is at most the maximum of those
of `f` and `g`. -/
lemma LSeries.abscissaOfAbsConv_convolution_le (f g : ℕ → ℂ) :
    abscissaOfAbsConv (f ⍟ g) ≤ max (abscissaOfAbsConv f) (abscissaOfAbsConv g) :=
  abscissaOfAbsConv_binop_le LSeriesSummable.convolution f g

namespace ArithmeticFunction

/-!
### Versions for arithmetic functions
-/

/-- The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
lemma LSeriesHasSum_mul {f g : ArithmeticFunction ℂ} {s a b : ℂ} (hf : LSeriesHasSum ↗f s a)
    (hg : LSeriesHasSum ↗g s b) :
    LSeriesHasSum ↗(f * g) s (a * b) :=
  coe_mul f g ▸ hf.convolution hg

/-- The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
lemma LSeries_mul' {f g : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable ↗f s)
    (hg : LSeriesSummable ↗g s) :
    LSeries ↗(f * g) s = LSeries ↗f s * LSeries ↗g s :=
  coe_mul f g ▸ LSeries_convolution' hf hg

/-- The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions `f` and `g`
equals the product of their L-series in their common half-plane of absolute convergence. -/
lemma LSeries_mul {f g : ArithmeticFunction ℂ} {s : ℂ}
    (hf : abscissaOfAbsConv ↗f < s.re) (hg : abscissaOfAbsConv ↗g < s.re) :
    LSeries ↗(f * g) s = LSeries ↗f s * LSeries ↗g s :=
  coe_mul f g ▸ LSeries_convolution hf hg

/-- The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions `f` and `g`
is summable when both L-series are summable. -/
lemma LSeriesSummable_mul {f g : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable ↗f s)
    (hg : LSeriesSummable ↗g s) :
    LSeriesSummable ↗(f * g) s :=
  coe_mul f g ▸ hf.convolution hg

end ArithmeticFunction
