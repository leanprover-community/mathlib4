/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Star.Module
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# The logarithm in a topological algebra

In this file we define `NormedSpace.log : 𝔸 → 𝔸`, the logarithm
`log x = ∑ₙ ((-1) ^ (n + 1) / n) • (x - 1) ^ n` in a topological ring `𝔸`, following the
development style of `NormedSpace.exp` (see `Mathlib/Analysis/Normed/Algebra/Exponential.lean`).
It is the value at `x - 1` of the `FormalMultilinearSeries` `NormedSpace.logSeries ℚ 𝔸`, where the
`ℚ`-algebra structure on `𝔸` is chosen using `Classical.choice`. It takes the junk value `0`
if the series does not converge or if `𝔸` has no `ℚ`-algebra structure (equivalently,
if `1 / n` doesn't correspond to what a mathematician thinks).

This file only contains the definition and its immediate algebraic properties; convergence of
the series and the relation to `NormedSpace.exp` are left to later files.

## Main definitions

* `NormedSpace.logSeries 𝕂 𝔸`: the formal multilinear series whose `n`-th term is
  `(xᵢ) ↦ ((-1) ^ (n + 1) / n : 𝕂) • ∏ xᵢ`; its sum at `x - 1` is `log x`.
* `NormedSpace.log`: the logarithm `𝔸 → 𝔸`.

## Main results

* `NormedSpace.log_eq_tsum`: `log` as a `tsum`.
* `NormedSpace.log_one`, `NormedSpace.log_op`, `NormedSpace.star_log`, `NormedSpace.log_mem`,
  `Commute.log`: immediate properties.

## TODO

* Ultrametric convergence: if `K` is a complete ultrametric normed field of characteristic zero
  then the series converges on the whole disc `‖x - 1‖ < 1` (no choice of prime is needed: the
  natural numbers of norm `< 1` form a prime ideal of `ℕ`, and if it is `pℕ` then
  `‖n‖ = ‖p‖ ^ padicValNat p n`).
* If moreover `‖(p : K)‖ < 1` for a prime `p`, Iwasawa's formula
  `log x = lim (x ^ p ^ k - 1) / p ^ k` gives `log (x * y) = log x + log y` on that disc, hence
  `log_inv`, `log_pow`, `log_zpow` etc.
* The formal identity `log ((1 + X) * (1 + Y)) = log (1 + X) + log (1 + Y)` in `ℚ⟦X, Y⟧`.
* Relation with `NormedSpace.exp`: `exp (log x) = x` and `log (exp x) = x` whenever both series
  converge.
* In the ultrametric case, the computation of where the series for exp and log converge
  (`‖x - 1‖ ^ (p - 1) < ‖(p : K)‖` for log).
* `‖log x‖ = ‖x - 1‖` when the series converges
* Analyticity: `HasFPowerSeriesOnBall log (logSeries 𝕂 𝔸) 1 (logSeries 𝕂 𝔸).radius` and its
  consequences, mirroring `NormedSpace.analyticAt_exp_of_mem_ball`.
* Over `ℝ` and `ℂ`, `NormedSpace.log` agrees with `Real.log` and `Complex.log` on `‖x - 1‖ < 1`.
* Analytic continuation of `log` in the ultrametric case (probably best to be opinionated
  and define `log p = 0` so we get a "canonical branch" analogous to how mathlib has
  chosen a branch of `Complex.log`).
-/

@[expose] public section

namespace NormedSpace

open FormalMultilinearSeries

section TopologicalAlgebra

variable (𝕂 𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

/-- `logSeries 𝕂 𝔸` is the `FormalMultilinearSeries` whose `n`-th term is the map
`(xᵢ) : 𝔸ⁿ ↦ ((-1) ^ (n + 1) / n : 𝕂) • ∏ xᵢ`; its `0`-th term is `0` since `1 / 0 = 0`.
The corresponding sum evaluated at `x - 1` is the logarithm `NormedSpace.log x`. -/
def logSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸 := fun n =>
  ((-1) ^ (n + 1) / n : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

theorem logSeries_eq_ofScalars : logSeries 𝕂 𝔸 = ofScalars 𝔸 fun n ↦ ((-1) ^ (n + 1) / n : 𝕂) := by
  simp_rw [FormalMultilinearSeries.ext_iff, logSeries, ofScalars, implies_true]

variable {𝕂 𝔸}

open scoped Classical in
/-- `NormedSpace.log : 𝔸 → 𝔸` is the logarithm `log x = ∑ₙ ((-1) ^ (n + 1) / n) • (x - 1) ^ n`.
It is defined as the sum of the `FormalMultilinearSeries` `logSeries ℚ 𝔸` at `x - 1`, in the same
way as `NormedSpace.exp`, and takes the junk value `0` where the series does not converge.

If `𝔸` can't be equipped with a `ℚ`-algebra structure, we use the junk value `0`.
-/
noncomputable irreducible_def log (x : 𝔸) : 𝔸 :=
  if h : Nonempty (Algebra ℚ 𝔸) then
    letI _ := h.some
    (NormedSpace.logSeries ℚ 𝔸).sum (x - 1)
  else
    0

/-- The junk value when `𝔸` can't be equipped with a `ℚ`-algebra structure. -/
@[simp]
theorem log_of_isEmpty_algebra_rat [IsEmpty (Algebra ℚ 𝔸)] (x : 𝔸) : log x = 0 := by
  rw [log, dite_eq_right (not_nonempty_iff.mpr ‹_›)]

theorem logSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (logSeries 𝕂 𝔸 n fun _ => x) = ((-1) ^ (n + 1) / n : 𝕂) • x ^ n := by simp [logSeries]

theorem logSeries_sum_eq (x : 𝔸) :
    (logSeries 𝕂 𝔸).sum x = ∑' n : ℕ, ((-1) ^ (n + 1) / n : 𝕂) • x ^ n :=
  tsum_congr fun n => logSeries_apply_eq x n

private lemma neg_one_pow_div_natCast_eq_inv_intCast (T : Type*) [DivisionRing T] (k n : ℕ) :
    ((-1) ^ k / n : T) = (((-1) ^ k * n : ℤ) : T)⁻¹ := by
  rcases Nat.even_or_odd k with hk | hk <;> simp [hk.neg_one_pow, div_eq_mul_inv, inv_neg]

/-- If `E` is a module over two division rings `R` and `S`, then scalar multiplication by the
coefficients `(-1) ^ k / n` of the logarithm series agree in `R` and `S`. -/
private lemma neg_one_pow_div_natCast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E]
    [DivisionRing R] [DivisionRing S] [Module R E] [Module S E] (k n : ℕ) (x : E) :
    ((-1) ^ k / n : R) • x = ((-1) ^ k / n : S) • x := by
  rw [neg_one_pow_div_natCast_eq_inv_intCast R, neg_one_pow_div_natCast_eq_inv_intCast S,
    inv_intCast_smul_eq R S]

theorem logSeries_sum_eq_rat [Algebra ℚ 𝔸] : (logSeries 𝕂 𝔸).sum = (logSeries ℚ 𝔸).sum := by
  ext; simp_rw [logSeries_sum_eq, neg_one_pow_div_natCast_smul_eq 𝕂 ℚ]

theorem logSeries_eq_logSeries_rat [Algebra ℚ 𝔸] (n : ℕ) :
    ⇑(logSeries 𝕂 𝔸 n) = logSeries ℚ 𝔸 n := by
  ext c
  simp [logSeries, neg_one_pow_div_natCast_smul_eq 𝕂 ℚ]

variable (𝕂) in
theorem log_eq_logSeries_sum [CharZero 𝕂] : log = fun x : 𝔸 ↦ (logSeries 𝕂 𝔸).sum (x - 1) := by
  ext x
  rw [log, dite_eq_left ⟨RestrictScalars.algebra ℚ 𝕂 𝔸⟩, ← @logSeries_sum_eq_rat (𝕂 := 𝕂)]

variable (𝕂) in
theorem log_eq_tsum [CharZero 𝕂] :
    log = fun x : 𝔸 ↦ ∑' n : ℕ, ((-1) ^ (n + 1) / n : 𝕂) • (x - 1) ^ n := by
  rw [log_eq_logSeries_sum 𝕂]
  ext x
  exact logSeries_sum_eq (x - 1)

theorem logSeries_apply_zero (n : ℕ) : logSeries 𝕂 𝔸 n (fun _ ↦ (0 : 𝔸)) = 0 := by
  rw [logSeries_apply_eq]
  rcases n with - | n
  · simp
  · rw [zero_pow (Nat.succ_ne_zero _), smul_zero]

@[simp]
theorem log_one : log (1 : 𝔸) = 0 := by
  rw [log]
  split_ifs
  · simp_rw [sub_self, logSeries_sum_eq, ← logSeries_apply_eq, logSeries_apply_zero, tsum_zero]
  · rfl

@[simp]
theorem log_op [T2Space 𝔸] (x : 𝔸) : log (MulOpposite.op x) = MulOpposite.op (log x) := by
  obtain h | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra ℚ 𝔸)
  · have : IsEmpty (Algebra ℚ 𝔸ᵐᵒᵖ) := ⟨fun _ => h.elim <| (RingEquiv.opOp 𝔸).algebra ℚ⟩
    simp
  · rw [log_eq_tsum ℚ, log_eq_tsum ℚ]
    simp_rw [← MulOpposite.op_one, ← MulOpposite.op_sub, ← MulOpposite.op_pow,
      ← MulOpposite.op_smul, tsum_op]

theorem star_log [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] (x : 𝔸) :
    star (log x) = log (star x) := by
  obtain _ | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra ℚ 𝔸)
  · simp
  · simp_rw [log_eq_tsum ℚ, tsum_star, star_rat_smul, star_pow, star_sub, star_one]

/-- A subring of `𝔸` that is closed topologically and under `ℚ`-scaling is closed under `log`. -/
theorem log_mem
    {R S : Type*} [Monoid R] [SMul ℚ R] [MulAction R 𝔸] [Algebra ℚ 𝔸] [IsScalarTower ℚ R 𝔸]
    [SetLike S 𝔸] [SubringClass S 𝔸] [SMulMemClass S R 𝔸] {s : S}
    (h_closed : IsClosed (s : Set 𝔸)) {x : 𝔸} (h : x ∈ s) :
    log x ∈ s := by
  have := SMulMemClass.ofIsScalarTower S ℚ R 𝔸
  rw [log_eq_tsum ℚ]
  exact tsum_mem h_closed fun i => SMulMemClass.smul_mem _ <| pow_mem (sub_mem h (one_mem s)) _

end NormedSpace.TopologicalAlgebra

namespace Commute

open NormedSpace

variable {𝔸 : Type*} [Ring 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

theorem log_right [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute x (log y) := by
  obtain _ | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra ℚ 𝔸)
  · simp
  · rw [log_eq_tsum ℚ]
    exact Commute.tsum_right x fun n =>
      ((h.sub_right (Commute.one_right x)).pow_right n).smul_right _

theorem log_left [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute (log x) y :=
  h.symm.log_right.symm

theorem log [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute (log x) (log y) :=
  h.log_left.log_right

end Commute
