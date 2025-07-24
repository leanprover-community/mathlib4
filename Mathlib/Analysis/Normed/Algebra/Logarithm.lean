/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, James Kiln, Anatole Dedecker, Eric Wieser
-/

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Logarithm in a Banach algebra



-/

namespace NormedSpace

open Filter ContinuousMultilinearMap NormedField Asymptotics FormalMultilinearSeries

open scoped Nat Topology ENNReal

section TopologicalAlgebra

variable (𝕂 𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

/-- `logSeries 𝕂 𝔸` is the `FormalMultilinearSeries` whose `n`-th term is the map
`(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`. Its sum is the logonential map `NormedSpace.log 𝕂 : 𝔸 → 𝔸`. -/
def logSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸 := fun n =>
  (-(-1) ^ n / n : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

/-- The logarithm series as an `ofScalars` series. -/
theorem logSeries_eq_ofScalars : logSeries 𝕂 𝔸 = ofScalars 𝔸 fun n ↦ (-(-1) ^ n / n : 𝕂) := by
  simp_rw [FormalMultilinearSeries.ext_iff, logSeries, ofScalars, implies_true]

variable {𝔸}

/-- `NormedSpace.log 𝕂 : 𝔸 → 𝔸` is the logonential map determined by the action of `𝕂` on `𝔸`.
It is defined as the sum of the `FormalMultilinearSeries` `logSeries 𝕂 𝔸`.

Note that when `𝔸 = Matrix n n 𝕂`, this is the **Matrix logonential**; see
[`Matrixlogonential`](./Mathlib/Analysis/Normed/Algebra/Matrixlogonential) for lemmas
specific to that case. -/
noncomputable def log (x : 𝔸) : 𝔸 :=
  (logSeries 𝕂 𝔸).sum x

variable {𝕂}

theorem logSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (logSeries 𝕂 𝔸 n fun _ => x) = (-(-1) ^ n / n : 𝕂) • x ^ n := by simp [logSeries]

omit [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] in
/-- This form for the `logSeries` coefficient is useful for rewriting. -/
theorem logSeries_coeff_eq_natSmul_zsmul (x : 𝔸) (n : ℕ) :
    (-(-1) ^ n / n : 𝕂) • x ^ n = ((n : 𝕂)⁻¹) • ((-(-1) ^ n : ℤ) • x ^ n) := by
  simp only [div_eq_inv_mul, mul_smul]
  norm_cast

theorem logSeries_apply_eq_inv (x : 𝔸) (n : ℕ) :
    (logSeries 𝕂 𝔸 n fun _ => x) = ((n : 𝕂)⁻¹ * -(-1) ^ n) • x ^ n := by
  simp [logSeries_apply_eq, div_eq_inv_mul]

theorem logSeries_apply_eq' (x : 𝔸) :
    (fun n => logSeries 𝕂 𝔸 n fun _ => x) = fun (n : ℕ) => (-(-1) ^ n / n : 𝕂) • x ^ n :=
  funext (logSeries_apply_eq x)

theorem logSeries_sum_eq (x : 𝔸) : (logSeries 𝕂 𝔸).sum x = ∑' n : ℕ, (-(-1) ^ n / n : 𝕂) • x ^ n :=
  tsum_congr fun n => logSeries_apply_eq x n

theorem logSeries_sum_eq_inv (x : 𝔸) :
    (logSeries 𝕂 𝔸).sum x = ∑' n : ℕ, ((n : 𝕂)⁻¹ * -(-1) ^ n)• x ^ n :=
  tsum_congr fun n => logSeries_apply_eq_inv x n

theorem log_eq_tsum : log 𝕂 = fun x : 𝔸 => ∑' n : ℕ, (-(-1) ^ n / n : 𝕂) • x ^ n :=
  funext logSeries_sum_eq

theorem log_eq_tsum_inv : log 𝕂 = fun x : 𝔸 => ∑' n : ℕ, ((n : 𝕂)⁻¹ * -(-1) ^ n) • x ^ n :=
  funext logSeries_sum_eq_inv

/-- The logonential sum as an `ofScalarsSum`. -/
theorem log_eq_ofScalarsSum : log 𝕂 = ofScalarsSum (E := 𝔸) fun n ↦ (-(-1) ^ n / n : 𝕂) := by
  rw [log_eq_tsum, ofScalarsSum_eq_tsum]

theorem logSeries_apply_zero (n : ℕ) :
    logSeries 𝕂 𝔸 n (fun _ => (0 : 𝔸)) = 0 := by
  rw [logSeries_apply_eq]
  simp
  by_cases h : n = 0
  · simp [h]
  · right
    exact zero_pow h

@[simp]
-- TODO: golf maybe?
theorem log_zero : log 𝕂 (0 : 𝔸) = 0 := by
  simp [log_eq_tsum, ← logSeries_apply_eq, logSeries_apply_zero]

@[simp]
theorem log_op [T2Space 𝔸] (x : 𝔸) : log 𝕂 (MulOpposite.op x) = MulOpposite.op (log 𝕂 x) := by
  simp_rw [log, logSeries_sum_eq, ← MulOpposite.op_pow, ← MulOpposite.op_smul, tsum_op]

@[simp]
theorem log_unop [T2Space 𝔸] (x : 𝔸ᵐᵒᵖ) :
    log 𝕂 (MulOpposite.unop x) = MulOpposite.unop (log 𝕂 x) := by
  simp_rw [log, logSeries_sum_eq, ← MulOpposite.unop_pow, ← MulOpposite.unop_smul, tsum_unop]

-- TODO: golf
theorem star_log [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] (x : 𝔸) :
    star (log 𝕂 x) = log 𝕂 (star x) := by
  rw [log_eq_tsum]
  simp only [logSeries_coeff_eq_natSmul_zsmul, tsum_star, star_inv_natCast_smul]
  congr! 3 with n
  simp only [star_smul, Int.reduceNeg, neg_smul, star_neg, neg_inj]
  simp only [Int.reduceNeg, star_trivial, star_pow, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one]

variable (𝕂)

@[aesop safe apply]
theorem _root_.IsSelfAdjoint.log [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
    (h : IsSelfAdjoint x) : IsSelfAdjoint (log 𝕂 x) :=
  (star_log x).trans <| h.symm ▸ rfl

theorem _root_.Commute.log_right [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute x (log 𝕂 y) := by
  rw [log_eq_tsum]
  exact Commute.tsum_right x fun n => (h.pow_right n).smul_right _

theorem _root_.Commute.log_left [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) : Commute (log 𝕂 x) y :=
  (h.symm.log_right 𝕂).symm

theorem _root_.Commute.log [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) : Commute (log 𝕂 x) (log 𝕂 y) :=
  (h.log_left _).log_right _

end TopologicalAlgebra

section TopologicalDivisionAlgebra

variable {𝕂 𝔸 : Type*} [Field 𝕂] [DivisionRing 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸]

example (k : 𝕂) (x : 𝔸) : k • x = (Algebra.cast k) * x := by exact Algebra.smul_def k x

theorem logSeries_apply_eq_mul (x : 𝔸) (n : ℕ) :
    (logSeries 𝕂 𝔸 n fun _ => x) = -(-1) ^ n / n * x ^ n := by
  simp [logSeries_apply_eq, Algebra.smul_def]

theorem logSeries_apply_eq_mul' (x : 𝔸) :
    (fun n => logSeries 𝕂 𝔸 n fun _ => x) = fun (n : ℕ) => -(-1) ^ n / n * x ^ n :=
  funext (logSeries_apply_eq_mul x)

theorem logSeries_sum_eq_div (x : 𝔸) : (logSeries 𝕂 𝔸).sum x = ∑' n : ℕ, -(-1) ^ n / n * x ^ n :=
  tsum_congr (logSeries_apply_eq_mul x)

theorem log_eq_tsum_div : log 𝕂 = fun x : 𝔸 => ∑' n : ℕ, -(-1) ^ n / n * x ^ n :=
  funext logSeries_sum_eq_div

end TopologicalDivisionAlgebra

section Normed

section AnyFieldAnyAlgebra

variable {𝕂 𝔸 𝔹 : Type*} [NontriviallyNormedField 𝕂]
variable [NormedRing 𝔸] [NormedRing 𝔹] [NormedAlgebra 𝕂 𝔸] [NormedAlgebra 𝕂 𝔹]

theorem norm_logSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖logSeries 𝕂 𝔸 n fun _ => x‖ :=
  (logSeries 𝕂 𝔸).summable_norm_apply hx

theorem norm_logSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    Summable fun (n : ℕ) => ‖(-(-1) ^ n / n : 𝕂) •  x ^ n‖ := by
  change Summable (norm ∘ _)
  rw [← logSeries_apply_eq']
  exact norm_logSeries_summable_of_mem_ball x hx

section CompleteAlgebra

variable [CompleteSpace 𝔸]

theorem logSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    Summable fun n => logSeries 𝕂 𝔸 n fun _ => x :=
  (norm_logSeries_summable_of_mem_ball x hx).of_norm

theorem logSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    Summable fun (n : ℕ) => (-(-1) ^ n / n : 𝕂) • x ^ n :=
  (norm_logSeries_summable_of_mem_ball' x hx).of_norm

theorem logSeries_hasSum_log_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    HasSum (fun n => logSeries 𝕂 𝔸 n fun _ => x) (log 𝕂 x) :=
  FormalMultilinearSeries.hasSum (logSeries 𝕂 𝔸) hx

theorem logSeries_hasSum_log_of_mem_ball' (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    HasSum (fun (n : ℕ) => (-(-1) ^ n / n : 𝕂) • x ^ n) (log 𝕂 x) := by
  rw [← logSeries_apply_eq']
  exact logSeries_hasSum_log_of_mem_ball x hx

theorem hasFPowerSeriesOnBall_log_of_radius_pos (h : 0 < (logSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesOnBall (log 𝕂) (logSeries 𝕂 𝔸) 0 (logSeries 𝕂 𝔸).radius :=
  (logSeries 𝕂 𝔸).hasFPowerSeriesOnBall h

theorem hasFPowerSeriesAt_log_zero_of_radius_pos (h : 0 < (logSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesAt (log 𝕂) (logSeries 𝕂 𝔸) 0 :=
  (hasFPowerSeriesOnBall_log_of_radius_pos h).hasFPowerSeriesAt

theorem continuousOn_log : ContinuousOn (log 𝕂 : 𝔸 → 𝔸) (EMetric.ball 0 (logSeries 𝕂 𝔸).radius) :=
  FormalMultilinearSeries.continuousOn

theorem analyticAt_log_of_mem_ball (x : 𝔸) (hx : x ∈ EMetric.ball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    AnalyticAt 𝕂 (log 𝕂) x := by
  by_cases h : (logSeries 𝕂 𝔸).radius = 0
  · rw [h] at hx; exact (ENNReal.not_lt_zero hx).elim
  · have h := pos_iff_ne_zero.mpr h
    exact (hasFPowerSeriesOnBall_log_of_radius_pos h).analyticAt_of_mem hx

-- /-- In a Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero, if `x` and `y` are
-- in the disk of convergence and commute, then
-- `NormedSpace.log 𝕂 (x + y) = (NormedSpace.log 𝕂 x) * (NormedSpace.log 𝕂 y)`. -/
-- theorem log_add_of_commute_of_mem_ball [CharZero 𝕂] {x y : 𝔸} (hxy : Commute x y)
--     (hx : x ∈ EMetric.ball (0 : 𝔸) (logSeries 𝕂 𝔸).radius)
--     (hy : y ∈ EMetric.ball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) : log 𝕂 (x + y + x * y) = log 𝕂 x + log 𝕂 y := by
--   rw [log_eq_tsum,
--     tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
--       (norm_logSeries_summable_of_mem_ball' x hx) (norm_logSeries_summable_of_mem_ball' y hy)]
--   dsimp only
--   conv_lhs =>
--     congr
--     ext
--     rw [hxy.add_pow' _, Finset.smul_sum]
--   refine tsum_congr fun n => Finset.sum_congr rfl fun kl hkl => ?_
--   rw [← Nat.cast_smul_eq_nsmul 𝕂, smul_smul, smul_mul_smul_comm, ← Finset.mem_antidiagonal.mp hkl,
--     Nat.cast_add_choose, Finset.mem_antidiagonal.mp hkl]
--   congr 1
--   have : (n ! : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
--   field_simp [this]

/-- Any continuous ring homomorphism commutes with `NormedSpace.log`. -/
theorem map_log_of_mem_ball {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹] (f : F) (hf : Continuous f)
    (x : 𝔸) (hx : x ∈ EMetric.ball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    f (log 𝕂 x) = log 𝕂 (f x) := by
  rw [log_eq_tsum, log_eq_tsum]
  refine ((logSeries_summable_of_mem_ball' _ hx).hasSum.map f hf).tsum_eq.symm.trans ?_
  dsimp only [Function.comp_def]
  -- TODO: golf
  congr! with n
  rw [div_eq_inv_mul, MulAction.mul_smul, MulAction.mul_smul, map_inv_natCast_smul f 𝕂 𝕂,
    show (-(-1) ^ n : 𝕂) = Int.cast (-(-1) ^ n : ℤ) by simp, map_intCast_smul f 𝕂 𝕂, map_pow]

end CompleteAlgebra

theorem algebraMap_log_comm_of_mem_ball [CompleteSpace 𝕂] (x : 𝕂)
    (hx : x ∈ EMetric.ball (0 : 𝕂) (logSeries 𝕂 𝕂).radius) :
    algebraMap 𝕂 𝔸 (log 𝕂 x) = log 𝕂 (algebraMap 𝕂 𝔸 x) :=
  map_log_of_mem_ball _ (continuous_algebraMap 𝕂 𝔸) _ hx

end AnyFieldAnyAlgebra

section AnyFieldDivisionAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
variable (𝕂)

theorem norm_logSeries_div_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    Summable fun (n : ℕ) => ‖-(-1) ^ n / n * x ^ n‖ := by
  change Summable (norm ∘ _)
  rw [← logSeries_apply_eq_mul' (𝕂 := 𝕂) x]
  exact norm_logSeries_summable_of_mem_ball x hx

theorem logSeries_div_summable_of_mem_ball [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
      Summable fun (n : ℕ) => -(-1) ^ n / n * x ^ n :=
  (norm_logSeries_div_summable_of_mem_ball 𝕂 x hx).of_norm

theorem logSeries_div_hasSum_log_of_mem_ball [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    HasSum (fun (n : ℕ) => -(-1) ^ n / n * x ^ n) (log 𝕂 x) := by
  rw [← logSeries_apply_eq_mul' (𝕂 := 𝕂) x]
  exact logSeries_hasSum_log_of_mem_ball x hx

end AnyFieldDivisionAlgebra

end Normed

section ScalarTower

variable (𝕂 𝕂' 𝔸 : Type*) [Field 𝕂] [Field 𝕂'] [Ring 𝔸] [Algebra 𝕂 𝔸] [Algebra 𝕂' 𝔸]
  [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
`logSeries` on `𝔸`. -/
theorem logSeries_eq_logSeries (n : ℕ) (x : 𝔸) :
    (logSeries 𝕂 𝔸 n fun _ => x) = logSeries 𝕂' 𝔸 n fun _ => x := by
  simp_rw [logSeries_apply_eq, logSeries_coeff_eq_natSmul_zsmul, inv_natCast_smul_eq 𝕂 𝕂']

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
logonential function on `𝔸`. -/
theorem log_eq_log : (log 𝕂 : 𝔸 → 𝔸) = log 𝕂' := by
  ext x
  rw [log, log]
  refine tsum_congr fun n => ?_
  rw [logSeries_eq_logSeries 𝕂 𝕂' 𝔸 n x]

theorem log_ℝ_ℂ_eq_log_ℂ_ℂ : (log ℝ : ℂ → ℂ) = log ℂ :=
  log_eq_log ℝ ℂ ℂ

end ScalarTower

end NormedSpace


#min_imports
