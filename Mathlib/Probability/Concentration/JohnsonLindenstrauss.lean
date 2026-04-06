import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Log.Inequalities
import Mathlib.Probability.Moments.ChiSquared

/-!
# Johnson–Lindenstrauss Lemma (Dasgupta–Gupta 2003)

A Lean 4 formalization of the elementary Gaussian proof of the Johnson–Lindenstrauss
lemma: for any finite set of `n` points in ℝᵈ there exists a linear map into ℝᵐ
with `m = O(ε⁻² log n)` that is an ε-isometry on the set.

## Main results

* `gaussianMatrixMeasure` : i.i.d. N(0,1) product measure on `Fin m → Fin d → ℝ`
* `jl_chisq_complement_bound` : chi-squared Chernoff tail bound for a unit vector
* `jl_concentration_single_pair` : probability that a single pair is ε-preserved
* `jl_union_bound` : existence of a good matrix via union bound over all pairs
* `johnson_lindenstrauss` : the main theorem (linear map formulation)

## References

Dasgupta, S. and Gupta, A. (2003). An elementary proof of a theorem of Johnson
and Lindenstrauss. *Random Structures & Algorithms* 22(1), 60–65.
<https://cseweb.ucsd.edu/~dasgupta/papers/jl.pdf>

## Status

-- STAGING: pending Mathlib PR targeting Mathlib.Probability.Concentration.JohnsonLindenstrauss
-- Sub-lemmas `Real.log_one_add_le`, `Real.log_one_sub_le` are staged in
--   Contrib.Analysis.SpecialFunctions.Log.Inequalities.
-- Sub-lemma `mgf_sq_gaussianReal` is staged in
--   Contrib.Probability.Moments.ChiSquared.
-- Retire all three files once their respective PRs are merged into Mathlib.

## Naming notes (for Mathlib PR)

* `gaussianMatrixMeasure` → consider `Matrix.gaussianMeasure` or a `GaussianMatrix` namespace
* `gaussianMatrix_iIndepFun_rows` → `GaussianMatrix.iIndepFun_rows` or similar
* `EuclideanSpace` vs `PiLp`: the proof uses both; align to one convention for Mathlib
-/

-- ─── Private helpers ─────────────────────────────────────────────────────────

-- Helper: scalar multiplication distributes over matrix-vector multiplication.
-- (c • M).mulVec x = c • M.mulVec x, proved by unfolding to an explicit sum.
private lemma smul_mulVec_real {m d : ℕ} (c : ℝ) (M : Fin m → Fin d → ℝ) (x : Fin d → ℝ) :
    Matrix.mulVec (c • M) x = c • Matrix.mulVec M x := by
  funext i
  show (∑ j : Fin d, (c • M) i j * x j : ℝ) = c * ∑ j : Fin d, M i j * x j
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_assoc]

-- ─── Gaussian matrix measure ──────────────────────────────────────────────────

/-- Gaussian i.i.d. product measure over `m × d` real matrices (each entry ~ N(0,1)).

**Construction**: nested product of `ProbabilityTheory.gaussianReal 0 1` measures,
one per entry, using `MeasureTheory.Measure.pi` twice (over rows, then columns).

**STATUS:** staging for `Mathlib.Probability.Concentration.JohnsonLindenstrauss`.
Retire once merged into Mathlib. -/
noncomputable def gaussianMatrixMeasure (m d : ℕ) :
    MeasureTheory.Measure (Fin m → Fin d → ℝ) :=
  MeasureTheory.Measure.pi (fun _ : Fin m =>
    MeasureTheory.Measure.pi (fun _ : Fin d => ProbabilityTheory.gaussianReal 0 1))

/-- The marginal of `gaussianMatrixMeasure` along row `i` is the i.i.d. N(0,1)
product measure on the `d` entries of that row. -/
lemma gaussianMatrixMeasure_row_map (m d : ℕ) (i : Fin m) :
    (gaussianMatrixMeasure m d).map (Function.eval i) =
    MeasureTheory.Measure.pi (fun _ : Fin d => ProbabilityTheory.gaussianReal 0 1) := by
  simp only [gaussianMatrixMeasure]
  exact (MeasureTheory.measurePreserving_eval
    (μ := fun _ : Fin m =>
      MeasureTheory.Measure.pi (fun _ : Fin d => ProbabilityTheory.gaussianReal 0 1)) i).map_eq

/-- Each individual entry `(i, j)` of a Gaussian matrix has marginal N(0,1). -/
lemma gaussianMatrixMeasure_entry_map (m d : ℕ) (i : Fin m) (j : Fin d) :
    (gaussianMatrixMeasure m d).map (fun A : Fin m → Fin d → ℝ => A i j) =
    ProbabilityTheory.gaussianReal 0 1 := by
  have h : (gaussianMatrixMeasure m d).map (fun A : Fin m → Fin d → ℝ => A i j) =
      ((gaussianMatrixMeasure m d).map (fun A : Fin m → Fin d → ℝ => A i)).map
      (fun v : Fin d → ℝ => v j) := by
    have hc : (fun A : Fin m → Fin d → ℝ => A i j) =
        (fun v : Fin d → ℝ => v j) ∘ (fun A : Fin m → Fin d → ℝ => A i) := by funext; rfl
    rw [hc, MeasureTheory.Measure.map_map (measurable_pi_apply j) (measurable_pi_apply i)]
  rw [h, gaussianMatrixMeasure_row_map]
  exact (MeasureTheory.measurePreserving_eval
    (μ := fun _ : Fin d => ProbabilityTheory.gaussianReal 0 1) j).map_eq

-- ─── Helper C: rows are iIndepFun under gaussianMatrixMeasure ────────────────
private lemma gaussianMatrix_iIndepFun_rows {m d : ℕ} :
    ProbabilityTheory.iIndepFun (fun i (A : Fin m → Fin d → ℝ) => A i)
      (gaussianMatrixMeasure m d) := by
  simp only [gaussianMatrixMeasure]
  exact ProbabilityTheory.iIndepFun_pi (fun _ => aemeasurable_id)

-- ─── Helper D: each row inner product ⟨Aᵢ, x⟩ ∼ N(0,1) for ‖x‖=1 ──────────
-- Stated using the sum directly (avoiding Matrix.dotProduct namespace issues).
private lemma gaussianRow_dotProduct_map {d : ℕ} (x : Fin d → ℝ)
    (hx : ∑ j, x j ^ 2 = 1) :
    (MeasureTheory.Measure.pi (fun _ : Fin d => ProbabilityTheory.gaussianReal 0 1)).map
      (fun v : Fin d → ℝ => ∑ j : Fin d, v j * x j) =
    ProbabilityTheory.gaussianReal 0 1 := by
  -- Strategy: compare characteristic functions then invoke Lévy uniqueness.
  -- charFun (pi.map φ) t = ∫ v, exp(t*(∑ j vj*xj)*I) ∂pi
  --   = ∏ j, ∫ vj, exp(t*xj*vj*I) ∂N(0,1)   (Fubini)
  --   = ∏ j, charFun N(0,1) (t*xj) = ∏ j, exp(-(t*xj)²/2)
  --   = exp(-t²*(∑ xj²)/2) = exp(-t²/2) = charFun N(0,1) t.
  apply MeasureTheory.Measure.ext_of_charFun (E := ℝ)
  ext t
  rw [MeasureTheory.charFun_apply_real,
      MeasureTheory.integral_map
        ((Finset.measurable_sum Finset.univ (fun j _ =>
          (measurable_pi_apply j).mul measurable_const)).aemeasurable)
        (by apply Measurable.aestronglyMeasurable; measurability)]
  -- Simplify charFun_gaussianReal 0 1: cexp(t*0*I - 1*t²/2) → cexp(-t²/2)
  rw [show MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 1) t =
      Complex.exp (-(↑t ^ 2 / 2)) from by
    rw [ProbabilityTheory.charFun_gaussianReal]; congr 1; push_cast; ring]
  -- Rewrite exp(↑t * ↑(∑j vjxj)*I) = ∏j exp(↑(t*xj*vj)*I)
  simp_rw [show ∀ v : Fin d → ℝ,
      Complex.exp (↑t * ↑(∑ j : Fin d, v j * x j) * Complex.I) =
      ∏ j : Fin d, Complex.exp (↑(t * x j * v j) * Complex.I) from fun v => by
    have heq : (↑t : ℂ) * ↑(∑ j : Fin d, v j * x j) * Complex.I =
               ∑ j : Fin d, ↑(t * x j * v j) * Complex.I := by
      push_cast [Finset.mul_sum, Finset.sum_mul]
      congr 1; funext j; ring
    rw [heq, Complex.exp_sum]]
  have hFubini : ∫ (v : Fin d → ℝ),
      ∏ j : Fin d, Complex.exp (↑(t * x j * v j) * Complex.I)
      ∂MeasureTheory.Measure.pi (fun _ => ProbabilityTheory.gaussianReal 0 1) =
      ∏ j : Fin d,
        ∫ (y : ℝ), Complex.exp (↑(t * x j * y) * Complex.I)
        ∂ProbabilityTheory.gaussianReal 0 1 :=
    MeasureTheory.integral_fintype_prod_eq_prod
      (μ := fun _ => ProbabilityTheory.gaussianReal 0 1)
      (fun j (y : ℝ) => Complex.exp (↑(t * x j * y) * Complex.I))
  rw [hFubini]
  -- Each factor equals charFun (gaussianReal 0 1) (t * xj)
  simp_rw [show ∀ (j : Fin d) (vj : ℝ),
      Complex.exp (↑(t * x j * vj) * Complex.I) =
      Complex.exp (↑(t * x j) * ↑vj * Complex.I) from
    fun j vj => by push_cast; ring_nf]
  simp_rw [← MeasureTheory.charFun_apply_real, ProbabilityTheory.charFun_gaussianReal]
  -- ∏ j, exp(-(t*xj)²/2) = exp(-t²/2)
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  -- Simplify μ=0, σ=1 terms (↑t*↑(xj)*0*I - 1*(↑t*↑(xj))²/2  →  -(↑t*↑(xj))²/2)
  simp only [mul_zero, zero_mul, zero_sub, one_mul]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [← Finset.sum_div]
  congr 1
  simp_rw [mul_pow]
  rw [← Finset.mul_sum,
      show (∑ j : Fin d, (x j : ℂ) ^ 2) = 1 from by exact_mod_cast hx]
  ring

-- ─── Main results ─────────────────────────────────────────────────────────────

/-- Chi-squared concentration complement bound (Dasgupta–Gupta 2003, Lemma 2.2).

For a Gaussian matrix `A` drawn from `gaussianMatrixMeasure m d` and a unit
vector `x`, the probability that `(1/√m)² · ‖Ax‖²` falls **outside** `[1−ε, 1+ε]`
is at most `2 · exp(−mε²/8)`.

**Proof sketch:**
Each row dot-product `⟨Aᵢ, x⟩` is N(0,1) (unit-vector rotation), so
`∑ᵢ ⟨Aᵢ, x⟩²` is chi-squared with `m` degrees of freedom.
Upper and lower Chernoff bounds via `measure_ge_le_exp_mul_mgf` /
`measure_le_le_exp_mul_mgf`, optimised at `t_u = ε/(2(1+ε))` and
`t_l = −ε/(2(1−ε))` respectively, yield the stated bound.

**STATUS:** staging for `Mathlib.Probability.Concentration.JohnsonLindenstrauss`.
Retire once merged into Mathlib. -/
lemma jl_chisq_complement_bound
    {m d : ℕ} (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (x : EuclideanSpace ℝ (Fin d)) (hx : ‖x‖ = 1) :
    (gaussianMatrixMeasure m d)
        {A : Fin m → Fin d → ℝ |
          (1 / Real.sqrt ↑m) ^ 2 *
            ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A x)‖ ^ 2
            ∉ Set.Icc (1 - ε) (1 + ε)} ≤
    ENNReal.ofReal (2 * Real.exp (-(↑m * ε ^ 2 / 8))) := by
  -- Basic setup
  haveI hPM : MeasureTheory.IsProbabilityMeasure (gaussianMatrixMeasure m d) := by
    simp only [gaussianMatrixMeasure]; infer_instance
  have hm_real : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm_ne : (m : ℝ) ≠ 0 := hm_real.ne'
  -- Unwrap x to a plain vector x' : Fin d → ℝ (EuclideanSpace ℝ (Fin d) = WithLp 2 (Fin d → ℝ))
  let x' : Fin d → ℝ := fun j => x j
  have hx' : ∑ j : Fin d, x' j ^ 2 = 1 := by
    have h1 : ‖x‖ ^ 2 = 1 := by rw [hx]; norm_num
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt
          (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h1
    simpa [x', Real.norm_eq_abs, sq_abs] using h1
  -- Row dot-product random variable Yi i A = ∑ j, A i j * x'j
  let Yi : Fin m → (Fin m → Fin d → ℝ) → ℝ := fun i A => ∑ j : Fin d, A i j * x' j
  -- Squared chi-squared factor Xi i = Yi i ^ 2
  let Xi : Fin m → (Fin m → Fin d → ℝ) → ℝ := fun i A => Yi i A ^ 2
  -- Key: the bad set equals {∑i Xi ∉ [m(1-ε), m(1+ε)]}
  -- First: (1/sqrt m)^2 * ‖mulVec A x‖^2 = (1/m) * ∑i Xi i A
  have hSqNorm : ∀ A : Fin m → Fin d → ℝ,
      (1 / Real.sqrt ↑m) ^ 2 *
        ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A x)‖ ^ 2 =
      (1 / ↑m) * ∑ i : Fin m, Xi i A := by
    intro A
    have hm_sq : Real.sqrt (↑m : ℝ) ^ 2 = (↑m : ℝ) := Real.sq_sqrt (Nat.cast_nonneg m)
    have hm_sqrt_ne : Real.sqrt (↑m : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hm_real
    -- LHS: (1/sqrt m)^2 * ‖...‖^2 = (1/m) * ∑ Xi
    -- Step A: unfold the EuclideanSpace norm squared as sum of squares
    have hNormSq : ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A x)‖ ^ 2 =
        ∑ i : Fin m, Xi i A := by
      rw [EuclideanSpace.real_norm_sq_eq]
      congr 1
    rw [hNormSq]
    have h1 : (1 / Real.sqrt ↑m) ^ 2 = 1 / (↑m : ℝ) := by
      rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    rw [h1]
  -- Rewrite bad set in terms of ∑ Xi
  have bad_eq : {A : Fin m → Fin d → ℝ |
      (1 / Real.sqrt ↑m) ^ 2 *
        ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A x)‖ ^ 2
        ∉ Set.Icc (1 - ε) (1 + ε)} =
      {A | ∑ i : Fin m, Xi i A ∉ Set.Icc (↑m * (1 - ε)) (↑m * (1 + ε))} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_Icc, not_and_or, not_le]
    rw [hSqNorm]
    have hm_pos := hm_real
    have hm_mul_inv : (m:ℝ) * (1/(m:ℝ)) = 1 := by field_simp
    constructor
    · rintro (h | h)
      · -- h : (1/m) * ∑Xi < 1 - ε, need ∑Xi < m*(1-ε)
        exact Or.inl (by
          have key := mul_lt_mul_of_pos_left h hm_pos
          rw [show (m:ℝ) * (1/(m:ℝ) * ∑ i : Fin m, Xi i A) =
              ∑ i : Fin m, Xi i A from by rw [← mul_assoc, hm_mul_inv, one_mul]] at key
          linarith)
      · -- h : 1 + ε < (1/m) * ∑Xi, need m*(1+ε) < ∑Xi
        exact Or.inr (by
          have key := mul_lt_mul_of_pos_left h hm_pos
          rw [show (m:ℝ) * (1/(m:ℝ) * ∑ i : Fin m, Xi i A) =
              ∑ i : Fin m, Xi i A from by rw [← mul_assoc, hm_mul_inv, one_mul]] at key
          linarith)
    · rintro (h | h)
      · -- h : ∑Xi < m*(1-ε), need (1/m)*∑Xi < 1 - ε
        exact Or.inl (by
          have key : (1/(m:ℝ)) * ∑ i : Fin m, Xi i A < (1/(m:ℝ)) * (↑m * (1 - ε)) :=
            mul_lt_mul_of_pos_left h (by positivity)
          simp only [one_div, ← mul_assoc, inv_mul_cancel₀ hm_ne, one_mul] at key
          rw [← one_div] at key
          linarith)
      · -- h : m*(1+ε) < ∑Xi, need 1 + ε < (1/m)*∑Xi
        exact Or.inr (by
          have key : (1/(m:ℝ)) * (↑m * (1 + ε)) < (1/(m:ℝ)) * ∑ i : Fin m, Xi i A :=
            mul_lt_mul_of_pos_left h (by positivity)
          simp only [one_div, ← mul_assoc, inv_mul_cancel₀ hm_ne, one_mul] at key
          rw [← one_div] at key
          linarith)
  rw [bad_eq]
  -- Use union bound: bad ⊆ upper_tail ∪ lower_tail
  have bad_subset : {A : Fin m → Fin d → ℝ | ∑ i : Fin m, Xi i A ∉ Set.Icc (↑m * (1 - ε)) (↑m * (1 + ε))} ⊆
      {A | ↑m * (1 + ε) < ∑ i : Fin m, Xi i A} ∪
      {A | ∑ i : Fin m, Xi i A < ↑m * (1 - ε)} := by
    intro A hA
    simp only [Set.mem_setOf_eq, Set.mem_Icc, not_and_or, not_le] at hA
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases hA with h | h
    · right; exact h
    · left; exact h
  apply (MeasureTheory.measure_mono bad_subset).trans
  rw [show (2 : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8)) =
      Real.exp (-(↑m * ε ^ 2 / 8)) + Real.exp (-(↑m * ε ^ 2 / 8)) from by ring]
  rw [ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
  -- iIndepFun for the Xi's (from rows being independent)
  have hYi_meas : ∀ i : Fin m, Measurable (Yi i) := fun i => by
    apply Finset.measurable_sum; intro j _
    exact ((measurable_pi_apply j).comp (measurable_pi_apply i)).mul measurable_const
  have hXi_meas : ∀ i : Fin m, Measurable (Xi i) :=
    fun i => (hYi_meas i).pow_const 2
  have hXi_indep : ProbabilityTheory.iIndepFun Xi (gaussianMatrixMeasure m d) := by
    have h_rows := gaussianMatrix_iIndepFun_rows (m := m) (d := d)
    -- Yi i = (fun v => ∑ j, v j * x' j) ∘ (fun A => A i)
    have hYi_indep : ProbabilityTheory.iIndepFun Yi (gaussianMatrixMeasure m d) := by
      have hcomp := h_rows.comp (g := fun _ v => ∑ j : Fin d, v j * x' j)
        (fun _ => Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).mul measurable_const))
      exact hcomp
    have hXi_eq : ∀ i, Xi i = (fun y : ℝ => y ^ 2) ∘ Yi i := fun i => rfl
    exact hYi_indep.comp (fun _ => (fun y : ℝ => y ^ 2))
      (fun _ => measurable_id.pow_const 2)
  -- MGF of each Xi i under gaussianMatrixMeasure = (1 - 2t)^{-1/2}
  have hXi_mgf : ∀ (i : Fin m) (t : ℝ), t < 1 / 2 →
      ProbabilityTheory.mgf (Xi i) (gaussianMatrixMeasure m d) t =
      (1 - 2 * t) ^ (-(1/2 : ℝ)) := by
    intro i t ht
    -- mgf Xi i μ t = mgf (· ^ 2) N(0,1) t by change-of-variables via gaussianRow_dotProduct_map
    have hmap : (gaussianMatrixMeasure m d).map (Yi i) = ProbabilityTheory.gaussianReal 0 1 := by
      have hrow := gaussianMatrixMeasure_row_map m d i
      have hdot := gaussianRow_dotProduct_map x' hx'
      rw [show Yi i = (fun v : Fin d → ℝ => ∑ j : Fin d, v j * x' j) ∘ (fun A => A i) from rfl]
      rw [← MeasureTheory.Measure.map_map
            (Finset.measurable_sum _ (fun j _ =>
              (measurable_pi_apply j).mul measurable_const)) (measurable_pi_apply i)]
      rw [hrow, hdot]
    rw [show ProbabilityTheory.mgf (Xi i) (gaussianMatrixMeasure m d) t =
         ProbabilityTheory.mgf (fun y : ℝ => y ^ 2) ((gaussianMatrixMeasure m d).map (Yi i)) t from
       (ProbabilityTheory.mgf_map (hYi_meas i).aemeasurable
         (((measurable_id.pow_const 2).const_mul t).exp.aestronglyMeasurable)).symm,
     hmap]
    exact mgf_sq_gaussianReal ht
  -- MGF of the sum ∑ Xi over all rows = (1 - 2t)^{-m/2}
  have hSum_mgf : ∀ t : ℝ, t < 1 / 2 →
      ProbabilityTheory.mgf (∑ i : Fin m, Xi i) (gaussianMatrixMeasure m d) t =
      (1 - 2 * t) ^ (-(↑m / 2 : ℝ)) := by
    intro t ht
    rw [hXi_indep.mgf_sum hXi_meas Finset.univ]
    simp_rw [hXi_mgf _ t ht]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Real.rpow_natCast ((1 - 2 * t) ^ (-(1 / 2 : ℝ))) m,
        ← Real.rpow_mul (by linarith [ht])]
    congr 1; ring
  -- Integrability of exp(t * ∑ Xi)
  have hInt_upper : ∀ t : ℝ, 0 ≤ t → t < 1 / 2 →
      MeasureTheory.Integrable (fun A => Real.exp (t * ∑ i : Fin m, Xi i A))
        (gaussianMatrixMeasure m d) := by
    intro t ht_nn ht
    by_contra h_not_int
    -- Non-integrable ↝ Bochner integral equals 0
    have h0 : ∫ A : Fin m → Fin d → ℝ, Real.exp (t * ∑ i : Fin m, Xi i A)
        ∂(gaussianMatrixMeasure m d) = 0 :=
      MeasureTheory.integral_undef h_not_int
    -- The MGF formula evaluates the same integral to (1-2t)^{-m/2}
    have hmgf_int : ∫ A : Fin m → Fin d → ℝ, Real.exp (t * ∑ i : Fin m, Xi i A)
        ∂(gaussianMatrixMeasure m d) = (1 - 2 * t) ^ (-(↑m / 2 : ℝ)) := by
      have hfun : (fun A : Fin m → Fin d → ℝ => ∑ i : Fin m, Xi i A) = ∑ i : Fin m, Xi i :=
        funext fun A => (Finset.sum_apply A Finset.univ Xi).symm
      have hval : ProbabilityTheory.mgf (fun A : Fin m → Fin d → ℝ => ∑ i : Fin m, Xi i A)
          (gaussianMatrixMeasure m d) t = (1 - 2 * t) ^ (-(↑m / 2 : ℝ)) := by
        rw [hfun]; exact hSum_mgf t ht
      simp only [ProbabilityTheory.mgf] at hval
      exact hval
    -- Contradiction: h0 gives 0 = (1-2t)^{-m/2} but (1-2t)^{-m/2} > 0
    rw [h0] at hmgf_int
    linarith [Real.rpow_pos_of_pos (by linarith : (0:ℝ) < 1 - 2 * t) (-(↑m / 2 : ℝ))]
  -- ── Upper tail ──────────────────────────────────────────────────────────────
  -- Set t_u = ε / (2 * (1 + ε)) which is in (0, 1/2)
  let t_u : ℝ := ε / (2 * (1 + ε))
  have ht_u_pos : 0 < t_u := by positivity
  have ht_u_half : t_u < 1 / 2 := by
    simp only [t_u]
    rw [div_lt_iff₀ (show (0:ℝ) < 2 * (1 + ε) from by positivity)]
    linarith
  have ht_u_val : 1 - 2 * t_u = 1 / (1 + ε) := by
    simp only [t_u]; field_simp; ring
  have hUpper : (gaussianMatrixMeasure m d)
      {A | ↑m * (1 + ε) < ∑ i : Fin m, Xi i A} ≤
      ENNReal.ofReal (Real.exp (-(↑m * ε ^ 2 / 8))) := by
    have hChern := ProbabilityTheory.measure_ge_le_exp_mul_mgf
        (↑m * (1 + ε)) (t := t_u) ht_u_pos.le (X := fun A => ∑ i : Fin m, Xi i A)
        (μ := gaussianMatrixMeasure m d)
        (hInt_upper t_u ht_u_pos.le ht_u_half)
    -- hChern : μ.real {A | ∑ Xi ≥ m*(1+ε)} ≤ exp(-t_u * m*(1+ε)) * mgf (∑ Xi) μ t_u
    have hmgf_u : ProbabilityTheory.mgf (fun A : Fin m → Fin d → ℝ => ∑ i : Fin m, Xi i A)
        (gaussianMatrixMeasure m d) t_u = (1 - 2 * t_u) ^ (-((↑m : ℝ) / 2)) := by
      have hfun : (fun A : Fin m → Fin d → ℝ => ∑ i : Fin m, Xi i A) = ∑ i : Fin m, Xi i :=
        funext fun A => (Finset.sum_apply A Finset.univ Xi).symm
      rw [hfun]; exact hSum_mgf t_u ht_u_half
    rw [hmgf_u] at hChern
    -- exp(-t_u * m*(1+ε)) * (1-2t_u)^{-m/2}
    --  = exp(-m*ε/2) * ((1+ε)^{1/2})^m = exp(-m*ε/2) * (1+ε)^{m/2}
    --  ≤ exp(-m*ε^2/8)
    have hbound : Real.exp (-t_u * (↑m * (1 + ε))) *
        (1 - 2 * t_u) ^ (-((↑m : ℝ) / 2)) ≤ Real.exp (-(↑m * ε ^ 2 / 8)) := by
      rw [ht_u_val]
      have hone_add_pos : (0 : ℝ) < 1 + ε := by linarith
      have hlog := Real.log_one_add_le (by linarith : -1 < ε) hε'.le
      have hrpow : (1 / (1 + ε)) ^ (-((↑m : ℝ) / 2)) = Real.exp ((↑m / 2) * Real.log (1 + ε)) := by
        have h_pos : (0 : ℝ) < 1 / (1 + ε) := by positivity
        rw [Real.rpow_def_of_pos h_pos]
        have hlog_div : Real.log (1 / (1 + ε)) = -Real.log (1 + ε) := by
          rw [Real.log_div one_ne_zero (ne_of_gt hone_add_pos), Real.log_one, zero_sub]
        rw [hlog_div]; congr 1; ring
      have ht_u_simp : -t_u * (↑m * (1 + ε)) = -(↑m * ε / 2) := by
        have heq : t_u = ε / (2 * (1 + ε)) := rfl
        rw [heq]; field_simp [show (1 + ε) ≠ 0 from by linarith]
      rw [hrpow, ht_u_simp, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ ↑m / 2)]
    -- Convert from real to ENNReal
    have hfin : (gaussianMatrixMeasure m d)
        {A : Fin m → Fin d → ℝ | ↑m * (1 + ε) < ∑ i : Fin m, Xi i A} ≠ ⊤ :=
      MeasureTheory.measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hfin]
    apply ENNReal.ofReal_le_ofReal
    have key : (gaussianMatrixMeasure m d).real
        {A : Fin m → Fin d → ℝ | ↑m * (1 + ε) ≤ ∑ i : Fin m, Xi i A} ≤
        Real.exp (-(↑m * ε ^ 2 / 8)) :=
      (hChern.trans (by exact_mod_cast hbound)).trans (by rfl)
    calc (gaussianMatrixMeasure m d).real {A | ↑m * (1 + ε) < ∑ i : Fin m, Xi i A}
      ≤ (gaussianMatrixMeasure m d).real {A | ↑m * (1 + ε) ≤ ∑ i : Fin m, Xi i A} := by
            apply ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
            apply MeasureTheory.measure_mono
            intro A hA
            simp only [Set.mem_setOf_eq] at hA ⊢
            exact hA.le
      _ ≤ Real.exp (-(↑m * ε ^ 2 / 8)) := key
  -- ── Lower tail ──────────────────────────────────────────────────────────────
  let t_l : ℝ := -(ε / (2 * (1 - ε)))
  have ht_l_neg : t_l < 0 := by
    have hdiv : 0 < ε / (2 * (1 - ε)) := div_pos hε (by linarith)
    simp only [t_l]; linarith
  have ht_l_half : t_l < 1 / 2 := by linarith
  have ht_l_val : 1 - 2 * t_l = 1 / (1 - ε) := by
    simp only [t_l]; field_simp [show (1 - ε) ≠ 0 from by linarith]; ring
  have hLower : (gaussianMatrixMeasure m d)
      {A | ∑ i : Fin m, Xi i A < ↑m * (1 - ε)} ≤
      ENNReal.ofReal (Real.exp (-(↑m * ε ^ 2 / 8))) := by
    have hChern := ProbabilityTheory.measure_le_le_exp_mul_mgf
        (↑m * (1 - ε)) (t := t_l) (le_of_lt ht_l_neg) (X := fun A => ∑ i : Fin m, Xi i A)
        (μ := gaussianMatrixMeasure m d)
        (by
          apply MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const 1)
          · exact (Real.measurable_exp.comp (measurable_const.mul
              (Finset.measurable_sum Finset.univ (fun i _ => hXi_meas i)))).aestronglyMeasurable
          · filter_upwards with A
            simp only [Real.norm_eq_abs, norm_one, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg ht_l_neg.le
              (Finset.sum_nonneg (fun i _ => sq_nonneg (Yi i A)))))
    have hmgf_l : ProbabilityTheory.mgf (fun A : Fin m → Fin d → ℝ => ∑ i : Fin m, Xi i A)
        (gaussianMatrixMeasure m d) t_l = (1 - 2 * t_l) ^ (-((↑m : ℝ) / 2)) := by
      have hfun : (fun A : Fin m → Fin d → ℝ => ∑ i : Fin m, Xi i A) = ∑ i : Fin m, Xi i :=
        funext fun A => (Finset.sum_apply A Finset.univ Xi).symm
      rw [hfun]; exact hSum_mgf t_l ht_l_half
    rw [hmgf_l] at hChern
    have hbound : Real.exp (-t_l * (↑m * (1 - ε))) *
        (1 - 2 * t_l) ^ (-((↑m : ℝ) / 2)) ≤ Real.exp (-(↑m * ε ^ 2 / 8)) := by
      rw [ht_l_val]
      have hone_sub_pos : (0 : ℝ) < 1 - ε := by linarith
      have hlog := Real.log_one_sub_le hε.le hε'
      have hrpow : (1 / (1 - ε)) ^ (-((↑m : ℝ) / 2)) = Real.exp ((↑m / 2) * Real.log (1 - ε)) := by
        have h_pos : (0 : ℝ) < 1 / (1 - ε) := by positivity
        rw [Real.rpow_def_of_pos h_pos]
        have hlog_div : Real.log (1 / (1 - ε)) = -Real.log (1 - ε) := by
          rw [Real.log_div one_ne_zero (ne_of_gt hone_sub_pos), Real.log_one, zero_sub]
        rw [hlog_div]; congr 1; ring
      have ht_l_simp : -t_l * (↑m * (1 - ε)) = ↑m * ε / 2 := by
        have heq : t_l = -(ε / (2 * (1 - ε))) := rfl
        rw [heq]; field_simp [show (1 - ε) ≠ 0 from by linarith]
      rw [hrpow, ht_l_simp, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ ↑m / 2)]
    have hfin : (gaussianMatrixMeasure m d)
        {A | ∑ i : Fin m, Xi i A < ↑m * (1 - ε)} ≠ ⊤ :=
      MeasureTheory.measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hfin]
    apply ENNReal.ofReal_le_ofReal
    have key : (gaussianMatrixMeasure m d).real
        {A : Fin m → Fin d → ℝ | ∑ i : Fin m, Xi i A ≤ ↑m * (1 - ε)} ≤
        Real.exp (-(↑m * ε ^ 2 / 8)) :=
      (hChern.trans (by exact_mod_cast hbound)).trans (by rfl)
    calc (gaussianMatrixMeasure m d).real {A | ∑ i : Fin m, Xi i A < ↑m * (1 - ε)}
      ≤ (gaussianMatrixMeasure m d).real {A | ∑ i : Fin m, Xi i A ≤ ↑m * (1 - ε)} := by
            apply ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
            apply MeasureTheory.measure_mono
            intro A hA
            simp only [Set.mem_setOf_eq] at hA ⊢
            exact hA.le
      _ ≤ Real.exp (-(↑m * ε ^ 2 / 8)) := key
  -- Combine via union bound
  calc (gaussianMatrixMeasure m d)
        ({A | ↑m * (1 + ε) < ∑ i : Fin m, Xi i A} ∪
         {A | ∑ i : Fin m, Xi i A < ↑m * (1 - ε)})
      ≤ (gaussianMatrixMeasure m d) {A | ↑m * (1 + ε) < ∑ i : Fin m, Xi i A} +
        (gaussianMatrixMeasure m d) {A | ∑ i : Fin m, Xi i A < ↑m * (1 - ε)} :=
            MeasureTheory.measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(↑m * ε ^ 2 / 8))) +
        ENNReal.ofReal (Real.exp (-(↑m * ε ^ 2 / 8))) :=
            add_le_add hUpper hLower

/-- A scaled Gaussian projection of a unit vector concentrates within `(1 ± ε)` of 1.

For a fixed unit vector `x ∈ ℝᵈ` and `A ∼ GaussianMatrix(m, d)`:

  `P[ (1/√m)² · ‖Ax‖² ∈ [1−ε, 1+ε] ] ≥ 1 − 2 · exp(−mε²/8)`

**Proof:** apply `jl_chisq_complement_bound` to the complement, then use
`prob_compl_eq_one_sub` to convert.

**STATUS:** staging for `Mathlib.Probability.Concentration.JohnsonLindenstrauss`.
Retire once merged into Mathlib. -/
lemma jl_concentration_single_pair
    {m d : ℕ} (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (x : EuclideanSpace ℝ (Fin d)) (hx : ‖x‖ = 1) :
    (gaussianMatrixMeasure m d)
        {A : Fin m → Fin d → ℝ |
          (1 / Real.sqrt ↑m) ^ 2 *
            ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A x)‖ ^ 2
            ∈ Set.Icc (1 - ε) (1 + ε)} ≥
    ENNReal.ofReal (1 - 2 * Real.exp (-(↑m * ε ^ 2 / 8))) := by
  -- Name S and note Sᶜ = {A | ... ∉ Icc} matches jl_chisq_complement_bound exactly
  set S : Set (Fin m → Fin d → ℝ) := {A |
    (1 / Real.sqrt ↑m) ^ 2 *
      ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A x)‖ ^ 2
      ∈ Set.Icc (1 - ε) (1 + ε)} with hS_def
  -- Measurability
  have hS_meas : MeasurableSet S := by
    simp only [hS_def]; measurability
  -- Establish that gaussianMatrixMeasure m d is a probability measure (needed for prob_compl)
  haveI hPM : MeasureTheory.IsProbabilityMeasure (gaussianMatrixMeasure m d) := by
    simp only [gaussianMatrixMeasure]
    infer_instance
  -- Complement bound from jl_chisq_complement_bound (Sᶜ = {A | ... ∉ Icc})
  have hSc : (gaussianMatrixMeasure m d) Sᶜ ≤
      ENNReal.ofReal (2 * Real.exp (-(↑m * ε ^ 2 / 8))) := by
    have hset : Sᶜ = {A : Fin m → Fin d → ℝ |
        (1 / Real.sqrt ↑m) ^ 2 *
          ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A x)‖ ^ 2
          ∉ Set.Icc (1 - ε) (1 + ε)} :=
      Set.ext (fun A => by simp [hS_def, Set.mem_compl_iff])
    rw [hset]
    exact jl_chisq_complement_bound hm ε hε hε' x hx
  -- Probability measure: μ S = 1 - μ Sᶜ  (from prob_compl applied to Sᶜ)
  have hS_eq : (gaussianMatrixMeasure m d) S =
      1 - (gaussianMatrixMeasure m d) Sᶜ := by
    have h := MeasureTheory.prob_compl_eq_one_sub
        (μ := gaussianMatrixMeasure m d) hS_meas.compl
    simp only [compl_compl] at h
    exact h
  -- ENNReal.ofReal (1 - 2r) = 1 - ENNReal.ofReal (2r) (truncated sub, no case split needed)
  have hge : (0 : ℝ) ≤ 2 * Real.exp (-(↑m * ε ^ 2 / 8)) := by positivity
  calc ENNReal.ofReal (1 - 2 * Real.exp (-(↑m * ε ^ 2 / 8)))
      = 1 - ENNReal.ofReal (2 * Real.exp (-(↑m * ε ^ 2 / 8))) := by
        rw [ENNReal.ofReal_sub 1 hge, ENNReal.ofReal_one]
    _ ≤ 1 - (gaussianMatrixMeasure m d) Sᶜ := by gcongr
    _ = (gaussianMatrixMeasure m d) S := hS_eq.symm

/-- With `m ≥ 8ε⁻² · log(n(n−1))` projection dimensions a single random Gaussian
matrix preserves **all** pairwise distances simultaneously (union bound).

**Proof sketch:**
Normalise each difference `u − v` to a unit vector, apply
`jl_concentration_single_pair`, union-bound over `|S|(|S|−1)` ordered pairs,
verify the product is `< 1` from the hypothesis on `m`, and extract a witness
by positive measure implies non-empty.

**STATUS:** staging for `Mathlib.Probability.Concentration.JohnsonLindenstrauss`.
Retire once merged into Mathlib. -/
lemma jl_union_bound
    {d : ℕ}
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (S : Finset (EuclideanSpace ℝ (Fin d)))
    (m : ℕ)
    (hm : (↑m : ℝ) > 8 * ε⁻¹ ^ 2 * Real.log (2 * ↑S.card * (↑S.card - 1))) :
    ∃ A : Fin m → Fin d → ℝ,
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
        (1 - ε) * ‖u - v‖ ^ 2 ≤
          (1 / Real.sqrt ↑m) ^ 2 *
            ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A (u - v))‖ ^ 2 ∧
        (1 / Real.sqrt ↑m) ^ 2 *
            ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A (u - v))‖ ^ 2 ≤
          (1 + ε) * ‖u - v‖ ^ 2 := by
  -- Case 1: |S| ≤ 1 → no u ≠ v pairs exist; any matrix satisfies the vacuous ∀.
  by_cases hS : S.card ≤ 1
  · exact ⟨0, fun u hu v hv huv =>
      absurd (Finset.card_le_one.mp hS u hu v hv) huv⟩
  · push Not at hS   -- hS : 1 < S.card
    -- Case 2: |S| ≥ 2 — probabilistic method.
    -- Define Good = {A | all (u,v) pairs are ε-preserved by (1/√m)·A}.
    set Good : Set (Fin m → Fin d → ℝ) :=
      {A | ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
        (1 - ε) * ‖u - v‖ ^ 2 ≤
          (1 / Real.sqrt ↑m) ^ 2 *
            ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A (u - v))‖ ^ 2 ∧
        (1 / Real.sqrt ↑m) ^ 2 *
            ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A (u - v))‖ ^ 2 ≤
          (1 + ε) * ‖u - v‖ ^ 2}
    -- P[Good] > 0 via union bound over S.offDiag pairs.
    have hGood_pos : 0 < gaussianMatrixMeasure m d Good := by
      haveI hPM : MeasureTheory.IsProbabilityMeasure (gaussianMatrixMeasure m d) := by
        simp only [gaussianMatrixMeasure]; infer_instance
      -- Step 0: m > 0
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp only [Nat.cast_zero, gt_iff_lt] at hm
          have h2' : (2 : ℝ) ≤ ↑S.card := by exact_mod_cast Nat.succ_le_of_lt hS
          have hlog : (0 : ℝ) ≤ Real.log (2 * ↑S.card * (↑S.card - 1)) := by
            apply Real.log_nonneg; nlinarith
          linarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8)
            (by positivity : (0:ℝ) ≤ ε⁻¹ ^ 2)) hlog]
        · exact h
      -- Numerical helpers
      have h2 : (2 : ℝ) ≤ ↑S.card := by exact_mod_cast Nat.succ_le_of_lt hS
      have hn_pos : (0 : ℝ) < ↑S.card * (↑S.card - 1) := by nlinarith
      have h2n_pos : (0 : ℝ) < 2 * ↑S.card * (↑S.card - 1) := by linarith
      have hε2_pos : (0 : ℝ) < ε ^ 2 := by positivity
      -- Measurability of Good via IsClosed (finite biInter of preimages of Icc under cts fn)
      have hGood_meas : MeasurableSet Good := by
        suffices h : IsClosed Good from h.measurableSet
        have heq : Good = ⋂ p ∈ S.offDiag,
            {A : Fin m → Fin d → ℝ |
              (1 - ε) * ‖p.1 - p.2‖ ^ 2 ≤
                (1 / Real.sqrt ↑m) ^ 2 *
                  ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A (p.1 - p.2))‖ ^ 2 ∧
              (1 / Real.sqrt ↑m) ^ 2 *
                  ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A (p.1 - p.2))‖ ^ 2 ≤
                (1 + ε) * ‖p.1 - p.2‖ ^ 2} := by
          ext A
          simp only [Good, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_offDiag]
          exact ⟨fun h p ⟨hu, hv, ne⟩ => h p.1 hu p.2 hv ne,
                 fun h u hu v hv ne => h ⟨u, v⟩ ⟨hu, hv, ne⟩⟩
        rw [heq]
        apply isClosed_biInter
        intro p _
        -- f(A) = (1/√m)^2 * ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (mulVec A w)‖^2 is continuous
        have hcont : Continuous (fun A : Fin m → Fin d → ℝ =>
            (1 / Real.sqrt ↑m) ^ 2 *
              ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A (p.1 - p.2))‖ ^ 2) := by
          apply Continuous.mul continuous_const
          apply Continuous.pow _ 2
          apply Continuous.norm
          apply Continuous.comp
          · exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.continuous
          · apply continuous_pi
            intro i
            rw [show (fun A : Fin m → Fin d → ℝ => Matrix.mulVec A (p.1 - p.2) i) =
                  (fun A : Fin m → Fin d → ℝ => ∑ j : Fin d, A i j * (p.1 - p.2) j) from
                funext fun A => rfl]
            apply continuous_finset_sum
            intro j _
            exact ((continuous_apply j : Continuous (fun g : Fin d → ℝ => g j)).mul
              continuous_const).comp
              (continuous_apply i : Continuous (fun A : Fin m → Fin d → ℝ => A i))
        apply IsClosed.inter
        · exact isClosed_le continuous_const hcont
        · exact isClosed_le hcont continuous_const
      -- Bad predicate for each ordered pair
      let Bad : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
          Set (Fin m → Fin d → ℝ) :=
        fun p => {A | (1 / Real.sqrt ↑m) ^ 2 *
            ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A (p.1 - p.2))‖ ^ 2
            ∉ Set.Icc ((1 - ε) * ‖p.1 - p.2‖ ^ 2) ((1 + ε) * ‖p.1 - p.2‖ ^ 2)}
      -- Step 1: Goodᶜ ⊆ ⋃_{p ∈ S.offDiag} Bad p
      have hsubset : Goodᶜ ⊆ ⋃ p ∈ S.offDiag, Bad p := by
        intro M hM
        simp only [Set.mem_compl_iff, Good, Set.mem_setOf_eq, not_forall] at hM
        obtain ⟨u, hu, v, hv, ne_uv, hbad⟩ := hM
        simp only [Set.mem_iUnion]
        exact ⟨(u, v), Finset.mem_offDiag.mpr ⟨hu, hv, ne_uv⟩, hbad⟩
      -- Step 2: Union bound
      have hunion : gaussianMatrixMeasure m d Goodᶜ ≤
          ∑ p ∈ S.offDiag, gaussianMatrixMeasure m d (Bad p) :=
        (MeasureTheory.measure_mono hsubset).trans
          (MeasureTheory.measure_biUnion_finset_le S.offDiag Bad)
      -- Step 3: Per-pair bound via normalization + jl_chisq_complement_bound
      have hbad_each : ∀ p ∈ S.offDiag, gaussianMatrixMeasure m d (Bad p) ≤
          ENNReal.ofReal (2 * Real.exp (-(↑m * ε ^ 2 / 8))) := by
        intro ⟨u, v⟩ hpair
        obtain ⟨_hu, _hv, hne⟩ := Finset.mem_offDiag.mp hpair
        have hnorm_pos : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
        have hnorm_ne : ‖u - v‖ ≠ 0 := ne_of_gt hnorm_pos
        -- Unit vector in the direction of u - v
        let w : EuclideanSpace ℝ (Fin d) := ‖u - v‖⁻¹ • (u - v)
        have hw : ‖w‖ = 1 := by
          simp only [w, norm_smul, norm_inv, norm_norm]
          exact inv_mul_cancel₀ hnorm_ne
        -- u.ofLp - v.ofLp = ‖u - v‖ • w.ofLp, proved component-wise
        have hdiff : (u.ofLp - v.ofLp : Fin d → ℝ) = ‖u - v‖ • w.ofLp := by
          funext j
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, w,
                     PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          field_simp [hnorm_ne]
        -- mulVec A (u.ofLp - v.ofLp) = ‖u-v‖ • mulVec A w.ofLp, by linearity
        have hmv : ∀ A : Fin m → Fin d → ℝ,
            Matrix.mulVec A (u.ofLp - v.ofLp) = ‖u - v‖ • Matrix.mulVec A w.ofLp := fun A => by
          nth_rw 1 [hdiff]
          exact (Matrix.mulVecLin A).map_smul _ _
        -- Subset bound: Bad(u,v) ⊆ chi-sq bad set for unit vector w
        have hsubset_pair : Bad (u, v) ⊆ {A : Fin m → Fin d → ℝ |
            (1 / Real.sqrt ↑m) ^ 2 *
              ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A w)‖ ^ 2
              ∉ Set.Icc (1 - ε) (1 + ε)} := by
          intro A hA
          simp only [Bad, Set.mem_setOf_eq, Set.mem_Icc, not_and_or, not_le] at hA
          simp only [Set.mem_setOf_eq, Set.mem_Icc, not_and_or, not_le]
          have hnorm_eq :
              ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A (u.ofLp - v.ofLp))‖ ^ 2 =
              ‖u - v‖ ^ 2 *
                ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A w)‖ ^ 2 := by
            rw [hmv A]
            -- (WithLp.equiv 2 ...).symm distributes over smul by rfl (WithLp p α = α definitionally)
            have h_smul : (WithLp.equiv 2 (Fin m → ℝ)).symm
                (‖u - v‖ • Matrix.mulVec A w.ofLp) =
                ‖u - v‖ • (WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A w) := rfl
            rw [h_smul, norm_smul, Real.norm_of_nonneg (le_of_lt hnorm_pos), mul_pow]
          have hfactor : (1 / Real.sqrt ↑m) ^ 2 *
              ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A (u.ofLp - v.ofLp))‖ ^ 2 =
              ‖u - v‖ ^ 2 * ((1 / Real.sqrt ↑m) ^ 2 *
                ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A w)‖ ^ 2) := by
            rw [hnorm_eq]; ring
          have hc : 0 < ‖u - v‖ ^ 2 := pow_pos hnorm_pos 2
          rw [hfactor] at hA
          set X := (1 / Real.sqrt ↑m) ^ 2 *
            ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A w)‖ ^ 2
          rcases hA with h | h
          · left; nlinarith
          · right; nlinarith
        calc gaussianMatrixMeasure m d (Bad (u, v))
            ≤ gaussianMatrixMeasure m d {A : Fin m → Fin d → ℝ |
                (1 / Real.sqrt ↑m) ^ 2 *
                  ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A w)‖ ^ 2
                  ∉ Set.Icc (1 - ε) (1 + ε)} :=
              MeasureTheory.measure_mono hsubset_pair
          _ ≤ ENNReal.ofReal (2 * Real.exp (-(↑m * ε ^ 2 / 8))) :=
              jl_chisq_complement_bound hm_pos ε hε hε' w hw
      -- Step 4: Sum ≤ ENNReal.ofReal(|offDiag| · 2·exp(-mε²/8))
      have hsum : ∑ p ∈ S.offDiag, gaussianMatrixMeasure m d (Bad p) ≤
          ENNReal.ofReal (↑S.offDiag.card * (2 * Real.exp (-(↑m * ε ^ 2 / 8)))) := by
        calc ∑ p ∈ S.offDiag, gaussianMatrixMeasure m d (Bad p)
            ≤ ∑ _p ∈ S.offDiag, ENNReal.ofReal (2 * Real.exp (-(↑m * ε ^ 2 / 8))) :=
                Finset.sum_le_sum hbad_each
          _ = ↑S.offDiag.card * ENNReal.ofReal (2 * Real.exp (-(↑m * ε ^ 2 / 8))) := by
                rw [Finset.sum_const, nsmul_eq_mul]
          _ = ENNReal.ofReal (↑S.offDiag.card * (2 * Real.exp (-(↑m * ε ^ 2 / 8)))) := by
                rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      -- Step 5: The sum < 1 (arithmetic from hm)
      have hlt_one : ENNReal.ofReal (↑S.offDiag.card * (2 * Real.exp (-(↑m * ε ^ 2 / 8)))) < 1 := by
        rw [ENNReal.ofReal_lt_one]
        have h1 : S.card ≤ S.card * S.card := by nlinarith
        have hcard : (↑S.offDiag.card : ℝ) = ↑S.card * (↑S.card - 1) := by
          rw [Finset.offDiag_card, Nat.cast_sub h1]; push_cast; ring
        have hrw : (↑S.card : ℝ) * ((↑S.card : ℝ) - 1) * (2 * Real.exp (-(↑m * ε ^ 2 / 8))) =
            2 * (↑S.card : ℝ) * ((↑S.card : ℝ) - 1) * Real.exp (-(↑m * ε ^ 2 / 8)) := by ring
        rw [hcard, hrw]
        have hlog_lt : Real.log (2 * ↑S.card * (↑S.card - 1)) < ↑m * ε ^ 2 / 8 := by
          calc Real.log (2 * ↑S.card * (↑S.card - 1))
              = ε ^ 2 / 8 * (8 * ε⁻¹ ^ 2 * Real.log (2 * ↑S.card * (↑S.card - 1))) := by
                  rw [inv_pow]; field_simp [ne_of_gt hε2_pos]
            _ < ε ^ 2 / 8 * ↑m := mul_lt_mul_of_pos_left hm (by positivity)
            _ = ↑m * ε ^ 2 / 8 := by ring
        have h2n_ne : (2 : ℝ) * ↑S.card * (↑S.card - 1) ≠ 0 := ne_of_gt h2n_pos
        have hexp_lt : Real.exp (-(↑m * ε ^ 2 / 8)) < ((2 : ℝ) * ↑S.card * (↑S.card - 1))⁻¹ := by
          rw [show ((2 : ℝ) * ↑S.card * (↑S.card - 1))⁻¹ =
              Real.exp (- Real.log ((2 : ℝ) * ↑S.card * (↑S.card - 1))) by
            rw [Real.exp_neg, Real.exp_log h2n_pos]]
          exact Real.exp_lt_exp.mpr (by linarith)
        calc 2 * (↑S.card : ℝ) * (↑S.card - 1) * Real.exp (-(↑m * ε ^ 2 / 8))
            < 2 * (↑S.card : ℝ) * (↑S.card - 1) * ((2 : ℝ) * ↑S.card * (↑S.card - 1))⁻¹ :=
                mul_lt_mul_of_pos_left hexp_lt h2n_pos
          _ = 1 := mul_inv_cancel₀ h2n_ne
      -- Step 6: μ(Goodᶜ) < 1 ⟹ μ(Good) = 1 - μ(Goodᶜ) > 0
      have hGc_lt : gaussianMatrixMeasure m d Goodᶜ < 1 :=
        lt_of_le_of_lt (hunion.trans hsum) hlt_one
      have hGood_eq : gaussianMatrixMeasure m d Good =
          1 - gaussianMatrixMeasure m d Goodᶜ := by
        have h := MeasureTheory.prob_compl_eq_one_sub
            (μ := gaussianMatrixMeasure m d) hGood_meas.compl
        simp only [compl_compl] at h; exact h
      rw [hGood_eq]
      exact tsub_pos_of_lt hGc_lt
    -- Positive measure ⟹ Good is non-empty ⟹ extract witness.
    have hGood_ne : Good.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      simp [h] at hGood_pos
    exact ⟨hGood_ne.choose, hGood_ne.choose_spec⟩

/-- **Johnson–Lindenstrauss Lemma** (Dasgupta & Gupta 2003, elementary Gaussian form).

For any `ε ∈ (0, 1)` and any finite set `S` of `n` points in ℝᵈ, there exists a
linear map `f : ℝᵈ →ₗ[ℝ] ℝᵐ` with `m = O(ε⁻² · log n)` satisfying:

  `(1 − ε) · ‖u − v‖² ≤ ‖f(u) − f(v)‖² ≤ (1 + ε) · ‖u − v‖²`   ∀ u, v ∈ S.

The required dimension `m` depends only on `|S|` and `ε`, NOT on the ambient
dimension `d`. A scaled random Gaussian matrix witnesses existence.

**NOTE on hypothesis:** `hm` requires `m > 8ε⁻² log(n(n−1))` while the classical
statement uses `log n`. For `n ≥ 2` these agree up to a constant; the current
form matches `jl_union_bound` exactly.

**STATUS:** staging for `Mathlib.Probability.Concentration.JohnsonLindenstrauss`.
Retire once merged into Mathlib. -/
theorem johnson_lindenstrauss
    {d : ℕ}
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (S : Finset (EuclideanSpace ℝ (Fin d)))
    (m : ℕ)
    (hm : (↑m : ℝ) > 8 * ε⁻¹ ^ 2 * Real.log (2 * ↑S.card * (↑S.card - 1))) :
    ∃ (f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)),
      ∀ u ∈ S, ∀ v ∈ S,
        (1 - ε) * ‖u - v‖ ^ 2 ≤ ‖f u - f v‖ ^ 2 ∧
        ‖f u - f v‖ ^ 2 ≤ (1 + ε) * ‖u - v‖ ^ 2 := by
  -- Step 1: Obtain a matrix A from jl_union_bound.
  obtain ⟨A, hA⟩ := jl_union_bound ε hε hε' S m hm
  -- Step 2: Define f = (1/√m)·A·(-) as a linear map via WithLp equivalences.
  refine ⟨(WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap ∘ₗ
      (Matrix.mulVecLin ((1 / Real.sqrt (↑m : ℝ)) • A) ∘ₗ
       (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap), ?_⟩
  intro u hu v hv
  -- Step 3: Norm identity: ‖f u - f v‖² = (1/√m)² · ‖(WithLp.equiv...) (A·(u-v))‖²
  have hnorm_eq : ‖((WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap ∘ₗ
        (Matrix.mulVecLin ((1 / Real.sqrt (↑m : ℝ)) • A) ∘ₗ
         (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap)) u -
      ((WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap ∘ₗ
        (Matrix.mulVecLin ((1 / Real.sqrt (↑m : ℝ)) • A) ∘ₗ
         (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap)) v‖ ^ 2 =
      (1 / Real.sqrt (↑m : ℝ)) ^ 2 *
        ‖(WithLp.equiv 2 (Fin m → ℝ)).symm (Matrix.mulVec A (u - v))‖ ^ 2 := by
    simp only [← map_sub, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
               Matrix.mulVecLin_apply, WithLp.linearEquiv_apply, smul_mulVec_real, ← smul_sub]
    change ‖(1 / Real.sqrt (↑m : ℝ)) •
        (WithLp.equiv 2 (Fin m → ℝ)).symm
          (Matrix.mulVec A ((WithLp.addEquiv 2 (Fin d → ℝ)).toFun u) -
            Matrix.mulVec A ((WithLp.addEquiv 2 (Fin d → ℝ)).toFun v))‖ ^ 2 = _
    rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_pow]
    congr 2; rw [← Matrix.mulVec_sub]; rfl
  -- Step 4: Handle u = v (both bounds collapse to 0) and u ≠ v (apply hA).
  by_cases huv : u = v
  · constructor <;> (subst huv; simp)
  · obtain ⟨hlb, hub⟩ := hA u hu v hv huv
    exact ⟨hnorm_eq ▸ hlb, hnorm_eq ▸ hub⟩
