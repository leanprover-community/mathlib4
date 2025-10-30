/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker, Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket


/-! # Functions and measures of temperate growth -/

noncomputable section

open scoped Nat NNReal ContDiff

open Asymptotics

variable {𝕜 R D E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace Function

/-- A function is called of temperate growth if it is smooth and all iterated derivatives are
polynomially bounded. -/
def HasTemperateGrowth (f : E → F) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ n : ℕ, ∃ (k : ℕ) (C : ℝ), ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C * (1 + ‖x‖) ^ k

/-- A function has temperate growth if and only if it is smooth and its `n`-th iterated
derivative is `O((1 + ‖x‖) ^ k)` for some `k : ℕ` (depending on `n`).

Note that the `O` here is with respect to the `⊤` filter, meaning that the bound holds everywhere.

TODO: when `E` is finite dimensional, this is equivalent to the derivatives being `O(‖x‖ ^ k)`
as `‖x‖ → ∞`.
-/
theorem hasTemperateGrowth_iff_isBigO {f : E → F} :
    f.HasTemperateGrowth ↔ ContDiff ℝ ∞ f ∧
      ∀ n, ∃ k, iteratedFDeriv ℝ n f =O[⊤] (fun x ↦ (1 + ‖x‖) ^ k) := by
  simp_rw [Asymptotics.isBigO_top]
  congrm ContDiff ℝ ∞ f ∧ (∀ n, ∃ k C, ∀ x, _ ≤ C * ?_)
  rw [norm_pow, Real.norm_of_nonneg (by positivity)]

/-- If `f` has temperate growth, then its `n`-th iterated derivative is `O((1 + ‖x‖) ^ k)` for
some `k : ℕ` (depending on `n`).

Note that the `O` here is with respect to the `⊤` filter, meaning that the bound holds everywhere.
-/
theorem HasTemperateGrowth.isBigO {f : E → F}
    (hf_temperate : f.HasTemperateGrowth) (n : ℕ) :
    ∃ k, iteratedFDeriv ℝ n f =O[⊤] (fun x ↦ (1 + ‖x‖) ^ k) :=
  Function.hasTemperateGrowth_iff_isBigO.mp hf_temperate |>.2 n

/-- If `f` has temperate growth, then for any `N : ℕ` one can find `k` such that *all* iterated
derivatives of `f` of order `≤ N` are `O((1 + ‖x‖) ^ k)`.

Note that the `O` here is with respect to the `⊤` filter, meaning that the bound holds everywhere.
-/
theorem HasTemperateGrowth.isBigO_uniform {f : E → F}
    (hf_temperate : f.HasTemperateGrowth) (N : ℕ) :
    ∃ k, ∀ n ≤ N, iteratedFDeriv ℝ n f =O[⊤] (fun x ↦ (1 + ‖x‖) ^ k) := by
  choose k hk using hf_temperate.isBigO
  use (Finset.range (N + 1)).sup k
  intro n hn
  refine (hk n).trans (isBigO_of_le _ fun x ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  gcongr
  · simp
  · exact Finset.le_sup (by simpa [← Finset.mem_range_succ_iff] using hn)

theorem HasTemperateGrowth.norm_iteratedFDeriv_le_uniform {f : E → F}
    (hf_temperate : f.HasTemperateGrowth) (n : ℕ) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ N ≤ n, ∀ x : E, ‖iteratedFDeriv ℝ N f x‖ ≤ C * (1 + ‖x‖) ^ k := by
  rcases hf_temperate.isBigO_uniform n with ⟨k, hk⟩
  set F := fun x (N : Fin (n+1)) ↦ iteratedFDeriv ℝ N f x
  have : F =O[⊤] (fun x ↦ (1 + ‖x‖) ^ k) := by
    simp_rw [F, isBigO_pi, Fin.forall_iff, Nat.lt_succ]
    exact hk
  rcases this.exists_nonneg with ⟨C, C_nonneg, hC⟩
  simp (discharger := positivity) only [isBigOWith_top, Real.norm_of_nonneg,
    pi_norm_le_iff_of_nonneg, Fin.forall_iff, Nat.lt_succ] at hC
  exact ⟨k, C, C_nonneg, fun N hN x ↦ hC x N hN⟩

@[deprecated (since := "2025-10-30")]
alias HasTemperateGrowth.norm_iteratedFDeriv_le_uniform_aux :=
  HasTemperateGrowth.norm_iteratedFDeriv_le_uniform

lemma HasTemperateGrowth.of_fderiv {f : E → F}
    (h'f : Function.HasTemperateGrowth (fderiv ℝ f)) (hf : Differentiable ℝ f) {k : ℕ} {C : ℝ}
    (h : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    Function.HasTemperateGrowth f := by
  refine ⟨contDiff_succ_iff_fderiv.2 ⟨hf, by simp, h'f.1⟩, fun n ↦ ?_⟩
  rcases n with rfl | m
  · exact ⟨k, C, fun x ↦ by simpa using h x⟩
  · rcases h'f.2 m with ⟨k', C', h'⟩
    refine ⟨k', C', ?_⟩
    simpa [iteratedFDeriv_succ_eq_comp_right] using h'

lemma HasTemperateGrowth.zero :
    Function.HasTemperateGrowth (fun _ : E ↦ (0 : F)) := by
  refine ⟨contDiff_const, fun n ↦ ⟨0, 0, fun x ↦ ?_⟩⟩
  simp only [iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
  positivity

lemma HasTemperateGrowth.const (c : F) :
    Function.HasTemperateGrowth (fun _ : E ↦ c) :=
  .of_fderiv (by simpa using .zero) (differentiable_const c) (k := 0) (C := ‖c‖) (fun x ↦ by simp)

section Multiplication

variable [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

/-- The product of two functions of temperate growth is again of temperate growth.

Version for bilinear maps. -/
theorem _root_.ContinuousLinearMap.bilinear_hasTemperateGrowth [NormedSpace 𝕜 E]
    (B : E →L[𝕜] F →L[𝕜] G) {f : D → E} {g : D → F} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) : (fun x ↦ B (f x) (g x)).HasTemperateGrowth := by
  rw [Function.hasTemperateGrowth_iff_isBigO]
  constructor
  · apply (B.bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp (hf.1.prodMk hg.1)
  intro n
  rcases hf.isBigO_uniform n with ⟨k1, h1⟩
  rcases hg.isBigO_uniform n with ⟨k2, h2⟩
  use k1 + k2
  have estimate (x : D) : ‖iteratedFDeriv ℝ n (fun x ↦ B (f x) (g x)) x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n+1), (n.choose i) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by
    refine (B.bilinearRestrictScalars ℝ).norm_iteratedFDeriv_le_of_bilinear hf.1 hg.1 x ?_
    exact WithTop.coe_le_coe.mpr le_top
  refine (IsBigO.of_norm_le estimate).trans (.const_mul_left (.sum fun i hi ↦ ?_) _)
  simp_rw [mul_assoc, pow_add]
  refine .const_mul_left (.mul (h1 i ?_).norm_left (h2 (n-i) ?_).norm_left) _ <;>
  grind

/-- The product of two functions of temperate growth is again of temperate growth.

Version for scalar multiplication. -/
theorem _root_.Function.HasTemperateGrowth.smul {f : E → 𝕜} {g : E → F} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) : (f • g).HasTemperateGrowth :=
  (ContinuousLinearMap.lsmul ℝ 𝕜).bilinear_hasTemperateGrowth hf hg

variable [NormedRing R] [NormedAlgebra ℝ R]

/-- The product of two functions of temperate growth is again of temperate growth. -/
theorem _root_.Function.HasTemperateGrowth.mul {f g : E → R} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) : (f * g).HasTemperateGrowth :=
  (ContinuousLinearMap.mul ℝ R).bilinear_hasTemperateGrowth hf hg

end Multiplication

lemma _root_.ContinuousLinearMap.hasTemperateGrowth (f : E →L[ℝ] F) :
    Function.HasTemperateGrowth f := by
  apply Function.HasTemperateGrowth.of_fderiv ?_ f.differentiable (k := 1) (C := ‖f‖) (fun x ↦ ?_)
  · have : fderiv ℝ f = fun _ ↦ f := by ext1 v; simp only [ContinuousLinearMap.fderiv]
    simpa [this] using .const _
  · exact (f.le_opNorm x).trans (by simp [mul_add])

end Function

variable [NormedAddCommGroup D] [MeasurableSpace D]

namespace MeasureTheory.Measure

open Module
open scoped ENNReal

/-- A measure `μ` has temperate growth if there is an `n : ℕ` such that `(1 + ‖x‖) ^ (- n)` is
`μ`-integrable. -/
class HasTemperateGrowth (μ : Measure D) : Prop where
  exists_integrable : ∃ (n : ℕ), Integrable (fun x ↦ (1 + ‖x‖) ^ (- (n : ℝ))) μ

open Classical in
/-- An integer exponent `l` such that `(1 + ‖x‖) ^ (-l)` is integrable if `μ` has
temperate growth. -/
def integrablePower (μ : Measure D) : ℕ :=
  if h : μ.HasTemperateGrowth then h.exists_integrable.choose else 0

lemma integrable_pow_neg_integrablePower
    (μ : Measure D) [h : μ.HasTemperateGrowth] :
    Integrable (fun x ↦ (1 + ‖x‖) ^ (- (μ.integrablePower : ℝ))) μ := by
  simpa [Measure.integrablePower, h] using h.exists_integrable.choose_spec

instance _root_.MeasureTheory.IsFiniteMeasure.instHasTemperateGrowth {μ : Measure D}
    [h : IsFiniteMeasure μ] : μ.HasTemperateGrowth := ⟨⟨0, by simp⟩⟩

variable [NormedSpace ℝ D] [FiniteDimensional ℝ D] [BorelSpace D] in
instance IsAddHaarMeasure.instHasTemperateGrowth {μ : Measure D}
    [h : μ.IsAddHaarMeasure] : μ.HasTemperateGrowth :=
  ⟨⟨finrank ℝ D + 1, by apply integrable_one_add_norm; norm_num⟩⟩

/-- Pointwise inequality to control `x ^ k * f` in terms of `1 / (1 + x) ^ l` if one controls both
`f` (with a bound `C₁`) and `x ^ (k + l) * f` (with a bound `C₂`). This will be used to check
integrability of `x ^ k * f x` when `f` is a Schwartz function, and to control explicitly its
integral in terms of suitable seminorms of `f`. -/
lemma _root_.pow_mul_le_of_le_of_pow_mul_le {C₁ C₂ : ℝ} {k l : ℕ} {x f : ℝ} (hx : 0 ≤ x)
    (hf : 0 ≤ f) (h₁ : f ≤ C₁) (h₂ : x ^ (k + l) * f ≤ C₂) :
    x ^ k * f ≤ 2 ^ l * (C₁ + C₂) * (1 + x) ^ (- (l : ℝ)) := by
  have : 0 ≤ C₂ := le_trans (by positivity) h₂
  have : 2 ^ l * (C₁ + C₂) * (1 + x) ^ (- (l : ℝ)) = ((1 + x) / 2) ^ (-(l : ℝ)) * (C₁ + C₂) := by
    rw [Real.div_rpow (by linarith) zero_le_two]
    simp [div_eq_inv_mul, ← Real.rpow_neg_one, ← Real.rpow_mul]
    ring
  rw [this]
  rcases le_total x 1 with h'x|h'x
  · gcongr
    · apply (pow_le_one₀ hx h'x).trans
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      · linarith
      · linarith
      · simp
    · linarith
  · calc
    x ^ k * f = x ^ (-(l : ℝ)) * (x ^ (k + l) * f) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← mul_assoc, ← Real.rpow_add (by linarith)]
      simp
    _ ≤ ((1 + x) / 2) ^ (-(l : ℝ)) * (C₁ + C₂) := by
      apply mul_le_mul _ _ (by positivity) (by positivity)
      · exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by simp)
      · exact h₂.trans (by linarith)

variable [BorelSpace D] [SecondCountableTopology D] in
/-- Given a function such that `f` and `x ^ (k + l) * f` are bounded for a suitable `l`, then
`x ^ k * f` is integrable. The bounds are not relevant for the integrability conclusion, but they
are relevant for bounding the integral in `integral_pow_mul_le_of_le_of_pow_mul_le`. We formulate
the two lemmas with the same set of assumptions for ease of applications. -/
-- We redeclare `E` here to avoid the `NormedSpace ℝ E` typeclass available throughout this file.
lemma _root_.integrable_of_le_of_pow_mul_le
    {E : Type*} [NormedAddCommGroup E]
    {μ : Measure D} [μ.HasTemperateGrowth] {f : D → E} {C₁ C₂ : ℝ} {k : ℕ}
    (hf : ∀ x, ‖f x‖ ≤ C₁) (h'f : ∀ x, ‖x‖ ^ (k + μ.integrablePower) * ‖f x‖ ≤ C₂)
    (h''f : AEStronglyMeasurable f μ) :
    Integrable (fun x ↦ ‖x‖ ^ k * ‖f x‖) μ := by
  apply ((integrable_pow_neg_integrablePower μ).const_mul (2 ^ μ.integrablePower * (C₁ + C₂))).mono'
  · exact AEStronglyMeasurable.mul (aestronglyMeasurable_id.norm.pow _) h''f.norm
  · filter_upwards with v
    simp only [norm_mul, norm_pow, norm_norm]
    apply pow_mul_le_of_le_of_pow_mul_le (norm_nonneg _) (norm_nonneg _) (hf v) (h'f v)

/-- Given a function such that `f` and `x ^ (k + l) * f` are bounded for a suitable `l`, then
one can bound explicitly the integral of `x ^ k * f`. -/
-- We redeclare `E` here to avoid the `NormedSpace ℝ E` typeclass available throughout this file.
lemma _root_.integral_pow_mul_le_of_le_of_pow_mul_le
    {E : Type*} [NormedAddCommGroup E]
    {μ : Measure D} [μ.HasTemperateGrowth] {f : D → E} {C₁ C₂ : ℝ} {k : ℕ}
    (hf : ∀ x, ‖f x‖ ≤ C₁) (h'f : ∀ x, ‖x‖ ^ (k + μ.integrablePower) * ‖f x‖ ≤ C₂) :
    ∫ x, ‖x‖ ^ k * ‖f x‖ ∂μ ≤ 2 ^ μ.integrablePower *
      (∫ x, (1 + ‖x‖) ^ (- (μ.integrablePower : ℝ)) ∂μ) * (C₁ + C₂) := by
  rw [← integral_const_mul, ← integral_mul_const]
  apply integral_mono_of_nonneg
  · filter_upwards with v using by positivity
  · exact ((integrable_pow_neg_integrablePower μ).const_mul _).mul_const _
  filter_upwards with v
  exact (pow_mul_le_of_le_of_pow_mul_le (norm_nonneg _) (norm_nonneg _) (hf v) (h'f v)).trans
    (le_of_eq (by ring))

/-- For any `HasTemperateGrowth` measure and `p`, there exists an integer power `k` such that
`(1 + ‖x‖) ^ (-k)` is in `L^p`. -/
theorem HasTemperateGrowth.exists_eLpNorm_lt_top (p : ℝ≥0∞)
    {μ : Measure D} (hμ : μ.HasTemperateGrowth) :
    ∃ k : ℕ, eLpNorm (fun x ↦ (1 + ‖x‖) ^ (-k : ℝ)) p μ < ⊤ := by
  cases p with
  | top => exact ⟨0, eLpNormEssSup_lt_top_of_ae_bound (C := 1) (by simp)⟩
  | coe p =>
    cases eq_or_ne (p : ℝ≥0∞) 0 with
    | inl hp => exact ⟨0, by simp [hp]⟩
    | inr hp =>
      have h_one_add (x : D) : 0 < 1 + ‖x‖ := lt_add_of_pos_of_le zero_lt_one (norm_nonneg x)
      have hp_pos : 0 < (p : ℝ) := by simpa [zero_lt_iff] using hp
      rcases hμ.exists_integrable with ⟨l, hl⟩
      let k := ⌈(l / p : ℝ)⌉₊
      have hlk : l ≤ k * (p : ℝ) := by simpa [div_le_iff₀ hp_pos] using Nat.le_ceil (l / p : ℝ)
      use k
      suffices HasFiniteIntegral (fun x ↦ ((1 + ‖x‖) ^ (-(k * p) : ℝ))) μ by
        rw [hasFiniteIntegral_iff_enorm] at this
        rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp ENNReal.coe_ne_top]
        simp only [ENNReal.coe_toReal]
        refine Eq.subst (motive := (∫⁻ x, · x ∂μ < ⊤)) (funext fun x ↦ ?_) this
        rw [← neg_mul, Real.rpow_mul (h_one_add x).le]
        exact Real.enorm_rpow_of_nonneg (by positivity) NNReal.zero_le_coe
      refine hl.hasFiniteIntegral.mono' (ae_of_all μ fun x ↦ ?_)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (h_one_add x).le _)]
      gcongr
      simp

end MeasureTheory.Measure
