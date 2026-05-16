/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FormalMultilinearSeries
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Radius of convergence of a power series

This file introduces the notion of the radius of convergence of a power series.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`.

* `p.radius`: the largest `r : ℝ≥0∞` such that `‖p n‖ * r^n` grows subexponentially.
* `p.le_radius_of_bound`, `p.le_radius_of_bound_nnreal`, `p.le_radius_of_isBigO`: if `‖p n‖ * r ^ n`
  is bounded above, then `r ≤ p.radius`;
* `p.isLittleO_of_lt_radius`, `p.norm_mul_pow_le_mul_pow_of_lt_radius`,
  `p.isLittleO_one_of_lt_radius`,
  `p.norm_mul_pow_le_of_lt_radius`, `p.nnnorm_mul_pow_le_of_lt_radius`: if `r < p.radius`, then
  `‖p n‖ * r ^ n` tends to zero exponentially;
* `p.lt_radius_of_isBigO`: if `r ≠ 0` and `‖p n‖ * r ^ n = O(a ^ n)` for some `-1 < a < 1`, then
  `r < p.radius`;
* `p.partialSum n x`: the sum `∑_{i = 0}^{n-1} pᵢ xⁱ`.
* `p.sum x`: the sum `∑'_{i = 0}^{∞} pᵢ xⁱ`.

## Implementation details

We only introduce the radius of convergence of a power series, as `p.radius`.
For a power series in finitely many dimensions, there is a finer (directional, coordinate-dependent)
notion, describing the polydisk of convergence. This notion is more specific, and not necessary to
build the general theory. We do not define it here.
-/

@[expose] public section

noncomputable section

variable {𝕜 E F G : Type*}

open Topology NNReal Filter ENNReal Set Asymptotics
open scoped Pointwise

namespace FormalMultilinearSeries

variable [Semiring 𝕜] [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F]
variable [TopologicalSpace E] [TopologicalSpace F]
variable [ContinuousAdd E] [ContinuousAdd F]
variable [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F]

/-- Given a formal multilinear series `p` and a vector `x`, then `p.sum x` is the sum `Σ pₙ xⁿ`. A
priori, it only behaves well when `‖x‖ < p.radius`. -/
protected def sum (p : FormalMultilinearSeries 𝕜 E F) (x : E) : F :=
  ∑' n : ℕ, p n fun _ => x

theorem sum_mem {S : Type*} {s : S} [SetLike S F] [AddSubmonoidClass S F]
    (h_closed : IsClosed (s : Set F)) (p : FormalMultilinearSeries 𝕜 E F) (x : E)
    (h : ∀ k, p k (fun _ : Fin k => x) ∈ s) :
    p.sum x ∈ s :=
  tsum_mem h_closed h

/-- Given a formal multilinear series `p` and a vector `x`, then `p.partialSum n x` is the sum
`Σ pₖ xᵏ` for `k ∈ {0,..., n-1}`. -/
def partialSum (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) (x : E) : F :=
  ∑ k ∈ Finset.range n, p k fun _ : Fin k => x

/-- The partial sums of a formal multilinear series are continuous. -/
theorem partialSum_continuous (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) :
    Continuous (p.partialSum n) := by
  unfold partialSum
  fun_prop

end FormalMultilinearSeries

/-! ### The radius of a formal multilinear series -/

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}

/-- The radius of a formal multilinear series is the largest `r` such that the sum `Σ ‖pₙ‖ ‖y‖ⁿ`
converges for all `‖y‖ < r`. This implies that `Σ pₙ yⁿ` converges for all `‖y‖ < r`, but these
definitions are *not* equivalent in general. -/
def radius (p : FormalMultilinearSeries 𝕜 E F) : ℝ≥0∞ :=
  ⨆ (r : ℝ≥0) (C : ℝ) (_ : ∀ n, ‖p n‖ * (r : ℝ) ^ n ≤ C), (r : ℝ≥0∞)

/-- If `‖pₙ‖ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_bound (C : ℝ) {r : ℝ≥0} (h : ∀ n : ℕ, ‖p n‖ * (r : ℝ) ^ n ≤ C) :
    (r : ℝ≥0∞) ≤ p.radius :=
  le_iSup_of_le r <| le_iSup_of_le C <| le_iSup (fun _ => (r : ℝ≥0∞)) h

/-- If `‖pₙ‖ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_bound_nnreal (C : ℝ≥0) {r : ℝ≥0} (h : ∀ n : ℕ, ‖p n‖₊ * r ^ n ≤ C) :
    (r : ℝ≥0∞) ≤ p.radius :=
  p.le_radius_of_bound C fun n => mod_cast h n

/-- If `‖pₙ‖ rⁿ = O(1)`, as `n → ∞`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_isBigO (h : (fun n => ‖p n‖ * (r : ℝ) ^ n) =O[atTop] fun _ => (1 : ℝ)) :
    ↑r ≤ p.radius :=
  Exists.elim (isBigO_one_nat_atTop_iff.1 h) fun C hC =>
    p.le_radius_of_bound C fun n => (le_abs_self _).trans (hC n)

theorem le_radius_of_eventually_le (C) (h : ∀ᶠ n in atTop, ‖p n‖ * (r : ℝ) ^ n ≤ C) :
    ↑r ≤ p.radius :=
  p.le_radius_of_isBigO <| IsBigO.of_bound C <| h.mono fun n hn => by simpa

theorem le_radius_of_summable_nnnorm (h : Summable fun n => ‖p n‖₊ * r ^ n) : ↑r ≤ p.radius :=
  p.le_radius_of_bound_nnreal (∑' n, ‖p n‖₊ * r ^ n) fun _ => h.le_tsum' _

theorem le_radius_of_summable (h : Summable fun n => ‖p n‖ * (r : ℝ) ^ n) : ↑r ≤ p.radius :=
  p.le_radius_of_summable_nnnorm <| by
    simp only [← coe_nnnorm] at h
    exact mod_cast h

theorem radius_eq_top_of_forall_nnreal_isBigO
    (h : ∀ r : ℝ≥0, (fun n => ‖p n‖ * (r : ℝ) ^ n) =O[atTop] fun _ => (1 : ℝ)) : p.radius = ∞ :=
  ENNReal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_isBigO (h r)

theorem radius_eq_top_of_eventually_eq_zero (h : ∀ᶠ n in atTop, p n = 0) : p.radius = ∞ :=
  p.radius_eq_top_of_forall_nnreal_isBigO fun r =>
    (isBigO_zero _ _).congr' (h.mono fun n hn => by simp [hn]) EventuallyEq.rfl

theorem radius_eq_top_of_forall_image_add_eq_zero (n : ℕ) (hn : ∀ m, p (m + n) = 0) :
    p.radius = ∞ :=
  p.radius_eq_top_of_eventually_eq_zero <|
    mem_atTop_sets.2 ⟨n, fun _ hk => tsub_add_cancel_of_le hk ▸ hn _⟩

@[simp]
theorem constFormalMultilinearSeries_radius {v : F} :
    (constFormalMultilinearSeries 𝕜 E v).radius = ⊤ :=
  (constFormalMultilinearSeries 𝕜 E v).radius_eq_top_of_forall_image_add_eq_zero 1
    (by simp [constFormalMultilinearSeries])

/-- `0` has infinite radius of convergence -/
@[simp] lemma zero_radius : (0 : FormalMultilinearSeries 𝕜 E F).radius = ∞ := by
  rw [← constFormalMultilinearSeries_zero]
  exact constFormalMultilinearSeries_radius

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` tends to zero exponentially:
for some `0 < a < 1`, `‖p n‖ rⁿ = o(aⁿ)`. -/
theorem isLittleO_of_lt_radius (h : ↑r < p.radius) :
    ∃ a ∈ Ioo (0 : ℝ) 1, (fun n => ‖p n‖ * (r : ℝ) ^ n) =o[atTop] (a ^ ·) := by
  have := (TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 1 4
  rw [this]
  -- Porting note: was
  -- rw [(TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 1 4]
  simp only [radius, lt_iSup_iff] at h
  rcases h with ⟨t, C, hC, rt⟩
  rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at rt
  have : 0 < (t : ℝ) := r.coe_nonneg.trans_lt rt
  rw [← div_lt_one this] at rt
  refine ⟨_, rt, C, Or.inr zero_lt_one, fun n => ?_⟩
  calc
    |‖p n‖ * (r : ℝ) ^ n| = ‖p n‖ * (t : ℝ) ^ n * (r / t : ℝ) ^ n := by
      simp [field, abs_mul, div_pow]
    _ ≤ C * (r / t : ℝ) ^ n := by gcongr; apply hC

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ = o(1)`. -/
theorem isLittleO_one_of_lt_radius (h : ↑r < p.radius) :
    (fun n => ‖p n‖ * (r : ℝ) ^ n) =o[atTop] (fun _ => 1 : ℕ → ℝ) :=
  let ⟨_, ha, hp⟩ := p.isLittleO_of_lt_radius h
  hp.trans <| (isLittleO_pow_pow_of_lt_left ha.1.le ha.2).congr (fun _ => rfl) one_pow

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` tends to zero exponentially:
for some `0 < a < 1` and `C > 0`, `‖p n‖ * r ^ n ≤ C * a ^ n`. -/
theorem norm_mul_pow_le_mul_pow_of_lt_radius (h : ↑r < p.radius) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n, ‖p n‖ * (r : ℝ) ^ n ≤ C * a ^ n := by
  have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 1 5).mp
    (p.isLittleO_of_lt_radius h)
  rcases this with ⟨a, ha, C, hC, H⟩
  exact ⟨a, ha, C, hC, fun n => (le_abs_self _).trans (H n)⟩

/-- If `r ≠ 0` and `‖pₙ‖ rⁿ = O(aⁿ)` for some `-1 < a < 1`, then `r < p.radius`. -/
theorem lt_radius_of_isBigO (h₀ : r ≠ 0) {a : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1)
    (hp : (fun n => ‖p n‖ * (r : ℝ) ^ n) =O[atTop] (a ^ ·)) : ↑r < p.radius := by
  have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 2 5)
  rcases this.mp ⟨a, ha, hp⟩ with ⟨a, ha, C, hC, hp⟩
  rw [← pos_iff_ne_zero, ← NNReal.coe_pos] at h₀
  lift a to ℝ≥0 using ha.1.le
  have : (r : ℝ) < r / a := by
    simpa only [div_one] using (div_lt_div_iff_of_pos_left h₀ zero_lt_one ha.1).2 ha.2
  norm_cast at this
  rw [← ENNReal.coe_lt_coe] at this
  refine this.trans_le (p.le_radius_of_bound C fun n => ?_)
  rw [NNReal.coe_div, div_pow, ← mul_div_assoc, div_le_iff₀ (pow_pos ha.1 n)]
  exact (le_abs_self _).trans (hp n)

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded. -/
theorem norm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}
    (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ‖p n‖ * (r : ℝ) ^ n ≤ C :=
  let ⟨_, ha, C, hC, h⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  ⟨C, hC, fun n => (h n).trans <| mul_le_of_le_one_right hC.lt.le (pow_le_one₀ ha.1.le ha.2.le)⟩

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded. -/
theorem norm_le_div_pow_of_pos_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}
    (h0 : 0 < r) (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ‖p n‖ ≤ C / (r : ℝ) ^ n :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨C, hC, fun n => Iff.mpr (le_div_iff₀ (pow_pos h0 _)) (hp n)⟩

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded. -/
theorem nnnorm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}
    (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ‖p n‖₊ * r ^ n ≤ C :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨⟨C, hC.lt.le⟩, hC, mod_cast hp⟩

theorem le_radius_of_tendsto (p : FormalMultilinearSeries 𝕜 E F) {l : ℝ}
    (h : Tendsto (fun n => ‖p n‖ * (r : ℝ) ^ n) atTop (𝓝 l)) : ↑r ≤ p.radius :=
  p.le_radius_of_isBigO (h.isBigO_one _)

theorem le_radius_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F)
    (hs : Summable fun n => ‖p n‖ * (r : ℝ) ^ n) : ↑r ≤ p.radius :=
  p.le_radius_of_tendsto hs.tendsto_atTop_zero

theorem not_summable_norm_of_radius_lt_nnnorm (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (h : p.radius < ‖x‖₊) : ¬Summable fun n => ‖p n‖ * ‖x‖ ^ n :=
  fun hs => not_le_of_gt h (p.le_radius_of_summable_norm hs)

theorem summable_norm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0} (h : ↑r < p.radius) :
    Summable fun n : ℕ => ‖p n‖ * (r : ℝ) ^ n := by
  obtain ⟨a, ha : a ∈ Ioo (0 : ℝ) 1, C, - : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  exact .of_nonneg_of_le (fun _ ↦ by positivity)
    hp ((summable_geometric_of_lt_one ha.1.le ha.2).mul_left _)

theorem summable_norm_apply (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ Metric.eball (0 : E) p.radius) : Summable fun n : ℕ => ‖p n fun _ => x‖ := by
  rw [mem_eball_zero_iff] at hx
  refine .of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (fun n ↦ ((p n).le_opNorm _).trans_eq ?_) (p.summable_norm_mul_pow hx)
  simp

theorem summable_nnnorm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0} (h : ↑r < p.radius) :
    Summable fun n : ℕ => ‖p n‖₊ * r ^ n := by
  rw [← NNReal.summable_coe]
  push_cast
  exact p.summable_norm_mul_pow h

protected theorem summable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ Metric.eball (0 : E) p.radius) : Summable fun n : ℕ => p n fun _ => x :=
  (p.summable_norm_apply hx).of_norm

theorem radius_eq_top_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F)
    (hs : ∀ r : ℝ≥0, Summable fun n => ‖p n‖ * (r : ℝ) ^ n) : p.radius = ∞ :=
  ENNReal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_summable_norm (hs r)

theorem radius_eq_top_iff_summable_norm (p : FormalMultilinearSeries 𝕜 E F) :
    p.radius = ∞ ↔ ∀ r : ℝ≥0, Summable fun n => ‖p n‖ * (r : ℝ) ^ n :=
  ⟨fun h _ ↦ p.summable_norm_mul_pow (h.symm ▸ ENNReal.coe_lt_top),
    p.radius_eq_top_of_summable_norm⟩

/-- If the radius of `p` is positive, then `‖pₙ‖` grows at most geometrically. -/
theorem le_mul_pow_of_radius_pos (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) :
    ∃ (C r : _) (_ : 0 < C) (_ : 0 < r), ∀ n, ‖p n‖ ≤ C * r ^ n := by
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨r, r0, rlt⟩
  have rpos : 0 < (r : ℝ) := by simp [ENNReal.coe_pos.1 r0]
  rcases norm_le_div_pow_of_pos_of_lt_radius p rpos rlt with ⟨C, Cpos, hCp⟩
  refine ⟨C, r⁻¹, Cpos, by simp only [inv_pos, rpos], fun n => ?_⟩
  rw [inv_pow, ← div_eq_mul_inv]
  exact hCp n

lemma radius_le_of_le {𝕜' E' F' : Type*}
    [NontriviallyNormedField 𝕜'] [NormedAddCommGroup E'] [NormedSpace 𝕜' E']
    [NormedAddCommGroup F'] [NormedSpace 𝕜' F']
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜' E' F'}
    (h : ∀ n, ‖p n‖ ≤ ‖q n‖) : q.radius ≤ p.radius := by
  apply le_of_forall_nnreal_lt (fun r hr ↦ ?_)
  rcases norm_mul_pow_le_of_lt_radius _ hr with ⟨C, -, hC⟩
  apply le_radius_of_bound _ C (fun n ↦ ?_)
  apply le_trans _ (hC n)
  gcongr
  exact h n

/-- The radius of the sum of two formal series is at least the minimum of their two radii. -/
theorem min_radius_le_radius_add (p q : FormalMultilinearSeries 𝕜 E F) :
    min p.radius q.radius ≤ (p + q).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  rw [lt_min_iff] at hr
  have := ((p.isLittleO_one_of_lt_radius hr.1).add (q.isLittleO_one_of_lt_radius hr.2)).isBigO
  refine (p + q).le_radius_of_isBigO ((isBigO_of_le _ fun n => ?_).trans this)
  rw [← add_mul, norm_mul, norm_mul, norm_norm]
  gcongr
  exact (norm_add_le _ _).trans (le_abs_self _)

@[simp]
theorem radius_neg (p : FormalMultilinearSeries 𝕜 E F) : (-p).radius = p.radius := by
  simp only [radius, neg_apply, norm_neg]

theorem radius_le_smul {p : FormalMultilinearSeries 𝕜 E F} {𝕜' : Type*} {c : 𝕜'} [NormedRing 𝕜']
    [Module 𝕜' F] [SMulCommClass 𝕜 𝕜' F] [IsBoundedSMul 𝕜' F] :
    p.radius ≤ (c • p).radius := by
  simp only [radius, smul_apply]
  refine iSup_mono fun r ↦ iSup_mono' fun C ↦ ⟨‖c‖ * C, iSup_mono' fun h ↦ ?_⟩
  simp only [le_refl, exists_prop, and_true]
  intro n
  grw [norm_smul_le, mul_assoc, h]

theorem radius_smul_eq (p : FormalMultilinearSeries 𝕜 E F)
    {𝕜' : Type*} {c : 𝕜'} [NormedDivisionRing 𝕜'] [Module 𝕜' F] [NormSMulClass 𝕜' F]
    [SMulCommClass 𝕜 𝕜' F] (hc : c ≠ 0) :
    (c • p).radius = p.radius := by
  apply eq_of_le_of_ge _ radius_le_smul
  exact radius_le_smul.trans_eq (congr_arg _ <| inv_smul_smul₀ hc p)

lemma norm_compContinuousLinearMap_le (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) (n : ℕ) :
    ‖p.compContinuousLinearMap u n‖ ≤ ‖p n‖ * ‖u‖ ^ n := by
  simp only [compContinuousLinearMap]
  apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)
  simp

lemma enorm_compContinuousLinearMap_le (p : FormalMultilinearSeries 𝕜 F G)
    (u : E →L[𝕜] F) (n : ℕ) : ‖p.compContinuousLinearMap u n‖ₑ ≤ ‖p n‖ₑ * ‖u‖ₑ ^ n := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_pow (by simp), ← ENNReal.ofReal_mul (by simp)]
  gcongr
  apply norm_compContinuousLinearMap_le

lemma nnnorm_compContinuousLinearMap_le (p : FormalMultilinearSeries 𝕜 F G)
    (u : E →L[𝕜] F) (n : ℕ) : ‖p.compContinuousLinearMap u n‖₊ ≤ ‖p n‖₊ * ‖u‖₊ ^ n :=
  norm_compContinuousLinearMap_le p u n

theorem div_le_radius_compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) :
    p.radius / ‖u‖ₑ ≤ (p.compContinuousLinearMap u).radius := by
  obtain (rfl | h_zero) := eq_zero_or_nnnorm_pos u
  · simp
  rw [ENNReal.div_le_iff (by simpa using h_zero) (by simp)]
  refine le_of_forall_nnreal_lt fun r hr ↦ ?_
  rw [← ENNReal.div_le_iff (by simpa using h_zero) (by simp), enorm_eq_nnnorm, ← coe_div h_zero.ne']
  obtain ⟨C, hC_pos, hC⟩ := p.norm_mul_pow_le_of_lt_radius hr
  refine le_radius_of_bound _ C fun n ↦ ?_
  calc
    ‖p.compContinuousLinearMap u n‖ * ↑(r / ‖u‖₊) ^ n ≤ ‖p n‖ * ‖u‖ ^ n * ↑(r / ‖u‖₊) ^ n := by
      gcongr
      exact nnnorm_compContinuousLinearMap_le p u n
    _ = ‖p n‖ * r ^ n := by
      simp only [NNReal.coe_div, coe_nnnorm, div_pow, mul_assoc]
      rw [mul_div_cancel₀]
      rw [← NNReal.coe_pos] at h_zero
      positivity
    _ ≤ C := hC n

theorem le_radius_compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E →ₗᵢ[𝕜] F) :
    p.radius ≤ (p.compContinuousLinearMap u.toContinuousLinearMap).radius := by
  obtain (h | h) := subsingleton_or_nontrivial E
  · simp [Subsingleton.elim u.toContinuousLinearMap 0]
  · simpa [u.norm_toContinuousLinearMap]
      using div_le_radius_compContinuousLinearMap p u.toContinuousLinearMap

theorem radius_compContinuousLinearMap_le [Nontrivial F]
    (p : FormalMultilinearSeries 𝕜 F G) (u : E ≃L[𝕜] F) :
    (p.compContinuousLinearMap u.toContinuousLinearMap).radius ≤
    ‖u.symm.toContinuousLinearMap‖ₑ * p.radius := by
  have := (p.compContinuousLinearMap u.toContinuousLinearMap).div_le_radius_compContinuousLinearMap
    u.symm.toContinuousLinearMap
  simp only [compContinuousLinearMap_comp, ContinuousLinearEquiv.coe_comp_coe_symm,
    compContinuousLinearMap_id] at this
  rwa [ENNReal.div_le_iff' (by simpa [DFunLike.ext_iff] using exists_ne 0) (by simp)] at this

@[simp]
theorem radius_compContinuousLinearMap_linearIsometryEquiv_eq [Nontrivial E]
    (p : FormalMultilinearSeries 𝕜 F G) (u : E ≃ₗᵢ[𝕜] F) :
    (p.compContinuousLinearMap u.toLinearIsometry.toContinuousLinearMap).radius = p.radius := by
  refine le_antisymm ?_ <| le_radius_compContinuousLinearMap _ _
  have _ : Nontrivial F := u.symm.toEquiv.nontrivial
  convert radius_compContinuousLinearMap_le p u.toContinuousLinearEquiv
  have : u.toContinuousLinearEquiv.symm.toContinuousLinearMap =
    u.symm.toLinearIsometry.toContinuousLinearMap := rfl
  simp [this]

/-- This is a version of `radius_compContinuousLinearMap_linearIsometryEquiv_eq` with better
opportunity for unification, at the cost of manually supplying some hypotheses. -/
theorem radius_compContinuousLinearMap_eq [Nontrivial E]
    (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) (hu_iso : Isometry u)
    (hu_surj : Function.Surjective u) :
    (p.compContinuousLinearMap u).radius = p.radius :=
  let v : E ≃ₗᵢ[𝕜] F :=
    { LinearEquiv.ofBijective u.toLinearMap ⟨hu_iso.injective, hu_surj⟩ with
      norm_map' := hu_iso.norm_map_of_map_zero (map_zero u) }
  radius_compContinuousLinearMap_linearIsometryEquiv_eq p v

@[simp]
theorem radius_compNeg [Nontrivial E] (p : FormalMultilinearSeries 𝕜 E F) :
    (p.compContinuousLinearMap (-(.id _ _))).radius = p.radius :=
  radius_compContinuousLinearMap_linearIsometryEquiv_eq _ (.neg 𝕜)

@[simp]
theorem radius_shift (p : FormalMultilinearSeries 𝕜 E F) : p.shift.radius = p.radius := by
  simp only [radius, shift, Nat.succ_eq_add_one, ContinuousMultilinearMap.curryRight_norm]
  congr
  ext r
  apply eq_of_le_of_ge
  · apply iSup_mono'
    intro C
    use ‖p 0‖ ⊔ (C * r)
    apply iSup_mono'
    intro h
    simp only [le_refl, le_sup_iff, exists_prop, and_true]
    intro n
    rcases n with - | m
    · simp
    right
    rw [pow_succ, ← mul_assoc]
    gcongr; apply h
  · apply iSup_mono'
    intro C
    use ‖p 1‖ ⊔ C / r
    apply iSup_mono'
    intro h
    simp only [le_refl, le_sup_iff, exists_prop, and_true]
    intro n
    cases eq_zero_or_pos r with
    | inl hr =>
      rw [hr]
      cases n <;> simp
    | inr hr =>
      right
      rw [← NNReal.coe_pos] at hr
      specialize h (n + 1)
      rw [le_div_iff₀ hr]
      rwa [pow_succ, ← mul_assoc] at h

@[simp]
theorem radius_unshift (p : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)) (z : F) :
    (p.unshift z).radius = p.radius := by
  rw [← radius_shift, unshift_shift]

protected theorem hasSum [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ Metric.eball (0 : E) p.radius) : HasSum (fun n : ℕ => p n fun _ => x) (p.sum x) :=
  (p.summable hx).hasSum

theorem radius_le_radius_continuousLinearMap_comp (p : FormalMultilinearSeries 𝕜 E F)
    (f : F →L[𝕜] G) : p.radius ≤ (f.compFormalMultilinearSeries p).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  apply le_radius_of_isBigO
  apply (IsBigO.trans_isLittleO _ (p.isLittleO_one_of_lt_radius hr)).isBigO
  refine IsBigO.mul (@IsBigOWith.isBigO _ _ _ _ _ ‖f‖ _ _ _ ?_) (isBigO_refl _ _)
  refine IsBigOWith.of_bound (Eventually.of_forall fun n => ?_)
  simpa only [norm_norm] using f.norm_compContinuousMultilinearMap_le (p n)

end FormalMultilinearSeries
