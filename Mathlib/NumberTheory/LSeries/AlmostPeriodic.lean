/-
Copyright (c) 2026 Peter W. Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter W. Murphy
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Almost periodicity of Dirichlet series

Bohr's theorem states that a Dirichlet series `∑ f n / n ^ s` which converges absolutely on a
half-plane is uniformly almost periodic on every smaller half-plane. This file proves the following
sequential form: if `LSeriesSummable f s` for all `s` with `σ < re s`, then there is a strictly
increasing sequence of natural numbers `τ j` such that the vertical translates
`s ↦ LSeries f (s + τ j * I)` converge to `LSeries f` locally uniformly on `{s | σ < re s}`
(`LSeries.exists_strictMono_tendstoLocallyUniformlyOn`). If the series converges absolutely
everywhere, the convergence is locally uniform on `ℂ`
(`LSeries.exists_strictMono_tendstoLocallyUniformly`).

The only arithmetic input is the recurrence of the finite vectors of unit twists
`(n ^ (-k * I))_{1 ≤ n ≤ N}` as `k` ranges over `ℕ` (`LSeries.exists_twist_close`), which follows
from sequential compactness of the closed unit ball in `Fin N → ℂ`: a subsequence converges, and the
difference of two far-apart members of that subsequence is an integer shift under which every twist
is close to `1`. No Diophantine approximation theorem is needed.

## Main results

* `LSeries.exists_twist_close`: for every `N`, `ε > 0` and `T` there is `k ≥ T` with
  `‖n ^ (-k * I) - 1‖ < ε` for all `1 ≤ n ≤ N`.
* `LSeries.exists_le_norm_sub_lt`: if the series converges absolutely at a real `r`, then for every
  `ε > 0` and `T` there is a shift `k ≥ T` with `‖LSeries f (s + k * I) - LSeries f s‖ < ε`
  uniformly on `r ≤ re s`.
* `LSeries.exists_strictMono_tendstoLocallyUniformlyOn`: Bohr almost periodicity on a half-plane of
  absolute convergence.
* `LSeries.exists_strictMono_tendstoLocallyUniformly`: Bohr almost periodicity on `ℂ` for an
  everywhere absolutely convergent Dirichlet series.

## References

* [H. Bohr, *Zur Theorie der fastperiodischen Funktionen*, Acta Math. 45 (1925)]
-/

@[expose] public section

open Complex Filter Topology Metric

namespace LSeries

/-! ### Unit twists and their recurrence -/

/-- The unit-modulus factor `n ^ (-k * I)` by which the `n`-th term of a Dirichlet series is
multiplied under the vertical shift `s ↦ s + k * I`; see `LSeries.term_add_natCast_mul_I`. -/
noncomputable def twist (k n : ℕ) : ℂ := (n : ℂ) ^ (-((k : ℂ) * I))

lemma norm_twist {n : ℕ} (hn : 0 < n) (k : ℕ) : ‖twist k n‖ = 1 := by
  unfold twist
  have hre : (-((k : ℂ) * I)).re = 0 := by simp
  rw [norm_natCast_cpow_of_pos hn, hre, Real.rpow_zero]

lemma twist_add {n : ℕ} (hn : 0 < n) (a b : ℕ) : twist (a + b) n = twist a n * twist b n := by
  unfold twist
  have h0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← cpow_add _ _ h0]
  congr 1
  push_cast
  ring

/-- The `n`-th term of the series at `s + k * I` is the term at `s` times the twist `n ^ (-k * I)`.
-/
lemma term_add_natCast_mul_I (f : ℕ → ℂ) (s : ℂ) (k n : ℕ) :
    term f (s + (k : ℂ) * I) n = term f s n * twist k n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [term_zero]
  · have h0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [term_of_ne_zero hn.ne', term_of_ne_zero hn.ne', twist, cpow_add _ _ h0, cpow_neg]
    field_simp

/-- The twist is within `2` of `1`, weighted by any Dirichlet term (the `n = 0` term vanishes). -/
lemma norm_term_mul_norm_twist_sub_one_le (f : ℕ → ℂ) (s : ℂ) (k n : ℕ) :
    ‖term f s n‖ * ‖twist k n - 1‖ ≤ 2 * ‖term f s n‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [term_zero]
  · have : ‖twist k n - 1‖ ≤ 2 := by
      calc ‖twist k n - 1‖ ≤ ‖twist k n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_twist hn, norm_one]; norm_num
    nlinarith [norm_nonneg (term f s n)]

/-- **Recurrence of the unit twists.** For every `N`, `ε > 0` and `T` there is a natural number
`k ≥ T` with `‖n ^ (-k * I) - 1‖ < ε` for all `1 ≤ n ≤ N`.

The vectors `(n ^ (-k * I))_{1 ≤ n ≤ N}` lie in the compact unit ball of `Fin N → ℂ`, so a
subsequence converges, and the difference of two far-apart members of that subsequence is such a
`k`. -/
theorem exists_twist_close (N : ℕ) {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    ∃ k : ℕ, T ≤ k ∧ ∀ n : ℕ, 1 ≤ n → n ≤ N → ‖twist k n - 1‖ < ε := by
  set v : ℕ → Fin N → ℂ := fun k i => twist k (i.1 + 1) with hv
  have hmem : ∀ k, v k ∈ closedBall (0 : Fin N → ℂ) 1 := fun k => by
    rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    exact (norm_twist (Nat.succ_pos _) k).le
  obtain ⟨L, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : Fin N → ℂ) 1).tendsto_subseq hmem
  have hclose : ∀ᶠ j in atTop, dist (v (φ j)) L < ε / 2 :=
    (Metric.tendsto_nhds.mp hlim) (ε / 2) (by positivity)
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hclose
  have hfar : ∀ᶠ j in atTop, φ j₀ + T ≤ φ j := hφ.tendsto_atTop.eventually_ge_atTop _
  obtain ⟨j₁, hj₁⟩ := eventually_atTop.mp ((eventually_ge_atTop j₀).and hfar)
  obtain ⟨hj₁₀, hφj₁⟩ := hj₁ j₁ le_rfl
  refine ⟨φ j₁ - φ j₀, by omega, ?_⟩
  intro n hn1 hnN
  -- the two twist vectors are within `ε` of each other
  have hd : dist (v (φ j₁)) (v (φ j₀)) < ε := by
    calc dist (v (φ j₁)) (v (φ j₀))
        ≤ dist (v (φ j₁)) L + dist (v (φ j₀)) L := dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hj₀ j₁ hj₁₀) (hj₀ j₀ le_rfl)
      _ = ε := by ring
  -- read off the `n`-th coordinate
  set i : Fin N := ⟨n - 1, by omega⟩ with hi
  have hcoord : dist (v (φ j₁) i) (v (φ j₀) i) < ε :=
    lt_of_le_of_lt (dist_le_pi_dist _ _ i) hd
  have hn0 : 0 < n := hn1
  have hni : i.1 + 1 = n := by simp [hi]; omega
  simp only [hv, hni, dist_eq_norm] at hcoord
  -- factor the shift: `twist (φ j₁) n = twist (φ j₀) n * twist (φ j₁ - φ j₀) n`
  have hsplit : twist (φ j₁) n = twist (φ j₀) n * twist (φ j₁ - φ j₀) n := by
    rw [← twist_add hn0]
    congr 1
    omega
  rw [hsplit] at hcoord
  have hunit : ‖twist (φ j₀) n‖ = 1 := norm_twist hn0 _
  calc ‖twist (φ j₁ - φ j₀) n - 1‖
      = ‖twist (φ j₀) n‖ * ‖twist (φ j₁ - φ j₀) n - 1‖ := by rw [hunit, one_mul]
    _ = ‖twist (φ j₀) n * twist (φ j₁ - φ j₀) n - twist (φ j₀) n‖ := by
        rw [← norm_mul, mul_sub, mul_one]
    _ < ε := hcoord

/-! ### The Dirichlet series under a vertical shift -/

/-- The basic estimate on the half-plane `r ≤ re s`: the first `m` terms are controlled by the
twists, the rest by the tail of the series at `r`. -/
theorem norm_sub_le_of_le_re (f : ℕ → ℂ) {r : ℝ} (hr : LSeriesSummable f r) {s : ℂ}
    (hs : r ≤ s.re) (k m : ℕ) :
    ‖LSeries f (s + (k : ℂ) * I) - LSeries f s‖ ≤
      (∑ n ∈ Finset.range m, ‖term f r n‖ * ‖twist k n - 1‖) + 2 * ∑' i, ‖term f r (i + m)‖ := by
  have hs' : (r : ℂ).re ≤ s.re := by simpa using hs
  have hsum_s : Summable (term f s) := hr.of_re_le_re hs'
  have hsum_sk : Summable (term f (s + (k : ℂ) * I)) := hr.of_re_le_re (by simpa using hs)
  -- the difference as one absolutely convergent series
  have hdiff : LSeries f (s + (k : ℂ) * I) - LSeries f s =
      ∑' n, term f s n * (twist k n - 1) := by
    unfold LSeries
    rw [← hsum_sk.tsum_sub hsum_s]
    congr 1
    funext n
    rw [term_add_natCast_mul_I, mul_sub, mul_one]
  -- termwise domination on `r ≤ re s`
  have hdom : ∀ n, ‖term f s n * (twist k n - 1)‖ ≤ ‖term f r n‖ * ‖twist k n - 1‖ := by
    intro n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_term_le_of_re_le_re f hs' n) (norm_nonneg _)
  have hsumR : Summable fun n => ‖term f r n‖ := hr.norm
  have hsumg : Summable fun n => ‖term f s n * (twist k n - 1)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hdom ?_
    exact Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => norm_term_mul_norm_twist_sub_one_le f _ k n) (hsumR.mul_left 2)
  have hsumG : Summable fun n => term f s n * (twist k n - 1) := hsumg.of_norm
  rw [hdiff]
  -- split at `m`
  rw [← hsumG.sum_add_tsum_nat_add m]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun n _ => hdom n
  · refine (norm_tsum_le_tsum_norm (hsumg.comp_injective (add_left_injective m))).trans ?_
    rw [← tsum_mul_left]
    exact (hsumg.comp_injective (add_left_injective m)).tsum_le_tsum
      (fun i => (hdom _).trans (norm_term_mul_norm_twist_sub_one_le f _ k _))
      ((hsumR.comp_injective (add_left_injective m)).mul_left 2)

/-- **Bohr almost periodicity, one level.** If the Dirichlet series converges absolutely at the
real point `r`, then for every `ε > 0` and `T` there is a natural number `k ≥ T` such that the
vertical translate by `k` is within `ε` of the series uniformly on the half-plane `r ≤ re s`. -/
theorem exists_le_norm_sub_lt (f : ℕ → ℂ) {r : ℝ} (hr : LSeriesSummable f r) {ε : ℝ}
    (hε : 0 < ε) (T : ℕ) :
    ∃ k : ℕ, T ≤ k ∧ ∀ s : ℂ, r ≤ s.re → ‖LSeries f (s + (k : ℂ) * I) - LSeries f s‖ < ε := by
  -- choose the cutoff `m` so that the tail is small
  have htail : Tendsto (fun m => ∑' i, ‖term f r (i + m)‖) atTop (𝓝 0) :=
    tendsto_sum_nat_add fun n => ‖term f r n‖
  obtain ⟨m, hm⟩ : ∃ m, 2 * ∑' i, ‖term f r (i + m)‖ < ε / 2 := by
    have h := (Metric.tendsto_nhds.mp htail) (ε / 4) (by positivity)
    obtain ⟨m, hm⟩ := eventually_atTop.mp h
    refine ⟨m, ?_⟩
    have h := hm m le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)] at h
    linarith
  -- choose the shift `k` so that the twists of the first `m` terms are close to `1`
  set H : ℝ := ∑ n ∈ Finset.range m, ‖term f r n‖ with hH
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨k, hkT, hk⟩ := exists_twist_close m (ε := ε / (2 * (H + 1))) (by positivity) T
  refine ⟨k, hkT, fun s hs => ?_⟩
  refine (norm_sub_le_of_le_re f hr hs k m).trans_lt ?_
  have hhead : (∑ n ∈ Finset.range m, ‖term f r n‖ * ‖twist k n - 1‖) ≤
      H * (ε / (2 * (H + 1))) := by
    rw [hH, Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [term_zero]
    · exact mul_le_mul_of_nonneg_left (hk n hn0 (Finset.mem_range.mp hn).le).le (norm_nonneg _)
  have hδ : H * (ε / (2 * (H + 1))) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-! ### Bohr almost periodicity -/

/-- The diagonal construction behind Bohr's theorem: given real levels `a j` at which the series
converges absolutely, there is a strictly increasing sequence of shifts `τ j` such that the
translate by `τ j` is within `1 / (j + 1)` of the series on the half-plane `a j ≤ re s`. -/
theorem exists_strictMono_forall_norm_sub_lt (f : ℕ → ℂ) {a : ℕ → ℝ}
    (ha : ∀ j, LSeriesSummable f (a j)) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∀ j, ∀ s : ℂ, a j ≤ s.re →
      ‖LSeries f (s + (τ j : ℂ) * I) - LSeries f s‖ < 1 / ((j : ℝ) + 1) := by
  have hε : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j => by positivity
  choose g hgT hg using fun j T => exists_le_norm_sub_lt f (ha j) (hε j) T
  let τ : ℕ → ℕ := fun j => Nat.rec (g 0 0) (fun j τj => g (j + 1) (τj + 1)) j
  have hτ : ∀ j, τ (j + 1) = g (j + 1) (τ j + 1) := fun j => rfl
  refine ⟨τ, strictMono_nat_of_lt_succ fun j => ?_, fun j => ?_⟩
  · rw [hτ]
    have := hgT (j + 1) (τ j + 1)
    omega
  · cases j with
    | zero => exact hg 0 0
    | succ j => rw [hτ]; exact hg (j + 1) (τ j + 1)

/-- **Bohr almost periodicity on a half-plane.** If the Dirichlet series `∑ f n / n ^ s` converges
absolutely for all `s` with `σ < re s`, there is a strictly increasing sequence of natural-number
vertical shifts `τ j` along which the translates `s ↦ LSeries f (s + τ j * I)` converge to
`LSeries f` locally uniformly on the half-plane `{s | σ < re s}`. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn (f : ℕ → ℂ) {σ : ℝ}
    (hf : ∀ s : ℂ, σ < s.re → LSeriesSummable f s) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ TendstoLocallyUniformlyOn
      (fun j s => LSeries f (s + (τ j : ℂ) * I)) (LSeries f) atTop {s | σ < s.re} := by
  have ha : ∀ j : ℕ, LSeriesSummable f ((σ + 1 / ((j : ℝ) + 1) : ℝ) : ℂ) := fun j => by
    refine hf _ ?_
    rw [ofReal_re]
    have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  obtain ⟨τ, hτ, h⟩ := exists_strictMono_forall_norm_sub_lt f ha
  refine ⟨τ, hτ, ?_⟩
  have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const continuous_re
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen]
  intro K hKs hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  -- `re` attains its minimum `re s₀ > σ` on `K`
  obtain ⟨s₀, hs₀K, hs₀⟩ := hK.exists_isMinOn hne continuous_re.continuousOn
  have hσ : σ < s₀.re := hKs hs₀K
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt (max (1 / (s₀.re - σ)) (1 / ε))
  filter_upwards [eventually_ge_atTop j₀] with j hj s hsK
  have hj' : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
  have hre : σ + 1 / ((j : ℝ) + 1) ≤ s.re := by
    have h1 : 1 / ((j : ℝ) + 1) < s₀.re - σ := by
      rw [one_div_lt (by positivity) (by linarith)]
      linarith [le_max_left (1 / (s₀.re - σ)) (1 / ε)]
    have h2 : s₀.re ≤ s.re := hs₀ hsK
    linarith
  have hεj : 1 / ((j : ℝ) + 1) < ε := by
    rw [one_div_lt (by positivity) hε]
    linarith [le_max_right (1 / (s₀.re - σ)) (1 / ε)]
  rw [dist_comm, dist_eq_norm]
  exact (h j s hre).trans hεj

/-- **Bohr almost periodicity on `ℂ`.** If the Dirichlet series `∑ f n / n ^ s` converges absolutely
for every `s`, there is a strictly increasing sequence of natural-number vertical shifts `τ j` along
which the translates `s ↦ LSeries f (s + τ j * I)` converge to `LSeries f` locally uniformly on
`ℂ`. -/
theorem exists_strictMono_tendstoLocallyUniformly (f : ℕ → ℂ)
    (hf : ∀ s : ℂ, LSeriesSummable f s) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧
      TendstoLocallyUniformly (fun j s => LSeries f (s + (τ j : ℂ) * I)) (LSeries f) atTop := by
  obtain ⟨τ, hτ, h⟩ :=
    exists_strictMono_forall_norm_sub_lt f (a := fun j : ℕ => -(j : ℝ)) fun j => hf _
  refine ⟨τ, hτ, ?_⟩
  rw [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- `K` is bounded: `re s ≥ -R` on `K`
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt (max R (1 / ε))
  filter_upwards [eventually_ge_atTop j₀] with j hj s hsK
  have hsR : ‖s‖ ≤ R := by simpa using hR hsK
  have hj' : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
  have hre : -(j : ℝ) ≤ s.re := by
    have h1 : -‖s‖ ≤ s.re := by linarith [abs_re_le_norm s, neg_abs_le s.re]
    linarith [le_max_left R (1 / ε)]
  have hεj : 1 / ((j : ℝ) + 1) < ε := by
    rw [one_div_lt (by positivity) hε]
    linarith [le_max_right R (1 / ε)]
  rw [dist_comm, dist_eq_norm]
  exact (h j s hre).trans hεj

end LSeries
