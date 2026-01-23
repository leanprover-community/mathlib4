/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/
import Mathlib.Analysis.Complex.DivisorComplement
import Mathlib.Analysis.Complex.DivisorConvergence
import Mathlib.Analysis.Complex.DivisorFiber
import Mathlib.Analysis.Complex.DivisorPartialProductFactor
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Order.Filter.Cofinite

/-!
# Quotient convergence for divisor-indexed canonical products

This file develops the convergence of quotients of finite partial products and of the
divisor-indexed canonical product by powers `(z - z₀)^k` away from `z₀`. It also proves the key
local identity on a punctured ball used later in removable-singularity arguments.
-/

noncomputable section

open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

theorem tendstoLocallyUniformlyOn_divisorPartialProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    TendstoLocallyUniformlyOn
      (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
      (divisorCanonicalProduct m f (Set.univ : Set ℂ))
      Filter.atTop
      (Set.univ : Set ℂ) := by
  classical
  have hprod :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
          weierstrassFactor m (z / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  simpa [HasProdLocallyUniformlyOn, divisorPartialProduct] using hprod

/-!
## Quotient convergence on compacts avoiding `z₀`

If `K` is compact and avoids `z₀`, then multiplying by `((z - z₀)^k)⁻¹` preserves uniform
convergence on `K`. -/

theorem tendstoUniformlyOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) {K : Set ℂ} (hK : IsCompact K) (hKz : ∀ z ∈ K, z ≠ z₀) :
    TendstoUniformlyOn
      (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
      K := by
  classical
  have hloc :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        Filter.atTop
        K :=
    (tendstoLocallyUniformlyOn_divisorPartialProduct_univ (m := m) (f := f) h_sum).mono
      (by intro z hz; simp)
  have hunif :
      TendstoUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        Filter.atTop
        K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 hloc
  let h : ℂ → ℂ := fun z => ((z - z₀) ^ k)⁻¹
  have hh : ∃ C, ∀ z ∈ K, ‖h z‖ ≤ C := by
    have hcont : ContinuousOn h K := by
      have hpow : ContinuousOn (fun z : ℂ => (z - z₀) ^ k) K := by
        fun_prop
      refine hpow.inv₀ ?_
      intro z hz
      have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr (hKz z hz)
      exact pow_ne_zero k hz0
    have hKimg : IsCompact (h '' K) := hK.image_of_continuousOn hcont
    rcases (isBounded_iff_forall_norm_le.1 hKimg.isBounded) with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro z hz
    exact hC (h z) ⟨z, hz, rfl⟩
  have hunif' :=
    (TendstoUniformlyOn.mul_left_bounded (p := (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f
    (Set.univ : Set ℂ)))))
        (K := K)
        (F := fun s z => divisorPartialProduct m f s z)
        (f := fun z => divisorCanonicalProduct m f (Set.univ : Set ℂ) z)
        (h := h)
        hunif hh)
  simpa [h, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hunif'

/-!
## Quotient locally uniform convergence on the punctured plane `ℂ \ {z₀}`
-/

theorem tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hopen : IsOpen ((Set.univ : Set ℂ) \ {z₀}) := by
    have hset : ((Set.univ : Set ℂ) \ {z₀}) = ({z₀} : Set ℂ)ᶜ := by
      ext z
      simp
    simp [hset]
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).2 ?_
  intro K hKsub hK
  have hKz : ∀ z ∈ K, z ≠ z₀ := by
    intro z hzK
    have : z ∈ (Set.univ : Set ℂ) \ {z₀} := hKsub hzK
    exact by simpa [Set.mem_diff, Set.mem_singleton_iff] using this.2
  exact tendstoUniformlyOn_divisorPartialProduct_div_pow_sub
    (m := m) (f := f) h_sum (z₀ := z₀) (k := k) (hK := hK) hKz

/-!
## Passing the fiber/complement factorization to the infinite product (punctured neighborhood)

This is the core “removable singularity” input: near `z₀`, the quotient
`divisorCanonicalProduct / (z - z₀)^k` agrees (on a punctured ball) with the product of
`divisorComplementCanonicalProduct` and the analytic factor `u` coming from the fiber-only product.
-/

open Filter

set_option maxHeartbeats 800000 in
-- The proof below is heartbeat-heavy: it combines local uniform convergence of partial products
-- with a removable singularity argument around `z₀`.
theorem exists_ball_eq_divisorCanonicalProduct_div_pow_eq
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
    ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) (z₀ : ℂ) : ∃ ε > 0, ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧
    u z₀ ≠ 0 ∧ ∀ z : ℂ, z ∈ Metric.ball z₀ ε → z ≠ z₀ → (divisorCanonicalProduct m f
    (Set.univ : Set ℂ) z) / (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card =
          (divisorComplementCanonicalProduct m f z₀ z) * u z := by
  classical
  let fiber : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    divisorZeroIndex₀_fiberFinset (f := f) z₀
  have hfib : ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧
          (fun z : ℂ => divisorPartialProduct m f fiber z) =ᶠ[𝓝 z₀]
            fun z : ℂ => (z - z₀) ^ fiber.card • u z := by
    simpa [fiber, divisorPartialProduct] using
      (exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber (m := m) (f := f) (z₀ := z₀)
        (s := fiber) (by rfl : fiber ⊆ fiber))
  rcases hfib with ⟨u, huA, hu0, huEq⟩
  have hmem : {z : ℂ | divisorPartialProduct m f fiber z =
      (z - z₀) ^ fiber.card • u z} ∈ 𝓝 z₀ := huEq
  rcases Metric.mem_nhds_iff.1 hmem with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, u, huA, hu0, ?_⟩
  have hq :
      TendstoLocallyUniformlyOn (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card)
        (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
        ((Set.univ : Set ℂ) \ {z₀}) :=
    tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
      (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀) (k := fiber.card)
  have hcomp :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s)
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) :=
    tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ (m := m) (f := f)
    (z₀ := z₀) h_sum
  intro z hz hzne
  have hz' : z ∈ ((Set.univ : Set ℂ) \ {z₀}) := by
    refine ⟨by simp, ?_⟩
    simpa [Set.mem_singleton_iff] using hzne
  have hF : Tendsto (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card) (Filter.atTop : Filter _)
        (𝓝 ((divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ fiber.card)) :=
    hq.tendsto_at hz'
  have hG0 : Tendsto  (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s z) (Filter.atTop : Filter _)
        (𝓝 (divisorComplementCanonicalProduct m f z₀ z)) :=
    hcomp.tendsto_at (by simp : z ∈ (Set.univ : Set ℂ))
  have hG : Tendsto (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorComplementPartialProduct m f z₀ s z) * u z) (Filter.atTop : Filter _)
        (𝓝 ((divisorComplementCanonicalProduct m f z₀ z) * u z)) :=
    (hG0.mul tendsto_const_nhds)
  have hsub : ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      fiber ⊆ s := eventually_atTop_subset_fiberFinset (f := f) z₀
  have heq_eventually :
      ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
        (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card
          = (divisorComplementPartialProduct m f z₀ s z) * u z := by
    filter_upwards [hsub] with s hs
    have hsplit :
        divisorPartialProduct m f s z =
          divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z := by
      simpa [fiber] using
        (divisorPartialProduct_eq_fiber_mul_complement_of_subset (m := m) (f := f) (z₀ := z₀)
          (z := z) (s := s) hs)
    have hfibz :
        divisorPartialProduct m f fiber z = (z - z₀) ^ fiber.card • u z := by
      exact hball hz
    have hzpow : (z - z₀) ^ fiber.card ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr hzne)
    set a : ℂ := (z - z₀) ^ fiber.card
    have ha : a ≠ 0 := by simpa [a] using hzpow
    set c : ℂ := divisorComplementPartialProduct m f z₀ s z with hc
    rw [hsplit, hfibz, smul_eq_mul]
    calc
      ((a * u z) * c) / a
          = (a * (u z * c)) / a := by simp [mul_assoc]
      _ = u z * c := by
            simpa [mul_assoc] using (mul_div_cancel_left₀ (u z * c) ha)
      _ = c * u z := by ac_rfl
      _ = (divisorComplementPartialProduct m f z₀ s z) * u z := by
            simp [c]
  have hG' :
      Tendsto
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter _)
        (𝓝 ((divisorComplementCanonicalProduct m f z₀ z) * u z)) := by
    have heq' :
        ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
          (divisorComplementPartialProduct m f z₀ s z) * u z
            = (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card := by
      filter_upwards [heq_eventually] with s hs
      exact hs.symm
    exact (hG.congr' heq')
  exact tendsto_nhds_unique hF hG'

/-!
## Boundedness of the quotient on a punctured ball

We only need boundedness of the analytic factor `u` near `z₀`, so `ContinuousAt` at `z₀` suffices.
-/

theorem bddAbove_norm_divisorCanonicalProduct_div_pow_puncturedBall
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ r > 0,
      BddAbove
        (norm ∘
          (fun z : ℂ =>
            (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) ''
            ((Metric.ball z₀ r) \ {z₀})) := by
  classical
  rcases exists_ball_eq_divisorCanonicalProduct_div_pow_eq (m := m) (f := f) (h_sum := h_sum)
    (z₀ := z₀) with ⟨ε, hε, u, huA, hu0, hEq⟩
  have huC : ContinuousAt u z₀ := huA.continuousAt
  have hpre : {z : ℂ | ‖u z - u z₀‖ < 1} ∈ 𝓝 z₀ := by
    have : u ⁻¹' Metric.ball (u z₀) (1 : ℝ) ∈ 𝓝 z₀ :=
      huC.preimage_mem_nhds (Metric.ball_mem_nhds (u z₀) (by norm_num))
    simpa [Metric.ball, dist_eq_norm, Set.preimage] using this
  rcases Metric.mem_nhds_iff.1 hpre with ⟨r0, hr0pos, hr0sub⟩
  set r : ℝ := min (ε / 2) r0
  have hrpos : 0 < r := lt_min (by nlinarith [hε]) hr0pos
  have hr_lt_ε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by nlinarith [hε])
  have huBound : ∀ z ∈ Metric.ball z₀ r, ‖u z‖ ≤ ‖u z₀‖ + 1 := by
    intro z hz
    have hz0 : z ∈ Metric.ball z₀ r0 := by
      have : r ≤ r0 := min_le_right _ _
      exact Metric.ball_subset_ball this hz
    have hdiff : ‖u z - u z₀‖ < 1 := hr0sub hz0
    have htri : ‖u z‖ ≤ ‖u z - u z₀‖ + ‖u z₀‖ := by
      simpa [sub_eq_add_neg, add_assoc] using
        (norm_add_le (u z - u z₀) (u z₀))
    have : ‖u z‖ ≤ 1 + ‖u z₀‖ := le_trans htri (by nlinarith [le_of_lt hdiff])
    nlinarith [this]
  have hdiffC :
      DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀) (Set.univ : Set ℂ) :=
    differentiableOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum
  have hcontC : ContinuousOn (divisorComplementCanonicalProduct m f z₀) (Metric.closedBall z₀ r) :=
    (hdiffC.continuousOn).mono (by intro z hz; simp)
  have hK : IsCompact (Metric.closedBall z₀ r) := isCompact_closedBall _ _
  rcases (isBounded_iff_forall_norm_le.1 (hK.image_of_continuousOn hcontC).isBounded) with ⟨C, hC⟩
  refine ⟨r, hrpos, ⟨C * (‖u z₀‖ + 1), ?_⟩⟩
  rintro _ ⟨z, hzset, rfl⟩
  rcases hzset with ⟨hzr, hzne⟩
  have hz_in_ε : z ∈ Metric.ball z₀ ε := Metric.ball_subset_ball hr_lt_ε.le hzr
  have hz_ne : z ≠ z₀ := by simpa [Set.mem_singleton_iff] using hzne
  have hq :
      (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card
        = divisorComplementCanonicalProduct m f z₀ z * u z :=
    hEq z hz_in_ε hz_ne
  have hCz : ‖divisorComplementCanonicalProduct m f z₀ z‖ ≤ C := by
    have hzK : z ∈ Metric.closedBall z₀ r := Metric.mem_closedBall.2 (le_of_lt hzr)
    exact hC _ ⟨z, hzK, rfl⟩
  have huZ : ‖u z‖ ≤ ‖u z₀‖ + 1 := huBound z hzr
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) hCz
  have hmul : ‖divisorComplementCanonicalProduct m f z₀ z * u z‖ ≤ C * (‖u z₀‖ + 1) := by
    calc
      ‖divisorComplementCanonicalProduct m f z₀ z * u z‖
          = ‖divisorComplementCanonicalProduct m f z₀ z‖ * ‖u z‖ := by simp
      _ ≤ C * (‖u z₀‖ + 1) := by
            exact mul_le_mul hCz huZ (norm_nonneg _) hCnonneg
  simpa [Function.comp, hq] using hmul

/-!
## Nonvanishing of the complement canonical product near `z₀`

Pointwise, the complement canonical product is an infinite product of factors of the form `1 + aₚ`
with `∑ ‖aₚ‖` summable, hence the product is nonzero.
-/

theorem divisorComplementCanonicalProduct_ne_zero_at
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    divisorComplementCanonicalProduct m f z₀ z₀ ≠ 0 := by
  classical
  let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ :=
    fun p => if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
      else weierstrassFactor m (z₀ / divisorZeroIndex₀_val p)
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ := fun p => Φ p - 1
  have hΦ_ne : ∀ p, Φ p ≠ 0 := by
    intro p
    by_cases hp : divisorZeroIndex₀_val p = z₀
    · simp [Φ, hp]
    · have hval : divisorZeroIndex₀_val p ≠ z₀ := hp
      have hz : z₀ / divisorZeroIndex₀_val p ≠ (1 : ℂ) := by
        intro h
        by_cases hp0 : divisorZeroIndex₀_val p = 0
        · have : z₀ / divisorZeroIndex₀_val p = (0 : ℂ) := by simp [hp0]
          have h01 := h
          rw [this] at h01
          exact (show False from (by simpa using (show (0 : ℂ) ≠ (1 : ℂ) from by simp) h01))
        · have : z₀ = divisorZeroIndex₀_val p := (div_eq_one_iff_eq hp0).1 h
          exact hval this.symm
      have hE : weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) ≠ 0 := by
        intro h0
        have : z₀ / divisorZeroIndex₀_val p = (1 : ℂ) :=
          (weierstrassFactor_eq_zero_iff (m := m) (z := z₀ / divisorZeroIndex₀_val p)).1 h0
        exact hz this
      simp [Φ, hp, hE]
  have hz0_le : ‖z₀‖ ≤ max ‖z₀‖ 1 := le_max_left _ _
  set R : ℝ := max ‖z₀‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀_val p‖ := by
    have hfin : ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤
        2 * R} : Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀_val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ‖a p‖ ≤ u p := by
    filter_upwards [h_big] with p hp
    have ha_pos : 0 < ‖divisorZeroIndex₀_val p‖ := lt_trans (by nlinarith [hRpos]) hp
    have hz_div : ‖z₀ / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) := by
      have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
      have hinv : ‖divisorZeroIndex₀_val p‖⁻¹ < (2 * R)⁻¹ := by
        simpa [one_div] using (one_div_lt_one_div_of_lt h2R_pos hp)
      have hmul_le : ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ ≤ R * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
        exact hz0_le
      have hmul_lt : R * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
        mul_lt_mul_of_pos_left hinv hRpos
      have hlt : ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
        lt_of_le_of_lt hmul_le hmul_lt
      have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
        have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
        have : R * (2 * R)⁻¹ = R / (2 * R) := by simp [div_eq_mul_inv]
        rw [this]
        field_simp [hRne]
      have hnorm : ‖z₀ / divisorZeroIndex₀_val p‖ = ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      have hzlt : ‖z₀ / divisorZeroIndex₀_val p‖ < (1 / 2 : ℝ) := by
        calc
          ‖z₀ / divisorZeroIndex₀_val p‖ = ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := hnorm
          _ < R * (2 * R)⁻¹ := hlt
          _ = (1 / 2 : ℝ) := hRhalf
      exact le_of_lt hzlt
    have hE :
        ‖weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) - 1‖ ≤
          4 * ‖z₀ / divisorZeroIndex₀_val p‖ ^ (m + 1) :=
      weierstrassFactor_sub_one_pow_bound (m := m) (z := z₀ / divisorZeroIndex₀_val p) hz_div
    have hz_pow :
        ‖z₀ / divisorZeroIndex₀_val p‖ ^ (m + 1) ≤
          (R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
      have : ‖z₀ / divisorZeroIndex₀_val p‖ = ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      rw [this]
      have : (‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹) ^ (m + 1) =
          ‖z₀‖ ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
        simp [mul_pow]
      rw [this]
      have hzle_pow : ‖z₀‖ ^ (m + 1) ≤ R ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg z₀) hz0_le (m + 1)
      gcongr
    have hp_ne : divisorZeroIndex₀_val p ≠ z₀ := by
      intro h
      have : ‖divisorZeroIndex₀_val p‖ ≤ R := by
        simp [h, R]  -- `‖z₀‖ ≤ max ‖z₀‖ 1`
      exact (not_lt_of_ge this) (lt_trans (by nlinarith [hRpos]) hp)
    have ha : ‖a p‖ = ‖weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) - 1‖ := by
      simp [a, Φ, hp_ne, sub_eq_add_neg]
    calc
      ‖a p‖ = ‖weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) - 1‖ := ha
      _ ≤ 4 * ‖z₀ / divisorZeroIndex₀_val p‖ ^ (m + 1) := by
            simpa [sub_eq_add_neg, add_comm] using hE
      _ ≤ 4 * (R ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) := by
            gcongr
      _ = u p := by
            simp [u, mul_assoc, mul_comm]
  have hsum_norm : Summable (fun p => ‖a p‖) := by
    refine (Summable.of_norm_bounded_eventually (E := ℝ) (f := fun p => ‖a p‖) (g := u) hu ?_)
    filter_upwards [hBound] with p hp
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (a p))] using hp
  have htprod_ne :
      (∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (1 + a p)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (R := ℂ) (f := a) (hf := fun p => by
      simpa [a, Φ, add_sub_cancel] using hΦ_ne p) hsum_norm
  have : (∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (1 + a p)) =
      divisorComplementCanonicalProduct m f z₀ z₀ := by
    simp [a, Φ, divisorComplementCanonicalProduct, mem_divisorZeroIndex₀_fiberFinset]
  exact by
    intro h0
    exact htprod_ne (by simpa [this] using h0)

theorem exists_ball_divisorComplementCanonicalProduct_ne_zero
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    ∃ r > 0, ∀ z ∈ Metric.ball z₀ r, divisorComplementCanonicalProduct m f z₀ z ≠ 0 := by
  classical
  have hdiff :
      DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀) (Set.univ : Set ℂ) :=
    differentiableOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum
  have hdiffAt : DifferentiableAt ℂ (divisorComplementCanonicalProduct m f z₀) z₀ := by
    exact (hdiff z₀ (by simp)).differentiableAt (by simp)
  have hcont : ContinuousAt (divisorComplementCanonicalProduct m f z₀) z₀ :=
    hdiffAt.continuousAt
  have h0 : divisorComplementCanonicalProduct m f z₀ z₀ ≠ 0 :=
    divisorComplementCanonicalProduct_ne_zero_at (m := m) (f := f) (z₀ := z₀) h_sum
  have hopen : IsOpen (({0} : Set ℂ)ᶜ) := isClosed_singleton.isOpen_compl
  have hmem : divisorComplementCanonicalProduct m f z₀ z₀ ∈ (({0} : Set ℂ)ᶜ) := by
    simp [h0]
  rcases (Metric.mem_nhds_iff.1 (hcont (hopen.mem_nhds hmem))) with ⟨r, hrpos, hr⟩
  refine ⟨r, hrpos, ?_⟩
  intro z hz
  have : divisorComplementCanonicalProduct m f z₀ z ∈ ({0} : Set ℂ)ᶜ := hr hz
  simpa using this

/-!
## Eventually: partial products factor at `z₀` with the fiber multiplicity

Along `atTop`, sufficiently large partial products contain the fiber, hence each such partial
product is locally divisible by `(z - z₀)^k`, where `k` is the fiber cardinality.
-/

theorem eventually_exists_analyticAt_eq_pow_smul_divisorPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
          (fun z : ℂ => divisorPartialProduct m f s z)
            =ᶠ[𝓝 z₀]
            fun z : ℂ =>
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card • g z := by
  classical
  refine (eventually_atTop_subset_fiberFinset (f := f) z₀).mono ?_
  intro s hs
  rcases
      exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber
        (m := m) (f := f) (z₀ := z₀) (s := s) hs with
    ⟨g, hg, hg0, hEq⟩
  refine ⟨g, hg, hg0, ?_⟩
  simpa [divisorPartialProduct] using hEq

/-!
## On `𝓝[≠] z₀`, large partial product quotients agree with an analytic function

This is the punctured-neighborhood version of
`eventually_exists_analyticAt_eq_pow_smul_divisorPartialProduct`,
obtained by dividing the factorization by `(z - z₀)^k` away from `z₀`.
-/

theorem eventually_eq_punctured_quotient_of_factorization
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ (fun z : ℂ => (divisorPartialProduct m f s z) /
            (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
            =ᶠ[𝓝[≠] z₀] g := by
  classical
  refine (eventually_exists_analyticAt_eq_pow_smul_divisorPartialProduct (m := m)
    (f := f) z₀).mono ?_
  intro s hs
  rcases hs with ⟨g, hg, hg0, hEq⟩
  refine ⟨g, hg, ?_⟩
  have hEq' : (fun z : ℂ => divisorPartialProduct m f s z) =ᶠ[𝓝[≠] z₀]
        fun z : ℂ => (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card • g z :=
    hEq.filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ z : ℂ in 𝓝[≠] z₀, z ≠ z₀ := by
    simpa [Filter.Eventually] using (self_mem_nhdsWithin : {z : ℂ | z ≠ z₀} ∈ 𝓝[≠] z₀)
  filter_upwards [hEq', hne] with z hz hzne
  have hz0 : (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr hzne)
  have : (divisorPartialProduct m f s z) / (z - z₀) ^ (divisorZeroIndex₀_fiberFinset
      (f := f) z₀).card = g z := by
    rw [hz]
    simpa [smul_eq_mul] using (mul_div_cancel_left₀ (g z) hz0)
  simpa [divisorPartialProduct] using this

theorem eventually_exists_ball_eq_punctured_quotient_of_factorization
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∃ ε > 0, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
        ∀ z : ℂ, z ∈ Metric.ball z₀ ε → z ≠ z₀ → (divisorPartialProduct m f s z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card
            = g z := by
  classical
  refine (eventually_eq_punctured_quotient_of_factorization (m := m) (f := f) z₀).mono ?_
  intro s hs
  rcases hs with ⟨g, hg, hEq⟩
  rcases (Metric.nhdsWithin_basis_ball (x := z₀) (s := {z : ℂ | z ≠ z₀})).mem_iff.1 hEq with
    ⟨ε, hε, hball⟩
  refine ⟨ε, hε, g, hg, ?_⟩
  intro z hz hz0
  have hz' : z ∈ Metric.ball z₀ ε ∩ {z : ℂ | z ≠ z₀} := ⟨hz, hz0⟩
  exact hball hz'

end Complex.Hadamard
