/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Ruben Van de Velde
-/
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.RCLike.Basic

/-!
# One-dimensional iterated derivatives

This file contains a number of further results on `iteratedDerivWithin` that need more imports
than are available in `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean`.
-/

section one_dimensional

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
  {n : ℕ} {x : 𝕜} {s : Set 𝕜} (hx : x ∈ s) (h : UniqueDiffOn 𝕜 s) {f g : 𝕜 → F}

section

theorem iteratedDerivWithin_congr (hfg : Set.EqOn f g s) :
    Set.EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n g s) s := by
  induction n generalizing f g with
  | zero => rwa [iteratedDerivWithin_zero]
  | succ n IH =>
    intro y hy
    rw [iteratedDerivWithin_succ, iteratedDerivWithin_succ]
    exact derivWithin_congr (IH hfg) (IH hfg hy)

include h hx in
theorem iteratedDerivWithin_add
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (f + g) s x =
      iteratedDerivWithin n f s x + iteratedDerivWithin n g s x := by
  simp_rw [iteratedDerivWithin, iteratedFDerivWithin_add_apply hf hg h hx,
    ContinuousMultilinearMap.add_apply]

theorem iteratedDerivWithin_const_add (hn : 0 < n) (c : F) :
    iteratedDerivWithin n (fun z => c + f z) s x = iteratedDerivWithin n f s x := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ', iteratedDerivWithin_succ']
  congr with y
  exact derivWithin_const_add _

theorem iteratedDerivWithin_const_sub (hn : 0 < n) (c : F) :
    iteratedDerivWithin n (fun z => c - f z) s x = iteratedDerivWithin n (fun z => -f z) s x := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ', iteratedDerivWithin_succ']
  congr with y
  rw [derivWithin.fun_neg]
  exact derivWithin_const_sub _

include h hx in
theorem iteratedDerivWithin_const_smul (c : R) (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (c • f) s x = c • iteratedDerivWithin n f s x := by
  simp_rw [iteratedDerivWithin]
  rw [iteratedFDerivWithin_const_smul_apply hf h hx]
  simp only [ContinuousMultilinearMap.smul_apply]

include h hx in
theorem iteratedDerivWithin_const_mul (c : 𝕜) {f : 𝕜 → 𝕜} (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (fun z => c * f z) s x = c * iteratedDerivWithin n f s x := by
  simpa using iteratedDerivWithin_const_smul (F := 𝕜) hx h c hf

variable (f) in
omit h hx in
theorem iteratedDerivWithin_neg :
    iteratedDerivWithin n (-f) s x = -iteratedDerivWithin n f s x := by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    simp only [iteratedDerivWithin_succ]
    rw [← derivWithin.neg]
    congr with y
    exact IH

variable (f) in
theorem iteratedDerivWithin_fun_neg :
    iteratedDerivWithin n (fun z => -f z) s x = -iteratedDerivWithin n f s x :=
  iteratedDerivWithin_neg f

@[deprecated (since := "2025-06-24")] alias iteratedDerivWithin_neg' := iteratedDerivWithin_fun_neg

include h hx

theorem iteratedDerivWithin_sub
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (f - g) s x =
      iteratedDerivWithin n f s x - iteratedDerivWithin n g s x := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Pi.neg_def, iteratedDerivWithin_add hx h hf hg.neg,
    iteratedDerivWithin_fun_neg]

theorem iteratedDerivWithin_comp_const_smul (hf : ContDiffOn 𝕜 n f s) (c : 𝕜)
    (hs : Set.MapsTo (c * ·) s s) :
    iteratedDerivWithin n (fun x => f (c * x)) s x = c ^ n • iteratedDerivWithin n f s (c * x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hcx : c * x ∈ s := hs hx
    have h₀ : s.EqOn
        (iteratedDerivWithin n (fun x ↦ f (c * x)) s)
        (fun x => c ^ n • iteratedDerivWithin n f s (c * x)) :=
      fun x hx => ih hx hf.of_succ
    have h₁ : DifferentiableWithinAt 𝕜 (iteratedDerivWithin n f s) s (c * x) :=
      hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr n.lt_succ_self) h _ hcx
    have h₂ : DifferentiableWithinAt 𝕜 (fun x => iteratedDerivWithin n f s (c * x)) s x := by
      rw [← Function.comp_def]
      apply DifferentiableWithinAt.comp
      · exact hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr n.lt_succ_self) h _ hcx
      · exact differentiableWithinAt_id'.const_mul _
      · exact hs
    rw [iteratedDerivWithin_succ, derivWithin_congr h₀ (ih hx hf.of_succ),
      derivWithin_fun_const_smul (c ^ n) h₂, iteratedDerivWithin_succ,
      ← Function.comp_def,
      derivWithin.scomp x h₁ (differentiableWithinAt_id'.const_mul _) hs,
      derivWithin_const_mul _ differentiableWithinAt_id', derivWithin_id' _ _ (h _ hx),
      smul_smul, mul_one, pow_succ]

end

lemma iteratedDeriv_add (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (f + g) x = iteratedDeriv n f x + iteratedDeriv n g x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_add (Set.mem_univ _) uniqueDiffOn_univ hf hg

theorem iteratedDeriv_const_add (hn : 0 < n) (c : F) :
    iteratedDeriv n (fun z => c + f z) x = iteratedDeriv n f x := by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_const_add hn c

theorem iteratedDeriv_const_sub (hn : 0 < n) (c : F) :
    iteratedDeriv n (fun z => c - f z) x = iteratedDeriv n (-f) x := by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_const_sub hn c

lemma iteratedDeriv_fun_neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (fun x ↦ -(f x)) a = -(iteratedDeriv n f a) := by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_neg f

lemma iteratedDeriv_neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (-f) a = -(iteratedDeriv n f a) := by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_neg f

lemma iteratedDeriv_sub (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (f - g) x = iteratedDeriv n f x - iteratedDeriv n g x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_sub (Set.mem_univ _) uniqueDiffOn_univ hf hg

theorem iteratedDeriv_const_smul {n : ℕ} {f : 𝕜 → F} (h : ContDiffAt 𝕜 n f x) (c : 𝕜) :
    iteratedDeriv n (c • f) x = c • iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_smul (Set.mem_univ x) uniqueDiffOn_univ
      c (contDiffWithinAt_univ.mpr h)

theorem iteratedDeriv_const_mul {n : ℕ} {f : 𝕜 → 𝕜} (h : ContDiffAt 𝕜 n f x) (c : 𝕜) :
    iteratedDeriv n (fun z => c * f z) x = c * iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_mul (Set.mem_univ x) uniqueDiffOn_univ
      c (contDiffWithinAt_univ.mpr h)

theorem iteratedDeriv_comp_const_smul {n : ℕ} {f : 𝕜 → F} (h : ContDiff 𝕜 n f) (c : 𝕜) :
    iteratedDeriv n (fun x => f (c * x)) = fun x => c ^ n • iteratedDeriv n f (c * x) := by
  funext x
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_comp_const_smul (Set.mem_univ x) uniqueDiffOn_univ (contDiffOn_univ.mpr h)
      c (Set.mapsTo_univ _ _)

theorem iteratedDeriv_comp_const_mul {n : ℕ} {f : 𝕜 → 𝕜} (h : ContDiff 𝕜 n f) (c : 𝕜) :
    iteratedDeriv n (fun x => f (c * x)) = fun x => c ^ n * iteratedDeriv n f (c * x) := by
  simpa only [smul_eq_mul] using iteratedDeriv_comp_const_smul h c

lemma iteratedDeriv_comp_neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (fun x ↦ f (-x)) a = (-1 : 𝕜) ^ n • iteratedDeriv n f (-a) := by
  induction' n with n ih generalizing a
  · simp only [iteratedDeriv_zero, pow_zero, one_smul]
  · have ih' : iteratedDeriv n (fun x ↦ f (-x)) = fun x ↦ (-1 : 𝕜) ^ n • iteratedDeriv n f (-x) :=
      funext ih
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ih', pow_succ', neg_mul, one_mul,
      deriv_comp_neg (f := fun x ↦ (-1 : 𝕜) ^ n • iteratedDeriv n f x), deriv_fun_const_smul',
      neg_smul]

open Topology in
lemma Filter.EventuallyEq.iteratedDeriv_eq (n : ℕ) {f g : 𝕜 → F} {x : 𝕜} (hfg : f =ᶠ[𝓝 x] g) :
    iteratedDeriv n f x = iteratedDeriv n g x := by
  simp only [← iteratedDerivWithin_univ, iteratedDerivWithin_eq_iteratedFDerivWithin]
  rw [(hfg.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq hfg.eq_of_nhds n]

lemma Set.EqOn.iteratedDeriv_of_isOpen (hfg : Set.EqOn f g s) (hs : IsOpen s) (n : ℕ) :
    Set.EqOn (iteratedDeriv n f) (iteratedDeriv n g) s := by
  refine fun x hx ↦ Filter.EventuallyEq.iteratedDeriv_eq n ?_
  filter_upwards [IsOpen.mem_nhds hs hx] with a ha
  exact hfg ha

end one_dimensional

/-!
### Invariance of iterated derivatives under translation
-/

section shift_invariance

variable {𝕜 F} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The iterated derivative commutes with shifting the function by a constant on the left. -/
lemma iteratedDeriv_comp_const_add (n : ℕ) (f : 𝕜 → F) (s : 𝕜) :
    iteratedDeriv n (fun z ↦ f (s + z)) = fun t ↦ iteratedDeriv n f (s + t) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n IH =>
    simpa only [iteratedDeriv_succ, IH] using funext <| deriv_comp_const_add _ s

/-- The iterated derivative commutes with shifting the function by a constant on the right. -/
lemma iteratedDeriv_comp_add_const (n : ℕ) (f : 𝕜 → F) (s : 𝕜) :
    iteratedDeriv n (fun z ↦ f (z + s)) = fun t ↦ iteratedDeriv n f (t + s) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n IH =>
    simpa only [iteratedDeriv_succ, IH] using funext <| deriv_comp_add_const _ s

end shift_invariance

/-- If `f` is analytic on `Bᵣ(x₀)` and its Taylor series converges on this ball, then it converges
to `f`. -/
theorem AnalyticOn_subball_hasFPowerSeriesOnBall {𝕜 : Type*} [RCLike 𝕜] {f : 𝕜 → 𝕜} {x : 𝕜}
    {r : ENNReal} (hr_pos : 0 < r) (h : AnalyticOn 𝕜 f (EMetric.ball x r)) :
    let p := FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ iteratedDeriv n f x / n.factorial);
    r ≤ p.radius → HasFPowerSeriesOnBall f p x r := by
  rw [EMetric.isOpen_ball.analyticOn_iff_analyticOnNhd] at h
  intro p hr
  let g (t : 𝕜) := p.sum (t - x)
  have hg : HasFPowerSeriesOnBall g p x p.radius := by
    simpa using
      (p.hasFPowerSeriesOnBall (lt_of_lt_of_le hr_pos hr)).comp_sub x
  have hg' : AnalyticOnNhd 𝕜 g (EMetric.ball x p.radius) := by
    simpa using AnalyticOnNhd.comp_sub p.AnalyticOnNhd x
  replace hg' : AnalyticOnNhd 𝕜 g (EMetric.ball x r) :=
    hg'.mono (EMetric.ball_subset_ball hr)
  apply h.eqOn_of_preconnected_of_eventuallyEq at hg'
  apply (hg.mono hr_pos hr).congr
  symm
  apply hg' (IsConnected.isPreconnected (Metric.isConnected_eball hr_pos))
    (show x ∈ EMetric.ball x r by simpa) ?_
  have hf : AnalyticAt 𝕜 f x := h _ (by simp [hr_pos])
  apply AnalyticAt.hasFPowerSeriesAt at hf
  unfold Filter.EventuallyEq Filter.Eventually
  rw [EMetric.mem_nhds_iff]
  obtain ⟨ε, hf⟩ := hf
  exact ⟨ε, hf.r_pos, hf.unique (hg.mono hf.r_pos hf.r_le)⟩

/-- If `f` is analytic on the ball of convergence of its Taylor series, then the series converges
to `f` on this ball. -/
theorem AnalyticOn.hasFPowerSeriesOnBall {𝕜 : Type*} [RCLike 𝕜] {f : 𝕜 → 𝕜} {x : 𝕜} :
    let p := FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ iteratedDeriv n f x / n.factorial);
    0 < p.radius → AnalyticOn 𝕜 f (EMetric.ball x p.radius) →
    HasFPowerSeriesOnBall f p x p.radius := by
  intro p hr hs
  exact AnalyticOn_subball_hasFPowerSeriesOnBall hr hs (by rfl)
