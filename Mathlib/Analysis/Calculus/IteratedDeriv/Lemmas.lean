/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Ruben Van de Velde
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

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
include h

theorem iteratedDerivWithin_congr (hfg : Set.EqOn f g s) :
    Set.EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n g s) s := by
  induction n generalizing f g with
  | zero => rwa [iteratedDerivWithin_zero]
  | succ n IH =>
    intro y hy
    have : UniqueDiffWithinAt 𝕜 s y := h.uniqueDiffWithinAt hy
    rw [iteratedDerivWithin_succ this, iteratedDerivWithin_succ this]
    exact derivWithin_congr (IH hfg) (IH hfg hy)

include hx

theorem iteratedDerivWithin_add (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    iteratedDerivWithin n (f + g) s x =
      iteratedDerivWithin n f s x + iteratedDerivWithin n g s x := by
  simp_rw [iteratedDerivWithin, iteratedFDerivWithin_add_apply hf hg h hx,
    ContinuousMultilinearMap.add_apply]

theorem iteratedDerivWithin_const_add (hn : 0 < n) (c : F) :
    iteratedDerivWithin n (fun z => c + f z) s x = iteratedDerivWithin n f s x := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ' h hx, iteratedDerivWithin_succ' h hx]
  refine iteratedDerivWithin_congr h ?_ hx
  intro y hy
  exact derivWithin_const_add (h.uniqueDiffWithinAt hy) _

theorem iteratedDerivWithin_const_sub (hn : 0 < n) (c : F) :
    iteratedDerivWithin n (fun z => c - f z) s x = iteratedDerivWithin n (fun z => -f z) s x := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ' h hx, iteratedDerivWithin_succ' h hx]
  refine iteratedDerivWithin_congr h ?_ hx
  intro y hy
  have : UniqueDiffWithinAt 𝕜 s y := h.uniqueDiffWithinAt hy
  rw [derivWithin.neg this]
  exact derivWithin_const_sub this _

@[deprecated (since := "2024-12-10")]
alias iteratedDerivWithin_const_neg := iteratedDerivWithin_const_sub

theorem iteratedDerivWithin_const_smul (c : R) (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (c • f) s x = c • iteratedDerivWithin n f s x := by
  simp_rw [iteratedDerivWithin]
  rw [iteratedFDerivWithin_const_smul_apply hf h hx]
  simp only [ContinuousMultilinearMap.smul_apply]

theorem iteratedDerivWithin_const_mul (c : 𝕜) {f : 𝕜 → 𝕜} (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (fun z => c * f z) s x = c * iteratedDerivWithin n f s x := by
  simpa using iteratedDerivWithin_const_smul (F := 𝕜) hx h c hf

variable (f) in
theorem iteratedDerivWithin_neg :
    iteratedDerivWithin n (-f) s x = -iteratedDerivWithin n f s x := by
  rw [iteratedDerivWithin, iteratedDerivWithin, iteratedFDerivWithin_neg_apply h hx,
    ContinuousMultilinearMap.neg_apply]

variable (f) in
theorem iteratedDerivWithin_neg' :
    iteratedDerivWithin n (fun z => -f z) s x = -iteratedDerivWithin n f s x :=
  iteratedDerivWithin_neg hx h f

theorem iteratedDerivWithin_sub (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    iteratedDerivWithin n (f - g) s x =
      iteratedDerivWithin n f s x - iteratedDerivWithin n g s x := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Pi.neg_def, iteratedDerivWithin_add hx h hf hg.neg,
    iteratedDerivWithin_neg' hx h]

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
    rw [iteratedDerivWithin_succ (h _ hx), derivWithin_congr h₀ (ih hx hf.of_succ),
      derivWithin_const_smul (h _ hx) (c ^ n) h₂, iteratedDerivWithin_succ (h _ hcx),
      ← Function.comp_def,
      derivWithin.scomp x h₁ (differentiableWithinAt_id'.const_mul _) hs (h _ hx),
      derivWithin_const_mul (h _ hx) _ differentiableWithinAt_id', derivWithin_id' _ _ (h _ hx),
      smul_smul, mul_one, pow_succ]

end

lemma iteratedDeriv_add (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    iteratedDeriv n (f + g) x = iteratedDeriv n f x + iteratedDeriv n g x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_add (Set.mem_univ _) uniqueDiffOn_univ
      (contDiffOn_univ.mpr hf) (contDiffOn_univ.mpr hg)

theorem iteratedDeriv_const_add (hn : 0 < n) (c : F) :
    iteratedDeriv n (fun z => c + f z) x = iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_add (Set.mem_univ _) uniqueDiffOn_univ hn c

theorem iteratedDeriv_const_sub (hn : 0 < n) (c : F) :
    iteratedDeriv n (fun z => c - f z) x = iteratedDeriv n (-f) x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_sub (Set.mem_univ _) uniqueDiffOn_univ hn c

lemma iteratedDeriv_neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (fun x ↦ -(f x)) a = -(iteratedDeriv n f a) := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_neg (Set.mem_univ a) uniqueDiffOn_univ f

lemma iteratedDeriv_sub (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    iteratedDeriv n (f - g) x = iteratedDeriv n f x - iteratedDeriv n g x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_sub (Set.mem_univ _) uniqueDiffOn_univ
      (contDiffOn_univ.mpr hf) (contDiffOn_univ.mpr hg)

theorem iteratedDeriv_comp_const_smul {n : ℕ} {f : 𝕜 → F} (h : ContDiff 𝕜 n f) (c : 𝕜) :
    iteratedDeriv n (fun x => f (c * x)) = fun x => c ^ n • iteratedDeriv n f (c * x) := by
  funext x
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_comp_const_smul (Set.mem_univ x) uniqueDiffOn_univ (contDiffOn_univ.mpr h)
      c (Set.mapsTo_univ _ _)

@[deprecated (since := "2024-12-20")]
alias iteratedDeriv_const_smul := iteratedDeriv_comp_const_smul

theorem iteratedDeriv_comp_const_mul {n : ℕ} {f : 𝕜 → 𝕜} (h : ContDiff 𝕜 n f) (c : 𝕜) :
    iteratedDeriv n (fun x => f (c * x)) = fun x => c ^ n * iteratedDeriv n f (c * x) := by
  simpa only [smul_eq_mul] using iteratedDeriv_comp_const_smul h c

@[deprecated (since := "2024-12-20")]
alias iteratedDeriv_const_mul := iteratedDeriv_comp_const_mul

lemma iteratedDeriv_comp_neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (fun x ↦ f (-x)) a = (-1 : 𝕜) ^ n • iteratedDeriv n f (-a) := by
  induction' n with n ih generalizing a
  · simp only [iteratedDeriv_zero, pow_zero, one_smul]
  · have ih' : iteratedDeriv n (fun x ↦ f (-x)) = fun x ↦ (-1 : 𝕜) ^ n • iteratedDeriv n f (-x) :=
      funext ih
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ih', pow_succ', neg_mul, one_mul,
      deriv_comp_neg (f := fun x ↦ (-1 : 𝕜) ^ n • iteratedDeriv n f x), deriv_const_smul',
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
