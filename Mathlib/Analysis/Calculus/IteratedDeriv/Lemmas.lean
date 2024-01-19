/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Ruben Van de Velde
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# One-dimensional iterated derivatives

This file contains a number of further results on `iteratedDerivWithin` that need more imports
than are available in `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean`.
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
  {n : ℕ} {x : 𝕜} {s : Set 𝕜} (hx : x ∈ s) (h : UniqueDiffOn 𝕜 s) {f g : 𝕜 → F}

theorem iteratedDerivWithin_add (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    iteratedDerivWithin n (f + g) s x =
      iteratedDerivWithin n f s x + iteratedDerivWithin n g s x := by
  simp_rw [iteratedDerivWithin, iteratedFDerivWithin_add_apply hf hg h hx,
    ContinuousMultilinearMap.add_apply]

theorem iteratedDerivWithin_congr (hfg : Set.EqOn f g s) :
    Set.EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n g s) s := by
  induction n generalizing f g with
  | zero => rwa [iteratedDerivWithin_zero]
  | succ n IH =>
    intro y hy
    have : UniqueDiffWithinAt 𝕜 s y := h.uniqueDiffWithinAt hy
    rw [iteratedDerivWithin_succ this, iteratedDerivWithin_succ this]
    exact derivWithin_congr (IH hfg) (IH hfg hy)

theorem iteratedDerivWithin_const_add (hn : 0 < n) (c : F) :
    iteratedDerivWithin n (fun z => c + f z) s x = iteratedDerivWithin n f s x := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ' h hx, iteratedDerivWithin_succ' h hx]
  refine iteratedDerivWithin_congr h ?_ hx
  intro y hy
  exact derivWithin_const_add (h.uniqueDiffWithinAt hy) _

theorem iteratedDerivWithin_const_neg (hn : 0 < n) (c : F) :
    iteratedDerivWithin n (fun z => c - f z) s x = iteratedDerivWithin n (fun z => -f z) s x := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ' h hx, iteratedDerivWithin_succ' h hx]
  refine iteratedDerivWithin_congr h ?_ hx
  intro y hy
  have : UniqueDiffWithinAt 𝕜 s y := h.uniqueDiffWithinAt hy
  rw [derivWithin.neg this]
  exact derivWithin_const_sub this _

theorem iteratedDerivWithin_const_smul (c : R) (hf : ContDiffOn 𝕜 n f s) :
    iteratedDerivWithin n (c • f) s x = c • iteratedDerivWithin n f s x := by
  simp_rw [iteratedDerivWithin]
  rw [iteratedFDerivWithin_const_smul_apply hf h hx]
  simp only [ContinuousMultilinearMap.smul_apply]

theorem iteratedDerivWithin_const_mul (c : 𝕜) {f : 𝕜 → 𝕜} (hf : ContDiffOn 𝕜 n f s) :
    iteratedDerivWithin n (fun z => c * f z) s x = c * iteratedDerivWithin n f s x := by
  simpa using iteratedDerivWithin_const_smul (F := 𝕜) hx h c hf

theorem iteratedDerivWithin_neg (hf : ContDiffOn 𝕜 n f s) :
    iteratedDerivWithin n (-f) s x = -iteratedDerivWithin n f s x := by
  have := iteratedDerivWithin_const_smul hx h (-1) hf
  simpa only [neg_smul, one_smul]

theorem iteratedDerivWithin_neg' (hf : ContDiffOn 𝕜 n f s) :
    iteratedDerivWithin n (fun z => -f z) s x = -iteratedDerivWithin n f s x :=
  iteratedDerivWithin_neg hx h hf

theorem iteratedDerivWithin_sub (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    iteratedDerivWithin n (f - g) s x =
      iteratedDerivWithin n f s x - iteratedDerivWithin n g s x := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Pi.neg_def, iteratedDerivWithin_add hx h hf hg.neg,
    iteratedDerivWithin_neg' hx h hg]
