/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.Harmonic.Analytic

/-!
# Liouville's Theorem for Harmonic Functions on the Complex Plane

A real-valued, bounded harmonic function on the complex plane is constant.

TODO: Prove this result for harmonic functions with values in vector spaces.
-/

public section

open Complex Real Set

set_option backward.isDefEq.respectTransparency false in
/-
**Liouville's theorem for harmonic functions on the complex plane** A real-valued, bounded harmonic
function on the complex plane is constant.
-/
theorem InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant (f : ℂ → ℝ)
    (h_harm : HarmonicOnNhd f univ) (h_bound : Bornology.IsBounded (range f)) :
    ∀ z w, f z = f w := by
  -- By assumption, there exists a holomorphic function $f$ such that $\Re(f) = u$.
  obtain ⟨F, hF_diff, hF_re⟩ := harmonic_is_realOfHolomorphic_univ h_harm
  -- Since $g(z)$ is bounded, by Liouville's theorem, $g(z)$ is constant.
  suffices ∀ z w, Complex.exp (F z) = Complex.exp (F w) by grind
  apply Differentiable.apply_eq_apply_of_bounded
  · apply (differentiable_exp.comp (fun x ↦ (hF_diff x (mem_univ x)).differentiableAt))
  rw [isBounded_iff_forall_norm_le] at *
  obtain ⟨M, hM⟩ := h_bound
  use Real.exp M
  simp_all only [mem_range, norm_eq_abs, forall_exists_index, forall_apply_eq_imp_iff,
    norm_exp, exp_le_exp]
  rw [← hF_re] at hM
  grind
