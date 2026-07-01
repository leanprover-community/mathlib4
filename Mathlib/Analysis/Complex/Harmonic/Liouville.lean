/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Liouville's Theorem for Harmonic Functions on the Complex Plane

A bounded harmonic function on the complex plane is constant.
-/

public section

open Bornology Complex Real Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Auxiliary version of Liouville's theorem, for real-valued harmonic functions on the complex
-- plane.
private theorem InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant_aux (f : ℂ → ℝ)
    (h_harm : HarmonicOnNhd f univ) (h_bound : Bornology.IsBounded (range f)) :
    ∀ z w, f z = f w := by
  -- By assumption, there exists a holomorphic function $f$ such that $\Re(f) = u$.
  obtain ⟨F, hF_diff, hF_re⟩ := h_harm.exists_analyticOnNhd_univ_re_eq
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

/--
**Liouville's theorem for harmonic functions on the complex plane** A bounded harmonic function on
the complex plane is constant.
-/
theorem InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant (f : ℂ → E)
    (h_harm : HarmonicOnNhd f univ) (h_bound : IsBounded (range f)) :
    ∀ z w, f z = f w := by
  intro z w
  obtain ⟨ℓ, h₁ℓ, h₂ℓ⟩ := exists_dual_vector'' ℝ (f z - f w)
  rw [map_sub, RCLike.ofReal_real_eq_id, id_eq] at h₂ℓ
  have η₁ : Bornology.IsBounded (range (ℓ ∘ f)) := by
    simpa [range_comp] using IsBounded.image ℓ h_bound
  rw [← sub_eq_zero, ← norm_eq_zero, ← h₂ℓ]
  grind [bounded_harmonic_on_complex_plane_is_constant_aux (ℓ ∘ f) (h_harm.comp_CLM ℓ) η₁]
