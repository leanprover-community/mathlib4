/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Topology.Algebra.UniformField
import Mathlib.Analysis.Normed.Field.Basic

/-!
# A normed field is a completable topological field
-/

open SeminormedAddGroup NormedAddCommGroup Filter

variable {F : Type*} [NormedField F]

instance NormedField.instCompletableTopField : CompletableTopField F where
  t0 := (inferInstanceAs <| T0Space _).t0
  nice f hc hn := by
    obtain ⟨δ, δ_pos, hδ⟩ := (disjoint_nhds_zero ..).mp <| disjoint_iff.mpr hn
    obtain ⟨V, V_in, hδV⟩ := eventually_iff_exists_mem.mp hδ
    have hδV' {y} (hy : y⁻¹ ∈ V) : ‖y‖ ≤ δ⁻¹ := le_inv_of_le_inv₀ δ_pos (by simpa using hδV _ hy)
    have h₀ {y} (hy : y⁻¹ ∈ V) : y ≠ 0 := by simpa using δ_pos.trans_le (hδV _ hy)
    rw [uniformity_basis_dist.cauchy_iff] at hc ⊢
    obtain ⟨hne, hsmall⟩ := hc
    refine ⟨hne.map _, fun ε ε_pos ↦ ?_⟩
    obtain ⟨U, U_in, hU⟩ := hsmall (δ * ε * δ) (by positivity)
    use (·⁻¹) ⁻¹' (U ∩ V), mem_map.mpr (by simp [U_in, V_in]), fun x hx y hy ↦ ?_
    calc
      ‖x - y‖ = ‖x‖ * ‖y⁻¹ - x⁻¹‖ * ‖y‖ := by have := h₀ hx.2; have := h₀ hy.2; field_simp; ring
      _       ≤ δ⁻¹ * ‖y⁻¹ - x⁻¹‖ * δ⁻¹ := by gcongr; exacts [hδV' hx.2, hδV' hy.2]
      _       < δ⁻¹ * (δ * ε * δ) * δ⁻¹ := by gcongr; rw [norm_sub_rev]; exact hU _ hx.1 _ hy.1
      _       = ε := by field_simp
