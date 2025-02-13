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

open SeminormedAddGroup NormedAddCommGroup UniformAddGroup Filter

variable {F : Type*} [NormedField F]

instance NormedField.instCompletableTopField : CompletableTopField F where
  t0 := (inferInstanceAs <| T0Space _).t0
  nice f hc hn := by
    have : UniformAddGroup F := sorry
    obtain ⟨δ, δ_pos, hδ⟩ := (disjoint_nhds_zero ..).mp <| disjoint_iff.mpr hn
    have f_bdd : f.IsBoundedUnder (· ≤ ·) (‖·⁻¹‖) :=
      ⟨δ⁻¹, hδ.mono fun y hy ↦ le_inv_of_le_inv₀ δ_pos (by simpa using hy)⟩
    have h₀ : ∀ᶠ y in f, y ≠ 0 := hδ.mono fun y hy ↦ by simpa using δ_pos.trans_le hy
    have : ∀ᶠ p in f ×ˢ f, p.1⁻¹ - p.2⁻¹ = p.1⁻¹ * (p.2 - p.1) * p.2⁻¹ :=
      h₀.prod_mk h₀ |>.mono fun ⟨x, y⟩ ⟨hx, hy⟩ ↦ by simp [mul_sub, sub_mul, hx, hy]
    rw [cauchy_iff_tendsto_swapped] at hc
    rw [cauchy_map_iff_tendsto, tendsto_congr' this]
    refine ⟨hc.1, .zero_mul_isBoundedUnder_le ?_ <| tendsto_snd.isBoundedUnder_comp f_bdd⟩
    exact isBoundedUnder_le_mul_tendsto_zero (tendsto_fst.isBoundedUnder_comp f_bdd) hc.2
    stop
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
