module

public import Mathlib

open Set Metric
open scoped Pointwise

public section

@[to_additive (attr := simp)]
theorem Set.smul_set_eq_univ {G α : Type*} [Group G] [MulAction G α] {g : G} {s : Set α} :
    g • s = univ ↔ s = univ := by
  rw [smul_eq_iff_eq_inv_smul, smul_set_univ]

namespace Complex

theorem exists_mapsTo_unitBall_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : SimplyConnectedSpace U) (hU : U ≠ univ) {x : ℂ} (hx : x ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ MapsTo f U (ball 0 1) ∧ deriv f x ≠ 0 := by
  wlog hU₀ : 0 ∉ U
  · rw [ne_univ_iff_exists_notMem] at hU
    rcases hU with ⟨a, ha⟩
    specialize this (hUo.vadd (-a)) ?_ (by simp [hU]) (x := -a + x)
      (by simpa [mem_vadd_set_iff_neg_vadd_mem]) (by simpa [mem_vadd_set_iff_neg_vadd_mem])
    · sorry
    · rcases this with ⟨f, hfd, hf₁, hdf⟩
      refine ⟨f ∘ (-a + ·), hfd.comp (by fun_prop) (mapsTo_image _ _), hf₁.comp (mapsTo_image _ _),
        ?_⟩
      simpa only [Function.comp_def, deriv_comp_const_add]
  have := hUo.locPathConnectedSpace
  have hx₀ : x ≠ 0 := ne_of_mem_of_not_mem hx hU₀
  lift x to U using hx
  rcases isCoveringMapOn_exp.existsUnique_continuousMap_lifts (.restrict U (.id ℂ)) (exp_log hx₀)
    (fun x ↦ ne_of_mem_of_not_mem x.2 hU₀) with ⟨f₀, ⟨hf, hf'⟩, -⟩




end Complex
