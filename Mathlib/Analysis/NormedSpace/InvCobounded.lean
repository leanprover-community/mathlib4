import Mathlib.Analysis.Normed.Field.Basic

namespace Filter

open Bornology Topology

variable (𝕜 : Type*) [NormedField 𝕜]

theorem tendsto_inv₀_cobounded : Tendsto Inv.inv (cobounded 𝕜) (𝓝 0) := by
  rw [←comap_norm_atTop, @NormedAddCommGroup.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [(atTop_basis.comap (‖·‖)).mem_of_mem (i := (ε / 2)⁻¹) (by trivial)] with x hx
  simp only [Set.mem_preimage, Set.mem_Ici] at hx
  rw [norm_inv, inv_lt (lt_of_lt_of_le (by positivity) hx) hε]
  exact ((inv_lt_inv hε (half_pos hε)).mpr <| half_lt_self hε).trans_le hx

lemma tendsto_inv₀_cobounded' : Tendsto Inv.inv (cobounded 𝕜) (𝓝[≠] 0) := by
  rw [nhdsWithin, tendsto_inf]
  refine And.intro (tendsto_inv₀_cobounded 𝕜) <| calc
    map Inv.inv (cobounded 𝕜) ≤ map Inv.inv cofinite := map_mono (le_cofinite 𝕜)
    _                         ≤ cofinite := inv_injective.tendsto_cofinite
    _                         ≤ 𝓟 {0}ᶜ := by simp

lemma tendsto_inv₀_nhdsWithin_ne_zero : Tendsto Inv.inv (𝓝[≠] 0) (cobounded 𝕜) := by
  rw [←comap_norm_atTop, tendsto_comap_iff]
  rw [(nhdsWithin_hasBasis Metric.nhds_basis_ball _).tendsto_iff (atTop_basis' 1)]
  refine fun x hx ↦ ⟨x⁻¹, by positivity, fun y ⟨hy₁, hy₂⟩ ↦ ?_⟩
  simp only [Set.mem_inter_iff, Metric.mem_ball, dist_zero_right, Set.mem_compl_iff,
    Set.mem_singleton_iff, Function.comp_apply, norm_inv, Set.mem_Ici] at *
  exact le_inv (by positivity) (norm_pos_iff.mpr hy₂) |>.mpr hy₁.le

lemma map_inv₀_nhdsWithin_ne_zero : map Inv.inv (𝓝[≠] 0) = cobounded 𝕜 :=
  le_antisymm (tendsto_inv₀_nhdsWithin_ne_zero 𝕜) <| le_map_of_right_inverse
    (by simpa using EventuallyEq.rfl) (tendsto_inv₀_cobounded' 𝕜)

lemma map_inv₀_cobounded : map Inv.inv (cobounded 𝕜) = 𝓝[≠] 0 :=
  le_antisymm (tendsto_inv₀_cobounded' 𝕜) <| le_map_of_right_inverse
    (by simpa using EventuallyEq.rfl) (tendsto_inv₀_nhdsWithin_ne_zero 𝕜)

end Filter
