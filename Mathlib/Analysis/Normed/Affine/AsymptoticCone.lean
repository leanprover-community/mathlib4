/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.AsymptoticCone

/-!
# Asymptotic cones in normed spaces

In this file, we prove that the asymptotic cone of a set is non-trivial if and only if the set is
unbounded.
-/

open AffineSpace Bornology Filter Topology

variable
  {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

theorem AffineSpace.asymptoticNhds_le_cobounded {v : V} (hv : v ≠ 0) :
    asymptoticNhds ℝ P v ≤ cobounded P := by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [← tendsto_id', ← Metric.tendsto_dist_right_atTop_iff p,
    asymptoticNhds_eq_smul_vadd v p, vadd_pure, ← map₂_smul, ← map_prod_eq_map₂, map_map,
    tendsto_map'_iff]
  change Tendsto (fun x : ℝ × V => dist (x.1 • x.2 +ᵥ p) p) (atTop ×ˢ 𝓝 v) atTop
  simp_rw [dist_vadd_left, norm_smul]
  exact Tendsto.atTop_mul_pos (norm_pos_iff.mpr hv)
    (tendsto_norm_atTop_atTop.comp tendsto_id.fst)
    tendsto_snd.norm

theorem asymptoticCone_subset_singleton_of_bounded {s : Set P} (hs : IsBounded s) :
    asymptoticCone ℝ s ⊆ {0} := by
  intro v h
  by_contra! hv
  exact h (asymptoticNhds_le_cobounded hv hs)

variable [FiniteDimensional ℝ V]

theorem AffineSpace.cobounded_eq_iSup_sphere_asymptoticNhds :
    cobounded P = ⨆ v ∈ Metric.sphere 0 1, asymptoticNhds ℝ P v := by
  refine le_antisymm ?_ <| iSup₂_le fun _ h => asymptoticNhds_le_cobounded <|
    Metric.ne_of_mem_sphere h one_ne_zero
  intro s hs
  have ⟨p⟩ : Nonempty P := inferInstance
  simp_rw [mem_iSup, asymptoticNhds_eq_smul_vadd _ p, vadd_pure] at hs
  choose! t ht u hu smul_subset_s using hs
  have ⟨cover, h₁, h₂⟩ := (isCompact_sphere 0 1).elim_nhds_subcover u hu
  rw [← Metric.comap_dist_left_atTop p]
  refine ⟨Set.Ioi 0 ∩ ⋂ x ∈ cover, t x, inter_mem (Ioi_mem_atTop 0)
    (cover.iInter_mem_sets.mpr fun x hx => ht x (h₁ x hx)), fun x hx => ?_⟩
  rw [Set.mem_preimage, dist_eq_norm_vsub'] at hx
  let x' := ‖x -ᵥ p‖⁻¹ • (x -ᵥ p)
  have x'_mem : x' ∈ Metric.sphere 0 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx.1.ne']
  have ⟨y, y_mem, hy⟩ := Set.mem_iUnion₂.mp (h₂ x'_mem)
  rw [← vsub_vadd x p, ← show ‖x -ᵥ p‖ • x' = x -ᵥ p from smul_inv_smul₀ hx.1.ne' (x -ᵥ p)]
  exact smul_subset_s y (h₁ y y_mem) <| Set.smul_mem_smul (Set.biInter_subset_of_mem y_mem hx.2) hy

/-- In a finite dimensional normed affine space over `ℝ`, a set is bounded if and only if its
asymptotic cone is trivial. -/
theorem isBounded_iff_asymptoticCone_subset_singleton {s : Set P} :
    IsBounded s ↔ asymptoticCone ℝ s ⊆ {0} := by
  refine ⟨asymptoticCone_subset_singleton_of_bounded, fun h => ?_⟩
  simp_rw [isBounded_def, cobounded_eq_iSup_sphere_asymptoticNhds, mem_iSup]
  intro v hv
  by_contra h'
  exact Metric.ne_of_mem_sphere hv one_ne_zero (h h')

/-- In a finite dimensional normed affine space over `ℝ`, a set is unbounded if and only if its
asymptotic cone contains a nonzero vector. -/
theorem not_bounded_iff_exists_ne_zero_mem_asymptoticCone {s : Set P} :
    ¬ IsBounded s ↔ ∃ v ≠ 0, v ∈ asymptoticCone ℝ s := by
  rw [isBounded_iff_asymptoticCone_subset_singleton, Set.subset_singleton_iff, not_forall]
  tauto
