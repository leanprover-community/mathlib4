/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# EmbeddingOfLocal
-/

@[expose] public section

open Topology Filter Bornology Set
open scoped Pointwise

section FinalVersion

variable {𝕜₁ 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  [AddCommGroup E] [AddCommGroup F] [Module 𝕜₁ E] [Module 𝕜₂ F] {σ : 𝕜₁ →+* 𝕜₂} {f : E →ₛₗ[σ] F}

variable (𝕜₁) in
lemma foo (t₁ t₂ : TopologicalSpace E) [@IsTopologicalAddGroup E t₁ _]
    [@IsTopologicalAddGroup E t₂ _] [@ContinuousSMul 𝕜₁ E _ _ t₁] [@ContinuousSMul 𝕜₁ E _ _ t₂]
    {V : Set E} (V_mem : V ∈ @nhds E t₁ 0) (H : @nhds E t₁ 0 ⊓ 𝓟 V = @nhds E t₂ 0 ⊓ 𝓟 V) :
    t₁ = t₂ := by
  classical
  -- For `i = 1, 2`, denote by `𝓕ᵢ` the filter of neighborhoods of `0` for the topology `tᵢ`.
  set 𝓕₁ := @nhds E t₁ 0
  set 𝓕₂ := @nhds E t₂ 0
  -- Note that, because `V ∈ 𝓕₁`, `H` may be rewritten as `𝓕₁ = 𝓕₂ ⊓ 𝓟 V`.
  replace H : 𝓕₁ = 𝓕₂ ⊓ 𝓟 V := by simpa [← H]
  -- Because both `t₁` and `t₂` are additive group topologies, we have to show `𝓕₁ = 𝓕₂`.
  suffices 𝓕₁ = 𝓕₂ by rwa [IsTopologicalAddGroup.ext_iff] <;> infer_instance
  -- If we can show that `V ∈ 𝓕₂`, we get `𝓕₁ = 𝓕₂ ⊓ 𝓟 V = 𝓕₂`.
  suffices V ∈ 𝓕₂ by simpa [H]
  -- Hence, let us show that `V ∈ 𝓕₂`. Fix a scalar `c` with `0 < ‖c‖ < 1`.
  obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt_one 𝕜₁
  have c_ne : c ≠ 0 := fun h ↦ by simp [h] at hc₀
  -- We know that `c • V ∈ 𝓕₁ = 𝓕₂ ⊓ 𝓟 V`.
  have cV_mem : c • V ∈ 𝓕₂ ⊓ 𝓟 V := by
    rw [← H]
    let := t₁
    simpa [𝓕₁, set_smul_mem_nhds_zero_iff c_ne]
  -- Furthermore, we know that `𝓕₂` has a basis of balanced sets
  have basis_𝓕₂ : HasBasis 𝓕₂ (fun (s : Set E) ↦ s ∈ 𝓕₂ ∧ Balanced 𝕜₁ s) id :=
    let := t₂; nhds_basis_balanced 𝕜₁ E
  -- Hence, we get a balanced set `W ∈ 𝓕₂` such that `W ∩ V ⊆ c • V`.
  obtain ⟨W, ⟨W_mem_𝓕₂, W_bal⟩, hW⟩ := basis_𝓕₂.inf_principal V |>.mem_iff.mp cV_mem
  -- We claim that `W ⊆ V`. This will conclude the proof, since `W ∈ 𝓕₂`.
  suffices W ⊆ V from mem_of_superset W_mem_𝓕₂ this
  -- By contradiction, assume that we have a point `w ∈ W \ V`
  intro w w_in_W
  by_contra! w_notin_V
  -- Now, because `V` is absorbent, there exists a natural `k` such that `c ^ k • w ∈ V`.
  have exists_scale : ∃ k : ℕ, c ^ k • w ∈ V := by
    have V_abs : Absorbent 𝕜₁ V := let := t₁; absorbent_nhds_zero V_mem
    have : Tendsto (fun k : ℕ ↦ c ^ k) atTop (𝓝[≠] 0) := by
      simp [tendsto_nhdsWithin_iff, c_ne, tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, hc₁]
    exact this.eventually (V_abs.eventually_nhdsNE_zero w) |>.exists
  -- Denote by `k₀` the *smallest* such `k`.
  set k₀ := Nat.find exists_scale
  have k₀_spec : c ^ k₀ • w ∈ V := Nat.find_spec exists_scale
  -- Note that `1 ≤ k₀` since `w ∉ V`
  have k₀_pos : 0 < k₀ := pos_iff_ne_zero.mpr fun h ↦ by simp [h, w_notin_V] at k₀_spec
  -- By definition, `c ^ k₀ • w ∈ V`, and becaus `W` is balanced `c ^ k₀ • w ∈ W`.
  -- Thus, `c ^ k₀ • w ∈ V ∩ W ⊆ c • V`.
  have : c ^ k₀ • w ∈ c • V :=
    hW ⟨W_bal.smul_mem (by simpa using pow_le_one₀ hc₀.le hc₁.le) w_in_W, k₀_spec⟩
  -- But then, we have `c ^ (k₀ - 1) • w ∈ V`.
  have : c ^ (k₀ - 1) • w ∈ V := by
    rwa [pow_sub₀ c c_ne k₀_pos, pow_one, mul_comm, mul_smul, ← mem_smul_set_iff_inv_smul_mem₀ c_ne]
  -- This contradicts the minimality of `k₀`.
  exact Nat.find_min exists_scale (tsub_lt_self k₀_pos one_pos) this

variable (𝕜₁) in
lemma bar (t₁ t₂ : TopologicalSpace E) [@IsTopologicalAddGroup E t₁ _]
    [@IsTopologicalAddGroup E t₂ _] [@ContinuousSMul 𝕜₁ E _ _ t₁] [@ContinuousSMul 𝕜₁ E _ _ t₂]
    {V : Set E} (V_mem : V ∈ @nhds E t₁ 0)
    (H : t₁.induced ((↑) : V → E) = t₂.induced ((↑) : V → E)) :
    t₁ = t₂ := by
  apply foo 𝕜₁ t₁ t₂ V_mem
  set o : V := ⟨0, letI := t₁; mem_of_mem_nhds V_mem⟩
  simp_rw [← map_comap_setCoe_val, show 0 = (o : E) from rfl, ← nhds_induced]
  congr

variable [TopologicalSpace E] [TopologicalSpace F]
  [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜₁ E] [ContinuousSMul 𝕜₂ F] [RingHomIsometric σ]

lemma LinearMap.isInducing_of_restrict_nhds_zero {V : Set E}
    (V_mem : V ∈ 𝓝 0) (H : IsInducing (Set.restrict V f)) : IsInducing f := by
  rw [isInducing_iff]
  have := topologicalAddGroup_induced f
  have := continuousSMul_inducedₛₗ f σ.isometry.continuous
  apply bar 𝕜₁ _ (.induced f _) V_mem
  rw [induced_compose, ← restrict_eq, ← H.eq_induced, ← IsInducing.subtypeVal.eq_induced]

lemma LinearMap.isEmbedding_of_restrict_nhds_zero {V : Set E}
    (V_mem : V ∈ 𝓝 0) (H : IsEmbedding (Set.restrict V f)) : IsEmbedding f := by
  sorry

end FinalVersion

private lemma Filter.comap_inf_congr_aux {α β : Type*} {m₁ m₂ : α → β} {f : Filter α} {g : Filter β}
    (H : m₁ =ᶠ[f] m₂) : comap m₁ g ⊓ f ≤ comap m₂ g ⊓ f := by
  refine le_inf ?_ inf_le_right
  rw [← map_le_iff_le_comap, ← Filter.map_congr (H.filter_mono inf_le_right), map_le_iff_le_comap]
  exact inf_le_left

lemma Filter.comap_inf_congr {α β : Type*} {m₁ m₂ : α → β} {f : Filter α} {g : Filter β}
    (H : m₁ =ᶠ[f] m₂) : comap m₁ g ⊓ f = comap m₂ g ⊓ f :=
  le_antisymm (comap_inf_congr_aux H) (comap_inf_congr_aux H.symm)

variable {𝕜₁ 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  [AddCommGroup E] [AddCommGroup F] [Module 𝕜₁ E] [Module 𝕜₂ F] {σ : 𝕜₁ →+* 𝕜₂} {f : E →ₛₗ[σ] F}

/-- Let `V` be an absorbent set in a vector space, and fix a "scale" `c : 𝕜` with `0 < ‖c‖ < 1`.
Then, we can build a retraction `p : E → V` such that:
* if `x` is outside of `V`, then `p x` is outside of `c • V`.
* for *any* topology on `E` compatible with the vector space structure, `p` is continuous at zero
  (crucially, this is the case even if `V` is not a neighborhood of zero).
-/
private lemma exists_good_retraction {V : Set E} (V_abs : Absorbent 𝕜₁ V)
    {c : 𝕜₁} (c_ne : c ≠ 0) (hc₁ : ‖c‖ < 1) :
    ∃ p : E → E, (∀ x, p x ∈ V) ∧ (MapsTo p Vᶜ (c • V)ᶜ) ∧
      ∀ (_t : TopologicalSpace E) [IsTopologicalAddGroup E] [ContinuousSMul 𝕜₁ E],
        Tendsto p (𝓝 0) (𝓝 0) := by
  classical
  have cover : ∀ x : E, ∃ k : ℕ, c ^ k • x ∈ V := by
    have : Tendsto (fun k : ℕ ↦ c ^ k) atTop (𝓝[≠] 0) := by
      simp [tendsto_nhdsWithin_iff, c_ne, tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, hc₁]
    exact fun x ↦ this.eventually (V_abs.eventually_nhdsNE_zero x) |>.exists
  -- For each `x`, denote `k x` the smallest natural number such that `c ^ k • x ∈ V`.
  -- This is well defined because `c ^ k → 0` as `k → +∞`, and `V` is absorbent.
  set k : E → ℕ := fun x ↦ Nat.find (cover x)
  -- We claim that `p : x ↦ c ^ (k x) • x` does the job
  set p : E → E := fun x ↦ c ^ (k x) • x
  -- By construction, it takes values in `V` (and is the identity on `V`, though we don't care)
  have p_mem : ∀ x, p x ∈ V := fun x ↦ Nat.find_spec (cover x)
  -- Furthermore, if `x` is not in `V`, then `k x > 0`. Hence, if `p x = c ^ (k x) • x ∈ c • V`,
  -- then `c ^ (k x - 1) • x ∈ V`, which contradicts minimality of `k x`.
  -- This shows that `p` maps `Vᶜ` to `(c • V)ᶜ`.
  have p_mapsto : MapsTo p Vᶜ (c • V)ᶜ := by
    intro x hx₁ hx₂
    have : c ^ (k x - 1) • x ∈ V := by
      rwa [pow_sub₀ c c_ne (by simpa [k]), pow_one, mul_comm, mul_smul,
        ← mem_smul_set_iff_inv_smul_mem₀ c_ne]
    exact Nat.find_min (cover x) (by simpa [k]) this
  use p, p_mem, p_mapsto
  -- Finally, if we fix an arbitrary vector space topology on `E`, then it has a basis of balanced
  -- neighborhoods. Since `p x = c ^ (k x) • x` and `‖c ^ (k x)‖ = ‖c‖ ^ (k x) ≤ 1`,
  -- this shows that `p x → 0` as `x → 0`.
  intro t _ _
  refine IsBoundedUnder.smul_tendsto_zero ?_ tendsto_id
  exact isBoundedUnder_of ⟨1, fun x ↦ by simpa using pow_le_one₀ (norm_nonneg _) hc₁.le⟩

variable (𝕜₁) in
lemma foo_old (t₁ t₂ : TopologicalSpace E) [@IsTopologicalAddGroup E t₁ _]
    [@IsTopologicalAddGroup E t₂ _] [@ContinuousSMul 𝕜₁ E _ _ t₁] [@ContinuousSMul 𝕜₁ E _ _ t₂]
    {V : Set E} (V_mem : V ∈ @nhds E t₁ 0) (H : @nhds E t₁ 0 ⊓ 𝓟 V = @nhds E t₂ 0 ⊓ 𝓟 V) :
    t₁ = t₂ := by
  -- For `i = 1, 2`, denote by `𝓕ᵢ` the filter of neighborhoods of `0` for the topology `tᵢ`.
  set 𝓕₁ := @nhds E t₁ 0
  set 𝓕₂ := @nhds E t₂ 0
  -- Because both `t₁` and `t₂` are additive group topologies, we have to show `𝓕₁ = 𝓕₂`.
  suffices 𝓕₁ = 𝓕₂ by rwa [IsTopologicalAddGroup.ext_iff] <;> infer_instance
  -- If we can show that `V ∈ 𝓕₂`, we get `𝓕₁ = 𝓕₁ ⊓ 𝓟 V = 𝓕₂ ⊓ 𝓟 V = 𝓕₂`.
  suffices V ∈ 𝓕₂ from
    calc 𝓕₁
      _ = 𝓕₁ ⊓ 𝓟 V := by simpa
      _ = 𝓕₂ ⊓ 𝓟 V := H
      _ = 𝓕₂ := by simpa
  -- Hence, let us show that `V ∈ 𝓕₂`. Equivalently, we have to show that the filter
  -- `𝓖 := 𝓕₂ ⊓ 𝓟 Vᶜ` is trivial (that is, you cannot go to `0` for `t₂` without entering `V`).
  rw [← compl_compl V, ← inf_principal_eq_bot]
  set 𝓖 := 𝓕₂ ⊓ 𝓟 Vᶜ
  -- Fix a scalar `c` with `0 < ‖c‖ < 1`. Note that `V` is absorbent, so we get a good retraction
  -- `p : E → V` as in the lemma above.
  obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt_one 𝕜₁
  have c_ne : c ≠ 0 := fun h ↦ by simp [h] at hc₀
  have V_abs : Absorbent 𝕜₁ V := letI := t₁; absorbent_nhds_zero V_mem
  obtain ⟨p, p_mem_V, p_mapsto, p_tendsto⟩ := exists_good_retraction V_abs c_ne hc₁
  -- We will show that `map p 𝓖 ≤ ⊥`.
  suffices map p 𝓖 ≤ ⊥ by simpa
  -- On the one hand, the inclusion `p '' Vᶜ ⊆ (c • V)ᶜ` guarantees that `map p 𝓖 ≤ 𝓟 (c • V)ᶜ`.
  have fact₁ : map p 𝓖 ≤ 𝓟 (c • V)ᶜ := (map_mono inf_le_right).trans p_mapsto.tendsto
  -- On the other hand, because `p` is `t₂`-continuous at zero, we have `map p 𝓖 ≤ 𝓕₂`,
  -- and because `p` takes values in `V`, `map p 𝓖 ≤ 𝓟 V`.
  -- Hence, `map p 𝓖 ≤ 𝓕₂ ⊓ 𝓟 V = 𝓕₁ ⊓ 𝓟 V ≤ 𝓕₁ ≤ 𝓟 (c • V)`.
  have fact₂ : map p 𝓖 ≤ 𝓟 (c • V) :=
    calc map p 𝓖
      _ ≤ map p 𝓕₂ := map_mono inf_le_left
      _ ≤ 𝓕₂ ⊓ 𝓟 (range p) := le_inf (p_tendsto t₂) (by simp)
      _ ≤ 𝓕₂ ⊓ 𝓟 V := by gcongr; simpa [range_subset_iff]
      _ = 𝓕₁ ⊓ 𝓟 V := by rw [H]
      _ ≤ 𝓕₁ := inf_le_left
      _ ≤ 𝓟 (c • V) := by letI := t₁; simpa [𝓕₁, set_smul_mem_nhds_zero_iff c_ne]
  -- Thus `𝓖` has to be trivial, and we are done.
  simpa using le_inf fact₁ fact₂

variable (𝕜₁) in
lemma bar_old (t₁ t₂ : TopologicalSpace E) [@IsTopologicalAddGroup E t₁ _]
    [@IsTopologicalAddGroup E t₂ _] [@ContinuousSMul 𝕜₁ E _ _ t₁] [@ContinuousSMul 𝕜₁ E _ _ t₂]
    {V : Set E} (V_mem : V ∈ @nhds E t₁ 0)
    (H : t₁.induced ((↑) : V → E) = t₂.induced ((↑) : V → E)) :
    t₁ = t₂ := by
  apply foo 𝕜₁ t₁ t₂ V_mem
  set o : V := ⟨0, letI := t₁; mem_of_mem_nhds V_mem⟩
  simp_rw [← map_comap_setCoe_val, show 0 = (o : E) from rfl, ← nhds_induced]
  congr
