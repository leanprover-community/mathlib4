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

/-!
## Third version
-/

/-- Let `V` be an absorbent set in a vector space, and fix a "scale" `c : 𝕜` with `0 < ‖c‖ < 1`.
Then, we can build a retraction `p : E → V` such that:
* if `x` is outside of `V`, then `p x` is outside of `c • V`.
* for *any* topology on `E` compatible with the vector space structure, `p` is continuous at zero.
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
lemma foo (t₁ t₂ : TopologicalSpace E) [@IsTopologicalAddGroup E t₁ _]
    [@IsTopologicalAddGroup E t₂ _] [@ContinuousSMul 𝕜₁ E _ _ t₁] [@ContinuousSMul 𝕜₁ E _ _ t₂]
    {V : Set E} (V_mem : V ∈ @nhds E t₁ 0) (H : @nhds E t₁ 0 ⊓ 𝓟 V = @nhds E t₂ 0 ⊓ 𝓟 V) :
    t₁ = t₂ := by
  -- For `i = 1, 2`, denote by `𝓕ᵢ` the filter of neighborhoods of `0` for the topology `tᵢ`.
  set 𝓕₁ := @nhds E t₁ 0
  set 𝓕₂ := @nhds E t₂ 0
  -- Because both `t₁` and `t₂` are additive group topologies, we have to show `𝓕₁ = 𝓕₂`.
  suffices 𝓕₁ = 𝓕₂ by rwa [IsTopologicalAddGroup.ext_iff] <;> infer_instance
  -- If we can show that `V ∈ 𝓕₂`, we get `𝓕₁ = 𝓕₁ ⊓ 𝓟 V = 𝓕₂ ⊓ 𝓟 V = 𝓕₂`.
  suffices 𝓕₂ ≤ 𝓟 V from
    calc 𝓕₁
      _ = 𝓕₁ ⊓ 𝓟 V := by simpa
      _ = 𝓕₂ ⊓ 𝓟 V := H
      _ = 𝓕₂ := by simpa
  -- Hence, let us show that `V ∈ 𝓕₂`. Fix a scalar `c` with `0 < ‖c‖ < 1`.
  -- Note that `V` is absorbent, so we get a good retraction `p : E → V` as in the lemma above.
  obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt_one 𝕜₁
  have c_ne : c ≠ 0 := fun h ↦ by simp [h] at hc₀
  have V_abs : Absorbent 𝕜₁ V := letI := t₁; absorbent_nhds_zero V_mem
  have cV_mem : c • V ∈ 𝓕₁ := letI := t₁; set_smul_mem_nhds_zero_iff c_ne |>.mpr V_mem
  obtain ⟨p, p_mem_V, p_mapsto, p_tendsto⟩ := exists_good_retraction V_abs c_ne hc₁
  replace p_mem_V : p ⁻¹' V = univ := by simpa [range_subset_iff]
  -- To finish the proof, we compute :
  calc 𝓕₂
    _ ≤ comap p 𝓕₂ := tendsto_iff_comap.mp <| p_tendsto t₂ -- because `p` is `t₂`-continuous at 0;
    _ = comap p (𝓕₂ ⊓ 𝓟 V) := by simp [p_mem_V] -- because `p` takes values in `V`;
    _ = comap p (𝓕₁ ⊓ 𝓟 V) := by rw [H] -- by hypothesis;
    _ = comap p 𝓕₁ := by simp [p_mem_V] -- because `p` takes values in `V`;
    _ ≤ 𝓟 V := by -- because the inequality `p '' Vᶜ ⊆ (c • V)ᶜ` implies `p ⁻¹' (c • V) ⊆ V`.
      grw [le_principal_iff, mem_comap_iff_compl, p_mapsto.image_subset, compl_compl]
      exact cV_mem

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

/-!
## Second version
-/

variable (𝕜₁) in
omit [IsTopologicalAddGroup E] in
private lemma exists_good_rescaling {V : Set E} (V_mem : V ∈ 𝓝 0) :
    ∃ d : E → 𝕜₁, (∀ x, ‖d x‖ ≤ 1) ∧ (∀ x, d x • x ∈ V) ∧
      (𝓝 (0 : E) = comap (fun x ↦ d x • x) (𝓝 0)) := by
  classical
  obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt_one 𝕜₁
  have c_ne : c ≠ 0 := fun h ↦ by simp [h] at hc₀
  have cover : ∀ x : E, ∃ k : ℕ, c ^ k • x ∈ V := by
    intro x
    have : Tendsto (fun k : ℕ ↦ c ^ k • x) atTop (𝓝 0) :=
      zero_smul 𝕜₁ x ▸ .smul_const (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc₁) _
    exact this.eventually V_mem |>.exists
  set k : E → ℕ := fun x ↦ Nat.find (cover x)
  set d : E → 𝕜₁ := fun x ↦ c ^ (k x)
  set p : E → E := fun x ↦ d x • x
  have norm_d : ∀ x, ‖d x‖ ≤ 1 := fun x ↦ by simpa [d] using pow_le_one₀ hc₀.le hc₁.le
  have p_mem : ∀ x, p x ∈ V := fun x ↦ Nat.find_spec (cover x)
  use d, norm_d, p_mem
  have k_eqOn_V : ∀ x ∈ V, k x = 0 := fun x ↦ by simp [k]
  have p_eqOn_V : ∀ x ∈ V, p x = x := fun x hx ↦ by simp [p, d, k_eqOn_V x hx]
  have p_mapsto : MapsTo p Vᶜ (c • V)ᶜ := by
    intro x hx₁ hx₂
    have : c ^ (k x - 1) • x ∈ V := by
      rwa [pow_sub₀ c c_ne (by simpa [k]), pow_one, mul_comm, mul_smul,
        ← mem_smul_set_iff_inv_smul_mem₀ c_ne]
    exact Nat.find_min (cover x) (by simpa [k]) this
  have V_mem' : V ∈ comap p (𝓝 0) := by
    grw [mem_comap_iff_compl, ← le_principal_iff, p_mapsto.image_subset, compl_compl]
    simpa [set_smul_mem_nhds_zero_iff c_ne]
  calc 𝓝 0
    _ = comap id (𝓝 0) ⊓ 𝓟 V := by simp [comap_id, V_mem]
    _ = comap p (𝓝 0) ⊓ 𝓟 V := .symm <| comap_inf_congr (by simpa)
    _ = comap p (𝓝 0) := by simp [V_mem']

lemma LinearMap.isInducing_of_restrict_nhds_zero_new {V : Set E}
    (V_mem : V ∈ 𝓝 0) (H : IsInducing (Set.restrict V f)) : IsInducing f := by
  replace H : comap f (𝓝 0) ⊓ 𝓟 V = 𝓝 0 := by
    set o : V := ⟨0, mem_of_mem_nhds V_mem⟩
    set f' : V → F := Set.restrict V f
    calc comap f (𝓝 0) ⊓ 𝓟 V
      _ = comap f (𝓝 (f' o)) ⊓ 𝓟 V := by simp [o, f']
      _ = map ((↑) : V → E) (comap f' (𝓝 (f' o))) := by
            simp [f', restrict_eq, ← comap_comap, map_comap_setCoe_val]
      _ = map ((↑) : V → E) (𝓝 o) := by rw [H.nhds_eq_comap]
      _ = 𝓝 0 := by
            rwa [IsInducing.subtypeVal.map_nhds_eq, Subtype.range_val, nhdsWithin_eq_nhds]
  suffices comap f (𝓝 0) ≤ 𝓝 0 from
    IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr (le_antisymm (by simp [← H]) this)
  obtain ⟨d, norm_d, p_mem, hp⟩ := exists_good_rescaling 𝕜₁ V_mem
  set p : E → E := fun x ↦ d x • x
  change ∀ x, p x ∈ V at p_mem
  have : comap f (𝓝 0) ≤ comap p (comap f (𝓝 0)) := by
    have : f ∘ p = (σ ∘ d) • f := by ext; simp [p]
    rw [comap_comap, ← tendsto_iff_comap, this]
    refine IsBoundedUnder.smul_tendsto_zero ?_ tendsto_comap
    exact isBoundedUnder_of ⟨1, fun x ↦ by simpa using norm_d x⟩
  calc comap f (𝓝 0)
    _ ≤ comap p (comap f (𝓝 0)) := this
    _ = comap p (comap f (𝓝 0) ⊓ 𝓟 (Set.range p)) := by rw [comap_inf_principal_range]
    _ ≤ comap p (comap f (𝓝 0) ⊓ 𝓟 V) := by gcongr; simpa [range_subset_iff]
    _ = comap p (𝓝 0) := by rw [H]
    _ = 𝓝 0 := by rw [← hp]

/-!
## First version
-/

lemma LinearMap.isInducing_of_restrict_nhds_zero_old {V : Set E} (V_mem : V ∈ 𝓝 0)
    (H : IsInducing (Set.restrict V f)) : IsInducing f := by
  classical
  replace H : comap f (𝓝 0) ⊓ 𝓟 V = 𝓝 0 := by
    set o : V := ⟨0, mem_of_mem_nhds V_mem⟩
    set f' : V → F := Set.restrict V f
    calc comap f (𝓝 0) ⊓ 𝓟 V
      _ = comap f (𝓝 (f' o)) ⊓ 𝓟 V := by simp [o, f']
      _ = map ((↑) : V → E) (comap f' (𝓝 (f' o))) := by
            simp [f', restrict_eq, ← comap_comap, map_comap_setCoe_val]
      _ = map ((↑) : V → E) (𝓝 o) := by rw [H.nhds_eq_comap]
      _ = 𝓝 0 := by
            rwa [IsInducing.subtypeVal.map_nhds_eq, Subtype.range_val, nhdsWithin_eq_nhds]
  refine IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr ?_
  suffices comap f (𝓝 0) ≤ 𝓟 V by rwa [← H, inf_eq_left]
  suffices comap f (𝓝 0) ⊓ 𝓟 Vᶜ = ⊥ by rwa [le_principal_iff, mem_iff_inf_principal_compl]
  set 𝓕 := comap (⇑f) (𝓝 0) ⊓ 𝓟 Vᶜ
  obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt_one 𝕜₁
  have c_ne : c ≠ 0 := fun h ↦ by simp [h] at hc₀
  have cover : ∀ x : E, ∃ k : ℕ, c ^ k • x ∈ V := by
    intro x
    suffices Tendsto (fun k : ℕ ↦ c ^ k • x) atTop (𝓝 0) from
      this.eventually V_mem |>.exists
    rw [← zero_smul 𝕜₁ x]
    exact .smul_const (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc₁) _
  set k : E → ℕ := fun x ↦ Nat.find (cover x)
  set p : E → E := fun x ↦ c ^ (k x) • x
  have p_mem_V : ∀ x, p x ∈ V := fun x ↦ Nat.find_spec (cover x)
  have p_mapsto : MapsTo p Vᶜ (c • V)ᶜ := by
    intro x hx₁ hx₂
    have : c ^ (k x - 1) • x ∈ V := by
      rwa [pow_sub₀ c c_ne (by simpa [k]), pow_one, mul_comm, mul_smul,
        ← mem_smul_set_iff_inv_smul_mem₀ c_ne]
    exact Nat.find_min (cover x) (by simpa [k]) this
  have p_tendsto : Tendsto p (comap f (𝓝 0)) (comap f (𝓝 0)) := by
    have : f ∘ p = (fun x ↦ (σ c) ^ (k x) • f x) := by ext; simp [p]
    rw [tendsto_comap_iff, this]
    refine IsBoundedUnder.smul_tendsto_zero ?_ tendsto_comap
    exact isBoundedUnder_of ⟨1, fun x ↦ by simpa using pow_le_one₀ hc₀.le hc₁.le⟩
  suffices map p 𝓕 ≤ ⊥ by rwa [le_bot_iff, map_eq_bot_iff] at this
  have h₁ : map p 𝓕 ≤ 𝓟 (c • V)ᶜ :=
    calc map p 𝓕
      _ ≤ map p (𝓟 Vᶜ) := map_mono inf_le_right
      _ ≤ 𝓟 (c • V)ᶜ := p_mapsto.tendsto
  have h₂ : map p 𝓕 ≤ 𝓟 (c • V) :=
    calc map p 𝓕
      _ ≤ map p (comap f (𝓝 0)) := map_mono inf_le_left
      _ ≤ map p (comap p (comap f (𝓝 0))) := map_mono (by rwa [← tendsto_iff_comap])
      _ = comap f (𝓝 0) ⊓ 𝓟 (Set.range p) := by rw [map_comap]
      _ ≤ comap f (𝓝 0) ⊓ 𝓟 V := by gcongr; simpa [range_subset_iff]
      _ = 𝓝 0 := by rw [H]
      _ ≤ 𝓟 (c • V) := by simpa [set_smul_mem_nhds_zero_iff c_ne]
  calc map p 𝓕
    _ ≤ 𝓟 (c • V)ᶜ ⊓ 𝓟 (c • V) := le_inf h₁ h₂
    _ = ⊥ := by simp
