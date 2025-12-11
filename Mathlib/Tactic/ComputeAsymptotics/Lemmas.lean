/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# TODO
-/

universe u v

@[expose] public section

open Filter Topology Asymptotics

namespace ComputeAsymptotics

variable {α : Type v} {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {l : Filter α} (f : 𝕜 → α)

theorem tendsto_bot_of_tendsto_top (h : Tendsto (fun x ↦ f (-x)) atTop l) :
    Tendsto f atBot l := by
  rw [show f = (f ∘ Neg.neg) ∘ Neg.neg by eta_expand; simp]
  exact Tendsto.comp h tendsto_neg_atBot_atTop

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]

theorem tendsto_zero_right_of_tendsto_top (h : Tendsto (fun x ↦ f x⁻¹) atTop l) :
    Tendsto f (𝓝[>] 0) l := by
  rw [show f = (f ∘ Inv.inv) ∘ Inv.inv by eta_expand; simp]
  apply Tendsto.comp h tendsto_inv_nhdsGT_zero

theorem tendsto_zero_left_of_tendsto_bot (h : Tendsto (fun x ↦ f x⁻¹) atBot l) :
    Tendsto f (𝓝[<] 0) l := by
  rw [show f = (f ∘ Inv.inv) ∘ Inv.inv by eta_expand; simp]
  apply Tendsto.comp h tendsto_inv_nhdsLT_zero

theorem tendsto_zero_left_of_tendsto_top (h : Tendsto (fun x ↦ f (-x⁻¹)) atTop l) :
    Tendsto f (𝓝[<] 0) l := by
  conv at h => arg 1; ext x; arg 1; rw [show -x⁻¹ = (-x)⁻¹ by ring]
  exact tendsto_zero_left_of_tendsto_bot _ (tendsto_bot_of_tendsto_top _ h)

theorem tendsto_zero_punctured_of_tendsto_top (h_pos : Tendsto (fun x ↦ f x⁻¹) atTop l)
    (h_neg : Tendsto (fun x ↦ f (-x⁻¹)) atTop l) :
    Tendsto f (𝓝[≠] 0) l := by
  rw [← nhdsLT_sup_nhdsGT]
  apply Tendsto.sup
  · exact tendsto_zero_left_of_tendsto_top _ h_neg
  · exact tendsto_zero_right_of_tendsto_top _ h_pos

private def subHomeomorph {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] (c : 𝕜) : 𝕜 ≃ₜ 𝕜 := by
  constructor
  pick_goal 3
  constructor
  pick_goal 3
  · exact fun x ↦ x - c
  pick_goal 3
  · exact fun x ↦ x + c
  · simp [Function.LeftInverse]
  · simp [Function.RightInverse, Function.LeftInverse]
  · exact continuous_sub_right c
  · exact continuous_add_right c

variable (c : 𝕜)

theorem tendsto_nhds_right_of_tendsto_top (h : Tendsto (fun x ↦ f (c + x⁻¹)) atTop l) :
    Tendsto f (𝓝[>] c) l := by
  have : Tendsto (fun x ↦ x - c) (𝓝[>] c) (𝓝[>] 0) := by
    simp only [Tendsto]
    convert le_refl _
    rw [IsEmbedding.map_nhdsWithin_eq]
    · simp
    · exact (subHomeomorph c).isEmbedding
  convert Tendsto.comp (g := fun x ↦ f (c + x)) _ this
  · ext x
    simp
  exact tendsto_zero_right_of_tendsto_top _ h

theorem tendsto_nhds_left_of_tendsto_top (h : Tendsto (fun x ↦ f (c - x⁻¹)) atTop l) :
    Tendsto f (𝓝[<] c) l := by
  have : Tendsto (fun x ↦ x - c) (𝓝[<] c) (𝓝[<] 0) := by
    simp only [Tendsto]
    convert le_refl _
    rw [IsEmbedding.map_nhdsWithin_eq]
    · simp
    · exact (subHomeomorph c).isEmbedding
  convert Tendsto.comp (g := fun x ↦ f (c + x)) _ this
  · ext x
    simp
  apply tendsto_zero_left_of_tendsto_top
  convert h using 3
  ring

-- set_option maxHeartbeats 0 in
theorem tendsto_nhds_punctured_of_tendsto_top (h_neg : Tendsto (fun x ↦ f (c - x⁻¹)) atTop l)
    (h_pos : Tendsto (fun x ↦ f (c + x⁻¹)) atTop l) :
    Tendsto f (𝓝[≠] c) l := by
  have : Tendsto (fun x ↦ x - c) (𝓝[≠] c) (𝓝[≠] 0) := by
    simp only [Tendsto]
    convert le_refl _
    rw [IsEmbedding.map_nhdsWithin_eq]
    · simp only [sub_self]
      congr
      rw [Set.image_compl_eq]
      · simp
      exact (subHomeomorph c).bijective
    · exact (subHomeomorph c).isEmbedding
  convert Tendsto.comp (g := fun x ↦ f (c + x)) _ this
  · ext x
    simp
  apply tendsto_zero_punctured_of_tendsto_top
  · exact h_pos
  convert h_neg using 3
  ring

theorem tendsto_nhds_punctured_of_tendsto_top_nhds_of_eq
    [TopologicalSpace α]
    {a b : α}
    (h_neg : Tendsto (fun x ↦ f (c - x⁻¹)) atTop (𝓝 a))
    (h_pos : Tendsto (fun x ↦ f (c + x⁻¹)) atTop (𝓝 b))
    (h_eq : a = b) :
    Tendsto f (𝓝[≠] c) (𝓝 a) := by
  apply tendsto_nhds_punctured_of_tendsto_top _ _ h_neg
  convert h_pos

-- TODO: generalize lemmas below

theorem isLittleO_of_tendsto_top {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l atTop) :
    f =o[l] g := by
  rw [isLittleO_iff]
  intro c hc
  apply (Filter.Tendsto.eventually_ge_atTop h c⁻¹).mono
  intro x hx
  replace hx : c⁻¹ ≤ |g x / f x| := by
    apply hx.trans
    apply le_abs_self
  simp only [abs_div] at hx
  by_cases hf : f x = 0
  · simp [hf] at hx
    linarith
  rw [le_div_iff₀ (abs_pos.mpr hf)] at hx
  exact (inv_mul_le_iff₀ hc).mp hx

theorem isLittleO_of_tendsto_bot {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l atBot) :
    f =o[l] g := by
  apply IsLittleO.of_neg_left
  apply isLittleO_of_tendsto_top
  rw [← tendsto_neg_atBot_iff]
  convert h using 1
  ext x
  simp [div_neg_eq_neg_div]

theorem isBigO_of_tendsto_top {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l atTop) :
    f =O[l] g :=
  Asymptotics.IsLittleO.isBigO (isLittleO_of_tendsto_top h)

theorem isBigO_of_tendsto_bot {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l atBot) :
    f =O[l] g :=
  Asymptotics.IsLittleO.isBigO (isLittleO_of_tendsto_bot h)

theorem isBigO_of_tendsto_nhds {f g : ℝ → ℝ} {l : Filter ℝ} {c : ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l (𝓝 c)) (hc : c ≠ 0) :
    f =O[l] g := by
  apply Asymptotics.isBigO_of_div_tendsto_nhds (c := c⁻¹)
  · have : ∀ᶠ x in l, g x / f x ≠ 0 := Filter.Tendsto.eventually_ne h hc
    apply this.mono
    intro x hx hg
    simp [hg] at hx
  · rw [← tendsto_inv_iff₀]
    · convert h using 1
      · ext x
        simp
      · simp
    · simpa

-- TODO: upstream
theorem isEquivalent_of_tendsto_one {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ f x / g x) l (𝓝 1)) :
    f ~[l] g := by
  apply Asymptotics.isEquivalent_of_tendsto_one _ h
  have : ∀ᶠ x in l, 1 / 2 ≤ f x / g x := by
    apply Filter.Tendsto.eventually_const_le _ h
    norm_num
  apply this.mono
  intro x hx hg
  norm_num [hg] at hx

end ComputeAsymptotics
