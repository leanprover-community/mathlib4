/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Maps.Basic

/-!
# TODO
-/

universe u v

open Filter Topology

namespace TendstoTactic

variable {α : Type v} {𝕜 : Type u} [LinearOrderedField 𝕜]
  {l : Filter α} (f : 𝕜 → α)

theorem tendsto_bot_of_tendsto_top (h : Tendsto (fun x ↦ f (-x)) atTop l) :
    Tendsto f atBot l := by
  rw [show f = (f ∘ Neg.neg) ∘ Neg.neg by eta_expand; simp]
  exact Tendsto.comp h tendsto_neg_atBot_atTop

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]

theorem tendsto_zero_right_of_tendsto_top (h : Tendsto (fun x ↦ f x⁻¹) atTop l) :
    Tendsto f (𝓝[>] 0) l := by
  rw [show f = (f ∘ Inv.inv) ∘ Inv.inv by eta_expand; simp]
  apply Tendsto.comp h tendsto_inv_zero_atTop

theorem tendsto_zero_left_of_tendsto_bot (h : Tendsto (fun x ↦ f x⁻¹) atBot l) :
    Tendsto f (𝓝[<] 0) l := by
  rw [show f = (f ∘ Inv.inv) ∘ Inv.inv by eta_expand; simp]
  apply Tendsto.comp h tendsto_inv_zero_atBot

theorem tendsto_zero_left_of_tendsto_top (h : Tendsto (fun x ↦ f (- x⁻¹)) atTop l) :
    Tendsto f (𝓝[<] 0) l := by
  conv at h => arg 1; ext x; arg 1; rw [show -x⁻¹ = (-x)⁻¹ by ring]
  exact tendsto_zero_left_of_tendsto_bot _ (tendsto_bot_of_tendsto_top _ h)

theorem tendsto_zero_punctured_of_tendsto_top (h_pos : Tendsto (fun x ↦ f x⁻¹) atTop l)
    (h_neg : Tendsto (fun x ↦ f (-x⁻¹)) atTop l) :
    Tendsto f (𝓝[≠] 0) l := by
  rw [← nhds_left'_sup_nhds_right']
  apply Tendsto.sup
  · exact tendsto_zero_left_of_tendsto_top _ h_neg
  · exact tendsto_zero_right_of_tendsto_top _ h_pos

private def subHomeomorph {𝕜 : Type u} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜]
    [OrderTopology 𝕜] (c : 𝕜) : 𝕜 ≃ₜ 𝕜 := by
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

variable {c : 𝕜}

theorem tendsto_nhds_right_of_tendsto_top (h : Tendsto (fun x ↦ f (c + x⁻¹)) atTop l) :
    Tendsto f (𝓝[>] c) l := by
  have : Tendsto (fun x ↦ x - c) (𝓝[>] c) (𝓝[>] 0) := by
    simp [Tendsto]
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
    simp [Tendsto]
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

theorem tendsto_nhds_punctured_of_tendsto_top (h_neg : Tendsto (fun x ↦ f (c - x⁻¹)) atTop l)
    (h_pos : Tendsto (fun x ↦ f (c + x⁻¹)) atTop l) :
    Tendsto f (𝓝[≠] c) l := by
  have : Tendsto (fun x ↦ x - c) (𝓝[≠] c) (𝓝[≠] 0) := by
    simp [Tendsto]
    convert le_refl _
    rw [IsEmbedding.map_nhdsWithin_eq]
    · simp
      congr
      rw [Set.image_compl_eq]
      · simp
      exact (subHomeomorph c).bijective
    · exact (subHomeomorph c).isEmbedding
  convert Tendsto.comp (g := fun x ↦ f (c + x)) _ this
  · ext x
    simp
  apply tendsto_zero_punctured_of_tendsto_top _ h_pos
  convert h_neg using 3
  ring

end TendstoTactic
