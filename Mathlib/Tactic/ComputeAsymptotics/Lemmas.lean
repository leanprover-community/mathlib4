/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Conversion lemmas

This file contains lemmas we use to reduce various asymptotic goals to the case `Tendsto f atTop l`.

## Main theorems

This file contains the following lemmas:
* `tendsto_atBot_of_tendsto_atTop` for `Tendsto f atBot l`
* `tendsto_nhdsGT_of_tendsto_atTop` for `Tendsto f (𝓝[>] c) l`
* `tendsto_nhdsLT_of_tendsto_atTop` for `Tendsto f (𝓝[<] c) l`
* `tendsto_nhdsNE_of_tendsto_atTop` for `Tendsto f (𝓝[≠] c) l`
* `isBigO_of_div_tendsto_atTop` and `isBigO_of_div_tendsto_atBot` for `f =O[l] g`

We also use lemmas from other files:
* `IsLittleO.of_tendsto_div_atBot` and `IsLittleO.of_tendsto_div_atTop` for `f =o[l] g`
* `isEquivalent_of_tendsto_one` for `f ∼ g`
-/

@[expose] public section

open Filter Topology Asymptotics

namespace Tactic.ComputeAsymptotics

variable {α 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {l : Filter α} (f : 𝕜 → α)

theorem tendsto_atBot_of_tendsto_atTop (h : Tendsto (fun x ↦ f (-x)) atTop l) :
    Tendsto f atBot l := by
  convert h.comp tendsto_neg_atBot_atTop
  ext
  simp

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]

theorem tendsto_nhdsGT_zero_of_tendsto_atTop (h : Tendsto (fun x ↦ f x⁻¹) atTop l) :
    Tendsto f (𝓝[>] 0) l := by
  convert h.comp tendsto_inv_nhdsGT_zero
  ext
  simp

theorem tendsto_nhdsLT_zero_of_tendsto_atBot (h : Tendsto (fun x ↦ f x⁻¹) atBot l) :
    Tendsto f (𝓝[<] 0) l := by
  convert h.comp tendsto_inv_nhdsLT_zero
  ext
  simp

theorem tendsto_nhdsLT_zero_of_tendsto_atTop (h : Tendsto (fun x ↦ f (-x⁻¹)) atTop l) :
    Tendsto f (𝓝[<] 0) l := by
  conv at h => arg 1; ext x; arg 1; rw [show -x⁻¹ = (-x)⁻¹ by ring]
  exact tendsto_nhdsLT_zero_of_tendsto_atBot _ (tendsto_atBot_of_tendsto_atTop _ h)

theorem tendsto_nhdsNE_zero_of_tendsto_atTop (h_pos : Tendsto (fun x ↦ f x⁻¹) atTop l)
    (h_neg : Tendsto (fun x ↦ f (-x⁻¹)) atTop l) :
    Tendsto f (𝓝[≠] 0) l := by
  rw [← nhdsLT_sup_nhdsGT]
  apply Tendsto.sup
  · exact tendsto_nhdsLT_zero_of_tendsto_atTop _ h_neg
  · exact tendsto_nhdsGT_zero_of_tendsto_atTop _ h_pos

variable (c : 𝕜)

theorem tendsto_nhdsGT_of_tendsto_atTop (h : Tendsto (fun x ↦ f (c + x⁻¹)) atTop l) :
    Tendsto f (𝓝[>] c) l := by
  have : map (· - c) (𝓝[>] c) = (𝓝[>] 0) := by
    convert (Homeomorph.addRight (-c)).isEmbedding.map_nhdsWithin_eq .. using 2
    all_goals simp [sub_eq_add_neg]
  convert tendsto_nhdsGT_zero_of_tendsto_atTop (fun x ↦ f (c + x)) h |>.comp this.le
  funext
  simp

theorem tendsto_nhdsLT_of_tendsto_atTop (h : Tendsto (fun x ↦ f (c - x⁻¹)) atTop l) :
    Tendsto f (𝓝[<] c) l := by
  have : map (· - c) (𝓝[<] c) = (𝓝[<] 0) := by
    convert (Homeomorph.addRight (-c)).isEmbedding.map_nhdsWithin_eq .. using 2
    all_goals simp [sub_eq_add_neg]
  convert (tendsto_nhdsLT_zero_of_tendsto_atTop (fun x ↦ f (c + x)) _).comp this.le
  · funext
    simp
  · convert h using 2
    grind

theorem tendsto_nhdsNE_of_tendsto_atTop
    (h_neg : Tendsto (fun x ↦ f (c - x⁻¹)) atTop l)
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
      convert (Homeomorph.addRight (-c)).bijective using 2
      grind [Homeomorph.coe_addRight]
    · convert (Homeomorph.addRight (-c)).isEmbedding using 2
      grind [Homeomorph.coe_addRight]
  convert Tendsto.comp (g := fun x ↦ f (c + x)) _ this
  · ext x
    simp
  apply tendsto_nhdsNE_zero_of_tendsto_atTop
  · exact h_pos
  convert h_neg using 3
  ring

theorem tendsto_nhdsNE_of_tendsto_atTop_nhds_of_eq
    [TopologicalSpace α]
    {a b : α}
    (h_neg : Tendsto (fun x ↦ f (c - x⁻¹)) atTop (𝓝 a))
    (h_pos : Tendsto (fun x ↦ f (c + x⁻¹)) atTop (𝓝 b))
    (h_eq : a = b) :
    Tendsto f (𝓝[≠] c) (𝓝 a) := by
  apply tendsto_nhdsNE_of_tendsto_atTop _ _ h_neg
  convert h_pos

theorem isBigO_of_div_tendsto_atTop {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l atTop) :
    f =O[l] g :=
  Asymptotics.IsLittleO.isBigO (.of_tendsto_div_atTop h)

theorem isBigO_of_div_tendsto_atBot {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l atBot) :
    f =O[l] g :=
  Asymptotics.IsLittleO.isBigO (.of_tendsto_div_atBot h)

end Tactic.ComputeAsymptotics
