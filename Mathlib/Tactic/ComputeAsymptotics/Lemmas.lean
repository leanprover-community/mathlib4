/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Conversion lemmas

The main procedure of the `compute_asymptotics` tactic is able to compute limits of functions at
`atTop` filter. This file contains lemmas we use to reduce other asymptotic goals to
the case `Tendsto f atTop l`.

## Main theorems

This file contains the following lemmas:
* `tendsto_nhdsGT_of_tendsto_atTop` for `Tendsto f (𝓝[>] c) l`
* `tendsto_nhdsLT_of_tendsto_atTop` for `Tendsto f (𝓝[<] c) l`
* `tendsto_nhdsNE_of_tendsto_atTop` for `Tendsto f (𝓝[≠] c) l`
* `isBigO_of_div_tendsto_atTop` and `isBigO_of_div_tendsto_atBot` for `f =O[l] g`

We also use lemmas from other files:
* `tendsto_comp_neg_atTop_iff` for `Tendsto f atBot l`
* `IsLittleO.of_tendsto_div_atBot` and `IsLittleO.of_tendsto_div_atTop` for `f =o[l] g`
* `isEquivalent_of_tendsto_one` for `f ∼ g`
-/

@[expose] public section

open Filter Topology Asymptotics

namespace Tactic.ComputeAsymptotics

variable {α 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] {l : Filter α} (f : 𝕜 → α) (c : 𝕜)

theorem tendsto_nhdsGT_of_tendsto_atTop (h : Tendsto (fun x ↦ f (c + x⁻¹)) atTop l) :
    Tendsto f (𝓝[>] c) l := by
  simpa [← Function.comp_def, Tendsto, ← Filter.map_map] using h

theorem tendsto_nhdsLT_of_tendsto_atTop (h : Tendsto (fun x ↦ f (c - x⁻¹)) atTop l) :
    Tendsto f (𝓝[<] c) l := by
  convert_to Tendsto (f ∘ (fun x ↦ c + x) ∘ Neg.neg ∘ Inv.inv) atTop l at h
  · ext
    simp [AddGroupWithOne.sub_eq_add_neg]
  simpa [Tendsto, ← Filter.map_map] using h

theorem tendsto_nhdsNE_of_tendsto_atTop (h_neg : Tendsto (fun x ↦ f (c - x⁻¹)) atTop l)
    (h_pos : Tendsto (fun x ↦ f (c + x⁻¹)) atTop l) :
    Tendsto f (𝓝[≠] c) l := by
  simpa [Tendsto, ← nhdsLT_sup_nhdsGT] using
    ⟨tendsto_nhdsLT_of_tendsto_atTop _ _ h_neg, tendsto_nhdsGT_of_tendsto_atTop _ _ h_pos⟩

theorem tendsto_nhdsNE_of_tendsto_atTop_nhds_of_eq [TopologicalSpace α] {a b : α}
    (h_neg : Tendsto (fun x ↦ f (c - x⁻¹)) atTop (𝓝 a))
    (h_pos : Tendsto (fun x ↦ f (c + x⁻¹)) atTop (𝓝 b)) (h_eq : a = b) :
    Tendsto f (𝓝[≠] c) (𝓝 a) := by
  apply tendsto_nhdsNE_of_tendsto_atTop _ _ h_neg
  convert h_pos

theorem isBigOWith_of_tendsto_top {C : ℝ} {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l atTop) (hC : 0 < C) :
    IsBigOWith C l f g :=
  Asymptotics.IsLittleO.forall_isBigOWith (.of_tendsto_div_atTop h) hC

theorem isBigOWith_of_tendsto_bot {C : ℝ} {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l atBot) (hC : 0 < C) :
    IsBigOWith C l f g :=
  Asymptotics.IsLittleO.forall_isBigOWith (.of_tendsto_div_atBot h) hC

theorem isBigO_of_div_tendsto_atTop {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l atTop) :
    f =O[l] g :=
  Asymptotics.IsLittleO.isBigO (.of_tendsto_div_atTop h)

theorem isBigO_of_div_tendsto_atBot {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l atBot) :
    f =O[l] g :=
  Asymptotics.IsLittleO.isBigO (.of_tendsto_div_atBot h)

end Tactic.ComputeAsymptotics
