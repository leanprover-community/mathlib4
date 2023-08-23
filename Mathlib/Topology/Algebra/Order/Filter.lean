/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Filter
import Mathlib.Topology.Order.Basic

#align_import topology.algebra.order.filter from "leanprover-community/mathlib"@"98e83c3d541c77cdb7da20d79611a780ff8e7d90"

/-!
# Topology on filters of a space with order topology

In this file we prove that `𝓝 (f x)` tends to `𝓝 Filter.atTop` provided that `f` tends to
`Filter.atTop`, and similarly for `Filter.atBot`.
-/


open Topology

namespace Filter

variable {α X : Type*} [TopologicalSpace X] [PartialOrder X] [OrderTopology X]

protected theorem tendsto_nhds_atTop [NoMaxOrder X] : Tendsto 𝓝 (atTop : Filter X) (𝓝 atTop) :=
  Filter.tendsto_nhds_atTop_iff.2 fun x => (eventually_gt_atTop x).mono fun _ => le_mem_nhds
#align filter.tendsto_nhds_at_top Filter.tendsto_nhds_atTop

protected theorem tendsto_nhds_atBot [NoMinOrder X] : Tendsto 𝓝 (atBot : Filter X) (𝓝 atBot) :=
  @Filter.tendsto_nhds_atTop Xᵒᵈ _ _ _ _
#align filter.tendsto_nhds_at_bot Filter.tendsto_nhds_atBot

theorem Tendsto.nhds_atTop [NoMaxOrder X] {f : α → X} {l : Filter α} (h : Tendsto f l atTop) :
    Tendsto (𝓝 ∘ f) l (𝓝 atTop) :=
  Filter.tendsto_nhds_atTop.comp h
#align filter.tendsto.nhds_at_top Filter.Tendsto.nhds_atTop

theorem Tendsto.nhds_atBot [NoMinOrder X] {f : α → X} {l : Filter α} (h : Tendsto f l atBot) :
    Tendsto (𝓝 ∘ f) l (𝓝 atBot) :=
  @Tendsto.nhds_atTop α Xᵒᵈ _ _ _ _ _ _ h
#align filter.tendsto.nhds_at_bot Filter.Tendsto.nhds_atBot

end Filter
