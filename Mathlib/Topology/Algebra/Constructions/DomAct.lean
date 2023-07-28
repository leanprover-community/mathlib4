/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Homeomorph
import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Topological space structure on `Mᵈᵐᵃ` and `Mᵃᵐᵃ`

In this file we define `TopologicalSpace` structure on `Mᵈᵐᵃ` and `Mᵃᵐᵃ`
and prove basic theorems about 

## Tags

topological space, domain action
-/


variable {M X : Type _}

open Filter Topology

namespace DomMulAct

/-- Put the same topological space structure on `DomMulAct M` as on the original space. -/
@[to_additive "Put the same topological space structure on `DomAddAct M`
as on the original space."]
instance [TopologicalSpace M] : TopologicalSpace Mᵈᵐᵃ :=
  TopologicalSpace.induced (mk.symm : Mᵈᵐᵃ → M) ‹_›

variable [TopologicalSpace M]

@[to_additive (attr := continuity)]
theorem continuous_mk_symm : Continuous (mk.symm : Mᵈᵐᵃ → M) :=
  continuous_induced_dom

@[to_additive (attr := continuity)]
theorem continuous_mk : Continuous (mk : M → Mᵈᵐᵃ) :=
  continuous_induced_rng.2 continuous_id

/-- `DomMulAct.mk` as a homeomorphism. -/
@[to_additive (attr := simps!) "`DomAddAct.mk` as a homeomorphism."]
def mkHomeomorph : M ≃ₜ Mᵈᵐᵃ where
  toEquiv := mk
  continuous_toFun := continuous_mk
  continuous_invFun := continuous_mk_symm

@[to_additive]
instance [T2Space M] : T2Space Mᵈᵐᵃ :=
  mkHomeomorph.symm.embedding.t2Space

@[to_additive (attr := simp)]
theorem map_mk_nhds (x : M) : map (mk : M → Mᵈᵐᵃ) (𝓝 x) = 𝓝 (mk x) :=
  mkHomeomorph.map_nhds_eq x


@[to_additive (attr := simp)]
theorem map_mk_symm_nhds (x : Mᵈᵐᵃ) : map (mk.symm : Mᵈᵐᵃ → M) (𝓝 x) = 𝓝 (mk.symm x) :=
  mkHomeomorph.symm.map_nhds_eq x

@[to_additive (attr := simp)]
theorem comap_mk_nhds (x : Mᵈᵐᵃ) : comap (mk : M → Mᵈᵐᵃ) (𝓝 x) = 𝓝 (mk.symm x) :=
  mkHomeomorph.comap_nhds_eq x

@[to_additive (attr := simp)]
theorem comap_mk.symm_nhds (x : M) : comap (mk.symm : Mᵈᵐᵃ → M) (𝓝 x) = 𝓝 (mk x) :=
  mkHomeomorph.symm.comap_nhds_eq x

end DomMulAct
