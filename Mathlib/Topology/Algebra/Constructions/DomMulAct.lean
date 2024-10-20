/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Homeomorph
import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Topological space structure on `Mᵈᵐᵃ` and `Mᵈᵃᵃ`

In this file we define `TopologicalSpace` structure on `Mᵈᵐᵃ` and `Mᵈᵃᵃ`
and prove basic theorems about these topologies.
The topologies on `Mᵈᵐᵃ` and `Mᵈᵃᵃ` are the same as the topology on `M`.
Formally, they are induced by `DomMulAct.mk.symm` and `DomAddAct.mk.symm`,
since the types aren't definitionally equal.

## Tags

topological space, group action, domain action
-/

open Filter TopologicalSpace
open scoped Topology

namespace DomMulAct

variable {M : Type*} [TopologicalSpace M]

/-- Put the same topological space structure on `Mᵈᵐᵃ` as on the original space. -/
@[to_additive "Put the same topological space structure on `Mᵈᵃᵃ` as on the original space."]
instance instTopologicalSpace : TopologicalSpace Mᵈᵐᵃ := .induced mk.symm  ‹_›

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_mk : Continuous (@mk M) := continuous_induced_rng.2 continuous_id

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_mk_symm : Continuous (@mk M).symm := continuous_induced_dom

/-- `DomMulAct.mk` as a homeomorphism. -/
@[to_additive (attr := simps toEquiv) "`DomAddAct.mk` as a homeomorphism."]
def mkHomeomorph : M ≃ₜ Mᵈᵐᵃ where
  toEquiv := mk

@[to_additive (attr := simp)] theorem coe_mkHomeomorph : ⇑(mkHomeomorph : M ≃ₜ Mᵈᵐᵃ) = mk := rfl

@[to_additive (attr := simp)]
theorem coe_mkHomeomorph_symm : ⇑(mkHomeomorph : M ≃ₜ Mᵈᵐᵃ).symm = mk.symm := rfl

@[to_additive] theorem inducing_mk : Inducing (@mk M) := mkHomeomorph.inducing
@[to_additive] theorem embedding_mk : Embedding (@mk M) := mkHomeomorph.embedding
@[to_additive] theorem isOpenEmbedding_mk : IsOpenEmbedding (@mk M) := mkHomeomorph.isOpenEmbedding
@[to_additive] theorem isClosedEmbedding_mk : IsClosedEmbedding (@mk M) :=
  mkHomeomorph.isClosedEmbedding
@[to_additive] theorem quotientMap_mk : QuotientMap (@mk M) := mkHomeomorph.quotientMap

@[deprecated (since := "2024-10-20")]
alias closedEmbedding_mk := isClosedEmbedding_mk

@[deprecated (since := "2024-10-18")]
alias openEmbedding_mk := isOpenEmbedding_mk

@[to_additive] theorem inducing_mk_symm : Inducing (@mk M).symm := mkHomeomorph.symm.inducing
@[to_additive] theorem embedding_mk_symm : Embedding (@mk M).symm := mkHomeomorph.symm.embedding

@[to_additive]
theorem isOpenEmbedding_mk_symm : IsOpenEmbedding (@mk M).symm := mkHomeomorph.symm.isOpenEmbedding

@[deprecated (since := "2024-10-18")]
alias openEmbedding_mk_symm := isOpenEmbedding_mk_symm

@[to_additive]
theorem isClosedEmbedding_mk_symm : IsClosedEmbedding (@mk M).symm :=
  mkHomeomorph.symm.isClosedEmbedding

@[deprecated (since := "2024-10-20")]
alias closedEmbedding_mk_symm := isClosedEmbedding_mk_symm

@[to_additive]
theorem quotientMap_mk_symm : QuotientMap (@mk M).symm := mkHomeomorph.symm.quotientMap

@[to_additive] instance instT0Space [T0Space M] : T0Space Mᵈᵐᵃ := embedding_mk_symm.t0Space
@[to_additive] instance instT1Space [T1Space M] : T1Space Mᵈᵐᵃ := embedding_mk_symm.t1Space
@[to_additive] instance instT2Space [T2Space M] : T2Space Mᵈᵐᵃ := embedding_mk_symm.t2Space
@[to_additive] instance instT25Space [T25Space M] : T25Space Mᵈᵐᵃ := embedding_mk_symm.t25Space
@[to_additive] instance instT3Space [T3Space M] : T3Space Mᵈᵐᵃ := embedding_mk_symm.t3Space
@[to_additive] instance instT4Space [T4Space M] : T4Space Mᵈᵐᵃ := isClosedEmbedding_mk_symm.t4Space
@[to_additive] instance instT5Space [T5Space M] : T5Space Mᵈᵐᵃ := isClosedEmbedding_mk_symm.t5Space

@[to_additive] instance instR0Space [R0Space M] : R0Space Mᵈᵐᵃ := embedding_mk_symm.r0Space
@[to_additive] instance instR1Space [R1Space M] : R1Space Mᵈᵐᵃ := embedding_mk_symm.r1Space

@[to_additive]
instance instRegularSpace [RegularSpace M] : RegularSpace Mᵈᵐᵃ := embedding_mk_symm.regularSpace

@[to_additive]
instance instNormalSpace [NormalSpace M] : NormalSpace Mᵈᵐᵃ := isClosedEmbedding_mk_symm.normalSpace

@[to_additive]
instance instCompletelyNormalSpace [CompletelyNormalSpace M] : CompletelyNormalSpace Mᵈᵐᵃ :=
  isClosedEmbedding_mk_symm.completelyNormalSpace

@[to_additive]
instance instDiscreteTopology [DiscreteTopology M] : DiscreteTopology Mᵈᵐᵃ :=
  embedding_mk_symm.discreteTopology

@[to_additive]
instance instSeparableSpace [SeparableSpace M] : SeparableSpace Mᵈᵐᵃ :=
  quotientMap_mk.separableSpace

@[to_additive]
instance instFirstCountableTopology [FirstCountableTopology M] : FirstCountableTopology Mᵈᵐᵃ :=
  inducing_mk_symm.firstCountableTopology

@[to_additive]
instance instSecondCountableTopology [SecondCountableTopology M] : SecondCountableTopology Mᵈᵐᵃ :=
  inducing_mk_symm.secondCountableTopology

@[to_additive]
instance instCompactSpace [CompactSpace M] : CompactSpace Mᵈᵐᵃ :=
  mkHomeomorph.compactSpace

@[to_additive]
instance instLocallyCompactSpace [LocallyCompactSpace M] : LocallyCompactSpace Mᵈᵐᵃ :=
  isOpenEmbedding_mk_symm.locallyCompactSpace

@[to_additive]
instance instWeaklyLocallyCompactSpace [WeaklyLocallyCompactSpace M] :
    WeaklyLocallyCompactSpace Mᵈᵐᵃ :=
  isClosedEmbedding_mk_symm.weaklyLocallyCompactSpace

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
