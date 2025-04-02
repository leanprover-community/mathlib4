/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Topological space structure on `Mᵈᵃ` and `Mᵈᵃ`

In this file we define `TopologicalSpace` structure on `Mᵈᵃ` and `Mᵈᵃ`
and prove basic theorems about these topologies.
The topologies on `Mᵈᵃ` and `Mᵈᵃ` are the same as the topology on `M`.
Formally, they are induced by `DomAct.mk.symm` and `DomAct.mk.symm`,
since the types aren't definitionally equal.

## Tags

topological space, group action, domain action
-/

open Filter TopologicalSpace Topology

namespace DomAct

variable {M : Type*} [TopologicalSpace M]

/-- Put the same topological space structure on `Mᵈᵃ` as on the original space. -/
@[to_additive "Put the same topological space structure on `Mᵈᵃ` as on the original space."]
instance instTopologicalSpace : TopologicalSpace Mᵈᵃ := .induced mk.symm  ‹_›

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_mk : Continuous (@mk M) := continuous_induced_rng.2 continuous_id

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_mk_symm : Continuous (@mk M).symm := continuous_induced_dom

/-- `DomAct.mk` as a homeomorphism. -/
@[to_additive (attr := simps toEquiv) "`DomAct.mk` as a homeomorphism."]
def mkHomeomorph : M ≃ₜ Mᵈᵃ where
  toEquiv := mk

@[to_additive (attr := simp)] theorem coe_mkHomeomorph : ⇑(mkHomeomorph : M ≃ₜ Mᵈᵃ) = mk := rfl

@[to_additive (attr := simp)]
theorem coe_mkHomeomorph_symm : ⇑(mkHomeomorph : M ≃ₜ Mᵈᵃ).symm = mk.symm := rfl

@[to_additive] theorem isInducing_mk : IsInducing (@mk M) := mkHomeomorph.isInducing
@[to_additive] theorem isEmbedding_mk : IsEmbedding (@mk M) := mkHomeomorph.isEmbedding
@[to_additive] theorem isOpenEmbedding_mk : IsOpenEmbedding (@mk M) := mkHomeomorph.isOpenEmbedding
@[to_additive] theorem isClosedEmbedding_mk : IsClosedEmbedding (@mk M) :=
  mkHomeomorph.isClosedEmbedding
@[to_additive] theorem isQuotientMap_mk : IsQuotientMap (@mk M) := mkHomeomorph.isQuotientMap

@[deprecated (since := "2024-10-28")] alias inducing_mk := isInducing_mk

@[deprecated (since := "2024-10-26")]
alias embedding_mk := isEmbedding_mk

@[deprecated (since := "2024-10-22")]
alias quotientMap_mk := isQuotientMap_mk

@[deprecated (since := "2024-10-20")]
alias closedEmbedding_mk := isClosedEmbedding_mk

@[deprecated (since := "2024-10-18")]
alias openEmbedding_mk := isOpenEmbedding_mk

@[to_additive] theorem isInducing_mk_symm : IsInducing (@mk M).symm := mkHomeomorph.symm.isInducing
@[to_additive] theorem isEmbedding_mk_symm : IsEmbedding (@mk M).symm :=
  mkHomeomorph.symm.isEmbedding

@[deprecated (since := "2024-10-28")] alias inducing_mk_symm := isInducing_mk_symm

@[deprecated (since := "2024-10-26")]
alias embedding_mk_symm := isEmbedding_mk_symm

@[to_additive]
theorem isOpenEmbedding_mk_symm : IsOpenEmbedding (@mk M).symm := mkHomeomorph.symm.isOpenEmbedding

@[to_additive]
theorem isClosedEmbedding_mk_symm : IsClosedEmbedding (@mk M).symm :=
  mkHomeomorph.symm.isClosedEmbedding

@[deprecated (since := "2024-10-20")]
alias closedEmbedding_mk_symm := isClosedEmbedding_mk_symm

@[to_additive]
theorem isQuotientMap_mk_symm : IsQuotientMap (@mk M).symm := mkHomeomorph.symm.isQuotientMap

@[deprecated (since := "2024-10-22")]
alias quotientMap_mk_symm := isQuotientMap_mk_symm

@[to_additive] instance instT0Space [T0Space M] : T0Space Mᵈᵃ := mkHomeomorph.t0Space
@[to_additive] instance instT1Space [T1Space M] : T1Space Mᵈᵃ := mkHomeomorph.t1Space
@[to_additive] instance instT2Space [T2Space M] : T2Space Mᵈᵃ := mkHomeomorph.t2Space
@[to_additive] instance instT25Space [T25Space M] : T25Space Mᵈᵃ := mkHomeomorph.t25Space
@[to_additive] instance instT3Space [T3Space M] : T3Space Mᵈᵃ := mkHomeomorph.t3Space
@[to_additive] instance instT4Space [T4Space M] : T4Space Mᵈᵃ := mkHomeomorph.t4Space
@[to_additive] instance instT5Space [T5Space M] : T5Space Mᵈᵃ := mkHomeomorph.t5Space

@[to_additive] instance instR0Space [R0Space M] : R0Space Mᵈᵃ := isEmbedding_mk_symm.r0Space
@[to_additive] instance instR1Space [R1Space M] : R1Space Mᵈᵃ := isEmbedding_mk_symm.r1Space

@[to_additive]
instance instRegularSpace [RegularSpace M] : RegularSpace Mᵈᵃ := isEmbedding_mk_symm.regularSpace

@[to_additive]
instance instNormalSpace [NormalSpace M] : NormalSpace Mᵈᵃ := mkHomeomorph.normalSpace

@[to_additive]
instance instCompletelyNormalSpace [CompletelyNormalSpace M] : CompletelyNormalSpace Mᵈᵃ :=
  isEmbedding_mk_symm.completelyNormalSpace

@[to_additive]
instance instDiscreteTopology [DiscreteTopology M] : DiscreteTopology Mᵈᵃ :=
  isEmbedding_mk_symm.discreteTopology

@[to_additive]
instance instSeparableSpace [SeparableSpace M] : SeparableSpace Mᵈᵃ :=
  isQuotientMap_mk.separableSpace

@[to_additive]
instance instFirstCountableTopology [FirstCountableTopology M] : FirstCountableTopology Mᵈᵃ :=
  isInducing_mk_symm.firstCountableTopology

@[to_additive]
instance instSecondCountableTopology [SecondCountableTopology M] : SecondCountableTopology Mᵈᵃ :=
  isInducing_mk_symm.secondCountableTopology

@[to_additive]
instance instCompactSpace [CompactSpace M] : CompactSpace Mᵈᵃ :=
  mkHomeomorph.compactSpace

@[to_additive]
instance instLocallyCompactSpace [LocallyCompactSpace M] : LocallyCompactSpace Mᵈᵃ :=
  isOpenEmbedding_mk_symm.locallyCompactSpace

@[to_additive]
instance instWeaklyLocallyCompactSpace [WeaklyLocallyCompactSpace M] :
    WeaklyLocallyCompactSpace Mᵈᵃ :=
  isClosedEmbedding_mk_symm.weaklyLocallyCompactSpace

@[to_additive (attr := simp)]
theorem map_mk_nhds (x : M) : map (mk : M → Mᵈᵃ) (𝓝 x) = 𝓝 (mk x) :=
  mkHomeomorph.map_nhds_eq x

@[to_additive (attr := simp)]
theorem map_mk_symm_nhds (x : Mᵈᵃ) : map (mk.symm : Mᵈᵃ → M) (𝓝 x) = 𝓝 (mk.symm x) :=
  mkHomeomorph.symm.map_nhds_eq x

@[to_additive (attr := simp)]
theorem comap_mk_nhds (x : Mᵈᵃ) : comap (mk : M → Mᵈᵃ) (𝓝 x) = 𝓝 (mk.symm x) :=
  mkHomeomorph.comap_nhds_eq x

@[to_additive (attr := simp)]
theorem comap_mk.symm_nhds (x : M) : comap (mk.symm : Mᵈᵃ → M) (𝓝 x) = 𝓝 (mk x) :=
  mkHomeomorph.symm.comap_nhds_eq x

end DomAct
