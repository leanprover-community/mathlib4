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
instance instTopologicalSpace : TopologicalSpace Mᵈᵃ := .induced mk.symm  ‹_›

@[continuity, fun_prop]
theorem continuous_mk : Continuous (@mk M) := continuous_induced_rng.2 continuous_id

@[continuity, fun_prop]
theorem continuous_mk_symm : Continuous (@mk M).symm := continuous_induced_dom

/-- `DomAct.mk` as a homeomorphism. -/
@[simps toEquiv]
def mkHomeomorph : M ≃ₜ Mᵈᵃ where
  toEquiv := mk

@[simp] theorem coe_mkHomeomorph : ⇑(mkHomeomorph : M ≃ₜ Mᵈᵃ) = mk := rfl

@[simp]
theorem coe_mkHomeomorph_symm : ⇑(mkHomeomorph : M ≃ₜ Mᵈᵃ).symm = mk.symm := rfl

theorem isInducing_mk : IsInducing (@mk M) := mkHomeomorph.isInducing
theorem isEmbedding_mk : IsEmbedding (@mk M) := mkHomeomorph.isEmbedding
theorem isOpenEmbedding_mk : IsOpenEmbedding (@mk M) := mkHomeomorph.isOpenEmbedding
theorem isClosedEmbedding_mk : IsClosedEmbedding (@mk M) :=
  mkHomeomorph.isClosedEmbedding
theorem isQuotientMap_mk : IsQuotientMap (@mk M) := mkHomeomorph.isQuotientMap

@[deprecated (since := "2024-10-28")] alias inducing_mk := isInducing_mk

@[deprecated (since := "2024-10-26")]
alias embedding_mk := isEmbedding_mk

@[deprecated (since := "2024-10-22")]
alias quotientMap_mk := isQuotientMap_mk

theorem isInducing_mk_symm : IsInducing (@mk M).symm := mkHomeomorph.symm.isInducing
theorem isEmbedding_mk_symm : IsEmbedding (@mk M).symm :=
  mkHomeomorph.symm.isEmbedding

@[deprecated (since := "2024-10-28")] alias inducing_mk_symm := isInducing_mk_symm

@[deprecated (since := "2024-10-26")]
alias embedding_mk_symm := isEmbedding_mk_symm

theorem isOpenEmbedding_mk_symm : IsOpenEmbedding (@mk M).symm := mkHomeomorph.symm.isOpenEmbedding

theorem isClosedEmbedding_mk_symm : IsClosedEmbedding (@mk M).symm :=
  mkHomeomorph.symm.isClosedEmbedding

theorem isQuotientMap_mk_symm : IsQuotientMap (@mk M).symm := mkHomeomorph.symm.isQuotientMap

@[deprecated (since := "2024-10-22")]
alias quotientMap_mk_symm := isQuotientMap_mk_symm

instance instT0Space [T0Space M] : T0Space Mᵈᵃ := mkHomeomorph.t0Space
instance instT1Space [T1Space M] : T1Space Mᵈᵃ := mkHomeomorph.t1Space
instance instT2Space [T2Space M] : T2Space Mᵈᵃ := mkHomeomorph.t2Space
instance instT25Space [T25Space M] : T25Space Mᵈᵃ := mkHomeomorph.t25Space
instance instT3Space [T3Space M] : T3Space Mᵈᵃ := mkHomeomorph.t3Space
instance instT4Space [T4Space M] : T4Space Mᵈᵃ := mkHomeomorph.t4Space
instance instT5Space [T5Space M] : T5Space Mᵈᵃ := mkHomeomorph.t5Space

instance instR0Space [R0Space M] : R0Space Mᵈᵃ := isEmbedding_mk_symm.r0Space
instance instR1Space [R1Space M] : R1Space Mᵈᵃ := isEmbedding_mk_symm.r1Space

instance instRegularSpace [RegularSpace M] : RegularSpace Mᵈᵃ := isEmbedding_mk_symm.regularSpace

instance instNormalSpace [NormalSpace M] : NormalSpace Mᵈᵃ := mkHomeomorph.normalSpace

instance instCompletelyNormalSpace [CompletelyNormalSpace M] : CompletelyNormalSpace Mᵈᵃ :=
  isEmbedding_mk_symm.completelyNormalSpace

instance instDiscreteTopology [DiscreteTopology M] : DiscreteTopology Mᵈᵃ :=
  isEmbedding_mk_symm.discreteTopology

instance instSeparableSpace [SeparableSpace M] : SeparableSpace Mᵈᵃ :=
  isQuotientMap_mk.separableSpace

instance instFirstCountableTopology [FirstCountableTopology M] : FirstCountableTopology Mᵈᵃ :=
  isInducing_mk_symm.firstCountableTopology

instance instSecondCountableTopology [SecondCountableTopology M] : SecondCountableTopology Mᵈᵃ :=
  isInducing_mk_symm.secondCountableTopology

instance instCompactSpace [CompactSpace M] : CompactSpace Mᵈᵃ :=
  mkHomeomorph.compactSpace

instance instLocallyCompactSpace [LocallyCompactSpace M] : LocallyCompactSpace Mᵈᵃ :=
  isOpenEmbedding_mk_symm.locallyCompactSpace

instance instWeaklyLocallyCompactSpace [WeaklyLocallyCompactSpace M] :
    WeaklyLocallyCompactSpace Mᵈᵃ :=
  isClosedEmbedding_mk_symm.weaklyLocallyCompactSpace

@[simp]
theorem map_mk_nhds (x : M) : map (mk : M → Mᵈᵃ) (𝓝 x) = 𝓝 (mk x) :=
  mkHomeomorph.map_nhds_eq x

@[simp]
theorem map_mk_symm_nhds (x : Mᵈᵃ) : map (mk.symm : Mᵈᵃ → M) (𝓝 x) = 𝓝 (mk.symm x) :=
  mkHomeomorph.symm.map_nhds_eq x

@[simp]
theorem comap_mk_nhds (x : Mᵈᵃ) : comap (mk : M → Mᵈᵃ) (𝓝 x) = 𝓝 (mk.symm x) :=
  mkHomeomorph.comap_nhds_eq x

@[simp]
theorem comap_mk.symm_nhds (x : M) : comap (mk.symm : Mᵈᵃ → M) (𝓝 x) = 𝓝 (mk x) :=
  mkHomeomorph.symm.comap_nhds_eq x

end DomAct
