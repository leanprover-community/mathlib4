/-
?
-/

module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Covering.Quotient


/-!
# What is this file

Idek tbh

## Alright

Other things
-/

@[expose] public section

open Topology MulAction.orbitRel

noncomputable section

namespace MulAction

-- auxiliar lemmas
-- necessary?

variable {M : Type*} [TopologicalSpace M]
variable {G : Type*} [Group G] [MulAction G M]
         [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M]
         [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]
-- these are all necessary for isCoveringMap_quotientMk

lemma isCoveringMap_quotient_mk :
    IsCoveringMap (Quotient.mk _ : M → Quotient G M) := by
  apply IsQuotientCoveringMap.isCoveringMap (G:=G)
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

lemma isLocalHomeomorph_quotient_mk :
    IsLocalHomeomorph (Quotient.mk _ : M → Quotient G M) :=
  isCoveringMap_quotient_mk.isLocalHomeomorph

noncomputable def quotientLocalHomeomorphAt (p : M) :
    OpenPartialHomeomorph M (Quotient G M) :=
  Classical.choose (isLocalHomeomorph_quotient_mk p)

lemma mem_quotientLocalHomeomorphAt_source (p : M) :
    p ∈ (quotientLocalHomeomorphAt (G:=G) p).source :=
  (Classical.choose_spec (isLocalHomeomorph_quotient_mk p)).1

lemma quotientLocalHomeomorphAt_eq_quotientMk (p : M) :
    quotientLocalHomeomorphAt (G:=G) p =
      (Quotient.mk _ : M → Quotient G M) :=
  (Classical.choose_spec (isLocalHomeomorph_quotient_mk p)).2.symm



end MulAction

end
