/-
Copyright (c) 2026 Michael Rothgang, Pepa Montero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Pepa Montero.
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Covering.Quotient

@[expose] public section

noncomputable section

namespace MulAction

variable {M : Type*} [TopologicalSpace M]
variable {G : Type*} [Group G] [MulAction G M]
         [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M]
         [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]

/-- If a group `G` acts properly discontinuously on a topological space `M`,
then the quotient map `Quotient.mk _ : M → M⧸G`
is a covering map. -/
lemma isCoveringMap_quotientMk_of_properlyDiscontinuousSMul :
    IsCoveringMap (Quotient.mk _ : M → orbitRel.Quotient G M) :=
  IsQuotientCoveringMap.isCoveringMap (G:=_) (f:=_)
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul)
-- should this go in Mathlib.Topology.Covering.Quotient?

end MulAction

namespace QuotientMk
open MulAction

variable {M : Type*} [TopologicalSpace M]
variable {G : Type*} [Group G] [MulAction G M]
         [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M]
         [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]

/-- If a group `G` acts properly discontinuously on a topological space `M`,
then the quotient map `Quotient.mk : M → M⧸G`
is a local homeomorphism. -/
lemma isLocalHomeomorph_of_properlyDiscontinuousSMul :
    IsLocalHomeomorph (Quotient.mk _ : M → orbitRel.Quotient G M) :=
  isCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isLocalHomeomorph

/-- A chosen local homeomorphism for the quotient map
`Quotient.mk : M → M⧸G` at a point `p : M`. -/
noncomputable def localHomeomorphAt (p : M) :
    OpenPartialHomeomorph M (orbitRel.Quotient G M) :=
  Classical.choose (isLocalHomeomorph_of_properlyDiscontinuousSMul p)
-- this could just be
-- Classical.choose (isCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isLocalHomeomorph p)

/-- The point `p` lies in the source of `localHomeomorphAt p`. -/
lemma mem_localHomeomorphAt_source {p : M} :
    p ∈ (localHomeomorphAt (G:=G) p).source :=
  (Classical.choose_spec (isLocalHomeomorph_of_properlyDiscontinuousSMul p)).1

/-- The local homeomorphism `localHomeomorphAt p` coincides with
`Quotient.mk : M → M⧸G`. -/
lemma localHomeomorphAt_eq_quotientMk {p : M} :
    localHomeomorphAt (G:=G) p =
      (Quotient.mk _ : M → orbitRel.Quotient G M) :=
  (Classical.choose_spec (isLocalHomeomorph_of_properlyDiscontinuousSMul p)).2.symm

/-- The equivalence class `⟦p⟧` lies in the target of `localHomeomorphAt p`. -/
lemma mem_localHomeomorphAt_target {p : M} :
    ⟦p⟧ ∈ (localHomeomorphAt (G:=G) p).target := by
  rw [← OpenPartialHomeomorph.image_source_eq_target, Set.mem_image]
  refine ⟨p, mem_localHomeomorphAt_source, ?_⟩
  rw [localHomeomorphAt_eq_quotientMk]

/-- A chosen local inverse for the quotient map
`Quotient.mk : M → M⧸G` at a point `p : M`. -/
def localInverseAt (p : M) :
  OpenPartialHomeomorph (orbitRel.Quotient G M) M :=
    (localHomeomorphAt p).symm

/-- The equivalence class `⟦p⟧` lies in the source of `localInverseAt p`. -/
lemma mem_localInverseAt_source {p : M} :
    ⟦p⟧ ∈ (localInverseAt (G:=G) p).source := by
  simp only [localInverseAt, OpenPartialHomeomorph.symm_source]
  exact mem_localHomeomorphAt_target

/-- If a point `k` lies on the source of `localHomeomorphAt p`
and its class `⟦k⟧` lies on the source of `localInverseAt p`,
then `localInverseAt p` sends `⟦k⟧` back to its representative `k`. -/
lemma localInverseAt_apply_other {p k : M}
    (h : k ∈ (localHomeomorphAt (G := G) p).source)
    (h' : ⟦k⟧ ∈ (localInverseAt (G := G) p).source) :
    (localInverseAt (G := G) p) ⟦k⟧ = k := by
  refine (localHomeomorphAt (G:=G) p).injOn ?_ h ?_
  · simp only [localInverseAt,
               OpenPartialHomeomorph.map_target (localHomeomorphAt p) h']
  · simp only [localInverseAt, (localHomeomorphAt p).right_inv h',
               localHomeomorphAt_eq_quotientMk]

/-- The local inverse at `p` sends the class `⟦p⟧` back to `p`. -/
lemma localInverseAt_apply_self {p : M}
    : (localInverseAt (G:=G) p) ⟦p⟧ = p :=
  localInverseAt_apply_other
    (mem_localHomeomorphAt_source)
    (mem_localInverseAt_source)

end QuotientMk

end
