/-
Copyright (c) 2025 Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz,
Juan José Madrigal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz, Juan José Madrigal
-/
module

public import Mathlib.Topology.Covering.Quotient

/-!
# Covering and local homeomorphism structure on orbit spaces

Let `G` be a group acting freely and properly discontinuously on a topological space `M`.

This file shows that the quotient map `Quotient.mk : M → orbitRel.Quotient G M`
is a covering map, and hence a local homeomorphism.

We also construct chosen local homeomorphisms and their inverses at each
point, and establish basic properties.
-/

public section

variable {M : Type*} [TopologicalSpace M]
  {G : Type*} [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M]

namespace MulAction

/-- If a group `G` acts properly discontinuously on a topological space `M`, the quotient map
`Quotient.mk _ : M → M⧸G` is a covering map. -/
lemma isCoveringMap_quotientMk_of_properlyDiscontinuousSMul :
    IsCoveringMap (Quotient.mk _ : M → orbitRel.Quotient G M) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap

end MulAction

noncomputable section

namespace QuotientMk

open MulAction

/-- If a group `G` acts properly discontinuously on a topological space `M`, the quotient map
`Quotient.mk : M → M⧸G` is a local homeomorphism. -/
lemma isLocalHomeomorph_of_properlyDiscontinuousSMul :
    IsLocalHomeomorph (Quotient.mk _ : M → orbitRel.Quotient G M) :=
  isCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isLocalHomeomorph

variable {p : M}

variable (G p) in
/-- A chosen local homeomorphism for the quotient map `Quotient.mk : M → M⧸G` at a point `p : M`. -/
def localHomeomorphAt : OpenPartialHomeomorph M (orbitRel.Quotient G M) :=
  Classical.choose (isLocalHomeomorph_of_properlyDiscontinuousSMul p)

/-- The point `p` lies in the source of `localHomeomorphAt p`. -/
lemma mem_localHomeomorphAt_source : p ∈ (localHomeomorphAt G p).source :=
  (Classical.choose_spec (isLocalHomeomorph_of_properlyDiscontinuousSMul p)).1

/-- The local homeomorphism `localHomeomorphAt p` coincides with `Quotient.mk : M → M⧸G`. -/
lemma localHomeomorphAt_eq_quotientMk :
    localHomeomorphAt G p = (Quotient.mk _ : M → orbitRel.Quotient G M) :=
  (Classical.choose_spec (isLocalHomeomorph_of_properlyDiscontinuousSMul p)).2.symm

/-- The equivalence class `⟦p⟧` lies in the target of `localHomeomorphAt p`. -/
lemma mem_localHomeomorphAt_target : ⟦p⟧ ∈ (localHomeomorphAt G p).target := by
  rw [← OpenPartialHomeomorph.image_source_eq_target, Set.mem_image]
  refine ⟨p, mem_localHomeomorphAt_source, ?_⟩
  rw [localHomeomorphAt_eq_quotientMk]

variable (G p) in
/-- A chosen local inverse for the quotient map `Quotient.mk : M → M⧸G` at a point `p : M`. -/
def localInverseAt : OpenPartialHomeomorph (orbitRel.Quotient G M) M :=
  (localHomeomorphAt G p).symm

/-- The equivalence class `⟦p⟧` lies in the source of `localInverseAt p`. -/
lemma mem_localInverseAt_source : ⟦p⟧ ∈ (localInverseAt G p).source := by
  simp [localInverseAt, mem_localHomeomorphAt_target]

/-- If a point `k` lies on the source of `localHomeomorphAt p` and its class `⟦k⟧` lies on the
source of `localInverseAt p`, then `localInverseAt p` sends `⟦k⟧` back to its representative `k`. -/
lemma localInverseAt_apply_other {k : M}
    (h : k ∈ (localHomeomorphAt G p).source) (h' : ⟦k⟧ ∈ (localInverseAt G p).source) :
    localInverseAt G p ⟦k⟧ = k := by
  refine (localHomeomorphAt G p).injOn ?_ h ?_
  · simp [localInverseAt, (localHomeomorphAt G p).map_target h']
  · simp [localInverseAt, (localHomeomorphAt G p).right_inv h', localHomeomorphAt_eq_quotientMk]

/-- The local inverse at `p` sends the class `⟦p⟧` back to `p`. -/
lemma localInverseAt_apply_self : localInverseAt G p ⟦p⟧ = p :=
  localInverseAt_apply_other mem_localHomeomorphAt_source mem_localInverseAt_source

end QuotientMk

end
