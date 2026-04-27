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

noncomputable section

namespace QuotientMk

open MulAction

/-- If a group `G` acts properly discontinuously on a topological space `M`, the quotient map
`Quotient.mk : M → M⧸G` is a local homeomorphism. -/
lemma isLocalHomeomorph_of_properlyDiscontinuousSMul :
    IsLocalHomeomorph (Quotient.mk _ : M → orbitRel.Quotient G M) :=
  isCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isLocalHomeomorph

end QuotientMk

end
