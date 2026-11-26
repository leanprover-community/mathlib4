/-
Copyright (c) 2026 Ziyan Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ziyan Wei, Anatole Dedecker
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Maps.Strict.Basic

/-!
# Strict Group Homomorphisms

In this file, we study homomorphisms of topological groups which are *strict* in the sense
of `Topology.IsStrictMap`.

We provide specialized variations of general facts about `IsStrictMap` for convenience.
But we also show that strict group homomorphisms enjoy some extra properties compared to general
strict maps. Namely, we provide:
* `isStrictMap_iff_isOpenQuotientMap_rangeRestrict`: `f` is a strict group homomorphism if
  and only if the `rangeRestrict` of `f` is an *open* quotient map. This ultimately relies
  on `MonoidHom.isOpenQuotientMap_of_isQuotientMap`.
* `isStrictMap_prodMap`: The product (in the sense of `MonoidHom.prodMap`) of strict group
  homomorphisms is strict. Note that this result is false for general maps; what makes things work
  in our context is that, unlike `IsQuotientMap`, `IsOpenQuotientMap` is stable under product.
-/

@[expose] public section

open Topology QuotientGroup

namespace MonoidHom

variable {G H G' H' : Type*} [Group G'] [Group H'] [Group G] [Group H] {f : G →* H} {g : G' →* H'}
  [TopologicalSpace G] [TopologicalSpace H]

/-- A group homomorphism is strict if and only if its `QuotientGroup.kerLift` is an embedding. -/
@[to_additive /-- An additive group homomorphism is strict if and only if its
`QuotientAddGroup.kerLift` is an embedding. -/]
protected lemma isStrictMap_iff_isEmbedding_kerLift :
    IsStrictMap f ↔ IsEmbedding (kerLift f) := by
  -- Note: `G ⧸ MonoidHom.ker f` and `G ⧸ Setoid.ker f` are not definitionally equal, so
  -- using `Topology.isStrictMap_iff_isEmbedding_kerLift` is too painful here.
  simp_rw [isEmbedding_iff_isStrictMap_injective, kerLift_injective, and_true,
    (isQuotientMap_mk _).isStrictMap_iff]
  rfl

/-- A group homomorphism is strict if and only if the canonical isomorphism
`G ⧸ f.ker ≃ f.range` is a homeomorphism. -/
@[to_additive /-- An additive group homomorphism is strict if and only if the canonical isomorphism
`G ⧸ f.ker ≃ f.range` is a homeomorphism. -/]
protected lemma isStrictMap_iff_isHomeomorph_quotientKerEquivRange :
    IsStrictMap f ↔ IsHomeomorph (quotientKerEquivRange f) := by
  -- Note: `G ⧸ MonoidHom.ker f` and `G ⧸ Setoid.ker f` are not definitionally equal, so
  -- using `Topology.isStrictMap_iff_isHomeomorph_quotientKerEquivRange` is too painful here.
  simp_rw [isHomeomorph_iff_isStrictMap_bijective, EquivLike.bijective, and_true,
    (isQuotientMap_mk _).isStrictMap_iff, IsEmbedding.subtypeVal.isStrictMap_iff]
  rfl

/-- The isomorphism of topological groups `G ⧸ f.ker ≃ f.range` given by a strict group
homomorphism `f`. This is an avatar of the first isomorphism theorem. -/
@[to_additive /-- The isomorphism of topological additive groups `G ⧸ f.ker ≃ f.range` given by a
strict additive group homomorphism `f`. This is an avatar of the first isomorphism theorem. -/]
noncomputable def _root_.ContinuousMulEquiv.quotientKerEquivRange
    (hf : IsStrictMap f) : G ⧸ f.ker ≃ₜ* f.range where
  toMulEquiv := QuotientGroup.quotientKerEquivRange f
  __ := (f.isStrictMap_iff_isHomeomorph_quotientKerEquivRange.mp hf).homeomorph

variable [IsTopologicalGroup G]

/-- A group homomorphism is strict if and only if its `rangeRestrict` is an open quotient map. -/
@[to_additive /-- An additive group homomorphism is strict if and only if its `rangeRestrict` is an
open quotient map. -/]
protected lemma isStrictMap_iff_isOpenQuotientMap_rangeRestrict :
    IsStrictMap f ↔ IsOpenQuotientMap f.rangeRestrict := by
  rw [isOpenQuotientMap_iff_isQuotientMap]
  rfl

variable [TopologicalSpace G'] [IsTopologicalGroup G'] [TopologicalSpace H']

/-- The product (in the sense of `MonoidHom.prodMap`) of group homomorphisms is strict if and only
if both homomorphisms are strict. -/
@[to_additive isStrictMap_prodMap_iff /-- The product (in the sense of `AddMonoidHom.prodMap`) of
additive group homomorphisms is strict if and only if both homomorphisms are strict. -/]
protected lemma isStrictMap_prodMap_iff :
    IsStrictMap (f.prodMap g) ↔ IsStrictMap f ∧ IsStrictMap g := by
  simp_rw [MonoidHom.isStrictMap_iff_isOpenQuotientMap_rangeRestrict]
  let Φ : (f.prodMap g).range ≃ₜ f.range × g.range :=
    (Homeomorph.setCongr (by simp [Subgroup.coe_prod])).trans (Homeomorph.Set.prod _ _)
  have eq : Φ ∘ (f.prodMap g).rangeRestrict = f.rangeRestrict.prodMap g.rangeRestrict := rfl
  rw [← Φ.comp_isOpenQuotientMap_iff, eq, MonoidHom.coe_prodMap, isOpenQuotientMap_prodMap_iff]

/-- The product (in the sense of `MonoidHom.prodMap`) of strict group homomorphisms is strict. -/
@[to_additive isStrictMap_prodMap /-- The product (in the sense of `AddMonoidHom.prodMap`) of strict
additive group homomorphisms is strict. -/]
protected lemma isStrictMap_prodMap (hf : IsStrictMap f)
    (hg : IsStrictMap g) : IsStrictMap (f.prodMap g) :=
  MonoidHom.isStrictMap_prodMap_iff.mpr ⟨hf, hg⟩

-- TODO: Add the lemma `isStrictMap_piMap` once `MonoidHom.piMap` has been defined.

end MonoidHom
