/-
Copyright (c) 2026 Ziyan Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ziyan Wei, Anatole Dedecker
-/
module

public import Mathlib.Topology.Maps.Strict.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Strict Group Homomorphisms

-/

@[expose] public section

open Function Set Topology QuotientGroup

namespace MonoidHom

variable {G H G' H' : Type*} [Group G'] [Group H'] [Group G] [Group H] (f : G →* H) (g : G' →* H')
  [TopologicalSpace G] [TopologicalSpace H]

/-- A group homomorphism is strict if and only if its `rangeRestrict` is an open quotient map. -/
@[to_additive] protected lemma isStrictMap_iff_isEmbedding_kerLift :
    IsStrictMap f ↔ IsEmbedding (kerLift f) := by
  -- Note: `G ⧸ MonoidHom.ker f` and `G ⧸ Setoid.ker f` are not definitionally equal, so
  -- using `Topology.isStrictMap_iff_isEmbedding_kerLift` is too painful here.
  simp_rw [isEmbedding_iff_isStrictMap_injective, kerLift_injective, and_true,
    (isQuotientMap_mk _).isStrictMap_iff]
  rfl

/-- A group homomorphism is strict if and only if its `rangeRestrict` is an open quotient map. -/
@[to_additive] protected lemma isStrictMap_iff_isHomeomorph_quotientKerEquivRange :
    IsStrictMap f ↔ IsHomeomorph (quotientKerEquivRange f) := by
  -- Note: `G ⧸ MonoidHom.ker f` and `G ⧸ Setoid.ker f` are not definitionally equal, so
  -- using `Topology.isStrictMap_iff_isHomeomorph_quotientKerEquivRange` is too painful here.
  simp_rw [isHomeomorph_iff_isStrictMap_bijective, EquivLike.bijective, and_true,
    (isQuotientMap_mk _).isStrictMap_iff, IsEmbedding.subtypeVal.isStrictMap_iff]
  rfl

variable {f} in
noncomputable def _root_.ContinuousMulEquiv.quotientKerEquivRange (hf : IsStrictMap f) :
    G ⧸ f.ker ≃ₜ* f.range where
  toMulEquiv := QuotientGroup.quotientKerEquivRange f
  __ := (f.isStrictMap_iff_isHomeomorph_quotientKerEquivRange.mp hf).homeomorph

variable [IsTopologicalGroup G]

/-- A group homomorphism is strict if and only if its `rangeRestrict` is an open quotient map. -/
@[to_additive] protected lemma isStrictMap_iff_isOpenQuotientMap_rangeRestrict :
    IsStrictMap f ↔ IsOpenQuotientMap f.rangeRestrict := by
  rw [isOpenQuotientMap_iff_isQuotientMap]
  rfl

variable {f g} [TopologicalSpace G'] [IsTopologicalGroup G'] [TopologicalSpace H']

/-- The product (in the sense of `Prod.map`) of group homomorphisms is strict if and only if each
of the morphisms is strict. -/
@[to_additive isStrictMap_prodMap_iff] protected lemma isStrictMap_prodMap_iff :
    IsStrictMap (f.prodMap g) ↔ IsStrictMap f ∧ IsStrictMap g := by
  simp_rw [MonoidHom.isStrictMap_iff_isOpenQuotientMap_rangeRestrict]
  let Φ : (f.prodMap g).range ≃ₜ f.range × g.range :=
    (Homeomorph.setCongr (by simp [Subgroup.coe_prod])).trans (Homeomorph.Set.prod _ _)
  have eq : Φ ∘ (f.prodMap g).rangeRestrict = f.rangeRestrict.prodMap g.rangeRestrict := rfl
  rw [← Φ.comp_isOpenQuotientMap_iff, eq, MonoidHom.coe_prodMap, isOpenQuotientMap_prodMap_iff]

/-- The product (in the sense of `Prod.map`) of strict group homomorphisms is strict -/
@[to_additive isStrictMap_prodMap] protected lemma isStrictMap_prodMap (hf : IsStrictMap f)
    (hg : IsStrictMap g) : IsStrictMap (f.prodMap g) :=
  MonoidHom.isStrictMap_prodMap_iff.mpr ⟨hf, hg⟩

-- TODO Add the lemma `isStrictMap_piMap` once `MonoidHom.piMap` has been defined.

end MonoidHom
