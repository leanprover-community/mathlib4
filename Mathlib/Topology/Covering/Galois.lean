/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Covering.Basic

/-!
# Galois Covering Maps

This file constructs of them from free and properly discontinuous group actions.

TODO: show the construction yields Galois covering maps (to be defined) when the action is
on a path-connected space.
-/

namespace Topology.IsQuotientMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}
  {G : Type*} [Group G] (hf : IsQuotientMap f)
include hf

section MulAction

variable [MulAction G E] [ContinuousConstSMul G E]
  (hfG : ∀ {e₁ e₂}, f e₁ = f e₂ ↔ e₁ ∈ MulAction.orbit G e₂)
include hfG

/-- If a group `G` acts on a space `E` and `U` is an open subset disjoint from all other
  `G`-translates of itself, and `p` is a quotient map by this action, then `p` admits a
  `Trivialization` over the base set `p(U)`. -/
@[to_additive "If a group `G` acts on a space `E` and `U` is an open subset disjoint from all
  other `G`-translates of itself, and `p` is a quotient map by this action, then `p` admits a
  `Trivialization` over the base set `p(U)`."]
noncomputable def trivializationOfSMulDisjoint [TopologicalSpace G] [DiscreteTopology G]
    (U : Set E) (open_U : IsOpen U) (disjoint : ∀ g : G, (g • ·) '' U ∩ U ≠ ∅ → g = 1) :
    Trivialization G f := by
  have pGE : ∀ (g : G) e, f (g • e) = f e := fun g e ↦ hfG.mpr ⟨g, rfl⟩
  simp_rw [← Set.nonempty_iff_ne_empty] at disjoint
  have preim_im : f ⁻¹' (f '' U) = ⋃ g : G, (g • ·) ⁻¹' U := by
    ext e; refine ⟨fun ⟨e', heU, he⟩ ↦ ?_, ?_⟩
    · obtain ⟨g, rfl⟩ := hfG.mp he; exact ⟨_, ⟨g, rfl⟩, heU⟩
    · intro ⟨_, ⟨g, rfl⟩, hg⟩; exact ⟨_, hg, pGE g e⟩
  refine IsOpen.trivialization_discrete (Or.inr hf.surjective) (fun g ↦ (g • ·) ⁻¹' U) (f '' U)
    ?_ (fun g W hWU ↦ ⟨fun hoW ↦ (hoW.preimage hf.continuous).inter (open_U.preimage <|
      continuous_const_smul g), fun isOpen ↦ hf.isOpen_preimage.mp ?_⟩) (fun g e₁ h₁ e₂ h₂ he ↦ ?_)
    ?_ (fun {g₁ g₂} hne ↦ disjoint_iff_inf_le.mpr fun e ⟨h₁, h₂⟩ ↦ hne <|
      mul_inv_eq_one.mp (disjoint _ ⟨_, ⟨_, h₂, ?_⟩, h₁⟩)) preim_im.subset
  · rw [← hf.isOpen_preimage, preim_im]
    exact isOpen_iUnion fun g ↦ open_U.preimage (continuous_const_smul g)
  · convert isOpen_iUnion fun g : G ↦ isOpen.preimage (continuous_const_smul g)
    ext e; refine ⟨fun hW ↦ ?_, ?_⟩
    · obtain ⟨e', he', hfe⟩ := hWU hW
      obtain ⟨g', rfl⟩ := hfG.mp hfe
      refine ⟨_, ⟨g⁻¹ * g', rfl⟩, ?_, ?_⟩
      · apply Set.mem_of_eq_of_mem (pGE _ e) hW
      · apply Set.mem_of_eq_of_mem _ he'; dsimp only; rw [mul_smul, smul_inv_smul]
    · rintro ⟨_, ⟨g, rfl⟩, hW, -⟩; apply Set.mem_of_eq_of_mem (pGE _ e).symm hW
  · rw [← pGE g, ← pGE g e₂] at he; obtain ⟨g', he⟩ := hfG.mp he
    rw [← smul_left_cancel_iff g, ← he, disjoint g' ⟨_, ⟨_, h₂, he⟩, h₁⟩]; apply one_smul
  · rintro g x ⟨e, hU, rfl⟩; refine ⟨g⁻¹ • e, ?_, pGE _ e⟩; apply (smul_inv_smul g e).symm ▸ hU
  · dsimp only; rw [mul_smul, inv_smul_smul]

@[to_additive] lemma isCoveringMapOn_of_smul_disjoint
    (disjoint : ∀ e : E, ∃ U ∈ 𝓝 e, ∀ g : G, (g • ·) '' U ∩ U ≠ ∅ → g • e = e) :
    IsCoveringMapOn f (f '' {e | MulAction.stabilizer G e = ⊥}) := by
  letI : TopologicalSpace G := ⊥; have : DiscreteTopology G := ⟨rfl⟩
  suffices ∀ x : f '' {e | MulAction.stabilizer G e = ⊥}, ∃ t : Trivialization G f, x.1 ∈ t.baseSet
    by choose t ht using this; exact IsCoveringMapOn.mk _ _ (fun _ ↦ G) t ht
  rintro ⟨_, e, he, rfl⟩
  obtain ⟨U, heU, hU⟩ := disjoint e
  refine ⟨hf.trivializationOfSMulDisjoint hfG (interior U) isOpen_interior
    fun g hg ↦ ?_, e, mem_interior_iff_mem_nhds.mpr heU, rfl⟩
  rw [← Subgroup.mem_bot, ← he]; apply hU; contrapose! hg; exact Set.subset_eq_empty
    (Set.inter_subset_inter (Set.image_subset _ interior_subset) interior_subset) hg

@[to_additive] lemma isCoveringMap_of_smul_disjoint
    (disjoint : ∀ e : E, ∃ U ∈ 𝓝 e, ∀ g : G, (g • ·) '' U ∩ U ≠ ∅ → g = 1) : IsCoveringMap f :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr <| by
    convert ← hf.isCoveringMapOn_of_smul_disjoint hfG fun e ↦ ?_
    · refine Set.eq_univ_of_forall fun x ↦ ?_
      obtain ⟨e, rfl⟩ := hf.surjective x
      obtain ⟨U, hU, hGU⟩ := disjoint e
      replace hU := mem_of_mem_nhds hU
      exact ⟨e, (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦
        hGU g (Set.nonempty_iff_ne_empty.mp ⟨e, ⟨e, hU, hg⟩, hU⟩), rfl⟩
    · obtain ⟨U, hU, hGU⟩ := disjoint e
      refine ⟨U, hU, fun g hg ↦ ?_⟩; rw [hGU g hg, one_smul]

section ProperlyDiscontinuousSMul

variable [ProperlyDiscontinuousSMul G E] [WeaklyLocallyCompactSpace E] [T2Space E]

@[to_additive] lemma isCoveringMapOn_of_properlyDiscontinuousSMul :
    IsCoveringMapOn f (f '' {e | MulAction.stabilizer G e = ⊥}) :=
  hf.isCoveringMapOn_of_smul_disjoint hfG (ProperlyDiscontinuousSMul.disjoint_image_nhds G)

@[to_additive] lemma isCoveringMap_of_properlyDiscontinuousSMul
    (free : ∀ (g : G) (e : E), g • e = e → g = 1) : IsCoveringMap f := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  convert ← hf.isCoveringMapOn_of_properlyDiscontinuousSMul hfG
  refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
  obtain ⟨e, rfl⟩ := hf.surjective x
  exact ⟨e, eq_bot_iff.mpr fun g hg ↦ free g e hg, rfl⟩

omit hf hfG

@[to_additive] lemma _root_.isCoveringMapOn_quotient_of_properlyDiscontinuousSMul :
    IsCoveringMapOn (Quotient.mk _) <|
      (Quotient.mk <| MulAction.orbitRel G E) '' {e | MulAction.stabilizer G e = ⊥} :=
  isQuotientMap_quotient_mk'.isCoveringMapOn_of_properlyDiscontinuousSMul Quotient.eq''

@[to_additive] lemma _root_.isCoveringMap_quotient_of_properlyDiscontinuousSMul
    (free : ∀ (g : G) (e : E), g • e = e → g = 1) :
    IsCoveringMap (Quotient.mk <| MulAction.orbitRel G E) :=
  isQuotientMap_quotient_mk'.isCoveringMap_of_properlyDiscontinuousSMul Quotient.eq'' free

end ProperlyDiscontinuousSMul

end MulAction

@[to_additive] lemma isCoveringMap_of_subgroup [Group E] [IsTopologicalGroup E] (G : Subgroup E)
    [DiscreteTopology G] (hfG : ∀ {e₁ e₂}, f e₁ = f e₂ ↔ e₁⁻¹ * e₂ ∈ G) :
    IsCoveringMap f := by
  obtain ⟨U, hU, disj⟩ := G.disjoint_nhds_of_discrete
  refine hf.isCoveringMap_of_smul_disjoint (G := G.op) (fun {_ _} ↦ ?_) fun e ↦ ?_
  · rw [hfG, ← QuotientGroup.leftRel_apply]; rfl
  refine ⟨_, singleton_mul_mem_nhds_of_nhds_one e hU, fun ⟨⟨s⟩, hS⟩ hs ↦ Subtype.ext <|
    MulOpposite.unop_injective <| disj _ hS <| Or.inr ?_⟩
  simp_rw [← Set.nonempty_iff_ne_empty] at hs ⊢
  obtain ⟨_, ⟨_, ⟨_, rfl, x, hx, rfl⟩, rfl⟩, g, rfl, y, hy, he⟩ := hs
  exact ⟨y, ⟨x, hx, mul_left_cancel (he.trans <| mul_assoc _ _ _).symm⟩, hy⟩

omit hf in
@[to_additive] lemma isCoveringMap_of_discrete_ker_monoidHom [Group E] [IsTopologicalGroup E]
    [Group X] {f : E →* X} (hf : IsQuotientMap f) (d : DiscreteTopology f.ker) : IsCoveringMap f :=
  hf.isCoveringMap_of_subgroup f.ker fun {_ _} ↦ by rw [← inv_mul_eq_one, ← map_inv, ← map_mul]; rfl

end Topology.IsQuotientMap

@[to_additive] lemma Subgroup.isCoveringMap {G} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (S : Subgroup G) [DiscreteTopology S] :
    IsCoveringMap (QuotientGroup.mk (s := S)) :=
  isQuotientMap_quotient_mk'.isCoveringMap_of_subgroup S fun {_ _} ↦
    Quotient.eq''.trans QuotientGroup.leftRel_apply
