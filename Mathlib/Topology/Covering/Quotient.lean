/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Covering.Basic

/-!
# Covering maps to quotients by free and properly discontinuous group actions
-/

@[expose] public section

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] (f : E → X)
variable (G : Type*) [Group G] [MulAction G E]

open Topology

/-- A function from a topological space `E` with an action by a discrete group to another
topological space `X` is a quotient covering map if it is a quotient map, the action is
continuous and transitive on fibers, and every point of `E` has a neighborhood whose translates
by the group elements are pairwise disjoint. -/
structure IsAddQuotientCoveringMap (G) [AddGroup G] [AddAction G E] : Prop
    extends IsQuotientMap f, ContinuousConstVAdd G E where
  apply_eq_iff_mem_orbit {e₁ e₂} : f e₁ = f e₂ ↔ e₁ ∈ AddAction.orbit G e₂
  disjoint (e : E) : ∃ U ∈ 𝓝 e, ∀ g : G, ((g +ᵥ ·) '' U ∩ U).Nonempty → g = 0

/-- A function from a topological space `E` with an action by a discrete group to another
topological space `X` is a quotient covering map if it is a quotient map, the action is
continuous and transitive on fibers, and every point of `E` has a neighborhood whose translates
by the group elements are pairwise disjoint. -/
@[mk_iff, to_additive]
structure IsQuotientCoveringMap : Prop extends IsQuotientMap f, ContinuousConstSMul G E where
  apply_eq_iff_mem_orbit {e₁ e₂} : f e₁ = f e₂ ↔ e₁ ∈ MulAction.orbit G e₂
  disjoint (e : E) : ∃ U ∈ 𝓝 e, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1

attribute [to_additive] isQuotientCoveringMap_iff

namespace IsQuotientCoveringMap

variable {f G} (hf : IsQuotientCoveringMap f G)
include hf

@[to_additive] theorem subgroup_congr (S S' : Subgroup G) (eq : S = S') :
    IsQuotientCoveringMap f S ↔ IsQuotientCoveringMap f S' := by rw [eq]

@[to_additive] protected theorem map_smul (g : G) {e : E} : f (g • e) = f e :=
  hf.apply_eq_iff_mem_orbit.mpr ⟨g, rfl⟩

/-- The group action on the domain of a quotient covering map is free. -/
@[to_additive] theorem isCancelSMul : IsCancelSMul G E where
  right_cancel' g g' e eq := by
    have ⟨U, heU, hU⟩ := hf.disjoint e
    simpa [inv_mul_eq_one, eq_comm] using hU (g'⁻¹ * g)
      ⟨e, ⟨e, mem_of_mem_nhds heU, by simpa [mul_smul, inv_smul_eq_iff]⟩, mem_of_mem_nhds heU⟩

@[to_additive] theorem homeomorph_comp {Y} [TopologicalSpace Y]
    (φ : X ≃ₜ Y) : IsQuotientCoveringMap (φ ∘ f) G where
  __ := φ.isQuotientMap.comp hf.toIsQuotientMap
  continuous_const_smul := hf.continuous_const_smul
  apply_eq_iff_mem_orbit := by simpa using @hf.apply_eq_iff_mem_orbit
  disjoint := hf.disjoint

omit hf in
@[to_additive (attr := simp)] theorem homeomorph_comp_iff {Y} [TopologicalSpace Y]
    (φ : X ≃ₜ Y) : IsQuotientCoveringMap (φ ∘ f) G ↔ IsQuotientCoveringMap f G where
  mp h := by convert h.homeomorph_comp φ.symm; ext; simp
  mpr h := h.homeomorph_comp φ

/-- Fibers of a quotient covering map by a group G is a G-torsor. -/
@[to_additive /-- Fibers of a quotient covering map by an additive group G is a G-torsor. -/]
noncomputable def fiberEquivGroup {x : X} (e : f ⁻¹' {x}) : f ⁻¹' {x} ≃ G :=
  have := hf.isCancelSMul
  .symm <| .ofBijective (fun g ↦ ⟨g • e, (hf.map_smul g).trans e.2⟩)
    ⟨fun _ _ eq ↦ IsCancelSMul.right_cancel _ _ e.1 congr($eq), fun e' ↦
      have ⟨g, eq⟩ := hf.apply_eq_iff_mem_orbit.mp (e'.2.trans e.2.symm); ⟨g, Subtype.ext eq⟩⟩

@[simp] theorem fiberEquivGroup_self {x : X} (e : f ⁻¹' {x}) : hf.fiberEquivGroup e e = 1 :=
  (Equiv.apply_eq_iff_eq_symm_apply _).mpr <| Subtype.ext (one_smul ..).symm

theorem fiberEquivGroup_smul_self {x : X} (e : f ⁻¹' {x}) {e' : f ⁻¹' {x}} :
    hf.fiberEquivGroup e e' • e = e'.1 :=
  congr($((hf.fiberEquivGroup e).symm_apply_apply e'))

/-- A quotient covering map `f` induces a permutation action on each fiber. -/
@[simps!] def toPermFiber (x : X) : G →* Equiv.Perm (f ⁻¹' {x}) :=
  SubMulAction.mulAction ⟨f ⁻¹' {x}, fun g _ h ↦ (hf.map_smul g).trans h⟩ |>.toPermHom

theorem toPermFiber_ext (x : X) (e : f ⁻¹' {x}) {g g' : G}
    (eq : hf.toPermFiber x g e = hf.toPermFiber x g' e) : g = g' :=
  have := hf.isCancelSMul
  IsCancelSMul.right_cancel _ _ e.1 congr($eq)

theorem toPermFiber_injective (x : X) : Function.Injective (hf.toPermFiber x) :=
  have ⟨e, he⟩ := hf.surjective x
  fun _ _ eq ↦ hf.toPermFiber_ext x ⟨e, he⟩ congr($eq _)

theorem toPermFiber_transitive {x : X} (e e' : f ⁻¹' {x}) : ∃ g : G, hf.toPermFiber x g e = e' :=
  have ⟨g, eq⟩ := hf.apply_eq_iff_mem_orbit.mp (e'.2.trans e.2.symm)
  ⟨g, Subtype.ext eq⟩

end IsQuotientCoveringMap

namespace Topology.IsQuotientMap

variable {f G} (hf : IsQuotientMap f)
include hf

section MulAction

open Bundle

variable [ContinuousConstSMul G E]
variable (hfG : ∀ {e₁ e₂}, f e₁ = f e₂ ↔ e₁ ∈ MulAction.orbit G e₂)
include hfG

/-- If a group `G` acts on a space `E` and `U` is an open subset disjoint from all other
`G`-translates of itself, and `p` is a quotient map by this action, then `p` admits a
`Bundle.Trivialization` over the base set `p(U)`. -/
@[to_additive (attr := simps! source target baseSet)
/-- If a group `G` acts on a space `E` and `U` is an open subset disjoint from all
other `G`-translates of itself, and `p` is a quotient map by this action, then `p` admits a
`Bundle.Trivialization` over the base set `p(U)`. -/]
noncomputable def trivializationOfSMulDisjoint [TopologicalSpace G] [DiscreteTopology G]
    (U : Set E) (open_U : IsOpen U) (disjoint : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    Trivialization G f := by
  have pGE (g : G) e : f (g • e) = f e := hfG.mpr ⟨g, rfl⟩
  have preim_im : f ⁻¹' (f '' U) = ⋃ g : G, (g • ·) ⁻¹' U := by
    ext e; refine ⟨fun ⟨e', heU, he⟩ ↦ ?_, ?_⟩
    · obtain ⟨g, rfl⟩ := hfG.mp he; exact ⟨_, ⟨g, rfl⟩, heU⟩
    · intro ⟨_, ⟨g, rfl⟩, hg⟩; exact ⟨_, hg, pGE g e⟩
  have : Nonempty (X → E) := ⟨Function.surjInv hf.surjective⟩
  refine IsOpen.trivializationDiscrete (fun g ↦ (g • ·) ⁻¹' U) (f '' U)
    ?_ (fun g W hWU ↦ ⟨fun hoW ↦ (hoW.preimage hf.continuous).inter (open_U.preimage <|
      continuous_const_smul g), fun isOpen ↦ hf.isOpen_preimage.mp ?_⟩) (fun g e₁ h₁ e₂ h₂ he ↦ ?_)
    ?_ (fun {g₁ g₂} hne ↦ disjoint_iff_inf_le.mpr fun e ⟨h₁, h₂⟩ ↦ hne <|
      mul_inv_eq_one.mp (disjoint _ ⟨_, ⟨_, h₂, ?_⟩, h₁⟩)) preim_im.subset
  · rw [← hf.isOpen_preimage, preim_im]
    exact isOpen_iUnion fun g ↦ open_U.preimage (continuous_const_smul g)
  · convert isOpen_iUnion fun g : G ↦ isOpen.preimage (continuous_const_smul g)
    ext e; refine ⟨fun hW ↦ ?_, ?_⟩
    · have ⟨e', he', hfe⟩ := hWU hW
      obtain ⟨g', rfl⟩ := hfG.mp hfe
      refine ⟨_, ⟨g⁻¹ * g', rfl⟩, ?_, ?_⟩
      · apply Set.mem_of_eq_of_mem (pGE _ e) hW
      · apply Set.mem_of_eq_of_mem _ he'; simp_rw [mul_smul, smul_inv_smul]
    · rintro ⟨_, ⟨g, rfl⟩, hW, -⟩; apply Set.mem_of_eq_of_mem (pGE _ e).symm hW
  · rw [← pGE g, ← pGE g e₂] at he
    have ⟨g', he⟩ := hfG.mp he
    rw [← smul_left_cancel_iff g, ← he, disjoint g' ⟨_, ⟨_, h₂, he⟩, h₁⟩]
    apply one_smul
  · rintro g x ⟨e, hU, rfl⟩; exact ⟨g⁻¹ • e, by apply (smul_inv_smul g e).symm ▸ hU, pGE _ e⟩
  · simp_rw [mul_smul, inv_smul_smul]

@[to_additive] lemma isCoveringMapOn_of_smul_disjoint
    (disjoint : ∀ e : E, ∃ U ∈ 𝓝 e, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g • e = e) :
    IsCoveringMapOn f (f '' {e | MulAction.stabilizer G e = ⊥}) := by
  letI : TopologicalSpace G := ⊥; have : DiscreteTopology G := ⟨rfl⟩
  suffices ∀ x ∈ f '' {e | MulAction.stabilizer G e = ⊥}, ∃ t : Trivialization G f, x ∈ t.baseSet by
    choose t ht using this; exact IsCoveringMapOn.mk _ _ _ _ fun x ↦ ht x x.2
  rintro x ⟨e, he, rfl⟩
  have ⟨U, heU, hU⟩ := disjoint e
  refine ⟨hf.trivializationOfSMulDisjoint hfG (interior U) isOpen_interior
    fun g hg ↦ ?_, e, mem_interior_iff_mem_nhds.mpr heU, rfl⟩
  rw [← Subgroup.mem_bot, ← he]
  exact hU _ (hg.mono (by grw [interior_subset]))

section ProperlyDiscontinuousSMul

variable [ProperlyDiscontinuousSMul G E] [LocallyCompactSpace E] [T2Space E]

@[to_additive] lemma isCoveringMapOn_of_properlyDiscontinuousSMul :
    IsCoveringMapOn f (f '' {e | MulAction.stabilizer G e = ⊥}) :=
  hf.isCoveringMapOn_of_smul_disjoint hfG
    (ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G)

@[to_additive] lemma isQuotientCoveringMap_of_properlyDiscontinuousSMul [IsCancelSMul G E] :
    IsQuotientCoveringMap f G where
  __ := hf
  apply_eq_iff_mem_orbit := hfG
  disjoint e :=
    have ⟨U, heU, hU⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G e
    ⟨U, heU, fun g hg ↦ isCancelSMul_iff_eq_one_of_smul_eq.mp ‹_› _ _ (hU g hg)⟩

omit hf hfG

@[to_additive] lemma _root_.isCoveringMapOn_quotientMk_of_properlyDiscontinuousSMul :
    IsCoveringMapOn (Quotient.mk _) <|
      (Quotient.mk <| MulAction.orbitRel G E) '' {e | MulAction.stabilizer G e = ⊥} :=
  isQuotientMap_quotient_mk'.isCoveringMapOn_of_properlyDiscontinuousSMul Quotient.eq''

@[to_additive] lemma _root_.isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    [IsCancelSMul G E] : IsQuotientCoveringMap (Quotient.mk <| MulAction.orbitRel G E) G :=
  isQuotientMap_quotient_mk'.isQuotientCoveringMap_of_properlyDiscontinuousSMul Quotient.eq''

end ProperlyDiscontinuousSMul

end MulAction

@[to_additive] lemma isQuotientCoveringMap_of_subgroup [Group E] [IsTopologicalGroup E]
    (G : Subgroup E) (hG : IsDiscrete (G : Set E)) (hfG : ∀ {e₁ e₂}, f e₁ = f e₂ ↔ e₂ * e₁⁻¹ ∈ G) :
    IsQuotientCoveringMap f G where
  __ := hf
  apply_eq_iff_mem_orbit := hfG.trans QuotientGroup.rightRel_apply.symm
  disjoint e := have ⟨U, hU, _, disj⟩ := hG.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty
    ⟨_, mul_singleton_mem_nhds_of_nhds_one e hU, fun s hs ↦ Subtype.ext <| disj _ s.2 <| by
      obtain ⟨_, ⟨_, ⟨x, hx, _, rfl, rfl⟩, rfl⟩, y, hy, g, rfl, he⟩ := hs
      exact ⟨y, ⟨x, hx, mul_right_cancel ((mul_assoc ..).trans he.symm)⟩, hy⟩⟩

@[to_additive] lemma isQuotientCoveringMap_of_subgroupOp [Group E] [IsTopologicalGroup E]
    (G : Subgroup E) (hG : IsDiscrete (G : Set E)) (hfG : ∀ {e₁ e₂}, f e₁ = f e₂ ↔ e₁⁻¹ * e₂ ∈ G) :
    IsQuotientCoveringMap f G.op where
  __ := hf
  apply_eq_iff_mem_orbit := hfG.trans QuotientGroup.leftRel_apply.symm
  disjoint e := have ⟨U, hU, _, disj⟩ := hG.exists_nhds_eq_one_of_image_mulRight_inter_nonempty
    ⟨_, singleton_mul_mem_nhds_of_nhds_one e hU, fun ⟨⟨s⟩, hS⟩ hs ↦ Subtype.ext <|
        MulOpposite.unop_injective <| disj _ hS <| by
      obtain ⟨_, ⟨_, ⟨_, rfl, x, hx, rfl⟩, rfl⟩, g, rfl, y, hy, he⟩ := hs
      exact ⟨y, ⟨x, hx, mul_left_cancel (he.trans <| mul_assoc ..).symm⟩, hy⟩⟩

omit hf in
@[to_additive] lemma isQuotientCoveringMap_of_isDiscrete_ker_monoidHom [Group E]
    [IsTopologicalGroup E] [Group X] {f : E →* X} (hf : IsQuotientMap f)
    (disc : IsDiscrete (f.ker : Set E)) :
    IsQuotientCoveringMap f f.ker :=
  hf.isQuotientCoveringMap_of_subgroup f.ker disc fun {_ _} ↦ by
    rw [eq_comm, ← mul_inv_eq_one, ← map_inv, ← map_mul]; rfl

end Topology.IsQuotientMap

@[to_additive] lemma Subgroup.isQuotientCoveringMap {G} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (S : Subgroup G) (hS : IsDiscrete (S : Set G)) :
    IsQuotientCoveringMap (QuotientGroup.mk (s := S)) S.op :=
  isQuotientMap_quotient_mk'.isQuotientCoveringMap_of_subgroupOp S hS <|
    Quotient.eq''.trans QuotientGroup.leftRel_apply

@[to_additive] lemma Subgroup.isQuotientCoveringMap_of_comm {G} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (S : Subgroup G) (hS : IsDiscrete (S : Set G)) :
    IsQuotientCoveringMap (QuotientGroup.mk (s := S)) S :=
  isQuotientMap_quotient_mk'.isQuotientCoveringMap_of_subgroup S hS <| Quotient.eq''.trans <|
    QuotientGroup.leftRel_apply.trans <| by rw [mul_comm]

namespace IsQuotientCoveringMap

@[to_additive] lemma isCoveringMap (h : IsQuotientCoveringMap f G) :
    IsCoveringMap f :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr <| by
    have := h.toContinuousConstSMul
    convert ← h.isCoveringMapOn_of_smul_disjoint h.apply_eq_iff_mem_orbit fun e ↦ ?_
    · refine Set.eq_univ_of_forall fun x ↦ ?_
      obtain ⟨e, rfl⟩ := h.surjective x
      have ⟨U, hU, hGU⟩ := h.disjoint e
      replace hU := mem_of_mem_nhds hU
      exact ⟨e, (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦ hGU g (⟨e, ⟨e, hU, hg⟩, hU⟩), rfl⟩
    · have ⟨U, hU, hGU⟩ := h.disjoint e
      exact ⟨U, hU, fun g hg ↦ by rw [hGU g hg, one_smul]⟩

@[to_additive] theorem isOpenQuotientMap (h : IsQuotientCoveringMap f G) :
    IsOpenQuotientMap f where
  surjective := h.surjective
  continuous := h.isCoveringMap.continuous
  isOpenMap := h.isCoveringMap.isOpenMap

end IsQuotientCoveringMap

@[to_additive] theorem isQuotientCoveringMap_iff_isCoveringMap_and :
    IsQuotientCoveringMap f G ↔ IsCoveringMap f ∧ f.Surjective ∧ ContinuousConstSMul G E ∧
      IsCancelSMul G E ∧ ∀ {e₁ e₂}, f e₁ = f e₂ ↔ e₁ ∈ MulAction.orbit G e₂ where
  mp h := have := h.toContinuousConstSMul
    ⟨h.isCoveringMap, h.surjective, this, h.isCancelSMul, h.apply_eq_iff_mem_orbit⟩
  mpr h := (isQuotientCoveringMap_iff ..).mpr ⟨h.1.isQuotientMap h.2.1, h.2.2.1, h.2.2.2.2, fun e ↦
    have ⟨_, U, heU, hU, hfU, H, hH⟩ := h.1 (f e)
    ⟨Subtype.val '' (Prod.snd ∘ H ⁻¹' {(H ⟨e, heU⟩).2}), (hfU.isOpenMap_subtype_val _ <|
        (isOpen_discrete _).preimage <| by fun_prop).mem_nhds ⟨⟨e, heU⟩, rfl, rfl⟩, fun g ↦ by
      rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, y, hy, eq⟩
      have := h.2.2.2.1
      apply IsCancelSMul.right_cancel _ _ x.1
      simp_rw [← eq, one_smul]
      refine congr($(H.injective <| Prod.ext (Subtype.ext ?_) <| hy.trans hx.symm))
      simp_rw [hH]
      exact h.2.2.2.2.mpr ⟨_, eq.symm⟩⟩⟩
