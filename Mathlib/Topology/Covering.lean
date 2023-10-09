/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.IsLocallyHomeomorph
import Mathlib.Topology.FiberBundle.Basic

#align_import topology.covering from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-!
# Covering Maps

This file defines covering maps.

## Main definitions

* `IsEvenlyCovered f x I`: A point `x` is evenly covered by `f : E → X` with fiber `I` if `I` is
  discrete and there is a `Trivialization` of `f` at `x` with fiber `I`.
* `IsCoveringMap f`: A function `f : E → X` is a covering map if every point `x` is evenly
  covered by `f` with fiber `f ⁻¹' {x}`. The fibers `f ⁻¹' {x}` must be discrete, but if `X` is
  not connected, then the fibers `f ⁻¹' {x}` are not necessarily isomorphic. Also, `f` is not
  assumed to be surjective, so the fibers are even allowed to be empty.
-/


open Bundle

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] (f : E → X) (s : Set X)

/-- A point `x : X` is evenly covered by `f : E → X` if `x` has an evenly covered neighborhood. -/
def IsEvenlyCovered (x : X) (I : Type*) [TopologicalSpace I] :=
  DiscreteTopology I ∧ ∃ t : Trivialization I f, x ∈ t.baseSet
#align is_evenly_covered IsEvenlyCovered

namespace IsEvenlyCovered

variable {f}

/-- If `x` is evenly covered by `f`, then we can construct a trivialization of `f` at `x`. -/
noncomputable def toTrivialization {x : X} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : Trivialization (f ⁻¹' {x}) f :=
  (Classical.choose h.2).transFiberHomeomorph
    ((Classical.choose h.2).preimageSingletonHomeomorph (Classical.choose_spec h.2)).symm
#align is_evenly_covered.to_trivialization IsEvenlyCovered.toTrivialization

theorem mem_toTrivialization_baseSet {x : X} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : x ∈ h.toTrivialization.baseSet :=
  Classical.choose_spec h.2
#align is_evenly_covered.mem_to_trivialization_base_set IsEvenlyCovered.mem_toTrivialization_baseSet

theorem toTrivialization_apply {x : E} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f (f x) I) : (h.toTrivialization x).2 = ⟨x, rfl⟩ :=
  let e := Classical.choose h.2
  let h := Classical.choose_spec h.2
  let he := e.mk_proj_snd' h
  Subtype.ext
    ((e.toLocalEquiv.eq_symm_apply (e.mem_source.mpr h)
            (by rwa [he, e.mem_target, e.coe_fst (e.mem_source.mpr h)])).mpr
        he.symm).symm
#align is_evenly_covered.to_trivialization_apply IsEvenlyCovered.toTrivialization_apply

protected theorem continuousAt {x : E} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f (f x) I) : ContinuousAt f x :=
  let e := h.toTrivialization
  e.continuousAt_proj (e.mem_source.mpr (mem_toTrivialization_baseSet h))
#align is_evenly_covered.continuous_at IsEvenlyCovered.continuousAt

theorem to_isEvenlyCovered_preimage {x : X} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x (f ⁻¹' {x}) :=
  let ⟨_, h2⟩ := h
  ⟨((Classical.choose h2).preimageSingletonHomeomorph
          (Classical.choose_spec h2)).embedding.discreteTopology,
    _, h.mem_toTrivialization_baseSet⟩
#align is_evenly_covered.to_is_evenly_covered_preimage IsEvenlyCovered.to_isEvenlyCovered_preimage

end IsEvenlyCovered

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMapOn :=
  ∀ x ∈ s, IsEvenlyCovered f x (f ⁻¹' {x})
#align is_covering_map_on IsCoveringMapOn

namespace IsCoveringMapOn

theorem mk (F : X → Type*) [∀ x, TopologicalSpace (F x)] [hF : ∀ x, DiscreteTopology (F x)]
    (e : ∀ x ∈ s, Trivialization (F x) f) (h : ∀ (x : X) (hx : x ∈ s), x ∈ (e x hx).baseSet) :
    IsCoveringMapOn f s := fun x hx =>
  IsEvenlyCovered.to_isEvenlyCovered_preimage ⟨hF x, e x hx, h x hx⟩
#align is_covering_map_on.mk IsCoveringMapOn.mk

variable {f} {s}

protected theorem continuousAt (hf : IsCoveringMapOn f s) {x : E} (hx : f x ∈ s) :
    ContinuousAt f x :=
  (hf (f x) hx).continuousAt
#align is_covering_map_on.continuous_at IsCoveringMapOn.continuousAt

protected theorem continuousOn (hf : IsCoveringMapOn f s) : ContinuousOn f (f ⁻¹' s) :=
  ContinuousAt.continuousOn fun _ => hf.continuousAt
#align is_covering_map_on.continuous_on IsCoveringMapOn.continuousOn

protected theorem isLocallyHomeomorphOn (hf : IsCoveringMapOn f s) :
    IsLocallyHomeomorphOn f (f ⁻¹' s) := by
  refine' IsLocallyHomeomorphOn.mk f (f ⁻¹' s) fun x hx => _
  let e := (hf (f x) hx).toTrivialization
  have h := (hf (f x) hx).mem_toTrivialization_baseSet
  let he := e.mem_source.2 h
  refine'
    ⟨e.toLocalHomeomorph.trans
        { toFun := fun p => p.1
          invFun := fun p => ⟨p, x, rfl⟩
          source := e.baseSet ×ˢ ({⟨x, rfl⟩} : Set (f ⁻¹' {f x}))
          target := e.baseSet
          open_source :=
            e.open_baseSet.prod (singletons_open_iff_discrete.2 (hf (f x) hx).1 ⟨x, rfl⟩)
          open_target := e.open_baseSet
          map_source' := fun p => And.left
          map_target' := fun p hp => ⟨hp, rfl⟩
          left_inv' := fun p hp => Prod.ext rfl hp.2.symm
          right_inv' := fun p _ => rfl
          continuous_toFun := continuous_fst.continuousOn
          continuous_invFun := (continuous_id'.prod_mk continuous_const).continuousOn },
      ⟨he, by rwa [e.toLocalHomeomorph.symm_symm, e.proj_toFun x he],
        (hf (f x) hx).toTrivialization_apply⟩,
      fun p h => (e.proj_toFun p h.1).symm⟩
#align is_covering_map_on.is_locally_homeomorph_on IsCoveringMapOn.isLocallyHomeomorphOn

end IsCoveringMapOn

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMap :=
  ∀ x, IsEvenlyCovered f x (f ⁻¹' {x})
#align is_covering_map IsCoveringMap

variable {f}

theorem isCoveringMap_iff_isCoveringMapOn_univ : IsCoveringMap f ↔ IsCoveringMapOn f Set.univ := by
  simp only [IsCoveringMap, IsCoveringMapOn, Set.mem_univ, forall_true_left]
#align is_covering_map_iff_is_covering_map_on_univ isCoveringMap_iff_isCoveringMapOn_univ

protected theorem IsCoveringMap.isCoveringMapOn (hf : IsCoveringMap f) :
    IsCoveringMapOn f Set.univ :=
  isCoveringMap_iff_isCoveringMapOn_univ.mp hf
#align is_covering_map.is_covering_map_on IsCoveringMap.isCoveringMapOn

variable (f)

namespace IsCoveringMap

theorem mk (F : X → Type*) [∀ x, TopologicalSpace (F x)] [∀ x, DiscreteTopology (F x)]
    (e : ∀ x, Trivialization (F x) f) (h : ∀ x, x ∈ (e x).baseSet) : IsCoveringMap f :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr
    (IsCoveringMapOn.mk f Set.univ F (fun x _ => e x) fun x _ => h x)
#align is_covering_map.mk IsCoveringMap.mk

variable {f}

protected theorem continuous (hf : IsCoveringMap f) : Continuous f :=
  continuous_iff_continuousOn_univ.mpr hf.isCoveringMapOn.continuousOn
#align is_covering_map.continuous IsCoveringMap.continuous

protected theorem isLocallyHomeomorph (hf : IsCoveringMap f) : IsLocallyHomeomorph f :=
  isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univ.mpr hf.isCoveringMapOn.isLocallyHomeomorphOn
#align is_covering_map.is_locally_homeomorph IsCoveringMap.isLocallyHomeomorph

protected theorem isOpenMap (hf : IsCoveringMap f) : IsOpenMap f :=
  hf.isLocallyHomeomorph.isOpenMap
#align is_covering_map.is_open_map IsCoveringMap.isOpenMap

protected theorem quotientMap (hf : IsCoveringMap f) (hf' : Function.Surjective f) :
    QuotientMap f :=
  hf.isOpenMap.to_quotientMap hf.continuous hf'
#align is_covering_map.quotient_map IsCoveringMap.quotientMap

end IsCoveringMap

variable {f}

protected theorem IsFiberBundle.isCoveringMap {F : Type*} [TopologicalSpace F] [DiscreteTopology F]
    (hf : ∀ x : X, ∃ e : Trivialization F f, x ∈ e.baseSet) : IsCoveringMap f :=
  IsCoveringMap.mk f (fun _ => F) (fun x => Classical.choose (hf x)) fun x =>
    Classical.choose_spec (hf x)
#align is_fiber_bundle.is_covering_map IsFiberBundle.isCoveringMap

protected theorem FiberBundle.isCoveringMap {F : Type*} {E : X → Type*} [TopologicalSpace F]
    [DiscreteTopology F] [TopologicalSpace (Bundle.TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] : IsCoveringMap (π F E) :=
  IsFiberBundle.isCoveringMap fun x => ⟨trivializationAt F E x, mem_baseSet_trivializationAt F E x⟩
#align fiber_bundle.is_covering_map FiberBundle.isCoveringMap

/-- Let `f : E → X` be a (not necessarily continuous) map between topological spaces, and let
  `V` be an open subset of `X`. Suppose that there is a family `U` of disjoint subsets of `E`
  that covers `f⁻¹(V)` such that for every `i`, (1) `f` is injective on `U_i`, (2) `V` is
  contained in the image `f(U_i), and (3) the open sets in `V` are determined by their preimages
  in `U_i`. Then `f` admits a `Trivialization` over the base set `V`. -/
noncomputable def IsOpen.trivialization_discrete (hE : Nonempty E ∨ f.Surjective)
    {ι} [Nonempty ι] [t : TopologicalSpace ι] [d : DiscreteTopology ι] (U : ι → Set E) (V : Set X)
    (open_V : IsOpen V) (open_iff : ∀ i {W}, W ⊆ V → (IsOpen W ↔ IsOpen (f ⁻¹' W ∩ U i)))
    (inj : ∀ i, (U i).InjOn f) (surj : ∀ i, (U i).SurjOn f V)
    (disjoint : ∀ {i j}, i ≠ j → Disjoint (U i) (U j)) (exhaustive : f ⁻¹' V ⊆ ⋃ i, U i) :
    Trivialization ι f := by
  have exhaustive' := exhaustive
  simp_rw [Set.subset_def, Set.mem_iUnion] at exhaustive
  choose idx idx_U using exhaustive
  choose inv inv_U f_inv using surj
  classical
  let F : LocalEquiv E (X × ι); refine
  { toFun := fun e ↦ (f e, if he : f e ∈ V then idx e he else Classical.arbitrary ι),
    invFun := fun x ↦ if hx : x.1 ∈ V then inv x.2 hx else
      if h : Nonempty E then Classical.arbitrary E else (hE.resolve_left h x.1).choose,
    source := f ⁻¹' V,
    target := V ×ˢ Set.univ,
    map_source' := fun x hx ↦ ⟨hx, trivial⟩
    map_target' := fun x ⟨hx, _⟩ ↦ by dsimp only; rw [dif_pos hx]; apply (f_inv _ hx).symm ▸ hx,
    left_inv' := fun e he ↦ ?_,
    right_inv' := fun x hx ↦ ?_ }
  · change f e ∈ V at he; dsimp only; simp_rw [dif_pos he]
    exact inj _ (inv_U _ he) (idx_U e he) (f_inv _ _)
  · dsimp only; rw [dif_pos hx.1]
    refine Prod.ext (f_inv _ hx.1) ?_
    dsimp only; rw [dif_pos ((f_inv _ hx.1).symm ▸ hx.1)]
    by_contra h; exact (disjoint h).le_bot ⟨idx_U _ _, inv_U _ _⟩
  have open_preim : ∀ {W}, W ⊆ V → IsOpen W → IsOpen (f ⁻¹' W)
  · intro W hWV hoW
    convert isOpen_iUnion (fun i ↦ (open_iff i hWV).mp hoW)
    rw [← Set.inter_iUnion, eq_comm, Set.inter_eq_left]
    exact (Set.preimage_mono hWV).trans exhaustive'
  have open_source : IsOpen F.source := open_preim subset_rfl open_V
  have cont_f : ContinuousOn f F.source := (continuousOn_open_iff open_source).mpr
    fun W open_W ↦ open_preim (V.inter_subset_left W) (open_V.inter open_W)
  refine
  { toLocalEquiv := F,
    open_source := open_source,
    open_target := open_V.prod isOpen_univ,
    continuous_toFun := cont_f.prod <| ContinuousAt.continuousOn fun e he ↦
      continuous_const (b := idx e he) |>.continuousAt.congr <| mem_nhds_iff.mpr
        ⟨U (idx e he) ∩ F.source, fun e' he' ↦ ?_, ?_, idx_U e he, he⟩
    continuous_invFun := continuousOn_prod_of_discrete_right.mpr fun i ↦ ?_,
    baseSet := V,
    open_baseSet := open_V,
    source_eq := rfl,
    target_eq := rfl,
    proj_toFun := fun _ _ ↦ rfl }
  · by_contra h; apply (disjoint h).le_bot
    dsimp only; erw [dif_pos he'.2]; exact ⟨he'.1, idx_U _ _⟩
  · rwa [Set.inter_comm, ← open_iff _ subset_rfl]
  · simp_rw [Set.prod_mk_mem_set_prod_eq, Set.mem_univ, and_true]
    refine (continuousOn_open_iff open_V).mpr fun W open_W ↦ ?_
    rw [open_iff i (V.inter_subset_left _)]
    convert ((open_iff i subset_rfl).mp open_V).inter open_W using 1
    ext e; refine and_right_comm.trans (and_congr_right fun ⟨hV, hU⟩ ↦ ?_)
    rw [Set.mem_preimage, dif_pos hV, inj i (inv_U i _) hU (f_inv i _)]

namespace QuotientMap

open Topology

variable {G} [t : TopologicalSpace G] [d : DiscreteTopology G]
  [Group G] [MulAction G E] [ContinuousConstSMul G E]
  {p : E → X} (hp : QuotientMap p) (hpG : ∀ {e₁ e₂}, p e₁ = p e₂ ↔ e₁ ∈ MulAction.orbit G e₂)

/-- If a group `G` acts on a space `E` and `U` is an open subset disjoint from all other
  `G`-translates of itself, and `p` is a quotient map by this action, then `p` admits a
  `Trivialization` over the base set `p(U)`. -/
@[to_additive] noncomputable def trivialization_of_mulAction (U : Set E) (open_U : IsOpen U)
    (disjoint : ∀ g : G, (g • ·) '' U ∩ U ≠ ∅ → g = 1) : Trivialization G p := by
  have pGE : ∀ (g : G) e, p (g • e) = p e := fun g e ↦ hpG.mpr ⟨g, rfl⟩
  simp_rw [← Set.nonempty_iff_ne_empty] at disjoint
  have preim_im : p ⁻¹' (p '' U) = ⋃ g : G, (g • ·) ⁻¹' U
  · ext e; refine ⟨fun ⟨e', heU, he⟩ ↦ ?_, ?_⟩
    · obtain ⟨g, rfl⟩ := hpG.mp he; exact ⟨_, ⟨g, rfl⟩, heU⟩
    · intro ⟨_, ⟨g, rfl⟩, hg⟩; exact ⟨_, hg, pGE g e⟩
  refine IsOpen.trivialization_discrete (Or.inr hp.surjective) (fun g ↦ (g • ·) ⁻¹' U) (p '' U)
    ?_ (fun g W hWU ↦ ⟨fun hoW ↦ (hoW.preimage hp.continuous).inter (open_U.preimage <|
      continuous_const_smul g), fun isOpen ↦ hp.isOpen_preimage.mp ?_⟩) (fun g e₁ h₁ e₂ h₂ he ↦ ?_)
    ?_ (fun {g₁ g₂} hne ↦ disjoint_iff_inf_le.mpr fun e ⟨h₁, h₂⟩ ↦ hne <|
      mul_inv_eq_one.mp (disjoint _ ⟨_, ⟨_, h₂, ?_⟩, h₁⟩)) preim_im.subset
  · rw [← hp.isOpen_preimage, preim_im]
    exact isOpen_iUnion fun g ↦ open_U.preimage (continuous_const_smul g)
  · convert isOpen_iUnion fun g : G ↦ isOpen.preimage (continuous_const_smul g)
    ext e; refine ⟨fun hW ↦ ?_, ?_⟩
    · obtain ⟨e', he', hpe⟩ := hWU hW
      obtain ⟨g', rfl⟩ := hpG.mp hpe
      refine ⟨_, ⟨g⁻¹ * g', rfl⟩, ?_, ?_⟩
      · apply Set.mem_of_eq_of_mem (pGE _ e) hW
      · apply Set.mem_of_eq_of_mem _ he'; dsimp only; rw [mul_smul, smul_inv_smul]
    · rintro ⟨_, ⟨g, rfl⟩, hW, -⟩; apply Set.mem_of_eq_of_mem (pGE _ e).symm hW
  · rw [← pGE g, ← pGE g e₂] at he; obtain ⟨g', he⟩ := hpG.mp he
    rw [← smul_left_cancel_iff g, ← he, disjoint g' ⟨_, ⟨_, h₂, he⟩, h₁⟩]; apply one_smul
  · rintro g x ⟨e, hU, rfl⟩; refine ⟨g⁻¹ • e, ?_, pGE _ e⟩; apply (smul_inv_smul g e).symm ▸ hU
  · dsimp only; rw [mul_smul, inv_smul_smul]

@[to_additive] lemma isCoveringMapOn_of_mulAction
    (disjoint : ∀ e : E, ∃ U ∈ 𝓝 e, ∀ g : G, (g • ·) '' U ∩ U ≠ ∅ → g • e = e) :
    IsCoveringMapOn p (p '' {e | MulAction.stabilizer G e = ⊥}) := by
  letI : TopologicalSpace G := ⊥; have : DiscreteTopology G := ⟨rfl⟩
  suffices : ∀ x ∈ p '' {e | MulAction.stabilizer G e = ⊥}, ∃ t : Trivialization G p, x ∈ t.baseSet
  · choose t ht using this; exact IsCoveringMapOn.mk _ _ (fun _ ↦ G) t ht
  rintro x ⟨e, he, rfl⟩
  obtain ⟨U, heU, hU⟩ := disjoint e
  refine ⟨hp.trivialization_of_mulAction hpG (interior U) isOpen_interior
    fun g hg ↦ ?_, e, mem_interior_iff_mem_nhds.mpr heU, rfl⟩
  rw [← Subgroup.mem_bot, ← he]; apply hU; contrapose! hg; exact Set.subset_eq_empty
    (Set.inter_subset_inter (Set.image_subset _ interior_subset) interior_subset) hg

@[to_additive] lemma isCoveringMap_of_mulAction
    (disjoint : ∀ e : E, ∃ U ∈ 𝓝 e, ∀ g : G, (g • ·) '' U ∩ U ≠ ∅ → g = 1) : IsCoveringMap p :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr <| by
    convert ← hp.isCoveringMapOn_of_mulAction hpG fun e ↦ ?_
    · refine Set.eq_univ_of_forall fun x ↦ ?_
      obtain ⟨e, rfl⟩ := hp.surjective x
      refine ⟨e, (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦ ?_, rfl⟩
      obtain ⟨U, hU, hGU⟩ := disjoint e
      have := mem_of_mem_nhds hU
      apply hGU g (Set.nonempty_iff_ne_empty.mp ⟨e, ⟨e, this, hg⟩, this⟩)
    · obtain ⟨U, hU, hGU⟩ := disjoint e
      refine ⟨U, hU, fun g hg ↦ ?_⟩; rw [hGU g hg, one_smul]

@[to_additive] lemma isCoveringMapOn_of_properlyDiscontinuousSmul
    [ProperlyDiscontinuousSMul G E] [WeaklyLocallyCompactSpace E] [T2Space E] :
    IsCoveringMapOn p (p '' {e | MulAction.stabilizer G e = ⊥}) :=
  hp.isCoveringMapOn_of_mulAction hpG (ProperlyDiscontinuousSMul.disjoint_image_nhds G)

@[to_additive] lemma _root_.isCoveringMapOn_quotient_of_properlyDiscontinuousSmul
    [ProperlyDiscontinuousSMul G E] [WeaklyLocallyCompactSpace E] [T2Space E] :
    IsCoveringMapOn (Quotient.mk _) <|
      (Quotient.mk <| MulAction.orbitRel G E) '' {e | MulAction.stabilizer G e = ⊥} :=
  quotientMap_quotient_mk'.isCoveringMapOn_of_properlyDiscontinuousSmul Quotient.eq''

end QuotientMap

@[to_additive] lemma Subgroup.isCoveringMap {G} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] (S : Subgroup G) [DiscreteTopology S] :
    IsCoveringMap (QuotientGroup.mk (s := S)) := by
  obtain ⟨U, hU, disj⟩ := S.disjoint_nhds_of_discrete
  refine quotientMap_quotient_mk'.isCoveringMap_of_mulAction (G := S.op) Quotient.eq'' fun g ↦ ?_
  refine ⟨_, singleton_mul_mem_nhds_of_nhds_one g hU, fun ⟨⟨s⟩, hS⟩ hs ↦ Subtype.ext <|
    MulOpposite.unop_injective <| disj _ hS <| Or.inr ?_⟩
  simp_rw [← Set.nonempty_iff_ne_empty] at hs ⊢
  obtain ⟨_, ⟨_, ⟨_, x, rfl, hx, rfl⟩, rfl⟩, g, y, rfl, hy, he⟩ := hs
  exact ⟨y, ⟨x, hx, mul_left_cancel (he.trans <| mul_assoc _ _ _).symm⟩, hy⟩

theorem isCoveringMap_coe_addCircle (p : ℝ) : IsCoveringMap ((↑) : ℝ → AddCircle p) :=
  AddSubgroup.isCoveringMap _
