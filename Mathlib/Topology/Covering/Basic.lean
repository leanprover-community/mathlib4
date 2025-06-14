/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.IsLocalHomeomorph

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

open Bundle Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] (f : E → X) (s : Set X)

/-- A point `x : X` is evenly covered by `f : E → X` if `x` has an evenly covered neighborhood. -/
def IsEvenlyCovered (x : X) (I : Type*) [TopologicalSpace I] :=
  DiscreteTopology I ∧ ∃ t : Trivialization I f, x ∈ t.baseSet

namespace IsEvenlyCovered

variable {f}

/-- If `x` is evenly covered by `f`, then we can construct a trivialization of `f` at `x`. -/
noncomputable def toTrivialization {x : X} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : Trivialization (f ⁻¹' {x}) f :=
  (Classical.choose h.2).transFiberHomeomorph
    ((Classical.choose h.2).preimageSingletonHomeomorph (Classical.choose_spec h.2)).symm

theorem mem_toTrivialization_baseSet {x : X} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : x ∈ h.toTrivialization.baseSet :=
  Classical.choose_spec h.2

theorem toTrivialization_apply {x : E} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f (f x) I) : (h.toTrivialization x).2 = ⟨x, rfl⟩ :=
  let e := Classical.choose h.2
  let h := Classical.choose_spec h.2
  let he := e.mk_proj_snd' h
  Subtype.ext
    ((e.toPartialEquiv.eq_symm_apply (e.mem_source.mpr h)
            (by rwa [he, e.mem_target, e.coe_fst (e.mem_source.mpr h)])).mpr
        he.symm).symm

protected theorem continuousAt {x : E} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f (f x) I) : ContinuousAt f x :=
  let e := h.toTrivialization
  e.continuousAt_proj (e.mem_source.mpr (mem_toTrivialization_baseSet h))

theorem to_isEvenlyCovered_preimage {x : X} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x (f ⁻¹' {x}) :=
  let ⟨_, h2⟩ := h
  ⟨((Classical.choose h2).preimageSingletonHomeomorph
          (Classical.choose_spec h2)).isEmbedding.discreteTopology,
    _, h.mem_toTrivialization_baseSet⟩

end IsEvenlyCovered

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMapOn :=
  ∀ x ∈ s, IsEvenlyCovered f x (f ⁻¹' {x})

namespace IsCoveringMapOn

theorem mk (F : X → Type*) [∀ x, TopologicalSpace (F x)] [hF : ∀ x, DiscreteTopology (F x)]
    (e : ∀ x ∈ s, Trivialization (F x) f) (h : ∀ (x : X) (hx : x ∈ s), x ∈ (e x hx).baseSet) :
    IsCoveringMapOn f s := fun x hx =>
  IsEvenlyCovered.to_isEvenlyCovered_preimage ⟨hF x, e x hx, h x hx⟩

variable {f} {s}

protected theorem continuousAt (hf : IsCoveringMapOn f s) {x : E} (hx : f x ∈ s) :
    ContinuousAt f x :=
  (hf (f x) hx).continuousAt

protected theorem continuousOn (hf : IsCoveringMapOn f s) : ContinuousOn f (f ⁻¹' s) :=
  continuousOn_of_forall_continuousAt fun _ => hf.continuousAt

protected theorem isLocalHomeomorphOn (hf : IsCoveringMapOn f s) :
    IsLocalHomeomorphOn f (f ⁻¹' s) := by
  refine IsLocalHomeomorphOn.mk f (f ⁻¹' s) fun x hx => ?_
  let e := (hf (f x) hx).toTrivialization
  have h := (hf (f x) hx).mem_toTrivialization_baseSet
  let he := e.mem_source.2 h
  refine
    ⟨e.toPartialHomeomorph.trans
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
          continuousOn_toFun := continuousOn_fst
          continuousOn_invFun := by fun_prop },
      ⟨he, by rwa [e.toPartialHomeomorph.symm_symm, e.proj_toFun x he],
        (hf (f x) hx).toTrivialization_apply⟩,
      fun p h => (e.proj_toFun p h.1).symm⟩

end IsCoveringMapOn

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMap :=
  ∀ x, IsEvenlyCovered f x (f ⁻¹' {x})

variable {f}

theorem isCoveringMap_iff_isCoveringMapOn_univ : IsCoveringMap f ↔ IsCoveringMapOn f Set.univ := by
  simp only [IsCoveringMap, IsCoveringMapOn, Set.mem_univ, forall_true_left]

protected theorem IsCoveringMap.isCoveringMapOn (hf : IsCoveringMap f) :
    IsCoveringMapOn f Set.univ :=
  isCoveringMap_iff_isCoveringMapOn_univ.mp hf

variable (f)

namespace IsCoveringMap

theorem mk (F : X → Type*) [∀ x, TopologicalSpace (F x)] [∀ x, DiscreteTopology (F x)]
    (e : ∀ x, Trivialization (F x) f) (h : ∀ x, x ∈ (e x).baseSet) : IsCoveringMap f :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr
    (IsCoveringMapOn.mk f Set.univ F (fun x _ => e x) fun x _ => h x)

variable {f}
variable (hf : IsCoveringMap f)
include hf

protected theorem continuous : Continuous f :=
  continuous_iff_continuousOn_univ.mpr hf.isCoveringMapOn.continuousOn

protected theorem isLocalHomeomorph : IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr hf.isCoveringMapOn.isLocalHomeomorphOn

protected theorem isOpenMap : IsOpenMap f :=
  hf.isLocalHomeomorph.isOpenMap

theorem isQuotientMap (hf' : Function.Surjective f) : IsQuotientMap f :=
  hf.isOpenMap.isQuotientMap hf.continuous hf'

@[deprecated (since := "2024-10-22")]
alias quotientMap := isQuotientMap

protected theorem isSeparatedMap : IsSeparatedMap f :=
  fun e₁ e₂ he hne ↦ by
    obtain ⟨_, t, he₁⟩ := hf (f e₁)
    have he₂ := he₁; simp_rw [he] at he₂; rw [← t.mem_source] at he₁ he₂
    refine ⟨t.source ∩ (Prod.snd ∘ t) ⁻¹' {(t e₁).2}, t.source ∩ (Prod.snd ∘ t) ⁻¹' {(t e₂).2},
      ?_, ?_, ⟨he₁, rfl⟩, ⟨he₂, rfl⟩, Set.disjoint_left.mpr fun x h₁ h₂ ↦ hne (t.injOn he₁ he₂ ?_)⟩
    iterate 2
      exact t.continuousOn_toFun.isOpen_inter_preimage t.open_source
        (continuous_snd.isOpen_preimage _ <| isOpen_discrete _)
    refine Prod.ext ?_ (h₁.2.symm.trans h₂.2)
    rwa [t.proj_toFun e₁ he₁, t.proj_toFun e₂ he₂]

variable {A} [TopologicalSpace A] {s : Set A} {g g₁ g₂ : A → E}

theorem eq_of_comp_eq [PreconnectedSpace A] (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (he : f ∘ g₁ = f ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ :=
  hf.isSeparatedMap.eq_of_comp_eq hf.isLocalHomeomorph.isLocallyInjective h₁ h₂ he a ha

theorem const_of_comp [PreconnectedSpace A] (cont : Continuous g)
    (he : ∀ a a', f (g a) = f (g a')) (a a') : g a = g a' :=
  hf.isSeparatedMap.const_of_comp hf.isLocalHomeomorph.isLocallyInjective cont he a a'

theorem eqOn_of_comp_eqOn (hs : IsPreconnected s) (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
    (he : s.EqOn (f ∘ g₁) (f ∘ g₂)) {a : A} (has : a ∈ s) (ha : g₁ a = g₂ a) : s.EqOn g₁ g₂ :=
  hf.isSeparatedMap.eqOn_of_comp_eqOn hf.isLocalHomeomorph.isLocallyInjective hs h₁ h₂ he has ha

theorem constOn_of_comp (hs : IsPreconnected s) (cont : ContinuousOn g s)
    (he : ∀ a ∈ s, ∀ a' ∈ s, f (g a) = f (g a'))
    {a a'} (ha : a ∈ s) (ha' : a' ∈ s) : g a = g a' :=
  hf.isSeparatedMap.constOn_of_comp hf.isLocalHomeomorph.isLocallyInjective hs cont he ha ha'

end IsCoveringMap

variable {f}

protected theorem IsFiberBundle.isCoveringMap {F : Type*} [TopologicalSpace F] [DiscreteTopology F]
    (hf : ∀ x : X, ∃ e : Trivialization F f, x ∈ e.baseSet) : IsCoveringMap f :=
  IsCoveringMap.mk f (fun _ => F) (fun x => Classical.choose (hf x)) fun x =>
    Classical.choose_spec (hf x)

protected theorem FiberBundle.isCoveringMap {F : Type*} {E : X → Type*} [TopologicalSpace F]
    [DiscreteTopology F] [TopologicalSpace (Bundle.TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] : IsCoveringMap (π F E) :=
  IsFiberBundle.isCoveringMap fun x => ⟨trivializationAt F E x, mem_baseSet_trivializationAt F E x⟩

/-- Let `f : E → X` be a (not necessarily continuous) map between topological spaces, and let
  `V` be an open subset of `X`. Suppose that there is a family `U` of disjoint subsets of `E`
  that covers `f⁻¹(V)` such that for every `i`, (1) `f` is injective on `U_i`, (2) `V` is
  contained in the image `f(U_i)`, and (3) the open sets in `V` are determined by their preimages
  in `U_i`. Then `f` admits a `Trivialization` over the base set `V`. -/
noncomputable def IsOpen.trivialization_discrete (hE : Nonempty E ∨ f.Surjective)
    {ι} [Nonempty ι] [TopologicalSpace ι] [DiscreteTopology ι] (U : ι → Set E) (V : Set X)
    (open_V : IsOpen V) (open_iff : ∀ i {W}, W ⊆ V → (IsOpen W ↔ IsOpen (f ⁻¹' W ∩ U i)))
    (inj : ∀ i, (U i).InjOn f) (surj : ∀ i, (U i).SurjOn f V)
    (disjoint : ∀ {i j}, i ≠ j → Disjoint (U i) (U j)) (exhaustive : f ⁻¹' V ⊆ ⋃ i, U i) :
    Trivialization ι f := by
  have exhaustive' := exhaustive
  simp_rw [Set.subset_def, Set.mem_iUnion] at exhaustive
  choose idx idx_U using exhaustive
  choose inv inv_U f_inv using surj
  classical
  let F : PartialEquiv E (X × ι) := by
    refine
    { toFun := fun e ↦ (f e, if he : f e ∈ V then idx e he else Classical.arbitrary ι),
      invFun := fun x ↦ if hx : x.1 ∈ V then inv x.2 hx else
        if h : Nonempty E then Classical.arbitrary E else (hE.resolve_left h x.1).choose,
      source := f ⁻¹' V,
      target := V ×ˢ Set.univ,
      map_source' := fun x hx ↦ ⟨hx, trivial⟩
      map_target' := fun x ⟨hx, _⟩ ↦ by rw [dif_pos hx]; apply (f_inv _ hx).symm ▸ hx,
      left_inv' := fun e he ↦ ?_,
      right_inv' := fun x hx ↦ ?_ }
    · change f e ∈ V at he; simp_rw [dif_pos he]
      exact inj _ (inv_U _ he) (idx_U e he) (f_inv _ _)
    · rw [dif_pos hx.1]
      refine Prod.ext (f_inv _ hx.1) ?_
      rw [dif_pos ((f_inv _ hx.1).symm ▸ hx.1)]
      by_contra h; exact (disjoint h).le_bot ⟨idx_U _ _, inv_U _ _⟩
  have open_preim {W} (hWV: W ⊆ V) (open_W : IsOpen W) : IsOpen (f ⁻¹' W) := by
    convert isOpen_iUnion (fun i ↦ (open_iff i hWV).mp open_W)
    rw [← Set.inter_iUnion, eq_comm, Set.inter_eq_left]
    exact (Set.preimage_mono hWV).trans exhaustive'
  have open_source : IsOpen F.source := open_preim subset_rfl open_V
  have cont_f : ContinuousOn f F.source := (continuousOn_open_iff open_source).mpr
    fun W open_W ↦ open_preim Set.inter_subset_left (open_V.inter open_W)
  refine
  { toPartialEquiv := F,
    open_source := open_source,
    open_target := open_V.prod isOpen_univ,
    continuousOn_toFun := cont_f.prodMk <| continuousOn_of_forall_continuousAt fun e he ↦
      continuous_const (y := idx e he) |>.continuousAt.congr <| mem_nhds_iff.mpr
        ⟨U (idx e he) ∩ F.source, fun e' he' ↦ ?_, ?_, idx_U e he, he⟩
    continuousOn_invFun := continuousOn_prod_of_discrete_right.mpr fun i ↦ ?_,
    baseSet := V,
    open_baseSet := open_V,
    source_eq := rfl,
    target_eq := rfl,
    proj_toFun := fun _ _ ↦ rfl }
  · by_contra h; apply (disjoint h).le_bot
    · dsimp only; rw [dif_pos (by exact he'.2)]; exact ⟨he'.1, idx_U _ _⟩
  · rwa [Set.inter_comm, ← open_iff _ subset_rfl]
  · simp_rw [F, Set.prodMk_mem_set_prod_eq, Set.mem_univ, and_true]
    refine (continuousOn_open_iff open_V).mpr fun W open_W ↦ ?_
    rw [open_iff i Set.inter_subset_left]
    convert ((open_iff i subset_rfl).mp open_V).inter open_W using 1
    ext e; refine and_right_comm.trans (and_congr_right fun ⟨hV, hU⟩ ↦ ?_)
    rw [Set.mem_preimage, dif_pos hV, inj i (inv_U i _) hU (f_inv i _)]
