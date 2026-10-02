/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Yury Kudryashov
-/
module

public import Mathlib.Data.Option.Basic
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.SigmaLocallyFinite

/-!
# Paracompact topological spaces

A topological space `X` is said to be paracompact if every open covering of `X` admits a locally
finite refinement.

The definition requires that each set of the new covering is a subset of one of the sets of the
initial covering. However, one can ensure that each open covering `s : ι → Set X` admits a *precise*
locally finite refinement, i.e., an open covering `t : ι → Set X` with the same index set such that
`∀ i, t i ⊆ s i`, see lemma `precise_refinement`. We also provide a convenience lemma
`precise_refinement_set` that deals with open coverings of a closed subset of `X` instead of the
whole space.

We also prove the following facts.

* Every compact space is paracompact, see instance `paracompact_of_compact`.

* A locally compact sigma compact Hausdorff space is paracompact, see instance
  `paracompact_of_locallyCompact_sigmaCompact`. Moreover, we can choose a locally finite
  refinement with sets in a given collection of filter bases of `𝓝 x`, `x : X`, see
  `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis`. For example, in a proper metric space
  every open covering `⋃ i, s i` admits a refinement `⋃ i, Metric.ball (c i) (r i)`.

* Every paracompact Hausdorff space is normal. This statement is not an instance to avoid loops in
  the instance graph.

* Every `EMetricSpace` is a paracompact space, see instance `EMetric.instParacompactSpace` in
  `Topology/EMetricSpace/Paracompact`.

## TODO

Prove (some of) [Michael's theorems](https://ncatlab.org/nlab/show/Michael%27s+theorem).

## Tags

compact space, paracompact space, locally finite covering
-/

public section


open Set Filter Function

open Filter Topology

universe u v w

/-- A topological space is called paracompact, if every open covering of this space admits a locally
finite refinement. We use the same universe for all types in the definition to avoid creating a
class like `ParacompactSpace.{u v}`. Due to lemma `precise_refinement` below, every open covering
`s : α → Set X` indexed on `α : Type v` has a *precise* locally finite refinement, i.e., a locally
finite refinement `t : α → Set X` indexed on the same type such that each `∀ i, t i ⊆ s i`. -/
class ParacompactSpace (X : Type v) [TopologicalSpace X] : Prop where
  /-- Every open cover of a paracompact space assumes a locally finite refinement. -/
  locallyFinite_refinement :
    ∀ (α : Type v) (s : α → Set X), (∀ a, IsOpen (s a)) → (⋃ a, s a = univ) →
      ∃ (β : Type v) (t : β → Set X),
        (∀ b, IsOpen (t b)) ∧ (⋃ b, t b = univ) ∧ LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a

variable {ι : Type u} {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- Any open cover of a paracompact space has a locally finite *precise* refinement, that is,
one indexed on the same type with each open set contained in the corresponding original one. -/
theorem precise_refinement [ParacompactSpace X] (u : ι → Set X) (uo : ∀ a, IsOpen (u a))
    (uc : ⋃ i, u i = univ) : ∃ v : ι → Set X, (∀ a, IsOpen (v a)) ∧ ⋃ i, v i = univ ∧
    LocallyFinite v ∧ ∀ a, v a ⊆ u a := by
  -- Apply definition to `range u`, then turn existence quantifiers into functions using `choose`
  have := ParacompactSpace.locallyFinite_refinement (range u) (fun r ↦ (r : Set X))
    (forall_subtype_range_iff.2 uo) (by rwa [← sUnion_range, Subtype.range_coe])
  simp only [exists_subtype_range_iff, iUnion_eq_univ_iff] at this
  choose α t hto hXt htf ind hind using this
  choose t_inv ht_inv using hXt
  choose U hxU hU using htf
  -- Send each `i` to the union of `t a` over `a ∈ ind ⁻¹' {i}`
  refine ⟨fun i ↦ ⋃ (a : α) (_ : ind a = i), t a, ?_, ?_, ?_, ?_⟩
  · exact fun a ↦ isOpen_iUnion fun a ↦ isOpen_iUnion fun _ ↦ hto a
  · simp only [eq_univ_iff_forall, mem_iUnion]
    exact fun x ↦ ⟨ind (t_inv x), _, rfl, ht_inv _⟩
  · refine fun x ↦ ⟨U x, hxU x, ((hU x).image ind).subset ?_⟩
    simp only [subset_def, mem_iUnion, mem_ofPred_eq, Set.Nonempty, mem_inter_iff]
    rintro i ⟨y, ⟨a, rfl, hya⟩, hyU⟩
    exact mem_image_of_mem _ ⟨y, hya, hyU⟩
  · simp only [subset_def, mem_iUnion]
    rintro i x ⟨a, rfl, hxa⟩
    exact hind _ hxa

/-- In a paracompact space, every open covering of a closed set admits a locally finite refinement
indexed by the same type. -/
theorem precise_refinement_set [ParacompactSpace X] {s : Set X} (hs : IsClosed s) (u : ι → Set X)
    (uo : ∀ i, IsOpen (u i)) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, (∀ i, IsOpen (v i)) ∧ (s ⊆ ⋃ i, v i) ∧ LocallyFinite v ∧ ∀ i, v i ⊆ u i := by
  have uc : (iUnion fun i => Option.elim' sᶜ u i) = univ := by
    apply Subset.antisymm (subset_univ _)
    · simp_rw [← compl_union_self s, Option.elim', iUnion_option]
      apply union_subset_union_right sᶜ us
  rcases precise_refinement (Option.elim' sᶜ u) (Option.forall.2 ⟨isOpen_compl_iff.2 hs, uo⟩)
      uc with
    ⟨v, vo, vc, vf, vu⟩
  refine ⟨v ∘ some, fun i ↦ vo _, ?_, vf.comp_injective (Option.some_injective _), fun i ↦ vu _⟩
  · simp only [iUnion_option, ← compl_subset_iff_union] at vc
    exact Subset.trans (subset_compl_comm.1 <| vu Option.none) vc

theorem ParacompactSpace.of_hasBasis {ι : X → Sort*} {p : ∀ x, ι x → Prop} {s : ∀ x, ι x → Set X}
    (hb : ∀ x, (𝓝 x).HasBasis (p x) (s x))
    (h : ∀ f : (x : X) → ι x, (∀ x, p x (f x)) →
      ∃ (β : Type u) (t : β → Set X), (∀ b, IsOpen (t b)) ∧ (⋃ b, t b) = univ ∧ LocallyFinite t ∧
        ∀ b, ∃ x, t b ⊆ s x (f x)) : ParacompactSpace X where
  locallyFinite_refinement α S ho hu := by
    have := fun x ↦ (iUnion_eq_univ_iff.1 hu x).imp fun a ha ↦ (hb _).mem_iff.1 ((ho a).mem_nhds ha)
    choose a f hp hsub using this
    rcases h f hp with ⟨β, t, hto, ht, htf, hts⟩
    refine ⟨range t, Subtype.val, forall_subtype_range_iff.2 hto, ?_, htf.on_range,
      forall_subtype_range_iff.2 fun b ↦ ?_⟩
    · rwa [iUnion_subtype, biUnion_range]
    · rcases hts b with ⟨x, hx⟩
      exact ⟨_, hx.trans (hsub _)⟩

theorem Topology.IsClosedEmbedding.paracompactSpace [ParacompactSpace Y] {e : X → Y}
    (he : IsClosedEmbedding e) : ParacompactSpace X where
  locallyFinite_refinement α s ho hu := by
    choose U hUo hU using fun a ↦ he.isOpen_iff.1 (ho a)
    simp only [← hU] at hu ⊢
    have heU : range e ⊆ ⋃ i, U i := by
      simpa only [range_subset_iff, mem_iUnion, iUnion_eq_univ_iff] using! hu
    rcases precise_refinement_set he.isClosed_range U hUo heU with ⟨V, hVo, heV, hVf, hVU⟩
    refine ⟨α, fun a ↦ e ⁻¹' (V a), fun a ↦ (hVo a).preimage he.continuous, ?_,
      hVf.preimage_continuous he.continuous, fun a ↦ ⟨a, preimage_mono (hVU a)⟩⟩
    simpa only [range_subset_iff, mem_iUnion, iUnion_eq_univ_iff] using! heV

theorem Homeomorph.paracompactSpace_iff (e : X ≃ₜ Y) : ParacompactSpace X ↔ ParacompactSpace Y :=
  ⟨fun _ ↦ e.symm.isClosedEmbedding.paracompactSpace, fun _ ↦ e.isClosedEmbedding.paracompactSpace⟩

/-- The product of a compact space and a paracompact space is a paracompact space. The formalization
is based on https://dantopology.wordpress.com/2009/10/24/compact-x-paracompact-is-paracompact/
with some minor modifications.

This version assumes that `X` in `X × Y` is compact and `Y` is paracompact, see next lemma for the
other case. -/
instance (priority := 200) [CompactSpace X] [ParacompactSpace Y] : ParacompactSpace (X × Y) where
  locallyFinite_refinement α s ho hu := by
    have : ∀ (x : X) (y : Y), ∃ (a : α) (U : Set X) (V : Set Y),
        IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ×ˢ V ⊆ s a := fun x y ↦
      (iUnion_eq_univ_iff.1 hu (x, y)).imp fun a ha ↦ isOpen_prod_iff.1 (ho a) x y ha
    choose a U V hUo hVo hxU hyV hUV using this
    choose T hT using fun y ↦ CompactSpace.elim_nhds_subcover (U · y) fun x ↦
      (hUo x y).mem_nhds (hxU x y)
    set W : Y → Set Y := fun y ↦ ⋂ x ∈ T y, V x y
    have hWo : ∀ y, IsOpen (W y) := fun y ↦ isOpen_biInter_finset fun _ _ ↦ hVo _ _
    have hW : ∀ y, y ∈ W y := fun _ ↦ mem_iInter₂.2 fun _ _ ↦ hyV _ _
    rcases precise_refinement W hWo (iUnion_eq_univ_iff.2 fun y ↦ ⟨y, hW y⟩)
      with ⟨E, hEo, hE, hEf, hEA⟩
    refine ⟨Σ y, T y, fun z ↦ U z.2.1 z.1 ×ˢ E z.1, fun _ ↦ (hUo _ _).prod (hEo _),
      iUnion_eq_univ_iff.2 fun (x, y) ↦ ?_, fun (x, y) ↦ ?_, fun ⟨y, x, hx⟩ ↦ ?_⟩
    · rcases iUnion_eq_univ_iff.1 hE y with ⟨b, hb⟩
      rcases iUnion₂_eq_univ_iff.1 (hT b) x with ⟨a, ha, hx⟩
      exact ⟨⟨b, a, ha⟩, hx, hb⟩
    · rcases hEf y with ⟨t, ht, htf⟩
      refine ⟨univ ×ˢ t, prod_mem_nhds univ_mem ht, ?_⟩
      refine (htf.biUnion fun y _ ↦ finite_range (Sigma.mk y)).subset ?_
      rintro ⟨b, a, ha⟩ ⟨⟨c, d⟩, ⟨-, hd : d ∈ E b⟩, -, hdt : d ∈ t⟩
      exact mem_iUnion₂.2 ⟨b, ⟨d, hd, hdt⟩, mem_range_self _⟩
    · refine ⟨a x y, (Set.prod_mono Subset.rfl ?_).trans (hUV x y)⟩
      exact (hEA _).trans (iInter₂_subset x hx)

instance (priority := 200) [ParacompactSpace X] [CompactSpace Y] : ParacompactSpace (X × Y) :=
  (Homeomorph.prodComm X Y).paracompactSpace_iff.2 inferInstance

-- See note [lower instance priority]
/-- A compact space is paracompact. -/
instance (priority := 100) paracompact_of_compact [CompactSpace X] : ParacompactSpace X := by
  -- the proof is trivial: we choose a finite subcover using compactness, and use it
  refine ⟨fun ι s ho hu ↦ ?_⟩
  rcases isCompact_univ.elim_finite_subcover _ ho hu.ge with ⟨T, hT⟩
  refine ⟨(T : Set ι), fun t ↦ s t, fun t ↦ ho _, ?_, locallyFinite_of_finite _,
    fun t ↦ ⟨t, Subset.rfl⟩⟩
  simpa only [iUnion_coe_set, ← univ_subset_iff]

/-- Let `X` be a locally compact sigma compact Hausdorff topological space, let `s` be a closed set
in `X`. Suppose that for each `x ∈ s` the sets `B x : ι x → Set X` with the predicate
`p x : ι x → Prop` form a basis of the filter `𝓝 x`. Then there exists a locally finite covering
`fun i ↦ B (c i) (r i)` of `s` such that all “centers” `c i` belong to `s` and each `r i` satisfies
`p (c i)`.

The notation is inspired by the case `B x r = Metric.ball x r` but the theorem applies to
`nhds_basis_opens` as well. If the covering must be subordinate to some open covering of `s`, then
the user should use a basis obtained by `Filter.HasBasis.restrict_subset` or a similar lemma, see
the proof of `paracompact_of_locallyCompact_sigmaCompact` for an example.

The formalization is based on two [ncatlab](https://ncatlab.org/) proofs:
* [locally compact and sigma compact spaces are paracompact](https://ncatlab.org/nlab/show/locally+compact+and+sigma-compact+spaces+are+paracompact);
* [open cover of smooth manifold admits locally finite refinement by closed balls](https://ncatlab.org/nlab/show/partition+of+unity#ExistenceOnSmoothManifolds).

See also `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis` for a version of this lemma
dealing with a covering of the whole space.

In most cases (namely, if `B c r ∪ B c r'` is again a set of the form `B c r''`) it is possible
to choose `α = X`. This fact is not yet formalized in `mathlib`. -/
theorem refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] [T2Space X] {ι : X → Type u} {p : ∀ x, ι x → Prop} {B : ∀ x, ι x → Set X}
    {s : Set X} (hs : IsClosed s) (hB : ∀ x ∈ s, (𝓝 x).HasBasis (p x) (B x)) :
    ∃ (α : Type v) (c : α → X) (r : ∀ a, ι (c a)),
      (∀ a, c a ∈ s ∧ p (c a) (r a)) ∧
        (s ⊆ ⋃ a, B (c a) (r a)) ∧ LocallyFinite fun a ↦ B (c a) (r a) := by
  -- For technical reasons we prepend two empty sets to the sequence `CompactExhaustion.choice X`
  set K' : CompactExhaustion X := CompactExhaustion.choice X
  set K : CompactExhaustion X := K'.shiftr.shiftr
  set Kdiff := fun n ↦ K (n + 1) \ interior (K n)
  -- Now we restate some properties of `CompactExhaustion` for `K`/`Kdiff`
  have hKcov : ∀ x, x ∈ Kdiff (K'.find x + 1) := fun x ↦ by
    simpa only [K'.find_shiftr] using
      sdiff_subset_sdiff_right interior_subset (K'.shiftr.mem_sdiff_shiftr_find x)
  have Kdiffc : ∀ n, IsCompact (Kdiff n ∩ s) :=
    fun n ↦ ((K.isCompact _).diff isOpen_interior).inter_right hs
  -- Next we choose a finite covering `B (c n i) (r n i)` of each
  -- `Kdiff (n + 1) ∩ s` such that `B (c n i) (r n i) ∩ s` is disjoint with `K n`
  have : ∀ (n) (x : ↑(Kdiff (n + 1) ∩ s)), (K n)ᶜ ∈ 𝓝 (x : X) :=
    fun n x ↦ (K.isClosed n).compl_mem_nhds fun hx' ↦ x.2.1.2 <| K.subset_interior_succ _ hx'
  choose! r hrp hr using fun n (x : ↑(Kdiff (n + 1) ∩ s)) ↦ (hB x x.2.2).mem_iff.1 (this n x)
  have hxr : ∀ (n x) (hx : x ∈ Kdiff (n + 1) ∩ s), B x (r n ⟨x, hx⟩) ∈ 𝓝 x := fun n x hx ↦
    (hB x hx.2).mem_of_mem (hrp _ ⟨x, hx⟩)
  choose T hT using fun n ↦ (Kdiffc (n + 1)).elim_nhds_subcover' _ (hxr n)
  set T' : ∀ n, Set ↑(Kdiff (n + 1) ∩ s) := fun n ↦ T n
  -- Finally, we take the union of all these coverings
  refine ⟨Σ n, T' n, fun a ↦ a.2, fun a ↦ r a.1 a.2, ?_, ?_, ?_⟩
  · rintro ⟨n, x, hx⟩
    exact ⟨x.2.2, hrp _ _⟩
  · refine fun x hx ↦ mem_iUnion.2 ?_
    rcases mem_iUnion₂.1 (hT _ ⟨hKcov x, hx⟩) with ⟨⟨c, hc⟩, hcT, hcx⟩
    exact ⟨⟨_, ⟨c, hc⟩, hcT⟩, hcx⟩
  · intro x
    refine
      ⟨interior (K (K'.find x + 3)),
        IsOpen.mem_nhds isOpen_interior (K.subset_interior_succ _ (hKcov x).1), ?_⟩
    have : (⋃ k ≤ K'.find x + 2, range (Sigma.mk k) : Set (Σ n, T' n)).Finite :=
      (finite_le_nat _).biUnion fun k _ ↦ finite_range _
    apply this.subset
    rintro ⟨k, c, hc⟩
    simp only [mem_iUnion, mem_ofPred_eq, Subtype.coe_mk]
    rintro ⟨x, hxB : x ∈ B c (r k c), hxK⟩
    refine ⟨k, ?_, ⟨c, hc⟩, rfl⟩
    have := (mem_compl_iff _ _).1 (hr k c hxB)
    contrapose! this with hnk
    exact K.subset hnk (interior_subset hxK)

/-- Let `X` be a locally compact sigma compact Hausdorff topological space. Suppose that for each
`x` the sets `B x : ι x → Set X` with the predicate `p x : ι x → Prop` form a basis of the filter
`𝓝 x`. Then there exists a locally finite covering `fun i ↦ B (c i) (r i)` of `X` such that each
`r i` satisfies `p (c i)`.

The notation is inspired by the case `B x r = Metric.ball x r` but the theorem applies to
`nhds_basis_opens` as well. If the covering must be subordinate to some open covering of `s`, then
the user should use a basis obtained by `Filter.HasBasis.restrict_subset` or a similar lemma, see
the proof of `paracompact_of_locallyCompact_sigmaCompact` for an example.

The formalization is based on two [ncatlab](https://ncatlab.org/) proofs:
* [locally compact and sigma compact spaces are paracompact](https://ncatlab.org/nlab/show/locally+compact+and+sigma-compact+spaces+are+paracompact);
* [open cover of smooth manifold admits locally finite refinement by closed balls](https://ncatlab.org/nlab/show/partition+of+unity#ExistenceOnSmoothManifolds).

See also `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set` for a version of this lemma
dealing with a covering of a closed set.

In most cases (namely, if `B c r ∪ B c r'` is again a set of the form `B c r''`) it is possible
to choose `α = X`. This fact is not yet formalized in `mathlib`. -/
theorem refinement_of_locallyCompact_sigmaCompact_of_nhds_basis [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] [T2Space X] {ι : X → Type u} {p : ∀ x, ι x → Prop} {B : ∀ x, ι x → Set X}
    (hB : ∀ x, (𝓝 x).HasBasis (p x) (B x)) :
    ∃ (α : Type v) (c : α → X) (r : ∀ a, ι (c a)),
      (∀ a, p (c a) (r a)) ∧ ⋃ a, B (c a) (r a) = univ ∧ LocallyFinite fun a ↦ B (c a) (r a) :=
  let ⟨α, c, r, hp, hU, hfin⟩ :=
    refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set isClosed_univ fun x _ ↦ hB x
  ⟨α, c, r, fun a ↦ (hp a).2, univ_subset_iff.1 hU, hfin⟩

-- See note [lower instance priority]
/-- A locally compact sigma compact Hausdorff space is paracompact. See also
`refinement_of_locallyCompact_sigmaCompact_of_nhds_basis` for a more precise statement. -/
instance (priority := 100) paracompact_of_locallyCompact_sigmaCompact [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] [T2Space X] : ParacompactSpace X := by
  refine ⟨fun α s ho hc ↦ ?_⟩
  choose i hi using iUnion_eq_univ_iff.1 hc
  have : ∀ x : X, (𝓝 x).HasBasis (fun t : Set X ↦ (x ∈ t ∧ IsOpen t) ∧ t ⊆ s (i x)) id :=
    fun x : X ↦ (nhds_basis_opens x).restrict_subset (IsOpen.mem_nhds (ho (i x)) (hi x))
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis this with
    ⟨β, c, t, hto, htc, htf⟩
  exact ⟨β, t, fun x ↦ (hto x).1.2, htc, htf, fun b ↦ ⟨i <| c b, (hto b).2⟩⟩

/-- **Dieudonné's theorem**: a paracompact R₁ space is normal.
Formalization is based on the proof
at [ncatlab](https://ncatlab.org/nlab/show/paracompact+Hausdorff+spaces+are+normal). -/
instance (priority := 100) NormalSpace.of_paracompactSpace_r1Space
    [R1Space X] [ParacompactSpace X] : NormalSpace X := by
  -- First we show how to go from points to a set on one side.
  have : ∀ s t : Set X, IsClosed s →
      (∀ x ∈ s, ∃ u v, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ t ⊆ v ∧ Disjoint u v) →
      ∃ u v, IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ Disjoint u v := fun s t hs H ↦ by
    /- For each `x ∈ s` we choose open disjoint `u x ∋ x` and `v x ⊇ t`. The sets `u x` form an
        open covering of `s`. We choose a locally finite refinement `u' : s → Set X`, then
        `⋃ i, u' i` and `(closure (⋃ i, u' i))ᶜ` are disjoint open neighborhoods of `s` and `t`. -/
    choose u v hu hv hxu htv huv using SetCoe.forall'.1 H
    rcases precise_refinement_set hs u hu fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hxu _⟩ with
      ⟨u', hu'o, hcov', hu'fin, hsub⟩
    refine ⟨⋃ i, u' i, (closure (⋃ i, u' i))ᶜ, isOpen_iUnion hu'o, isClosed_closure.isOpen_compl,
      hcov', ?_, disjoint_compl_right.mono le_rfl (compl_le_compl subset_closure)⟩
    rw [hu'fin.closure_iUnion, compl_iUnion, subset_iInter_iff]
    refine fun i x hxt hxu ↦
      absurd (htv i hxt) (closure_minimal ?_ (isClosed_compl_iff.2 <| hv _) hxu)
    exact fun y hyu hyv ↦ (huv i).le_bot ⟨hsub _ hyu, hyv⟩
  -- Now we apply the lemma twice: first to `s` and `t`, then to `t` and each point of `s`.
  refine { normal := fun s t hs ht hst ↦ this s t hs fun x hx ↦ ?_ }
  rcases this t {x} ht fun y hy ↦ (by
    simp_rw [singleton_subset_iff]
    exact r1_separation <| ht.not_inseparable hy <| hst.notMem_of_mem_left hx)
    with ⟨v, u, hv, hu, htv, hxu, huv⟩
  exact ⟨u, v, hu, hv, singleton_subset_iff.1 hxu, htv, huv.symm⟩

/-- In order for `X` to be paracompact, it suffices for every open cover of `X` to
admit a closed locally finite refinement instead of an open one. -/
lemma ParacompactSpace.of_isClosed_refinements {X : Type u} [TopologicalSpace X]
    (h : ∀ (ι : Type u) (u : ι → Set X), (∀ i, IsOpen (u i)) → ⋃ i, u i = univ →
      ∃ ι' : Type u, ∃ v : ι' → Set X, LocallyFinite v ∧ (∀ i, IsClosed (v i)) ∧ ⋃ i, v i = univ ∧
        ∀ i', ∃ i, v i' ⊆ u i) :
    ParacompactSpace X := by
  /- For any open cover `u`, we can use `h` to get a locally finite closed refinement `w`. -/
  refine ⟨fun ι u hu hu' ↦ ?_⟩
  have ⟨ι', w, hw⟩ := h ι u hu hu'
  /- Using `h` again, we can obtain a locally finite closed cover `w'` of `X` such that each
  `w' i''` meets only finitely many `w i'`. -/
  have ⟨ι'', w', hw'⟩ : ∃ ι'' : Type u, ∃ w' : ι'' → Set X, LocallyFinite w' ∧
      (∀ i'', IsClosed (w' i'')) ∧ ⋃ i'', w' i'' = univ ∧
        ∀ i'', {i' | (w i' ∩ w' i'').Nonempty}.Finite := by
    have ⟨ι'', w', hw'⟩ := h {v : Set X | IsOpen v ∧ {i' | (w i' ∩ v).Nonempty}.Finite} (↑)
      (fun v ↦ v.2.1) (iUnion_eq_univ_iff.2 fun x ↦ by
        have ⟨v, hv⟩ := hw.1 x
        have ⟨v', hv'⟩ := mem_nhds_iff.1 hv.1
        exact ⟨⟨v', hv'.2.1, (by grw [hv'.1]; exact hv.2)⟩, hv'.2.2⟩)
    refine ⟨ι'', w', hw'.1, hw'.2.1, hw'.2.2.1, fun i'' ↦ ?_⟩
    have ⟨v, hv⟩ := hw'.2.2.2 i''
    grw [hv]
    exact v.2.2
  /- An open locally finite refinement of `u` can now be given by enlarging each `w i'` to a `u i`
  containing it minus the union of all `w' i''` that don't intersect `w i'`. -/
  choose f hf using hw.2.2.2
  refine ⟨ι', fun i' ↦ u (f i') \ ⋃ i'' ∈ {i'' | w i' ∩ w' i'' = ∅}, w' i'', ?_, ?_, ?_, ?_⟩
  · exact fun i' ↦ (hu _).sdiff <| hw'.1.isClosed_biUnion fun i'' _ ↦ hw'.2.1 i''
  · refine iUnion_eq_univ_iff.2 <| forall_imp (fun x ↦ Exists.imp fun i' hi' ↦ ?_) <|
      iUnion_eq_univ_iff.1 hw.2.2.1
    simp only [← disjoint_iff_inter_eq_empty, Set.mem_sdiff, mem_iUnion]
    grind
  · refine forall_imp (fun x ↦ Exists.imp fun v ⟨hv, hv'⟩ ↦ ⟨hv, ?_⟩) hw'.1
    refine (hv'.biUnion (fun i'' _ ↦ hw'.2.2.2 i'')).subset fun i' ⟨x, hx⟩ ↦ ?_
    simp only [mem_ofPred_eq, mem_inter_iff, Set.mem_sdiff, mem_iUnion, exists_prop, not_exists,
      not_and] at hx ⊢
    have ⟨i'', hi''⟩ := iUnion_eq_univ_iff.1 hw'.2.2.1 x
    have ⟨x', hx'⟩ : (w i' ∩ w' i'').Nonempty := by grind [nonempty_def]
    exact ⟨i'', ⟨x, by grind⟩, x', by grind⟩
  · exact fun i' ↦ ⟨f i', by simp⟩

/-- For a regular space `X`, the following are equivalent:
* `X` is paracompact, i.e. every open cover of `X` has a locally finite open refinement
* every open cover of `X` has a σ-locally finite open refinement
* every open cover of `X` has a locally finite refinement
* every open cover of `X` has a locally finite closed refinement

See Engelking, theorem 5.1.11. -/
lemma paracompactSpace_tfae_of_regularSpace {X : Type u} [TopologicalSpace X] [RegularSpace X] :
    List.TFAE [ParacompactSpace X,
      ∀ ι : Type u, ∀ u : ι → Set X, (∀ i, IsOpen (u i)) → ⋃ i, u i = univ →
        ∃ ι' : Type u, ∃ v : ι' → Set X, SigmaLocallyFinite v ∧ (∀ i, IsOpen (v i)) ∧
          ⋃ i, v i = univ ∧ ∀ i', ∃ i, v i' ⊆ u i,
      ∀ ι : Type u, ∀ u : ι → Set X, (∀ i, IsOpen (u i)) → ⋃ i, u i = univ →
        ∃ ι' : Type u, ∃ v : ι' → Set X, LocallyFinite v ∧ ⋃ i, v i = univ ∧
          ∀ i', ∃ i, v i' ⊆ u i,
      ∀ ι : Type u, ∀ u : ι → Set X, (∀ i, IsOpen (u i)) → ⋃ i, u i = univ →
        ∃ ι' : Type u, ∃ v : ι' → Set X, LocallyFinite v ∧ (∀ i, IsClosed (v i)) ∧ ⋃ i, v i = univ ∧
          ∀ i', ∃ i, v i' ⊆ u i] := by
  /- `1 → 2` holds because every locally finite cover is in particular sigma-locally finite. -/
  tfae_have 1 → 2 := fun _ ι u hu hu' ↦ by
    have ⟨v, hv⟩ := precise_refinement u hu hu'
    exact ⟨ι, v, hv.2.2.1.sigmaLocallyFinite, hv.1, hv.2.1, fun i ↦ ⟨i, hv.2.2.2 i⟩⟩
  /- `2 → 3` holds because every sigma-locally finite open cover admits a
  locally finite refinement. -/
  tfae_have 2 → 3 := forall₂_imp fun ι u  ↦ forall₂_imp fun hu hu' h ↦ by
    obtain ⟨ι', v, hv⟩ := h
    have ⟨v', hv'⟩ := hv.1.exists_locallyFinite_refinement hv.2.1 hv.2.2.1
    exact ⟨ι', v', hv'.1, hv'.2.1, fun i' ↦ ⟨_, (hv'.2.2 i').trans (hv.2.2.2 i').choose_spec⟩⟩
  /- `3 → 4` holds because by regularity every open cover `u` of `X` admits an open refinement `w`
  whose family of closures is also a refinement of `u`, and a cover as needed for `4`
  can be constructed by applying `3` to `w` and then taking closures. -/
  tfae_have 3 → 4 := fun h ι u hu hu' ↦ by
    have ⟨ι', w, hw⟩ : ∃ ι' : Type u, ∃ w : ι' → Set X, (∀ i', IsOpen (w i')) ∧ ⋃ i', w i' = univ ∧
        ∀ i', ∃ i, closure (w i') ⊆ u i := by
      refine ⟨{w : Set X | IsOpen w ∧ ∃ i, closure w ⊆ u i}, (↑), fun w ↦ w.2.1, ?_, fun w ↦ w.2.2⟩
      refine iUnion_eq_univ_iff.2 <| forall_imp (fun x ⟨i, hx⟩ ↦ ?_) <| iUnion_eq_univ_iff.1 hu'
      have ⟨w, hw⟩ := (hasBasis_opens_closure x).mem_iff.1 ((hu i).mem_nhds hx)
      exact ⟨⟨w, hw.1.2, i, hw.2⟩, hw.1.1⟩
    have ⟨ι'', v, hv⟩ := h ι' w hw.1 hw.2.1
    refine ⟨ι'', _, hv.1.closure, by simp, ?_, fun i'' ↦ ?_⟩
    · grw [← univ_subset_iff, ← hv.2.1, ← subset_closure]
    · have ⟨i', hi'⟩ := hv.2.2 i''
      have ⟨i, hi⟩ := hw.2.2 i'
      exact ⟨i, (closure_mono hi').trans hi⟩
  /- `4 → 1` was proven more generally in `ParacompactSpace.of_isClosed_refinements`. -/
  tfae_have 4 → 1 := ParacompactSpace.of_isClosed_refinements
  tfae_finish
