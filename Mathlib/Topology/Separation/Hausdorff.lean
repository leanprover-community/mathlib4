/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Separation.Basic

/-!
# T₂ and T₂.₅ spaces.

This file defines the T₂ (Hausdorff) condition, which is the most commonly-used among the various
separation axioms, and the related T₂.₅ condition.

## Main definitions

* `T2Space`: A T₂/Hausdorff space is a space where, for every two points `x ≠ y`,
  there is two disjoint open sets, one containing `x`, and the other `y`. T₂ implies T₁ and R₁.
* `T25Space`: A T₂.₅/Urysohn space is a space where, for every two points `x ≠ y`,
  there is two open sets, one containing `x`, and the other `y`, whose closures are disjoint.
  T₂.₅ implies T₂.

See `Mathlib/Topology/Separation/Regular.lean` for regular, T₃, etc spaces; and
`Mathlib/Topology/Separation/GDelta.lean` for the definitions of `PerfectlyNormalSpace` and
`T6Space`.

Note that `mathlib` adopts the modern convention that `m ≤ n` if and only if `T_m → T_n`, but
occasionally the literature swaps definitions for e.g. T₃ and regular.

## Main results

### T₂ spaces

* `t2_iff_nhds`: A space is T₂ iff the neighbourhoods of distinct points generate the bottom filter.
* `t2_iff_isClosed_diagonal`: A space is T₂ iff the `diagonal` of `X` (that is, the set of all
  points of the form `(a, a) : X × X`) is closed under the product topology.
* `separatedNhds_of_finset_finset`: Any two disjoint finsets are `SeparatedNhds`.
* Most topological constructions preserve Hausdorffness;
  these results are part of the typeclass inference system (e.g. `Topology.IsEmbedding.t2Space`)
* `Set.EqOn.closure`: If two functions are equal on some set `s`, they are equal on its closure.
* `IsCompact.isClosed`: All compact sets are closed.
* `WeaklyLocallyCompactSpace.locallyCompactSpace`: If a topological space is both
  weakly locally compact (i.e., each point has a compact neighbourhood)
  and is T₂, then it is locally compact.
* `totallySeparatedSpace_of_t1_of_basis_clopen`: If `X` has a clopen basis, then
  it is a `TotallySeparatedSpace`.
* `loc_compact_t2_tot_disc_iff_tot_sep`: A locally compact T₂ space is totally disconnected iff
  it is totally separated.
* `T2Quotient`: the largest T2 quotient of a given topological space.

If the space is also compact:

* `normalOfCompactT2`: A compact T₂ space is a `NormalSpace`.
* `connectedComponent_eq_iInter_isClopen`: The connected component of a point
  is the intersection of all its clopen neighbourhoods.
* `compact_t2_tot_disc_iff_tot_sep`: Being a `TotallyDisconnectedSpace`
  is equivalent to being a `TotallySeparatedSpace`.
* `ConnectedComponents.t2`: `ConnectedComponents X` is T₂ for `X` T₂ and compact.

## References

* <https://en.wikipedia.org/wiki/Separation_axiom>
* [Willard's *General Topology*][zbMATH02107988]

-/

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

/-- A T₂ space, also known as a Hausdorff space, is one in which for every
  `x ≠ y` there exists disjoint open sets around `x` and `y`. This is
  the most widely used of the separation axioms. -/
@[mk_iff]
class T2Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Every two points in a Hausdorff space admit disjoint open neighbourhoods. -/
  t2 : Pairwise fun x y => ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v

/-- Two different points can be separated by open sets. -/
theorem t2_separation [T2Space X] {x y : X} (h : x ≠ y) :
    ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v :=
  T2Space.t2 h

-- todo: use this as a definition?
theorem t2Space_iff_disjoint_nhds : T2Space X ↔ Pairwise fun x y : X => Disjoint (𝓝 x) (𝓝 y) := by
  refine (t2Space_iff X).trans (forall₃_congr fun x y _ => ?_)
  simp only [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens y), ← exists_and_left,
    and_assoc, and_comm, and_left_comm]

@[simp]
theorem disjoint_nhds_nhds [T2Space X] {x y : X} : Disjoint (𝓝 x) (𝓝 y) ↔ x ≠ y :=
  ⟨fun hd he => by simp [he, nhds_neBot.ne] at hd, (t2Space_iff_disjoint_nhds.mp ‹_› ·)⟩

theorem pairwise_disjoint_nhds [T2Space X] : Pairwise (Disjoint on (𝓝 : X → Filter X)) := fun _ _ =>
  disjoint_nhds_nhds.2

protected theorem Set.pairwiseDisjoint_nhds [T2Space X] (s : Set X) : s.PairwiseDisjoint 𝓝 :=
  pairwise_disjoint_nhds.set_pairwise s

/-- Points of a finite set can be separated by open sets from each other. -/
theorem Set.Finite.t2_separation [T2Space X] {s : Set X} (hs : s.Finite) :
    ∃ U : X → Set X, (∀ x, x ∈ U x ∧ IsOpen (U x)) ∧ s.PairwiseDisjoint U :=
  s.pairwiseDisjoint_nhds.exists_mem_filter_basis hs nhds_basis_opens

-- see Note [lower instance priority]
instance (priority := 100) T2Space.t1Space [T2Space X] : T1Space X :=
  t1Space_iff_disjoint_pure_nhds.mpr fun _ _ hne =>
    (disjoint_nhds_nhds.2 hne).mono_left <| pure_le_nhds _

-- see Note [lower instance priority]
instance (priority := 100) T2Space.r1Space [T2Space X] : R1Space X :=
  ⟨fun x y ↦ (eq_or_ne x y).imp specializes_of_eq disjoint_nhds_nhds.2⟩

theorem SeparationQuotient.t2Space_iff : T2Space (SeparationQuotient X) ↔ R1Space X := by
  simp only [t2Space_iff_disjoint_nhds, Pairwise, surjective_mk.forall₂, ne_eq, mk_eq_mk,
    r1Space_iff_inseparable_or_disjoint_nhds, ← disjoint_comap_iff surjective_mk, comap_mk_nhds_mk,
    ← or_iff_not_imp_left]

instance SeparationQuotient.t2Space [R1Space X] : T2Space (SeparationQuotient X) :=
  t2Space_iff.2 ‹_›

instance (priority := 80) [R1Space X] [T0Space X] : T2Space X :=
  t2Space_iff_disjoint_nhds.2 fun _x _y hne ↦ disjoint_nhds_nhds_iff_not_inseparable.2 fun hxy ↦
    hne hxy.eq

theorem R1Space.t2Space_iff_t0Space [R1Space X] : T2Space X ↔ T0Space X := by
  constructor <;> intro <;> infer_instance

/-- A space is T₂ iff the neighbourhoods of distinct points generate the bottom filter. -/
theorem t2_iff_nhds : T2Space X ↔ ∀ {x y : X}, NeBot (𝓝 x ⊓ 𝓝 y) → x = y := by
  simp only [t2Space_iff_disjoint_nhds, disjoint_iff, neBot_iff, Ne, not_imp_comm, Pairwise]

theorem eq_of_nhds_neBot [T2Space X] {x y : X} (h : NeBot (𝓝 x ⊓ 𝓝 y)) : x = y :=
  t2_iff_nhds.mp ‹_› h

theorem t2Space_iff_nhds :
    T2Space X ↔ Pairwise fun x y : X => ∃ U ∈ 𝓝 x, ∃ V ∈ 𝓝 y, Disjoint U V := by
  simp only [t2Space_iff_disjoint_nhds, Filter.disjoint_iff, Pairwise]

theorem t2_separation_nhds [T2Space X] {x y : X} (h : x ≠ y) :
    ∃ u v, u ∈ 𝓝 x ∧ v ∈ 𝓝 y ∧ Disjoint u v :=
  let ⟨u, v, open_u, open_v, x_in, y_in, huv⟩ := t2_separation h
  ⟨u, v, open_u.mem_nhds x_in, open_v.mem_nhds y_in, huv⟩

theorem t2_separation_compact_nhds [LocallyCompactSpace X] [T2Space X] {x y : X} (h : x ≠ y) :
    ∃ u v, u ∈ 𝓝 x ∧ v ∈ 𝓝 y ∧ IsCompact u ∧ IsCompact v ∧ Disjoint u v := by
  simpa only [exists_prop, ← exists_and_left, and_comm, and_assoc, and_left_comm] using
    ((compact_basis_nhds x).disjoint_iff (compact_basis_nhds y)).1 (disjoint_nhds_nhds.2 h)

theorem t2_iff_ultrafilter :
    T2Space X ↔ ∀ {x y : X} (f : Ultrafilter X), ↑f ≤ 𝓝 x → ↑f ≤ 𝓝 y → x = y :=
  t2_iff_nhds.trans <| by simp only [← exists_ultrafilter_iff, and_imp, le_inf_iff, exists_imp]

theorem t2_iff_isClosed_diagonal : T2Space X ↔ IsClosed (diagonal X) := by
  simp only [t2Space_iff_disjoint_nhds, ← isOpen_compl_iff, isOpen_iff_mem_nhds, Prod.forall,
    nhds_prod_eq, compl_diagonal_mem_prod, mem_compl_iff, mem_diagonal_iff, Pairwise]

theorem isClosed_diagonal [T2Space X] : IsClosed (diagonal X) :=
  t2_iff_isClosed_diagonal.mp ‹_›

theorem tendsto_nhds_unique [T2Space X] {f : Y → X} {l : Filter Y} {a b : X} [NeBot l]
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : a = b :=
  (tendsto_nhds_unique_inseparable ha hb).eq

theorem tendsto_nhds_unique' [T2Space X] {f : Y → X} {l : Filter Y} {a b : X} (_ : NeBot l)
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb

theorem tendsto_nhds_unique_of_eventuallyEq [T2Space X] {f g : Y → X} {l : Filter Y} {a b : X}
    [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) (hfg : f =ᶠ[l] g) : a = b :=
  tendsto_nhds_unique (ha.congr' hfg) hb

theorem tendsto_nhds_unique_of_frequently_eq [T2Space X] {f g : Y → X} {l : Filter Y} {a b : X}
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) (hfg : ∃ᶠ x in l, f x = g x) : a = b :=
  have : ∃ᶠ z : X × X in 𝓝 (a, b), z.1 = z.2 := (ha.prodMk_nhds hb).frequently hfg
  not_not.1 fun hne => this (isClosed_diagonal.isOpen_compl.mem_nhds hne)

/-- If `s` and `t` are compact sets in a T₂ space, then the set neighborhoods filter of `s ∩ t`
is the infimum of set neighborhoods filters for `s` and `t`.

For general sets, only the `≤` inequality holds, see `nhdsSet_inter_le`. -/
theorem IsCompact.nhdsSet_inter_eq [T2Space X] {s t : Set X} (hs : IsCompact s) (ht : IsCompact t) :
    𝓝ˢ (s ∩ t) = 𝓝ˢ s ⊓ 𝓝ˢ t := by
  refine le_antisymm (nhdsSet_inter_le _ _) ?_
  simp_rw [hs.nhdsSet_inf_eq_biSup, ht.inf_nhdsSet_eq_biSup, nhdsSet, sSup_image]
  refine iSup₂_le fun x hxs ↦ iSup₂_le fun y hyt ↦ ?_
  rcases eq_or_ne x y with (rfl | hne)
  · exact le_iSup₂_of_le x ⟨hxs, hyt⟩ (inf_idem _).le
  · exact (disjoint_nhds_nhds.mpr hne).eq_bot ▸ bot_le

/-- In a `T2Space X`, for a compact set `t` and a point `x` outside `t`, there are open sets `U`,
`V` that separate `t` and `x`. -/
lemma IsCompact.separation_of_notMem {X : Type u_1} [TopologicalSpace X] [T2Space X] {x : X}
    {t : Set X} (H1 : IsCompact t) (H2 : x ∉ t) :
    ∃ (U : Set X), ∃ (V : Set X), IsOpen U ∧ IsOpen V ∧ t ⊆ U ∧ x ∈ V ∧ Disjoint U V := by
  simpa [SeparatedNhds] using SeparatedNhds.of_isCompact_isCompact_isClosed H1 isCompact_singleton
    isClosed_singleton <| disjoint_singleton_right.mpr H2

@[deprecated (since := "2025-05-23")]
alias IsCompact.separation_of_not_mem := IsCompact.separation_of_notMem

/-- In a `T2Space X`, for a compact set `t` and a point `x` outside `t`, `𝓝ˢ t` and `𝓝 x` are
disjoint. -/
lemma IsCompact.disjoint_nhdsSet_nhds {X : Type u_1} [TopologicalSpace X] [T2Space X] {x : X}
    {t : Set X} (H1 : IsCompact t) (H2 : x ∉ t) :
    Disjoint (𝓝ˢ t) (𝓝 x) := by
  simpa using SeparatedNhds.disjoint_nhdsSet <| .of_isCompact_isCompact_isClosed H1
    isCompact_singleton isClosed_singleton <| disjoint_singleton_right.mpr H2

/-- If a function `f` is

- injective on a compact set `s`;
- continuous at every point of this set;
- injective on a neighborhood of each point of this set,

then it is injective on a neighborhood of this set. -/
theorem Set.InjOn.exists_mem_nhdsSet {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} {s : Set X} (inj : InjOn f s) (sc : IsCompact s)
    (fc : ∀ x ∈ s, ContinuousAt f x) (loc : ∀ x ∈ s, ∃ u ∈ 𝓝 x, InjOn f u) :
    ∃ t ∈ 𝓝ˢ s, InjOn f t := by
  have : ∀ x ∈ s ×ˢ s, ∀ᶠ y in 𝓝 x, f y.1 = f y.2 → y.1 = y.2 := fun (x, y) ⟨hx, hy⟩ ↦ by
    rcases eq_or_ne x y with rfl | hne
    · rcases loc x hx with ⟨u, hu, hf⟩
      exact Filter.mem_of_superset (prod_mem_nhds hu hu) <| forall_prod_set.2 hf
    · suffices ∀ᶠ z in 𝓝 (x, y), f z.1 ≠ f z.2 from this.mono fun _ hne h ↦ absurd h hne
      refine (fc x hx).prodMap' (fc y hy) <| isClosed_diagonal.isOpen_compl.mem_nhds ?_
      exact inj.ne hx hy hne
  rw [← eventually_nhdsSet_iff_forall, sc.nhdsSet_prod_eq sc] at this
  exact eventually_prod_self_iff.1 this

/-- If a function `f` is

- injective on a compact set `s`;
- continuous at every point of this set;
- injective on a neighborhood of each point of this set,

then it is injective on an open neighborhood of this set. -/
theorem Set.InjOn.exists_isOpen_superset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} {s : Set X} (inj : InjOn f s) (sc : IsCompact s)
    (fc : ∀ x ∈ s, ContinuousAt f x) (loc : ∀ x ∈ s, ∃ u ∈ 𝓝 x, InjOn f u) :
    ∃ t, IsOpen t ∧ s ⊆ t ∧ InjOn f t :=
  let ⟨_t, hst, ht⟩ := inj.exists_mem_nhdsSet sc fc loc
  let ⟨u, huo, hsu, hut⟩ := mem_nhdsSet_iff_exists.1 hst
  ⟨u, huo, hsu, ht.mono hut⟩

section limUnder

variable [T2Space X] {f : Filter X}

/-!
### Properties of `lim` and `limUnder`

In this section we use explicit `Nonempty X` instances for `lim` and `limUnder`. This way the lemmas
are useful without a `Nonempty X` instance.
-/


theorem lim_eq {x : X} [NeBot f] (h : f ≤ 𝓝 x) : @lim _ _ ⟨x⟩ f = x :=
  tendsto_nhds_unique (le_nhds_lim ⟨x, h⟩) h

theorem lim_eq_iff [NeBot f] (h : ∃ x : X, f ≤ 𝓝 x) {x} : @lim _ _ ⟨x⟩ f = x ↔ f ≤ 𝓝 x :=
  ⟨fun c => c ▸ le_nhds_lim h, lim_eq⟩

theorem Ultrafilter.lim_eq_iff_le_nhds [CompactSpace X] {x : X} {F : Ultrafilter X} :
    F.lim = x ↔ ↑F ≤ 𝓝 x :=
  ⟨fun h => h ▸ F.le_nhds_lim, lim_eq⟩

theorem isOpen_iff_ultrafilter' [CompactSpace X] (U : Set X) :
    IsOpen U ↔ ∀ F : Ultrafilter X, F.lim ∈ U → U ∈ F.1 := by
  rw [isOpen_iff_ultrafilter]
  refine ⟨fun h F hF => h F.lim hF F F.le_nhds_lim, ?_⟩
  intro cond x hx f h
  rw [← Ultrafilter.lim_eq_iff_le_nhds.2 h] at hx
  exact cond _ hx

theorem Filter.Tendsto.limUnder_eq {x : X} {f : Filter Y} [NeBot f] {g : Y → X}
    (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g = x :=
  lim_eq h

theorem Filter.limUnder_eq_iff {f : Filter Y} [NeBot f] {g : Y → X} (h : ∃ x, Tendsto g f (𝓝 x))
    {x} : @limUnder _ _ _ ⟨x⟩ f g = x ↔ Tendsto g f (𝓝 x) :=
  ⟨fun c => c ▸ tendsto_nhds_limUnder h, Filter.Tendsto.limUnder_eq⟩

theorem Continuous.limUnder_eq [TopologicalSpace Y] {f : Y → X} (h : Continuous f) (y : Y) :
    @limUnder _ _ _ ⟨f y⟩ (𝓝 y) f = f y :=
  (h.tendsto y).limUnder_eq

@[simp]
theorem lim_nhds (x : X) : @lim _ _ ⟨x⟩ (𝓝 x) = x :=
  lim_eq le_rfl

@[simp]
theorem limUnder_nhds_id (x : X) : @limUnder _ _ _ ⟨x⟩ (𝓝 x) id = x :=
  lim_nhds x

@[simp]
theorem lim_nhdsWithin {x : X} {s : Set X} (h : x ∈ closure s) : @lim _ _ ⟨x⟩ (𝓝[s] x) = x :=
  haveI : NeBot (𝓝[s] x) := mem_closure_iff_clusterPt.1 h
  lim_eq inf_le_left

@[simp]
theorem limUnder_nhdsWithin_id {x : X} {s : Set X} (h : x ∈ closure s) :
    @limUnder _ _ _ ⟨x⟩ (𝓝[s] x) id = x :=
  lim_nhdsWithin h

end limUnder

/-!
### `T2Space` constructions

We use two lemmas to prove that various standard constructions generate Hausdorff spaces from
Hausdorff spaces:

* `separated_by_continuous` says that two points `x y : X` can be separated by open neighborhoods
  provided that there exists a continuous map `f : X → Y` with a Hausdorff codomain such that
  `f x ≠ f y`. We use this lemma to prove that topological spaces defined using `induced` are
  Hausdorff spaces.

* `separated_by_isOpenEmbedding` says that for an open embedding `f : X → Y` of a Hausdorff space
  `X`, the images of two distinct points `x y : X`, `x ≠ y` can be separated by open neighborhoods.
  We use this lemma to prove that topological spaces defined using `coinduced` are Hausdorff spaces.
-/

-- see Note [lower instance priority]
instance (priority := 100) DiscreteTopology.toT2Space
    [DiscreteTopology X] : T2Space X :=
  ⟨fun x y h => ⟨{x}, {y}, isOpen_discrete _, isOpen_discrete _, rfl, rfl, disjoint_singleton.2 h⟩⟩

theorem separated_by_continuous [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {x y : X} (h : f x ≠ f y) :
    ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v :=
  let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f ⁻¹' u, f ⁻¹' v, uo.preimage hf, vo.preimage hf, xu, yv, uv.preimage _⟩

theorem separated_by_isOpenEmbedding [TopologicalSpace Y] [T2Space X]
    {f : X → Y} (hf : IsOpenEmbedding f) {x y : X} (h : x ≠ y) :
    ∃ u v : Set Y, IsOpen u ∧ IsOpen v ∧ f x ∈ u ∧ f y ∈ v ∧ Disjoint u v :=
  let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f '' u, f '' v, hf.isOpenMap _ uo, hf.isOpenMap _ vo, mem_image_of_mem _ xu,
    mem_image_of_mem _ yv, disjoint_image_of_injective hf.injective uv⟩

instance {p : X → Prop} [T2Space X] : T2Space (Subtype p) := inferInstance

instance Prod.t2Space [T2Space X] [TopologicalSpace Y] [T2Space Y] : T2Space (X × Y) :=
  inferInstance

/-- If the codomain of an injective continuous function is a Hausdorff space, then so is its
domain. -/
theorem T2Space.of_injective_continuous [TopologicalSpace Y] [T2Space Y] {f : X → Y}
    (hinj : Injective f) (hc : Continuous f) : T2Space X :=
  ⟨fun _ _ h => separated_by_continuous hc (hinj.ne h)⟩

/-- If the codomain of a topological embedding is a Hausdorff space, then so is its domain.
See also `T2Space.of_continuous_injective`. -/
theorem Topology.IsEmbedding.t2Space [TopologicalSpace Y] [T2Space Y] {f : X → Y}
    (hf : IsEmbedding f) : T2Space X :=
  .of_injective_continuous hf.injective hf.continuous

protected theorem Homeomorph.t2Space [TopologicalSpace Y] [T2Space X] (h : X ≃ₜ Y) : T2Space Y :=
  h.symm.isEmbedding.t2Space

instance ULift.instT2Space [T2Space X] : T2Space (ULift X) :=
  IsEmbedding.uliftDown.t2Space

instance [T2Space X] [TopologicalSpace Y] [T2Space Y] :
    T2Space (X ⊕ Y) := by
  constructor
  rintro (x | x) (y | y) h
  · exact separated_by_isOpenEmbedding .inl <| ne_of_apply_ne _ h
  · exact separated_by_continuous continuous_isLeft <| by simp
  · exact separated_by_continuous continuous_isLeft <| by simp
  · exact separated_by_isOpenEmbedding .inr <| ne_of_apply_ne _ h

instance Pi.t2Space {Y : X → Type v} [∀ a, TopologicalSpace (Y a)]
    [∀ a, T2Space (Y a)] : T2Space (∀ a, Y a) :=
  inferInstance

instance Sigma.t2Space {ι} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ a, T2Space (X a)] :
    T2Space (Σ i, X i) := by
  constructor
  rintro ⟨i, x⟩ ⟨j, y⟩ neq
  rcases eq_or_ne i j with (rfl | h)
  · replace neq : x ≠ y := ne_of_apply_ne _ neq
    exact separated_by_isOpenEmbedding .sigmaMk neq
  · let _ := (⊥ : TopologicalSpace ι); have : DiscreteTopology ι := ⟨rfl⟩
    exact separated_by_continuous (continuous_def.2 fun u _ => isOpen_sigma_fst_preimage u) h

section
variable (X)

/-- The smallest equivalence relation on a topological space giving a T2 quotient. -/
def t2Setoid : Setoid X := sInf {s | T2Space (Quotient s)}

/-- The largest T2 quotient of a topological space. This construction is left-adjoint to the
inclusion of T2 spaces into all topological spaces. -/
def T2Quotient := Quotient (t2Setoid X)

@[deprecated (since := "2025-05-15")] alias t2Quotient := T2Quotient

namespace T2Quotient
variable {X}

instance : TopologicalSpace (T2Quotient X) :=
  inferInstanceAs <| TopologicalSpace (Quotient _)

/-- The map from a topological space to its largest T2 quotient. -/
def mk : X → T2Quotient X := Quotient.mk (t2Setoid X)

lemma mk_eq {x y : X} : mk x = mk y ↔ ∀ s : Setoid X, T2Space (Quotient s) → s x y :=
  Setoid.quotient_mk_sInf_eq

variable (X)

lemma surjective_mk : Surjective (mk : X → T2Quotient X) := Quotient.mk_surjective

lemma continuous_mk : Continuous (mk : X → T2Quotient X) :=
  continuous_quotient_mk'

variable {X}

@[elab_as_elim]
protected lemma inductionOn {motive : T2Quotient X → Prop} (q : T2Quotient X)
    (h : ∀ x, motive (T2Quotient.mk x)) : motive q := Quotient.inductionOn q h

@[elab_as_elim]
protected lemma inductionOn₂ [TopologicalSpace Y] {motive : T2Quotient X → T2Quotient Y → Prop}
    (q : T2Quotient X) (q' : T2Quotient Y) (h : ∀ x y, motive (mk x) (mk y)) : motive q q' :=
  Quotient.inductionOn₂ q q' h

/-- The largest T2 quotient of a topological space is indeed T2. -/
instance : T2Space (T2Quotient X) := by
  rw [t2Space_iff]
  rintro ⟨x⟩ ⟨y⟩ (h : ¬ T2Quotient.mk x = T2Quotient.mk y)
  obtain ⟨s, hs, hsxy⟩ : ∃ s, T2Space (Quotient s) ∧ Quotient.mk s x ≠ Quotient.mk s y := by
    simpa [T2Quotient.mk_eq] using h
  exact separated_by_continuous (continuous_map_sInf (by exact hs)) hsxy

lemma compatible {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) : letI _ := t2Setoid X
    ∀ (a b : X), a ≈ b → f a = f b := by
  change t2Setoid X ≤ Setoid.ker f
  exact sInf_le <| .of_injective_continuous
    (Setoid.ker_lift_injective _) (hf.quotient_lift fun _ _ ↦ id)

/-- The universal property of the largest T2 quotient of a topological space `X`: any continuous
map from `X` to a T2 space `Y` uniquely factors through `T2Quotient X`. This declaration builds the
factored map. Its continuity is `T2Quotient.continuous_lift`, the fact that it indeed factors the
original map is `T2Quotient.lift_mk` and uniqueness is `T2Quotient.unique_lift`. -/
def lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) : T2Quotient X → Y :=
  Quotient.lift f (T2Quotient.compatible hf)

lemma continuous_lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) : Continuous (T2Quotient.lift hf) :=
  continuous_coinduced_dom.mpr hf

@[simp]
lemma lift_mk {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (x : X) : lift hf (mk x) = f x :=
  Quotient.lift_mk (s := t2Setoid X) f (T2Quotient.compatible hf) x

lemma unique_lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {g : T2Quotient X → Y} (hfg : g ∘ mk = f) :
    g = lift hf := by
  apply surjective_mk X |>.right_cancellable |>.mp <| funext _
  simp [← hfg]

end T2Quotient
end

variable {Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

theorem isClosed_eq [T2Space X] {f g : Y → X} (hf : Continuous f) (hg : Continuous g) :
    IsClosed { y : Y | f y = g y } :=
  continuous_iff_isClosed.mp (hf.prodMk hg) _ isClosed_diagonal

/-- If functions `f` and `g` are continuous on a closed set `s`,
then the set of points `x ∈ s` such that `f x = g x` is a closed set. -/
protected theorem IsClosed.isClosed_eq [T2Space Y] {f g : X → Y} {s : Set X} (hs : IsClosed s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) : IsClosed {x ∈ s | f x = g x} :=
  (hf.prodMk hg).preimage_isClosed_of_isClosed hs isClosed_diagonal

theorem isOpen_ne_fun [T2Space X] {f g : Y → X} (hf : Continuous f) (hg : Continuous g) :
    IsOpen { y : Y | f y ≠ g y } :=
  isOpen_compl_iff.mpr <| isClosed_eq hf hg

/-- If two continuous maps are equal on `s`, then they are equal on the closure of `s`. See also
`Set.EqOn.of_subset_closure` for a more general version. -/
protected theorem Set.EqOn.closure [T2Space X] {s : Set Y} {f g : Y → X} (h : EqOn f g s)
    (hf : Continuous f) (hg : Continuous g) : EqOn f g (closure s) :=
  closure_minimal h (isClosed_eq hf hg)

/-- If two continuous functions are equal on a dense set, then they are equal. -/
theorem Continuous.ext_on [T2Space X] {s : Set Y} (hs : Dense s) {f g : Y → X} (hf : Continuous f)
    (hg : Continuous g) (h : EqOn f g s) : f = g :=
  funext fun x => h.closure hf hg (hs x)

theorem eqOn_closure₂' [T2Space Z] {s : Set X} {t : Set Y} {f g : X → Y → Z}
    (h : ∀ x ∈ s, ∀ y ∈ t, f x y = g x y) (hf₁ : ∀ x, Continuous (f x))
    (hf₂ : ∀ y, Continuous fun x => f x y) (hg₁ : ∀ x, Continuous (g x))
    (hg₂ : ∀ y, Continuous fun x => g x y) : ∀ x ∈ closure s, ∀ y ∈ closure t, f x y = g x y :=
  suffices closure s ⊆ ⋂ y ∈ closure t, { x | f x y = g x y } by simpa only [subset_def, mem_iInter]
  (closure_minimal fun x hx => mem_iInter₂.2 <| Set.EqOn.closure (h x hx) (hf₁ _) (hg₁ _)) <|
    isClosed_biInter fun _ _ => isClosed_eq (hf₂ _) (hg₂ _)

theorem eqOn_closure₂ [T2Space Z] {s : Set X} {t : Set Y} {f g : X → Y → Z}
    (h : ∀ x ∈ s, ∀ y ∈ t, f x y = g x y) (hf : Continuous (uncurry f))
    (hg : Continuous (uncurry g)) : ∀ x ∈ closure s, ∀ y ∈ closure t, f x y = g x y :=
  eqOn_closure₂' h hf.uncurry_left hf.uncurry_right hg.uncurry_left hg.uncurry_right

/-- If `f x = g x` for all `x ∈ s` and `f`, `g` are continuous on `t`, `s ⊆ t ⊆ closure s`, then
`f x = g x` for all `x ∈ t`. See also `Set.EqOn.closure`. -/
theorem Set.EqOn.of_subset_closure [T2Space Y] {s t : Set X} {f g : X → Y} (h : EqOn f g s)
    (hf : ContinuousOn f t) (hg : ContinuousOn g t) (hst : s ⊆ t) (hts : t ⊆ closure s) :
    EqOn f g t := by
  intro x hx
  have : (𝓝[s] x).NeBot := mem_closure_iff_clusterPt.mp (hts hx)
  exact
    tendsto_nhds_unique_of_eventuallyEq ((hf x hx).mono_left <| nhdsWithin_mono _ hst)
      ((hg x hx).mono_left <| nhdsWithin_mono _ hst) (h.eventuallyEq_of_mem self_mem_nhdsWithin)

theorem Function.LeftInverse.isClosed_range [T2Space X] {f : X → Y} {g : Y → X}
    (h : Function.LeftInverse f g) (hf : Continuous f) (hg : Continuous g) : IsClosed (range g) :=
  have : EqOn (g ∘ f) id (closure <| range g) :=
    h.rightInvOn_range.eqOn.closure (hg.comp hf) continuous_id
  isClosed_of_closure_subset fun x hx => ⟨f x, this hx⟩

theorem Function.LeftInverse.isClosedEmbedding [T2Space X] {f : X → Y} {g : Y → X}
    (h : Function.LeftInverse f g) (hf : Continuous f) (hg : Continuous g) : IsClosedEmbedding g :=
  ⟨.of_leftInverse h hf hg, h.isClosed_range hf hg⟩

theorem SeparatedNhds.of_isCompact_isCompact [T2Space X] {s t : Set X} (hs : IsCompact s)
    (ht : IsCompact t) (hst : Disjoint s t) : SeparatedNhds s t := by
  simp only [SeparatedNhds, prod_subset_compl_diagonal_iff_disjoint.symm] at hst ⊢
  exact generalized_tube_lemma hs ht isClosed_diagonal.isOpen_compl hst

/-- In a `T2Space X`, for disjoint closed sets `s t` such that `closure sᶜ` is compact,
there are neighbourhoods that separate `s` and `t`. -/
lemma SeparatedNhds.of_isClosed_isCompact_closure_compl_isClosed [T2Space X] {s : Set X}
    {t : Set X} (H1 : IsClosed s) (H2 : IsCompact (closure sᶜ)) (H3 : IsClosed t)
    (H4 : Disjoint s t) : SeparatedNhds s t := by
  -- Since `t` is a closed subset of the compact set `closure sᶜ`, it is compact.
  have ht : IsCompact t := .of_isClosed_subset H2 H3 <| H4.subset_compl_left.trans subset_closure
  -- we split `s` into its frontier and its interior.
  rw [← diff_union_of_subset (interior_subset (s := s))]
  -- since `t ⊆ sᶜ`, which is open, and `interior s` is open, we have
  -- `SeparatedNhds (interior s) t`, which leaves us only with the frontier.
  refine .union_left ?_ ⟨interior s, sᶜ, isOpen_interior, H1.isOpen_compl, le_rfl,
    H4.subset_compl_left, disjoint_compl_right.mono_left interior_subset⟩
  -- Since the frontier of `s` is compact (as it is a subset of `closure sᶜ`), we simply apply
  -- `SeparatedNhds_of_isCompact_isCompact`.
  rw [← H1.frontier_eq, frontier_eq_closure_inter_closure, H1.closure_eq]
  refine .of_isCompact_isCompact ?_ ht (disjoint_of_subset_left inter_subset_left H4)
  exact H2.of_isClosed_subset (H1.inter isClosed_closure) inter_subset_right

section SeparatedFinset

theorem SeparatedNhds.of_finset_finset [T2Space X] (s t : Finset X) (h : Disjoint s t) :
    SeparatedNhds (s : Set X) t :=
  .of_isCompact_isCompact s.finite_toSet.isCompact t.finite_toSet.isCompact <| mod_cast h

theorem SeparatedNhds.of_singleton_finset [T2Space X] {x : X} {s : Finset X} (h : x ∉ s) :
    SeparatedNhds ({x} : Set X) s :=
  mod_cast .of_finset_finset {x} s (Finset.disjoint_singleton_left.mpr h)

end SeparatedFinset

/-- In a `T2Space`, every compact set is closed. -/
theorem IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsCompact s) : IsClosed s :=
  isClosed_iff_forall_filter.2 fun _x _f _ hfs hfx =>
    let ⟨_y, hy, hfy⟩ := hs.exists_clusterPt hfs
    mem_of_eq_of_mem (eq_of_nhds_neBot (hfy.mono hfx).neBot).symm hy

theorem IsCompact.preimage_continuous [CompactSpace X] [T2Space Y] {f : X → Y} {s : Set Y}
    (hs : IsCompact s) (hf : Continuous f) : IsCompact (f ⁻¹' s) :=
  (hs.isClosed.preimage hf).isCompact

lemma Pi.isCompact_iff {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] {s : Set (Π i, X i)} :
    IsCompact s ↔ IsClosed s ∧ ∀ i, IsCompact (eval i '' s) := by
  constructor <;> intro H
  · exact ⟨H.isClosed, fun i ↦ H.image <| continuous_apply i⟩
  · exact IsCompact.of_isClosed_subset (isCompact_univ_pi H.2) H.1 (subset_pi_eval_image univ s)

lemma Pi.isCompact_closure_iff {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] {s : Set (Π i, X i)} :
    IsCompact (closure s) ↔ ∀ i, IsCompact (closure <| eval i '' s) := by
  simp_rw [← exists_isCompact_superset_iff, Pi.exists_compact_superset_iff, image_subset_iff]

/-- If `V : ι → Set X` is a decreasing family of compact sets then any neighborhood of
`⋂ i, V i` contains some `V i`. This is a version of `exists_subset_nhds_of_isCompact'` where we
don't need to assume each `V i` closed because it follows from compactness since `X` is
assumed to be Hausdorff. -/
theorem exists_subset_nhds_of_isCompact [T2Space X] {ι : Type*} [Nonempty ι] {V : ι → Set X}
    (hV : Directed (· ⊇ ·) V) (hV_cpct : ∀ i, IsCompact (V i)) {U : Set X}
    (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U :=
  exists_subset_nhds_of_isCompact' hV hV_cpct (fun i => (hV_cpct i).isClosed) hU

theorem CompactExhaustion.isClosed [T2Space X] (K : CompactExhaustion X) (n : ℕ) : IsClosed (K n) :=
  (K.isCompact n).isClosed

theorem IsCompact.inter [T2Space X] {s t : Set X} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ∩ t) :=
  hs.inter_right <| ht.isClosed

theorem image_closure_of_isCompact [T2Space Y] {s : Set X} (hs : IsCompact (closure s)) {f : X → Y}
    (hf : ContinuousOn f (closure s)) : f '' closure s = closure (f '' s) :=
  Subset.antisymm hf.image_closure <|
    closure_minimal (image_mono subset_closure) (hs.image_of_continuousOn hf).isClosed

/-- Two continuous maps into a Hausdorff space agree at a point iff they agree in a
neighborhood. -/
theorem ContinuousAt.ne_iff_eventually_ne [T2Space Y] {x : X} {f g : X → Y}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    f x ≠ g x ↔ ∀ᶠ x in 𝓝 x, f x ≠ g x := by
  constructor <;> intro hfg
  · obtain ⟨Uf, Ug, h₁U, h₂U, h₃U, h₄U, h₅U⟩ := t2_separation hfg
    rw [Set.disjoint_iff_inter_eq_empty] at h₅U
    filter_upwards [inter_mem
      (hf.preimage_mem_nhds (IsOpen.mem_nhds h₁U h₃U))
      (hg.preimage_mem_nhds (IsOpen.mem_nhds h₂U h₄U))]
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_preimage] at hx
    by_contra H
    rw [H] at hx
    have : g x ∈ Uf ∩ Ug := hx
    simp [h₅U] at this
  · obtain ⟨t, h₁t, h₂t, h₃t⟩ := eventually_nhds_iff.1 hfg
    exact h₁t x h₃t

/-- **Local identity principle** for continuous maps: Two continuous maps into a Hausdorff space
agree in a punctured neighborhood of a non-isolated point iff they agree in a neighborhood. -/
theorem ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE [T2Space Y] {x : X} {f g : X → Y}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) [(𝓝[≠] x).NeBot] :
    f =ᶠ[𝓝[≠] x] g ↔ f =ᶠ[𝓝 x] g := by
  constructor <;> intro hfg
  · apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE hfg
    by_contra hCon
    obtain ⟨a, ha⟩ : {x | f x ≠ g x ∧ f x = g x}.Nonempty := by
      have h₁ := (eventually_nhdsWithin_of_eventually_nhds
        ((hf.ne_iff_eventually_ne hg).1 hCon)).and hfg
      have h₂ : ∅ ∉ 𝓝[≠] x := by exact empty_notMem (𝓝[≠] x)
      simp_all
    simp at ha
  · exact hfg.filter_mono nhdsWithin_le_nhds

@[deprecated (since := "2025-05-22")]
alias ContinuousAt.eventuallyEq_nhd_iff_eventuallyEq_nhdNE :=
  ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE

/-- A continuous map from a compact space to a Hausdorff space is a closed map. -/
protected theorem Continuous.isClosedMap [CompactSpace X] [T2Space Y] {f : X → Y}
    (h : Continuous f) : IsClosedMap f := fun _s hs => (hs.isCompact.image h).isClosed

/-- A continuous injective map from a compact space to a Hausdorff space is a closed embedding. -/
theorem Continuous.isClosedEmbedding [CompactSpace X] [T2Space Y] {f : X → Y} (h : Continuous f)
    (hf : Function.Injective f) : IsClosedEmbedding f :=
  .of_continuous_injective_isClosedMap h hf h.isClosedMap

/-- A continuous surjective map from a compact space to a Hausdorff space is a quotient map. -/
theorem IsQuotientMap.of_surjective_continuous [CompactSpace X] [T2Space Y] {f : X → Y}
    (hsurj : Surjective f) (hcont : Continuous f) : IsQuotientMap f :=
  hcont.isClosedMap.isQuotientMap hcont hsurj

theorem isPreirreducible_iff_subsingleton [T2Space X] {S : Set X} :
    IsPreirreducible S ↔ S.Subsingleton := by
  refine ⟨fun h x hx y hy => ?_, Set.Subsingleton.isPreirreducible⟩
  by_contra e
  obtain ⟨U, V, hU, hV, hxU, hyV, h'⟩ := t2_separation e
  exact ((h U V hU hV ⟨x, hx, hxU⟩ ⟨y, hy, hyV⟩).mono inter_subset_right).not_disjoint h'

-- todo: use `alias` + `attribute [protected]` once we get `attribute [protected]`
protected lemma IsPreirreducible.subsingleton [T2Space X] {S : Set X} (h : IsPreirreducible S) :
    S.Subsingleton :=
  isPreirreducible_iff_subsingleton.1 h

theorem isIrreducible_iff_singleton [T2Space X] {S : Set X} : IsIrreducible S ↔ ∃ x, S = {x} := by
  rw [IsIrreducible, isPreirreducible_iff_subsingleton,
    exists_eq_singleton_iff_nonempty_subsingleton]

/-- There does not exist a nontrivial preirreducible T₂ space. -/
theorem not_preirreducible_nontrivial_t2 (X) [TopologicalSpace X] [PreirreducibleSpace X]
    [Nontrivial X] [T2Space X] : False :=
  (PreirreducibleSpace.isPreirreducible_univ (X := X)).subsingleton.not_nontrivial nontrivial_univ

theorem t2Space_antitone {X : Type*} : Antitone (@T2Space X) :=
  fun inst₁ inst₂ h_top h_t2 ↦ @T2Space.of_injective_continuous _ _ inst₁ inst₂
    h_t2 _ Function.injective_id <| continuous_id_of_le h_top

end Separation
