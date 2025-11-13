/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Topology.Bases
import Mathlib.Order.Filter.CountableInter
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Lindelöf sets and Lindelöf spaces

## Main definitions

We define the following properties for sets in a topological space:

* `IsLindelof s`: Two definitions are possible here. The more standard definition is that
  every open cover that contains `s` contains a countable subcover. We choose for the equivalent
  definition where we require that every nontrivial filter on `s` with the countable intersection
  property has a clusterpoint. Equivalence is established in `isLindelof_iff_countable_subcover`.
* `LindelofSpace X`: `X` is Lindelöf if it is Lindelöf as a set.
* `NonLindelofSpace`: a space that is not a Lindëlof space, e.g. the Long Line.

## Main results

* `isLindelof_iff_countable_subcover`: A set is Lindelöf iff every open cover has a
  countable subcover.

## Implementation details

* This API is mainly based on the API for IsCompact and follows notation and style as much
  as possible.
-/
open Set Filter Topology TopologicalSpace


universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Lindelof

/-- A set `s` is Lindelöf if every nontrivial filter `f` with the countable intersection
  property that contains `s`, has a clusterpoint in `s`. The filter-free definition is given by
  `isLindelof_iff_countable_subcover`. -/
def IsLindelof (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f] [CountableInterFilter f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f

/-- The complement to a Lindelöf set belongs to a filter `f` with the countable intersection
  property if it belongs to each filter `𝓝 x ⊓ f`, `x ∈ s`. -/
theorem IsLindelof.compl_mem_sets (hs : IsLindelof s) {f : Filter X} [CountableInterFilter f]
    (hf : ∀ x ∈ s, sᶜ ∈ 𝓝 x ⊓ f) : sᶜ ∈ f := by
  contrapose! hf
  simp only [notMem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact hs inf_le_right

/-- The complement to a Lindelöf set belongs to a filter `f` with the countable intersection
  property if each `x ∈ s` has a neighborhood `t` within `s` such that `tᶜ` belongs to `f`. -/
theorem IsLindelof.compl_mem_sets_of_nhdsWithin (hs : IsLindelof s) {f : Filter X}
    [CountableInterFilter f] (hf : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, tᶜ ∈ f) : sᶜ ∈ f := by
  refine hs.compl_mem_sets fun x hx ↦ ?_
  rw [← disjoint_principal_right, disjoint_right_comm, (basis_sets _).disjoint_iff_left]
  exact hf x hx

/-- If `p : Set X → Prop` is stable under restriction and union, and each point `x`
  of a Lindelöf set `s` has a neighborhood `t` within `s` such that `p t`, then `p s` holds. -/
@[elab_as_elim]
theorem IsLindelof.induction_on (hs : IsLindelof s) {p : Set X → Prop}
    (hmono : ∀ ⦃s t⦄, s ⊆ t → p t → p s)
    (hcountable_union : ∀ (S : Set (Set X)), S.Countable → (∀ s ∈ S, p s) → p (⋃₀ S))
    (hnhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, p t) : p s := by
  let f : Filter X := ofCountableUnion p hcountable_union (fun t ht _ hsub ↦ hmono hsub ht)
  have : sᶜ ∈ f := hs.compl_mem_sets_of_nhdsWithin (by simpa [f] using hnhds)
  rwa [← compl_compl s]

/-- The intersection of a Lindelöf set and a closed set is a Lindelöf set. -/
theorem IsLindelof.inter_right (hs : IsLindelof s) (ht : IsClosed t) : IsLindelof (s ∩ t) := by
  intro f hnf _ hstf
  rw [← inf_principal, le_inf_iff] at hstf
  obtain ⟨x, hsx, hx⟩ : ∃ x ∈ s, ClusterPt x f := hs hstf.1
  have hxt : x ∈ t := ht.mem_of_nhdsWithin_neBot <| hx.mono hstf.2
  exact ⟨x, ⟨hsx, hxt⟩, hx⟩

/-- The intersection of a closed set and a Lindelöf set is a Lindelöf set. -/
theorem IsLindelof.inter_left (ht : IsLindelof t) (hs : IsClosed s) : IsLindelof (s ∩ t) :=
  inter_comm t s ▸ ht.inter_right hs

/-- The set difference of a Lindelöf set and an open set is a Lindelöf set. -/
theorem IsLindelof.diff (hs : IsLindelof s) (ht : IsOpen t) : IsLindelof (s \ t) :=
  hs.inter_right (isClosed_compl_iff.mpr ht)

/-- A closed subset of a Lindelöf set is a Lindelöf set. -/
theorem IsLindelof.of_isClosed_subset (hs : IsLindelof s) (ht : IsClosed t) (h : t ⊆ s) :
    IsLindelof t := inter_eq_self_of_subset_right h ▸ hs.inter_right ht

/-- A continuous image of a Lindelöf set is a Lindelöf set. -/
theorem IsLindelof.image_of_continuousOn {f : X → Y} (hs : IsLindelof s) (hf : ContinuousOn f s) :
    IsLindelof (f '' s) := by
  intro l lne _ ls
  have : NeBot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_neBot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨x, hxs, hx⟩ : ∃ x ∈ s, ClusterPt x (l.comap f ⊓ 𝓟 s) := @hs _ this _ inf_le_right
  haveI := hx.neBot
  use f x, mem_image_of_mem f hxs
  have : Tendsto f (𝓝 x ⊓ (comap f l ⊓ 𝓟 s)) (𝓝 (f x) ⊓ l) := by
    convert (hf x hxs).inf (@tendsto_comap _ _ f l) using 1
    rw [nhdsWithin]
    ac_rfl
  exact this.neBot

/-- A continuous image of a Lindelöf set is a Lindelöf set within the codomain. -/
theorem IsLindelof.image {f : X → Y} (hs : IsLindelof s) (hf : Continuous f) :
    IsLindelof (f '' s) := hs.image_of_continuousOn hf.continuousOn

/-- A filter with the countable intersection property that is finer than the principal filter on
a Lindelöf set `s` contains any open set that contains all clusterpoints of `s`. -/
theorem IsLindelof.adherence_nhdset {f : Filter X} [CountableInterFilter f] (hs : IsLindelof s)
    (hf₂ : f ≤ 𝓟 s) (ht₁ : IsOpen t) (ht₂ : ∀ x ∈ s, ClusterPt x f → x ∈ t) : t ∈ f :=
  (eq_or_neBot _).casesOn mem_of_eq_bot fun _ ↦
    let ⟨x, hx, hfx⟩ := @hs (f ⊓ 𝓟 tᶜ) _ _ <| inf_le_of_left_le hf₂
    have : x ∈ t := ht₂ x hx hfx.of_inf_left
    have : tᶜ ∩ t ∈ 𝓝[tᶜ] x := inter_mem_nhdsWithin _ (ht₁.mem_nhds this)
    have A : 𝓝[tᶜ] x = ⊥ := empty_mem_iff_bot.1 <| compl_inter_self t ▸ this
    have : 𝓝[tᶜ] x ≠ ⊥ := hfx.of_inf_right.ne
    absurd A this

/-- For every open cover of a Lindelöf set, there exists a countable subcover. -/
theorem IsLindelof.elim_countable_subcover {ι : Type v} (hs : IsLindelof s) (U : ι → Set X)
    (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) :
    ∃ r : Set ι, r.Countable ∧ (s ⊆ ⋃ i ∈ r, U i) := by
  have hmono : ∀ ⦃s t : Set X⦄, s ⊆ t → (∃ r : Set ι, r.Countable ∧ t ⊆ ⋃ i ∈ r, U i)
      → (∃ r : Set ι, r.Countable ∧ s ⊆ ⋃ i ∈ r, U i) := by
    intro _ _ hst ⟨r, ⟨hrcountable, hsub⟩⟩
    exact ⟨r, hrcountable, Subset.trans hst hsub⟩
  have hcountable_union : ∀ (S : Set (Set X)), S.Countable
      → (∀ s ∈ S, ∃ r : Set ι, r.Countable ∧ (s ⊆ ⋃ i ∈ r, U i))
      → ∃ r : Set ι, r.Countable ∧ (⋃₀ S ⊆ ⋃ i ∈ r, U i) := by
    intro S hS hsr
    choose! r hr using hsr
    refine ⟨⋃ s ∈ S, r s, hS.biUnion_iff.mpr (fun s hs ↦ (hr s hs).1), ?_⟩
    refine sUnion_subset ?h.right.h
    simp only [mem_iUnion, exists_prop, iUnion_exists, biUnion_and']
    exact fun i is x hx ↦ mem_biUnion is ((hr i is).2 hx)
  have h_nhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∃ r : Set ι, r.Countable ∧ (t ⊆ ⋃ i ∈ r, U i) := by
    intro x hx
    let ⟨i, hi⟩ := mem_iUnion.1 (hsU hx)
    refine ⟨U i, mem_nhdsWithin_of_mem_nhds ((hUo i).mem_nhds hi), {i}, by simp, ?_⟩
    simp only [mem_singleton_iff, iUnion_iUnion_eq_left]
    exact Subset.refl _
  exact hs.induction_on hmono hcountable_union h_nhds

theorem IsLindelof.elim_nhds_subcover' (hs : IsLindelof s) (U : ∀ x ∈ s, Set X)
    (hU : ∀ x (hx : x ∈ s), U x ‹x ∈ s› ∈ 𝓝 x) :
    ∃ t : Set s, t.Countable ∧ s ⊆ ⋃ x ∈ t, U (x : s) x.2 := by
  have := hs.elim_countable_subcover (fun x : s ↦ interior (U x x.2)) (fun _ ↦ isOpen_interior)
    fun x hx ↦
      mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 <| hU _ _⟩
  rcases this with ⟨r, ⟨hr, hs⟩⟩
  use r, hr
  apply Subset.trans hs
  apply iUnion₂_subset
  intro i hi
  apply Subset.trans interior_subset
  exact subset_iUnion_of_subset i (subset_iUnion_of_subset hi (Subset.refl _))

theorem IsLindelof.elim_nhds_subcover (hs : IsLindelof s) (U : X → Set X)
    (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
    ∃ t : Set X, t.Countable ∧ (∀ x ∈ t, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x := by
  let ⟨t, ⟨htc, htsub⟩⟩ := hs.elim_nhds_subcover' (fun x _ ↦ U x) hU
  refine ⟨↑t, Countable.image htc Subtype.val, ?_⟩
  constructor
  · intro _
    simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, forall_exists_index]
    tauto
  · have : ⋃ x ∈ t, U ↑x = ⋃ x ∈ Subtype.val '' t, U x := biUnion_image.symm
    rwa [← this]

/-- For every nonempty open cover of a Lindelöf set, there exists a subcover indexed by ℕ. -/
theorem IsLindelof.indexed_countable_subcover {ι : Type v} [Nonempty ι]
    (hs : IsLindelof s) (U : ι → Set X) (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) :
    ∃ f : ℕ → ι, s ⊆ ⋃ n, U (f n) := by
  obtain ⟨c, ⟨c_count, c_cov⟩⟩ := hs.elim_countable_subcover U hUo hsU
  rcases c.eq_empty_or_nonempty with rfl | c_nonempty
  · simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty] at c_cov
    simp only [subset_eq_empty c_cov rfl, empty_subset, exists_const]
  obtain ⟨f, f_surj⟩ := (Set.countable_iff_exists_surjective c_nonempty).mp c_count
  refine ⟨fun x ↦ f x, c_cov.trans <| iUnion₂_subset_iff.mpr (?_ : ∀ i ∈ c, U i ⊆ ⋃ n, U (f n))⟩
  intro x hx
  obtain ⟨n, hn⟩ := f_surj ⟨x, hx⟩
  exact subset_iUnion_of_subset n <| subset_of_eq (by rw [hn])

/-- The neighborhood filter of a Lindelöf set is disjoint with a filter `l` with the countable
intersection property if and only if the neighborhood filter of each point of this set
is disjoint with `l`. -/
theorem IsLindelof.disjoint_nhdsSet_left {l : Filter X} [CountableInterFilter l]
    (hs : IsLindelof s) :
    Disjoint (𝓝ˢ s) l ↔ ∀ x ∈ s, Disjoint (𝓝 x) l := by
  refine ⟨fun h x hx ↦ h.mono_left <| nhds_le_nhdsSet hx, fun H ↦ ?_⟩
  choose! U hxU hUl using fun x hx ↦ (nhds_basis_opens x).disjoint_iff_left.1 (H x hx)
  choose hxU hUo using hxU
  rcases hs.elim_nhds_subcover U fun x hx ↦ (hUo x hx).mem_nhds (hxU x hx) with ⟨t, htc, hts, hst⟩
  refine (hasBasis_nhdsSet _).disjoint_iff_left.2
    ⟨⋃ x ∈ t, U x, ⟨isOpen_biUnion fun x hx ↦ hUo x (hts x hx), hst⟩, ?_⟩
  rw [compl_iUnion₂]
  exact (countable_bInter_mem htc).mpr (fun i hi ↦ hUl _ (hts _ hi))

/-- A filter `l` with the countable intersection property is disjoint with the neighborhood
filter of a Lindelöf set if and only if it is disjoint with the neighborhood filter of each point
of this set. -/
theorem IsLindelof.disjoint_nhdsSet_right {l : Filter X} [CountableInterFilter l]
    (hs : IsLindelof s) : Disjoint l (𝓝ˢ s) ↔ ∀ x ∈ s, Disjoint l (𝓝 x) := by
  simpa only [disjoint_comm] using hs.disjoint_nhdsSet_left

/-- For every family of closed sets whose intersection avoids a Lindelöf set,
there exists a countable subfamily whose intersection avoids this Lindelöf set. -/
theorem IsLindelof.elim_countable_subfamily_closed {ι : Type v} (hs : IsLindelof s)
    (t : ι → Set X) (htc : ∀ i, IsClosed (t i)) (hst : (s ∩ ⋂ i, t i) = ∅) :
    ∃ u : Set ι, u.Countable ∧ (s ∩ ⋂ i ∈ u, t i) = ∅ := by
  let U := tᶜ
  have hUo : ∀ i, IsOpen (U i) := by simp only [U, Pi.compl_apply, isOpen_compl_iff]; exact htc
  have hsU : s ⊆ ⋃ i, U i := by
    simp only [U, Pi.compl_apply]
    rw [← compl_iInter]
    apply disjoint_compl_left_iff_subset.mp
    simp only [compl_iInter, compl_iUnion, compl_compl]
    apply Disjoint.symm
    exact disjoint_iff_inter_eq_empty.mpr hst
  rcases hs.elim_countable_subcover U hUo hsU with ⟨u, ⟨hucount, husub⟩⟩
  use u, hucount
  rw [← disjoint_compl_left_iff_subset] at husub
  simp only [U, Pi.compl_apply, compl_iUnion, compl_compl] at husub
  exact disjoint_iff_inter_eq_empty.mp (Disjoint.symm husub)

/-- To show that a Lindelöf set intersects the intersection of a family of closed sets,
  it is sufficient to show that it intersects every countable subfamily. -/
theorem IsLindelof.inter_iInter_nonempty {ι : Type v} (hs : IsLindelof s) (t : ι → Set X)
    (htc : ∀ i, IsClosed (t i)) (hst : ∀ u : Set ι, u.Countable ∧ (s ∩ ⋂ i ∈ u, t i).Nonempty) :
    (s ∩ ⋂ i, t i).Nonempty := by
  contrapose! hst
  rcases hs.elim_countable_subfamily_closed t htc hst with ⟨u, ⟨_, husub⟩⟩
  exact ⟨u, fun _ ↦ husub⟩

/-- For every open cover of a Lindelöf set, there exists a countable subcover. -/
theorem IsLindelof.elim_countable_subcover_image {b : Set ι} {c : ι → Set X} (hs : IsLindelof s)
    (hc₁ : ∀ i ∈ b, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i ∈ b, c i) :
    ∃ b', b' ⊆ b ∧ Set.Countable b' ∧ s ⊆ ⋃ i ∈ b', c i := by
  simp only [Subtype.forall', biUnion_eq_iUnion] at hc₁ hc₂
  rcases hs.elim_countable_subcover (fun i ↦ c i : b → Set X) hc₁ hc₂ with ⟨d, hd⟩
  refine ⟨Subtype.val '' d, by simp, Countable.image hd.1 Subtype.val, ?_⟩
  rw [biUnion_image]
  exact hd.2


/-- A set `s` is Lindelöf if for every open cover of `s`, there exists a countable subcover. -/
theorem isLindelof_of_countable_subcover
    (h : ∀ {ι : Type u} (U : ι → Set X), (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) →
    ∃ t : Set ι, t.Countable ∧ s ⊆ ⋃ i ∈ t, U i) :
    IsLindelof s := fun f hf hfs ↦ by
  contrapose! h
  simp only [ClusterPt, not_neBot, ← disjoint_iff, SetCoe.forall',
    (nhds_basis_opens _).disjoint_iff_left] at h
  choose fsub U hU hUf using h
  refine ⟨s, U, fun x ↦ (hU x).2, fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).1 ⟩, ?_⟩
  intro t ht h
  have uinf := f.sets_of_superset (le_principal_iff.1 fsub) h
  have uninf : ⋂ i ∈ t, (U i)ᶜ ∈ f := (countable_bInter_mem ht).mpr (fun _ _ ↦ hUf _)
  rw [← compl_iUnion₂] at uninf
  have uninf := compl_notMem uninf
  simp only [compl_compl] at uninf
  contradiction

/-- A set `s` is Lindelöf if for every family of closed sets whose intersection avoids `s`,
there exists a countable subfamily whose intersection avoids `s`. -/
theorem isLindelof_of_countable_subfamily_closed
    (h :
      ∀ {ι : Type u} (t : ι → Set X), (∀ i, IsClosed (t i)) → (s ∩ ⋂ i, t i) = ∅ →
        ∃ u : Set ι, u.Countable ∧ (s ∩ ⋂ i ∈ u, t i) = ∅) :
    IsLindelof s :=
  isLindelof_of_countable_subcover fun U hUo hsU ↦ by
    rw [← disjoint_compl_right_iff_subset, compl_iUnion, disjoint_iff] at hsU
    rcases h (fun i ↦ (U i)ᶜ) (fun i ↦ (hUo _).isClosed_compl) hsU with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rwa [← disjoint_compl_right_iff_subset, compl_iUnion₂, disjoint_iff]

/-- A set `s` is Lindelöf if and only if
for every open cover of `s`, there exists a countable subcover. -/
theorem isLindelof_iff_countable_subcover :
    IsLindelof s ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Set ι, t.Countable ∧ s ⊆ ⋃ i ∈ t, U i :=
  ⟨fun hs ↦ hs.elim_countable_subcover, isLindelof_of_countable_subcover⟩

/-- A set `s` is Lindelöf if and only if
for every family of closed sets whose intersection avoids `s`,
there exists a countable subfamily whose intersection avoids `s`. -/
theorem isLindelof_iff_countable_subfamily_closed :
    IsLindelof s ↔ ∀ {ι : Type u} (t : ι → Set X),
    (∀ i, IsClosed (t i)) → (s ∩ ⋂ i, t i) = ∅
    → ∃ u : Set ι, u.Countable ∧ (s ∩ ⋂ i ∈ u, t i) = ∅ :=
  ⟨fun hs ↦ hs.elim_countable_subfamily_closed, isLindelof_of_countable_subfamily_closed⟩

/-- The empty set is a Lindelof set. -/
@[simp]
theorem isLindelof_empty : IsLindelof (∅ : Set X) := fun _f hnf _ hsf ↦
  Not.elim hnf.ne <| empty_mem_iff_bot.1 <| le_principal_iff.1 hsf

/-- A singleton set is a Lindelof set. -/
@[simp]
theorem isLindelof_singleton {x : X} : IsLindelof ({x} : Set X) := fun _ hf _ hfa ↦
  ⟨x, rfl, ClusterPt.of_le_nhds'
    (hfa.trans <| by simpa only [principal_singleton] using pure_le_nhds x) hf⟩

theorem Set.Subsingleton.isLindelof (hs : s.Subsingleton) : IsLindelof s :=
  Subsingleton.induction_on hs isLindelof_empty fun _ ↦ isLindelof_singleton

theorem Set.Countable.isLindelof_biUnion {s : Set ι} {f : ι → Set X} (hs : s.Countable)
    (hf : ∀ i ∈ s, IsLindelof (f i)) : IsLindelof (⋃ i ∈ s, f i) := by
  apply isLindelof_of_countable_subcover
  intro i U hU hUcover
  have hiU : ∀ i ∈ s, f i ⊆ ⋃ i, U i :=
    fun _ is ↦ _root_.subset_trans (subset_biUnion_of_mem is) hUcover
  have iSets := fun i is ↦ (hf i is).elim_countable_subcover U hU (hiU i is)
  choose! r hr using iSets
  use ⋃ i ∈ s, r i
  constructor
  · refine (Countable.biUnion_iff hs).mpr ?h.left.a
    exact fun s hs ↦ (hr s hs).1
  · refine iUnion₂_subset ?h.right.h
    intro i is
    simp only [mem_iUnion, exists_prop, iUnion_exists, biUnion_and']
    intro x hx
    exact mem_biUnion is ((hr i is).2 hx)


theorem Set.Finite.isLindelof_biUnion {s : Set ι} {f : ι → Set X} (hs : s.Finite)
    (hf : ∀ i ∈ s, IsLindelof (f i)) : IsLindelof (⋃ i ∈ s, f i) :=
  Set.Countable.isLindelof_biUnion (countable hs) hf

theorem Finset.isLindelof_biUnion (s : Finset ι) {f : ι → Set X} (hf : ∀ i ∈ s, IsLindelof (f i)) :
    IsLindelof (⋃ i ∈ s, f i) :=
  s.finite_toSet.isLindelof_biUnion hf

theorem isLindelof_accumulate {K : ℕ → Set X} (hK : ∀ n, IsLindelof (K n)) (n : ℕ) :
    IsLindelof (Accumulate K n) :=
  (finite_le_nat n).isLindelof_biUnion fun k _ => hK k

theorem Set.Countable.isLindelof_sUnion {S : Set (Set X)} (hf : S.Countable)
    (hc : ∀ s ∈ S, IsLindelof s) : IsLindelof (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact hf.isLindelof_biUnion hc

theorem Set.Finite.isLindelof_sUnion {S : Set (Set X)} (hf : S.Finite)
    (hc : ∀ s ∈ S, IsLindelof s) : IsLindelof (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact hf.isLindelof_biUnion hc

theorem isLindelof_iUnion {ι : Sort*} {f : ι → Set X} [Countable ι] (h : ∀ i, IsLindelof (f i)) :
    IsLindelof (⋃ i, f i) := (countable_range f).isLindelof_sUnion  <| forall_mem_range.2 h

theorem Set.Countable.isLindelof (hs : s.Countable) : IsLindelof s :=
  biUnion_of_singleton s ▸ hs.isLindelof_biUnion fun _ _ => isLindelof_singleton

theorem Set.Finite.isLindelof (hs : s.Finite) : IsLindelof s :=
  biUnion_of_singleton s ▸ hs.isLindelof_biUnion fun _ _ => isLindelof_singleton

theorem IsLindelof.countable_of_discrete [DiscreteTopology X] (hs : IsLindelof s) :
    s.Countable := by
  have : ∀ x : X, ({x} : Set X) ∈ 𝓝 x := by simp [nhds_discrete]
  rcases hs.elim_nhds_subcover (fun x => {x}) fun x _ => this x with ⟨t, ht, _, hssubt⟩
  rw [biUnion_of_singleton] at hssubt
  exact ht.mono hssubt

theorem isLindelof_iff_countable [DiscreteTopology X] : IsLindelof s ↔ s.Countable :=
  ⟨fun h => h.countable_of_discrete, fun h => h.isLindelof⟩

theorem IsLindelof.union (hs : IsLindelof s) (ht : IsLindelof t) : IsLindelof (s ∪ t) := by
  rw [union_eq_iUnion]; exact isLindelof_iUnion fun b => by cases b <;> assumption

protected theorem IsLindelof.insert (hs : IsLindelof s) (a) : IsLindelof (insert a s) :=
  isLindelof_singleton.union hs

/-- If `X` has a basis consisting of compact opens, then an open set in `X` is compact open iff
it is a finite union of some elements in the basis -/
theorem isLindelof_open_iff_eq_countable_iUnion_of_isTopologicalBasis (b : ι → Set X)
    (hb : IsTopologicalBasis (Set.range b)) (hb' : ∀ i, IsLindelof (b i)) (U : Set X) :
    IsLindelof U ∧ IsOpen U ↔ ∃ s : Set ι, s.Countable ∧ U = ⋃ i ∈ s, b i := by
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨Y, f, rfl, hf⟩ := hb.open_eq_iUnion h₂
    choose f' hf' using hf
    have : b ∘ f' = f := funext hf'
    subst this
    obtain ⟨t, ht⟩ :=
      h₁.elim_countable_subcover (b ∘ f') (fun i => hb.isOpen (Set.mem_range_self _)) Subset.rfl
    refine ⟨t.image f', Countable.image (ht.1) f', le_antisymm ?_ ?_⟩
    · refine Set.Subset.trans ht.2 ?_
      simp only [Set.iUnion_subset_iff]
      intro i hi
      rw [← Set.iUnion_subtype (fun x : ι => x ∈ t.image f') fun i => b i.1]
      exact Set.subset_iUnion (fun i : t.image f' => b i) ⟨_, mem_image_of_mem _ hi⟩
    · apply Set.iUnion₂_subset
      rintro i hi
      obtain ⟨j, -, rfl⟩ := (mem_image ..).mp hi
      exact Set.subset_iUnion (b ∘ f') j
  · rintro ⟨s, hs, rfl⟩
    constructor
    · exact hs.isLindelof_biUnion fun i _ => hb' i
    · exact isOpen_biUnion fun i _ => hb.isOpen (Set.mem_range_self _)

/-- `Filter.coLindelof` is the filter generated by complements to Lindelöf sets. -/
def Filter.coLindelof (X : Type*) [TopologicalSpace X] : Filter X :=
  --`Filter.coLindelof` is the filter generated by complements to Lindelöf sets.
  ⨅ (s : Set X) (_ : IsLindelof s), 𝓟 sᶜ

theorem hasBasis_coLindelof : (coLindelof X).HasBasis IsLindelof compl :=
  hasBasis_biInf_principal'
    (fun s hs t ht =>
      ⟨s ∪ t, hs.union ht, compl_subset_compl.2 subset_union_left,
        compl_subset_compl.2 subset_union_right⟩)
    ⟨∅, isLindelof_empty⟩

theorem mem_coLindelof : s ∈ coLindelof X ↔ ∃ t, IsLindelof t ∧ tᶜ ⊆ s :=
  hasBasis_coLindelof.mem_iff

theorem mem_coLindelof' : s ∈ coLindelof X ↔ ∃ t, IsLindelof t ∧ sᶜ ⊆ t :=
  mem_coLindelof.trans <| exists_congr fun _ => and_congr_right fun _ => compl_subset_comm

theorem _root_.IsLindelof.compl_mem_coLindelof (hs : IsLindelof s) : sᶜ ∈ coLindelof X :=
  hasBasis_coLindelof.mem_of_mem hs

theorem coLindelof_le_cofinite : coLindelof X ≤ cofinite := fun s hs =>
  compl_compl s ▸ hs.isLindelof.compl_mem_coLindelof

theorem Tendsto.isLindelof_insert_range_of_coLindelof {f : X → Y} {y}
    (hf : Tendsto f (coLindelof X) (𝓝 y)) (hfc : Continuous f) :
    IsLindelof (insert y (range f)) := by
  intro l hne _ hle
  by_cases hy : ClusterPt y l
  · exact ⟨y, Or.inl rfl, hy⟩
  simp only [clusterPt_iff_nonempty, not_forall, ← not_disjoint_iff_nonempty_inter, not_not] at hy
  rcases hy with ⟨s, hsy, t, htl, hd⟩
  rcases mem_coLindelof.1 (hf hsy) with ⟨K, hKc, hKs⟩
  have : f '' K ∈ l := by
    filter_upwards [htl, le_principal_iff.1 hle] with y hyt hyf
    rcases hyf with (rfl | ⟨x, rfl⟩)
    exacts [(hd.le_bot ⟨mem_of_mem_nhds hsy, hyt⟩).elim,
      mem_image_of_mem _ (not_not.1 fun hxK => hd.le_bot ⟨hKs hxK, hyt⟩)]
  rcases hKc.image hfc (le_principal_iff.2 this) with ⟨y, hy, hyl⟩
  exact ⟨y, Or.inr <| image_subset_range _ _ hy, hyl⟩

/-- `Filter.coclosedLindelof` is the filter generated by complements to closed Lindelof sets. -/
def Filter.coclosedLindelof (X : Type*) [TopologicalSpace X] : Filter X :=
  -- `Filter.coclosedLindelof` is the filter generated by complements to closed Lindelof sets.
  ⨅ (s : Set X) (_ : IsClosed s) (_ : IsLindelof s), 𝓟 sᶜ

theorem hasBasis_coclosedLindelof :
    (Filter.coclosedLindelof X).HasBasis (fun s => IsClosed s ∧ IsLindelof s) compl := by
  simp only [Filter.coclosedLindelof, iInf_and']
  refine hasBasis_biInf_principal' ?_ ⟨∅, isClosed_empty, isLindelof_empty⟩
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  exact ⟨s ∪ t, ⟨⟨hs₁.union ht₁, hs₂.union ht₂⟩, compl_subset_compl.2 subset_union_left,
    compl_subset_compl.2 subset_union_right⟩⟩

theorem mem_coclosedLindelof : s ∈ coclosedLindelof X ↔
    ∃ t, IsClosed t ∧ IsLindelof t ∧ tᶜ ⊆ s := by
  simp only [hasBasis_coclosedLindelof.mem_iff, and_assoc]

theorem mem_coclosed_Lindelof' : s ∈ coclosedLindelof X ↔
    ∃ t, IsClosed t ∧ IsLindelof t ∧ sᶜ ⊆ t := by
  simp only [mem_coclosedLindelof, compl_subset_comm]

theorem coLindelof_le_coclosedLindelof : coLindelof X ≤ coclosedLindelof X :=
  iInf_mono fun _ => le_iInf fun _ => le_rfl

theorem IsLindeof.compl_mem_coclosedLindelof_of_isClosed (hs : IsLindelof s) (hs' : IsClosed s) :
    sᶜ ∈ Filter.coclosedLindelof X :=
  hasBasis_coclosedLindelof.mem_of_mem ⟨hs', hs⟩

/-- X is a Lindelöf space iff every open cover has a countable subcover. -/
class LindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a Lindelöf space, `Set.univ` is a Lindelöf set. -/
  isLindelof_univ : IsLindelof (univ : Set X)

instance (priority := 10) Subsingleton.lindelofSpace [Subsingleton X] : LindelofSpace X :=
  ⟨subsingleton_univ.isLindelof⟩

theorem isLindelof_univ_iff : IsLindelof (univ : Set X) ↔ LindelofSpace X :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

theorem isLindelof_univ [h : LindelofSpace X] : IsLindelof (univ : Set X) :=
  h.isLindelof_univ

theorem cluster_point_of_Lindelof [LindelofSpace X] (f : Filter X) [NeBot f]
    [CountableInterFilter f] : ∃ x, ClusterPt x f := by
  simpa using isLindelof_univ (show f ≤ 𝓟 univ by simp)

theorem LindelofSpace.elim_nhds_subcover [LindelofSpace X] (U : X → Set X) (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Set X, t.Countable ∧ ⋃ x ∈ t, U x = univ := by
  obtain ⟨t, tc, -, s⟩ := IsLindelof.elim_nhds_subcover isLindelof_univ U fun x _ => hU x
  use t, tc
  apply top_unique s

theorem lindelofSpace_of_countable_subfamily_closed
    (h : ∀ {ι : Type u} (t : ι → Set X), (∀ i, IsClosed (t i)) → ⋂ i, t i = ∅ →
      ∃ u : Set ι, u.Countable ∧ ⋂ i ∈ u, t i = ∅) :
    LindelofSpace X where
  isLindelof_univ := isLindelof_of_countable_subfamily_closed fun t => by simpa using h t

theorem IsClosed.isLindelof [LindelofSpace X] (h : IsClosed s) : IsLindelof s :=
  isLindelof_univ.of_isClosed_subset h (subset_univ _)

/-- A compact set `s` is Lindelöf. -/
theorem IsCompact.isLindelof (hs : IsCompact s) :
    IsLindelof s := by tauto

/-- A σ-compact set `s` is Lindelöf -/
theorem IsSigmaCompact.isLindelof (hs : IsSigmaCompact s) :
    IsLindelof s := by
  rw [IsSigmaCompact] at hs
  rcases hs with ⟨K, ⟨hc, huniv⟩⟩
  rw [← huniv]
  have hl : ∀ n, IsLindelof (K n) := fun n ↦ IsCompact.isLindelof (hc n)
  exact isLindelof_iUnion hl

/-- A compact space `X` is Lindelöf. -/
instance (priority := 100) [CompactSpace X] : LindelofSpace X :=
  { isLindelof_univ := isCompact_univ.isLindelof}

/-- A sigma-compact space `X` is Lindelöf. -/
instance (priority := 100) [SigmaCompactSpace X] : LindelofSpace X :=
  { isLindelof_univ := isSigmaCompact_univ.isLindelof}

/-- `X` is a non-Lindelöf topological space if it is not a Lindelöf space. -/
class NonLindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a non-Lindelöf space, `Set.univ` is not a Lindelöf set. -/
  nonLindelof_univ : ¬IsLindelof (univ : Set X)

lemma nonLindelof_univ (X : Type*) [TopologicalSpace X] [NonLindelofSpace X] :
    ¬IsLindelof (univ : Set X) :=
  NonLindelofSpace.nonLindelof_univ

theorem IsLindelof.ne_univ [NonLindelofSpace X] (hs : IsLindelof s) : s ≠ univ := fun h ↦
  nonLindelof_univ X (h ▸ hs)

instance [NonLindelofSpace X] : NeBot (Filter.coLindelof X) := by
  refine hasBasis_coLindelof.neBot_iff.2 fun {s} hs => ?_
  contrapose hs
  rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hs
  rw [hs]
  exact nonLindelof_univ X

@[simp]
theorem Filter.coLindelof_eq_bot [LindelofSpace X] : Filter.coLindelof X = ⊥ :=
  hasBasis_coLindelof.eq_bot_iff.mpr ⟨Set.univ, isLindelof_univ, Set.compl_univ⟩

instance [NonLindelofSpace X] : NeBot (Filter.coclosedLindelof X) :=
  neBot_of_le coLindelof_le_coclosedLindelof

theorem nonLindelofSpace_of_neBot (_ : NeBot (Filter.coLindelof X)) : NonLindelofSpace X :=
  ⟨fun h' => (Filter.nonempty_of_mem h'.compl_mem_coLindelof).ne_empty compl_univ⟩

theorem Filter.coLindelof_neBot_iff : NeBot (Filter.coLindelof X) ↔ NonLindelofSpace X :=
  ⟨nonLindelofSpace_of_neBot, fun _ => inferInstance⟩


theorem not_LindelofSpace_iff : ¬LindelofSpace X ↔ NonLindelofSpace X :=
  ⟨fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩, fun ⟨h₁⟩ ⟨h₂⟩ => h₁ h₂⟩

theorem countable_of_Lindelof_of_discrete [LindelofSpace X] [DiscreteTopology X] : Countable X :=
  countable_univ_iff.mp isLindelof_univ.countable_of_discrete

theorem countable_cover_nhds_interior [LindelofSpace X] {U : X → Set X} (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Set X, t.Countable ∧ ⋃ x ∈ t, interior (U x) = univ :=
  let ⟨t, ht⟩ := isLindelof_univ.elim_countable_subcover (fun x => interior (U x))
    (fun _ => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  ⟨t, ⟨ht.1, univ_subset_iff.1 ht.2⟩⟩

theorem countable_cover_nhds [LindelofSpace X] {U : X → Set X} (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Set X, t.Countable ∧ ⋃ x ∈ t, U x = univ :=
  let ⟨t, ht⟩ := countable_cover_nhds_interior hU
  ⟨t, ⟨ht.1, univ_subset_iff.1 <| ht.2.symm.subset.trans <|
    iUnion₂_mono fun _ _ => interior_subset⟩⟩

/-- The comap of the coLindelöf filter on `Y` by a continuous function `f : X → Y` is less than or
equal to the coLindelöf filter on `X`.
This is a reformulation of the fact that images of Lindelöf sets are Lindelöf. -/
theorem Filter.comap_coLindelof_le {f : X → Y} (hf : Continuous f) :
    (Filter.coLindelof Y).comap f ≤ Filter.coLindelof X := by
  rw [(hasBasis_coLindelof.comap f).le_basis_iff hasBasis_coLindelof]
  intro t ht
  refine ⟨f '' t, ht.image hf, ?_⟩
  simpa using t.subset_preimage_image f

theorem isLindelof_range [LindelofSpace X] {f : X → Y} (hf : Continuous f) :
    IsLindelof (range f) := by rw [← image_univ]; exact isLindelof_univ.image hf

theorem isLindelof_diagonal [LindelofSpace X] : IsLindelof (diagonal X) :=
  @range_diag X ▸ isLindelof_range (continuous_id.prodMk continuous_id)

/-- If `f : X → Y` is an inducing map, the image `f '' s` of a set `s` is Lindelöf
  if and only if `s` is compact. -/
theorem Topology.IsInducing.isLindelof_iff {f : X → Y} (hf : IsInducing f) :
    IsLindelof s ↔ IsLindelof (f '' s) := by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot _ F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x ∈ s, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

/-- If `f : X → Y` is an embedding, the image `f '' s` of a set `s` is Lindelöf
if and only if `s` is Lindelöf. -/
theorem Topology.IsEmbedding.isLindelof_iff {f : X → Y} (hf : IsEmbedding f) :
    IsLindelof s ↔ IsLindelof (f '' s) := hf.isInducing.isLindelof_iff

/-- The preimage of a Lindelöf set under an inducing map is a Lindelöf set. -/
theorem Topology.IsInducing.isLindelof_preimage {f : X → Y} (hf : IsInducing f)
    (hf' : IsClosed (range f)) {K : Set Y} (hK : IsLindelof K) : IsLindelof (f ⁻¹' K) := by
  replace hK := hK.inter_right hf'
  rwa [hf.isLindelof_iff, image_preimage_eq_inter_range]

/-- The preimage of a Lindelöf set under a closed embedding is a Lindelöf set. -/
theorem Topology.IsClosedEmbedding.isLindelof_preimage {f : X → Y} (hf : IsClosedEmbedding f)
    {K : Set Y} (hK : IsLindelof K) : IsLindelof (f ⁻¹' K) :=
  hf.isInducing.isLindelof_preimage (hf.isClosed_range) hK

/-- A closed embedding is proper, i.e., inverse images of Lindelöf sets are contained in Lindelöf.
Moreover, the preimage of a Lindelöf set is Lindelöf, see
`Topology.IsClosedEmbedding.isLindelof_preimage`. -/
theorem Topology.IsClosedEmbedding.tendsto_coLindelof {f : X → Y} (hf : IsClosedEmbedding f) :
    Tendsto f (Filter.coLindelof X) (Filter.coLindelof Y) :=
  hasBasis_coLindelof.tendsto_right_iff.mpr fun _K hK =>
    (hf.isLindelof_preimage hK).compl_mem_coLindelof

/-- Sets of subtype are Lindelöf iff the image under a coercion is. -/
theorem Subtype.isLindelof_iff {p : X → Prop} {s : Set { x // p x }} :
    IsLindelof s ↔ IsLindelof ((↑) '' s : Set X) :=
  IsEmbedding.subtypeVal.isLindelof_iff

theorem isLindelof_iff_isLindelof_univ : IsLindelof s ↔ IsLindelof (univ : Set s) := by
  rw [Subtype.isLindelof_iff, image_univ, Subtype.range_coe]

theorem isLindelof_iff_LindelofSpace : IsLindelof s ↔ LindelofSpace s :=
  isLindelof_iff_isLindelof_univ.trans isLindelof_univ_iff

lemma IsLindelof.of_coe [LindelofSpace s] : IsLindelof s := isLindelof_iff_LindelofSpace.mpr ‹_›

theorem IsLindelof.countable (hs : IsLindelof s) (hs' : DiscreteTopology s) : s.Countable :=
  countable_coe_iff.mp
  (@countable_of_Lindelof_of_discrete _ _ (isLindelof_iff_LindelofSpace.mp hs) hs')

protected theorem Topology.IsClosedEmbedding.nonLindelofSpace [NonLindelofSpace X] {f : X → Y}
    (hf : IsClosedEmbedding f) : NonLindelofSpace Y :=
  nonLindelofSpace_of_neBot hf.tendsto_coLindelof.neBot

protected theorem Topology.IsClosedEmbedding.LindelofSpace [h : LindelofSpace Y] {f : X → Y}
    (hf : IsClosedEmbedding f) : LindelofSpace X :=
  ⟨by rw [hf.isInducing.isLindelof_iff, image_univ]; exact hf.isClosed_range.isLindelof⟩

/-- Countable topological spaces are Lindelof. -/
instance (priority := 100) Countable.LindelofSpace [Countable X] : LindelofSpace X where
  isLindelof_univ := countable_univ.isLindelof

/-- The disjoint union of two Lindelöf spaces is Lindelöf. -/
instance [LindelofSpace X] [LindelofSpace Y] : LindelofSpace (X ⊕ Y) where
  isLindelof_univ := by
    rw [← range_inl_union_range_inr]
    exact (isLindelof_range continuous_inl).union (isLindelof_range continuous_inr)

instance {X : ι → Type*} [Countable ι] [∀ i, TopologicalSpace (X i)] [∀ i, LindelofSpace (X i)] :
    LindelofSpace (Σ i, X i) where
  isLindelof_univ := by
    rw [Sigma.univ]
    exact isLindelof_iUnion fun i => isLindelof_range continuous_sigmaMk

instance Quot.LindelofSpace {r : X → X → Prop} [LindelofSpace X] : LindelofSpace (Quot r) where
  isLindelof_univ := by
    rw [← range_quot_mk]
    exact isLindelof_range continuous_quot_mk

instance Quotient.LindelofSpace {s : Setoid X} [LindelofSpace X] : LindelofSpace (Quotient s) :=
  Quot.LindelofSpace

/-- A continuous image of a Lindelöf set is a Lindelöf set within the codomain. -/
theorem LindelofSpace.of_continuous_surjective {f : X → Y} [LindelofSpace X] (hf : Continuous f)
    (hsur : Function.Surjective f) : LindelofSpace Y where
  isLindelof_univ := by
    rw [← Set.image_univ_of_surjective hsur]
    exact IsLindelof.image (isLindelof_univ_iff.mpr ‹_›) hf

/-- A set `s` is Hereditarily Lindelöf if every subset is a Lindelof set. We require this only
for open sets in the definition, and then conclude that this holds for all sets by ADD. -/
def IsHereditarilyLindelof (s : Set X) :=
  ∀ t ⊆ s, IsLindelof t

/-- Type class for Hereditarily Lindelöf spaces. -/
class HereditarilyLindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a Hereditarily Lindelöf space, `Set.univ` is a Hereditarily Lindelöf set. -/
  isHereditarilyLindelof_univ : IsHereditarilyLindelof (univ : Set X)

lemma IsHereditarilyLindelof.isLindelof_subset (hs : IsHereditarilyLindelof s) (ht : t ⊆ s) :
    IsLindelof t := hs t ht

lemma IsHereditarilyLindelof.isLindelof (hs : IsHereditarilyLindelof s) :
    IsLindelof s := hs.isLindelof_subset Subset.rfl

instance (priority := 100) HereditarilyLindelof.to_Lindelof [HereditarilyLindelofSpace X] :
    LindelofSpace X where
  isLindelof_univ := HereditarilyLindelofSpace.isHereditarilyLindelof_univ.isLindelof

theorem HereditarilyLindelof_LindelofSets [HereditarilyLindelofSpace X] (s : Set X) :
    IsLindelof s := by
  apply HereditarilyLindelofSpace.isHereditarilyLindelof_univ
  exact subset_univ s

instance (priority := 100) SecondCountableTopology.toHereditarilyLindelof
    [SecondCountableTopology X] : HereditarilyLindelofSpace X where
  isHereditarilyLindelof_univ t _ _ := by
    apply isLindelof_iff_countable_subcover.mpr
    intro ι U hι hcover
    have := @isOpen_iUnion_countable X _ _ ι U hι
    rcases this with ⟨t, ⟨htc, htu⟩⟩
    use t, htc
    exact subset_of_subset_of_eq hcover (id htu.symm)

lemma eq_open_union_countable [HereditarilyLindelofSpace X] {ι : Type u} (U : ι → Set X)
    (h : ∀ i, IsOpen (U i)) : ∃ t : Set ι, t.Countable ∧ ⋃ i∈t, U i = ⋃ i, U i := by
  have : IsLindelof (⋃ i, U i) := HereditarilyLindelof_LindelofSets (⋃ i, U i)
  rcases isLindelof_iff_countable_subcover.mp this U h (Eq.subset rfl) with ⟨t, ⟨htc, htu⟩⟩
  use t, htc
  apply eq_of_subset_of_subset (iUnion₂_subset_iUnion (fun i ↦ i ∈ t) fun i ↦ U i) htu

instance HereditarilyLindelof.lindelofSpace_subtype [HereditarilyLindelofSpace X] (p : X → Prop) :
    LindelofSpace {x // p x} := by
  apply isLindelof_iff_LindelofSpace.mp
  exact HereditarilyLindelof_LindelofSets fun x ↦ p x

end Lindelof
