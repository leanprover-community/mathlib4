/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Order.Filter.CardinalInter
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Compactness.Lindelof
/-!
# Κ-Lindelöf sets and κ-Lindelöf spaces
(Note, this is different from k-Lindelöf spaces, e.g.
  https://topology.pi-base.org/properties/P000128)

## Main definitions

We define the following properties for sets in a topological space:

* `IsKLindelof κ s`: Two definitions are possible here. The more standard definition is that
every open cover that contains `s` contains a subcover of cardinality less than `κ`.
We choose for the equivalent definition where we require that every nontrivial CardinalInterFilter
with cardinality `κ` has a clusterpoint.
Equivalence is established in `isKLindelof_iff_cardinal_subcover` when `κ` is regular.

* `KLindelofSpace X`: `X` is `κ`-Lindelöf if it is `κ`-Lindelöf as a set.
* `NonKLindelofSpace`: a space that is not a `κ`-Lindelöf space, e.g. the Long Line.

## Main results

* `isKLindelof_iff_cardinal_subcover`: A set is `κ`-Lindelöf iff every open cover has a
  subcover of cardinality κ.

## Implementation details

* This API is mainly based on the API for `IsCompact` and `IsLindelof` and follows notation
  and style as much as possible.
-/
open Set Filter Topology TopologicalSpace Cardinal

universe u v

variable {X : Type u} {Y : Type u} {ι : Type u}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}
variable {κ : Cardinal.{u}}

section KLindelof

/-- A set `s` is `κ`-Lindelöf if every nontrivial `CardinalInterFilter f κ` that contains `s`,
  has a clusterpoint in `s`. The filter-free definition is given by
  `isKLindelof_iff_cardinal_subcover`. -/
def IsKLindelof (κ : Cardinal) (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f] [CardinalInterFilter f κ], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f

/-- The complement to a `κ`-Lindelöf set belongs to a `CardinalInterFilter f κ` if it belongs to
each filter `𝓝 x ⊓ f`, `x ∈ s`. -/
theorem IsKLindelof.compl_mem_sets (hs : IsKLindelof κ s) {f : Filter X}
    [CardinalInterFilter f κ] (hf : ∀ x ∈ s, sᶜ ∈ 𝓝 x ⊓ f) : sᶜ ∈ f := by
  contrapose! hf
  simp only [not_mem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact hs inf_le_right

/-- The complement to a `κ`-Lindelöf set belongs to a `CardinalInterFilter f κ` if each `x ∈ s` has
a neighborhood `t` within `s` such that `tᶜ` belongs to `f`. -/
theorem IsKLindelof.compl_mem_sets_of_nhdsWithin (hs : IsKLindelof κ s)
    {f : Filter X} [CardinalInterFilter f κ] (hf : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, tᶜ ∈ f) : sᶜ ∈ f := by
  refine hs.compl_mem_sets fun x hx ↦ ?_
  rw [← disjoint_principal_right, disjoint_right_comm, (basis_sets _).disjoint_iff_left]
  exact hf x hx

/-- If `p : Set X → Prop` is stable under restriction and union, and each point `x`
  of a `κ`-Lindelöf set `s` has a neighborhood `t` within `s` such that `p t`, then `p s` holds. -/
@[elab_as_elim]
theorem IsKLindelof.induction_on {hκ: 2 < κ} (hs : IsKLindelof κ s) {p : Set X → Prop}
    (hmono : ∀ ⦃s t⦄, s ⊆ t → p t → p s)
    (hcardinal_union : ∀ (S : Set (Set X)), (#S < κ) → (∀ s ∈ S, p s) → p (⋃₀ S))
    (hnhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, p t) : p s := by
  let f : Filter X := ofCardinalUnion p hκ hcardinal_union (fun t ht _ hsub ↦ hmono hsub ht)
  have : sᶜ ∈ f := hs.compl_mem_sets_of_nhdsWithin (by simpa [f] using hnhds)
  rwa [← compl_compl s]

/-- The intersection of a `κ`-Lindelöf set and a closed set is a `κ`-Lindelöf set. -/
theorem IsKLindelof.inter_right (hs : IsKLindelof κ s) (ht : IsClosed t) :
    IsKLindelof κ (s ∩ t) := by
  intro f hnf _ hstf
  rw [← inf_principal, le_inf_iff] at hstf
  obtain ⟨x, hsx, hx⟩ : ∃ x ∈ s, ClusterPt x f := hs hstf.1
  have hxt : x ∈ t := ht.mem_of_nhdsWithin_neBot <| hx.mono hstf.2
  exact ⟨x, ⟨hsx, hxt⟩, hx⟩

  /-- The intersection of a closed set and a `κ`-Lindelöf set is a `κ`-Lindelöf set. -/
theorem IsKLindelof.inter_left (ht : IsKLindelof κ t) (hs : IsClosed s) : IsKLindelof κ (s ∩ t) :=
  inter_comm t s ▸ ht.inter_right hs

  /-- The set difference of a `κ`-Lindelöf set and an open set is a `κ`-Lindelöf set. -/
theorem IsKLindelof.diff (hs : IsKLindelof κ s) (ht : IsOpen t) : IsKLindelof κ (s \ t) :=
  hs.inter_right (isClosed_compl_iff.mpr ht)

/-- A closed subset of a `κ`-Lindelöf set is a `κ`-Lindelöf set. -/
theorem IsKLindelof.of_isClosed_subset (hs : IsKLindelof κ s) (ht : IsClosed t) (h : t ⊆ s) :
    IsKLindelof κ t := inter_eq_self_of_subset_right h ▸ hs.inter_right ht

/-- A continuous image of a `κ`-Lindelöf set is a `κ`-Lindelöf set. -/
theorem IsKLindelof.image_of_continuousOn {f : X → Y} (hs : IsKLindelof κ s)
    (hf : ContinuousOn f s) : IsKLindelof (X := Y) κ (f '' s) := by
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

/-- A continuous image of a `κ`-Lindelöf set is a `κ`-Lindelöf set within the codomain. -/
theorem IsKLindelof.image {f : X → Y} (hs : IsKLindelof κ s) (hf : Continuous f) :
    IsKLindelof (X := Y) κ (f '' s) := hs.image_of_continuousOn hf.continuousOn

/-- A filter with the cardinal intersection property that is finer than the principal filter on
a `κ`-Lindelöf set `s` contains any open set that contains all clusterpoints of `f` in `s`. -/
theorem IsKLindelof.adherence_nhdset {f : Filter X} [CardinalInterFilter f κ] (hs : IsKLindelof κ s)
    (hf₂ : f ≤ 𝓟 s) (ht₁ : IsOpen t) (ht₂ : ∀ x ∈ s, ClusterPt x f → x ∈ t) : t ∈ f :=
  (eq_or_neBot _).casesOn mem_of_eq_bot fun _ ↦
    let ⟨x, hx, hfx⟩ := @hs (f ⊓ 𝓟 tᶜ) _ _ <| inf_le_of_left_le hf₂
    have : x ∈ t := ht₂ x hx hfx.of_inf_left
    have : tᶜ ∩ t ∈ 𝓝[tᶜ] x := inter_mem_nhdsWithin _ (ht₁.mem_nhds this)
    have A : 𝓝[tᶜ] x = ⊥ := empty_mem_iff_bot.1 <| compl_inter_self t ▸ this
    have : 𝓝[tᶜ] x ≠ ⊥ := hfx.of_inf_right.ne
    absurd A this

/-- For every open cover of a `κ`-Lindelöf set, there exists a subcover with cardinality less
than `κ`. -/
theorem IsKLindelof.elim_cardinal_subcover {ι : Type u} (hreg : κ.IsRegular)
    (hs : IsKLindelof κ s) (U : ι → Set X) (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) :
    ∃ r : Set ι, (#r < κ) ∧ (s ⊆ ⋃ i ∈ r, U i) := by
  have hκ : 2 < κ := IsRegular.nat_lt hreg 2
  have hmono : ∀ ⦃s t : Set X⦄, s ⊆ t → (∃ r : Set ι, (#r < κ) ∧ t ⊆ ⋃ i ∈ r, U i)
      → (∃ r : Set ι, (#r < κ) ∧ s ⊆ ⋃ i ∈ r, U i) := by
    intro s t hst ⟨r, ⟨hrcardinal, hsub⟩⟩
    exact ⟨r, hrcardinal, Subset.trans hst hsub⟩
  have hcardinal_union : ∀ (S : Set (Set X)), (#S < κ)
      → (∀ s ∈ S, ∃ r : Set ι, (#r < κ) ∧ (s ⊆ ⋃ i ∈ r, U i))
      → ∃ r : Set ι, (#r < κ) ∧ (⋃₀ S ⊆ ⋃ i ∈ r, U i) := by
    intro S hS hsr
    choose! r hr using hsr
    refine ⟨⋃ s ∈ S, r s, ?_, ?_⟩
    · rw [card_biUnion_lt_iff_forall_of_isRegular hreg]
      exact fun a ha ↦ (hr a ha).1
      exact hS
    refine sUnion_subset ?h.right.h
    simp only [mem_iUnion, exists_prop, iUnion_exists, biUnion_and']
    exact fun i is x hx ↦ mem_biUnion is ((hr i is).2 hx)
  have h_nhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∃ r : Set ι, (#r < κ) ∧ (t ⊆ ⋃ i ∈ r, U i) := by
    intro x hx
    let ⟨i, hi⟩ := mem_iUnion.1 (hsU hx)
    have : 1 < κ := IsRegular.nat_lt hreg 1
    refine ⟨U i, mem_nhdsWithin_of_mem_nhds ((hUo i).mem_nhds hi), {i}, by simp [this], ?_⟩
    simp only [mem_singleton_iff, iUnion_iUnion_eq_left]
    exact subset_rfl
  exact hs.induction_on (hκ := hκ) hmono hcardinal_union h_nhds

theorem IsKLindelof.elim_nhds_subcover' (hreg : κ.IsRegular) (hs : IsKLindelof κ s)
    (U : ∀ x ∈ s, Set X) (hU : ∀ x (hx : x ∈ s), U x ‹x ∈ s› ∈ 𝓝 x) :
    ∃ t : Set s, (#t < κ) ∧ s ⊆ ⋃ x ∈ t, U (x : s) x.2 := by
  have := hs.elim_cardinal_subcover hreg (fun x : s ↦ interior (U x x.2))
    (fun _ ↦ isOpen_interior)
    fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 <| hU _ _⟩
  rcases this with ⟨r, ⟨hr, hs⟩⟩
  use r, hr
  apply Subset.trans hs
  apply iUnion₂_subset
  intro i hi
  apply Subset.trans interior_subset
  exact subset_iUnion_of_subset i (subset_iUnion_of_subset hi (Subset.refl _))

theorem IsKLindelof.elim_nhds_subcover (hreg : κ.IsRegular) (hs : IsKLindelof κ s)
    (U : X → Set X) (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
    ∃ t : Set X, (#t < κ) ∧ (∀ x ∈ t, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x := by
  let ⟨t, ⟨htc, htsub⟩⟩ := hs.elim_nhds_subcover' hreg (fun x _ ↦ U x) hU
  refine ⟨↑t,  lt_of_le_of_lt Cardinal.mk_image_le htc, ?_⟩
  constructor
  · intro _
    simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, forall_exists_index]
    tauto
  · have : ⋃ x ∈ t, U ↑x = ⋃ x ∈ Subtype.val '' t, U x := biUnion_image.symm
    rwa [← this]

/-- The neighborhood filter of a `κ`-Lindelöf set is disjoint with a `CardinalInterFilter l κ`
filter if and only if the neighborhood filter of each point of this set is disjoint with `l`. -/
theorem IsKLindelof.disjoint_nhdsSet_left (hreg : κ.IsRegular) {l : Filter X}
    [CardinalInterFilter l κ] (hs : IsKLindelof κ s) :
    Disjoint (𝓝ˢ s) l ↔ ∀ x ∈ s, Disjoint (𝓝 x) l := by
  refine ⟨fun h x hx ↦ h.mono_left <| nhds_le_nhdsSet hx, fun H ↦ ?_⟩
  choose! U hxU hUl using fun x hx ↦ (nhds_basis_opens x).disjoint_iff_left.1 (H x hx)
  choose hxU hUo using hxU
  rcases hs.elim_nhds_subcover hreg U fun x hx ↦ (hUo x hx).mem_nhds (hxU x hx)
    with ⟨t, htc, hts, hst⟩
  refine (hasBasis_nhdsSet _).disjoint_iff_left.2
    ⟨⋃ x ∈ t, U x, ⟨isOpen_biUnion fun x hx ↦ hUo x (hts x hx), hst⟩, ?_⟩
  rw [compl_iUnion₂]
  exact (cardinal_bInter_mem htc).mpr (fun i hi ↦ hUl _ (hts _ hi))

/-- A `CardinalInterFilter l κ` filter is disjoint with the neighborhood
filter of a `κ`-Lindelöf set if and only if it is disjoint with the neighborhood filter of each
point of this set. -/
theorem IsKLindelof.disjoint_nhdsSet_right (hreg : κ.IsRegular) {l : Filter X}
    [CardinalInterFilter l κ] (hs : IsKLindelof κ s) :
    Disjoint l (𝓝ˢ s) ↔ ∀ x ∈ s, Disjoint l (𝓝 x) := by
  simpa only [disjoint_comm] using (hs.disjoint_nhdsSet_left hreg)

/-- For every family of closed sets whose intersection avoids a `κ`-Lindelöf set,
there exists a subfamil of size less than `κ` whose intersection avoids this `κ`-Lindelöf set. -/
theorem IsKLindelof.elim_cardinal_subfamily_closed (hreg : κ.IsRegular) {ι : Type u}
    (hs : IsKLindelof κ s) (t : ι → Set X) (htc : ∀ i, IsClosed (t i)) (hst : (s ∩ ⋂ i, t i) = ∅) :
    ∃ u : Set ι, (#u < κ) ∧ (s ∩ ⋂ i ∈ u, t i) = ∅ := by
  let U := tᶜ
  have hUo : ∀ i, IsOpen (U i) := by simp only [U, Pi.compl_apply, isOpen_compl_iff]; exact htc
  have hsU : s ⊆ ⋃ i, U i := by
    simp only [U, Pi.compl_apply]
    rw [← compl_iInter]
    apply disjoint_compl_left_iff_subset.mp
    simp only [compl_iInter, compl_iUnion, compl_compl]
    apply Disjoint.symm
    exact disjoint_iff_inter_eq_empty.mpr hst
  rcases hs.elim_cardinal_subcover hreg U hUo hsU with ⟨u, ⟨hucount, husub⟩⟩
  use u, hucount
  rw [← disjoint_compl_left_iff_subset] at husub
  simp only [U, Pi.compl_apply, compl_iUnion, compl_compl] at husub
  exact disjoint_iff_inter_eq_empty.mp (Disjoint.symm husub)

/-- To show that a `κ`-Lindelöf set intersects the intersection of a family of closed sets,
  it is sufficient to show that it intersects every subfamily of cardinality below `κ`. -/
theorem IsKLindelof.inter_iInter_nonempty (hreg : κ.IsRegular) {ι : Type u}
    (hs : IsKLindelof κ s) (t : ι → Set X) (htc : ∀ i, IsClosed (t i))
    (hst : ∀ u : Set ι, (#u < κ) ∧ (s ∩ ⋂ i ∈ u, t i).Nonempty) : (s ∩ ⋂ i, t i).Nonempty := by
  contrapose! hst
  rcases hs.elim_cardinal_subfamily_closed hreg t htc hst with ⟨u, ⟨_, husub⟩⟩
  exact ⟨u, fun _ ↦ husub⟩

/-- For every open cover of a `κ`-Lindelöf set, there exists a subcover of cardinality less than
`κ`. -/
theorem IsKLindelof.elim_cardinal_subcover_image (hreg : κ.IsRegular) {b : Set ι}
    {c : ι → Set X} (hs : IsKLindelof κ s) (hc₁ : ∀ i ∈ b, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i ∈ b, c i) :
    ∃ b', b' ⊆ b ∧ (#b' < κ) ∧ s ⊆ ⋃ i ∈ b', c i := by
  simp only [Subtype.forall', biUnion_eq_iUnion] at hc₁ hc₂
  rcases hs.elim_cardinal_subcover hreg (fun i ↦ c i : b → Set X) hc₁ hc₂ with ⟨d, hd⟩
  refine ⟨Subtype.val '' d, by simp, lt_of_le_of_lt Cardinal.mk_image_le hd.1, ?_⟩
  rw [biUnion_image]
  exact hd.2

/-- A set `s` is `κ`-Lindelöf if for every open cover of `s`, there exists a subcover of cardinality
below `κ`. -/
theorem isKLindelof_of_cardinal_subcover
    (h : ∀ {ι : Type u} (U : ι → Set X), (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) →
    ∃ t : Set ι, (#t < κ) ∧ s ⊆ ⋃ i ∈ t, U i) :
    IsKLindelof κ s := fun f hf hfs ↦ by
  contrapose! h
  simp only [ClusterPt, not_neBot, ← disjoint_iff, SetCoe.forall',
    (nhds_basis_opens _).disjoint_iff_left] at h
  choose fsub U hU hUf using h
  refine ⟨s, U, fun x ↦ (hU x).2, fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).1 ⟩, ?_⟩
  intro t ht h
  have uinf := f.sets_of_superset (le_principal_iff.1 fsub) h
  have uninf : ⋂ i ∈ t, (U i)ᶜ ∈ f := (cardinal_bInter_mem ht).mpr (fun _ _ ↦ hUf _)
  rw [← compl_iUnion₂] at uninf
  have uninf := compl_not_mem uninf
  simp only [compl_compl] at uninf
  contradiction

/-- A set `s` is `κ`-Lindelöf if for every family of closed sets whose intersection avoids `s`,
there exists a cardinal subfamily whose intersection avoids `s`. -/
theorem isKLindelof_of_cardinal_subfamily_closed
    (h : ∀ {ι : Type u} (t : ι → Set X), (∀ i, IsClosed (t i)) → (s ∩ ⋂ i, t i) = ∅ →
        ∃ u : Set ι, (#u < κ) ∧ (s ∩ ⋂ i ∈ u, t i) = ∅) :
    IsKLindelof κ s :=
  isKLindelof_of_cardinal_subcover fun U hUo hsU ↦ by
    rw [← disjoint_compl_right_iff_subset, compl_iUnion, disjoint_iff] at hsU
    rcases h (fun i ↦ (U i)ᶜ) (fun i ↦ (hUo _).isClosed_compl) hsU with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rwa [← disjoint_compl_right_iff_subset, compl_iUnion₂, disjoint_iff]

/-- A set `s` is `κ`-Lindelöf if and only if
for every open cover of `s`, there exists a subcover of cardinality less than `κ`. -/
theorem isKLindelof_iff_cardinal_subcover (hreg : κ.IsRegular) :
    IsKLindelof κ s ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Set ι, (#t < κ) ∧ s ⊆ ⋃ i ∈ t, U i :=
  ⟨fun hs ↦ hs.elim_cardinal_subcover hreg, isKLindelof_of_cardinal_subcover⟩

/-- A set `s` is `κ`-Lindelöf if and only if
for every family of closed sets whose intersection avoids `s`,
there exists a subfamily of cardinality below `κ` whose intersection avoids `s`. -/
theorem isKLindelof_iff_cardinal_subfamily_closed (hreg : κ.IsRegular) :
    IsKLindelof κ s ↔ ∀ {ι : Type u} (t : ι → Set X),
    (∀ i, IsClosed (t i)) → (s ∩ ⋂ i, t i) = ∅
    → ∃ u : Set ι, (#u < κ) ∧ (s ∩ ⋂ i ∈ u, t i) = ∅ :=
  ⟨fun hs ↦ hs.elim_cardinal_subfamily_closed hreg, isKLindelof_of_cardinal_subfamily_closed⟩

/-- The empty set is a κ-Lindelof set. -/
@[simp]
theorem isKLindelof_empty : IsKLindelof κ (∅ : Set X) := fun _f hnf _ hsf ↦
  Not.elim hnf.ne <| empty_mem_iff_bot.1 <| le_principal_iff.1 hsf

/-- A singleton set is a κ-Lindelof set. -/
@[simp]
theorem isKLindelof_singleton {x : X} : IsKLindelof κ ({x} : Set X) := fun f hf _ hfa ↦
  ⟨x, rfl, ClusterPt.of_le_nhds'
    (hfa.trans <| by simpa only [principal_singleton] using pure_le_nhds x) hf⟩

theorem Set.Subsingleton.isKLindelof (hs : s.Subsingleton) : IsKLindelof κ s :=
  Subsingleton.induction_on hs isKLindelof_empty fun _ ↦ isKLindelof_singleton

theorem cardinal_isKLindelof_biUnion_of_isRegular {s : Set ι} {f : ι → Set X}
    (hreg : κ.IsRegular) (hs : #s < κ) (hf : ∀ i ∈ s, IsKLindelof κ (f i)) :
    IsKLindelof κ (⋃ i ∈ s, f i) := by
  apply isKLindelof_of_cardinal_subcover
  intro i U hU hUcover
  have hiU : ∀ i ∈ s, f i ⊆ ⋃ i, U i :=
    fun _ is ↦ _root_.subset_trans (subset_biUnion_of_mem is) hUcover
  have iSets := fun i is ↦ (hf i is).elim_cardinal_subcover hreg U hU (hiU i is)
  choose! r hr using iSets
  use ⋃ i ∈ s, r i
  constructor
  · refine (card_biUnion_lt_iff_forall_of_isRegular hreg hs).mpr ?h.left.a
    exact fun s hs ↦ (hr s hs).1
  · refine iUnion₂_subset ?h.right.h
    intro i is
    simp only [mem_iUnion, exists_prop, iUnion_exists, biUnion_and']
    intro x hx
    exact mem_biUnion is ((hr i is).2 hx)

theorem Set.Finite.isKLindelof_biUnion {s : Set ι} {f : ι → Set X} (hs : s.Finite)
    (hreg : κ.IsRegular) (hf : ∀ i ∈ s, IsKLindelof κ (f i)) :
    IsKLindelof κ (⋃ i ∈ s, f i) := by
  apply cardinal_isKLindelof_biUnion_of_isRegular hreg ?_ hf
  exact lt_of_lt_of_le (Cardinal.lt_aleph0_iff_set_finite.mpr hs) hreg.aleph0_le

theorem Finset.isKLindelof_biUnion (s : Finset ι) {f : ι → Set X} (hreg : κ.IsRegular)
    (hf : ∀ i ∈ s, IsKLindelof κ (f i)) : IsKLindelof κ (⋃ i ∈ s, f i) :=
  s.finite_toSet.isKLindelof_biUnion hreg hf

theorem cardinal_isKLindelof_sUnion_of_isRegular {S : Set (Set X)} (hreg : κ.IsRegular)
    (hf : #S < κ) (hc : ∀ s ∈ S, IsKLindelof κ s) : IsKLindelof κ (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact cardinal_isKLindelof_biUnion_of_isRegular hreg hf hc

theorem Set.Finite.isKLindelof_sUnion {S : Set (Set X)} (hreg : κ.IsRegular)
    (hf : S.Finite) (hc : ∀ s ∈ S, IsKLindelof κ s) : IsKLindelof κ (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact hf.isKLindelof_biUnion hreg hc

theorem isKLindelof_iUnion {ι : Type u} {f : ι → Set X} (hreg : κ.IsRegular) (hι : #ι < κ)
    (h : ∀ i, IsKLindelof κ (f i)) : IsKLindelof κ (⋃ i, f i) :=
  cardinal_isKLindelof_sUnion_of_isRegular hreg (lt_of_le_of_lt Cardinal.mk_range_le hι)
    (forall_mem_range.2 h)

theorem cardinal_isKLindelof_of_isRegular (hreg : κ.IsRegular) (hs : #s < κ) :
    IsKLindelof κ s :=
  biUnion_of_singleton s ▸
    cardinal_isKLindelof_biUnion_of_isRegular hreg hs fun _ _ => isKLindelof_singleton

theorem Set.Finite.isKLindelof (hs : s.Finite) (hreg : κ.IsRegular) : IsKLindelof κ s :=
  biUnion_of_singleton s ▸ hs.isKLindelof_biUnion hreg fun _ _ => isKLindelof_singleton

theorem IsKLindelof.cardinal_of_discrete_of_isRegular [DiscreteTopology X]
    (hreg : κ.IsRegular) (hs : IsKLindelof κ s) : #s < κ := by
  have : ∀ x : X, ({x} : Set X) ∈ 𝓝 x := by simp [nhds_discrete]
  rcases hs.elim_nhds_subcover hreg (fun x => {x}) fun x _ => this x with ⟨t, ht, _, hssubt⟩
  rw [biUnion_of_singleton] at hssubt
  exact lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset hssubt) ht

theorem isKLindelof_iff_cardinal_of_isRegular [DiscreteTopology X] (hreg : κ.IsRegular) :
    IsKLindelof κ s ↔ #s < κ :=
  ⟨fun h => h.cardinal_of_discrete_of_isRegular hreg,
    fun h => cardinal_isKLindelof_of_isRegular hreg h⟩

theorem IsKLindelof.union (hreg : κ.IsRegular) (hs : IsKLindelof κ s)
    (ht : IsKLindelof κ t) : IsKLindelof κ (s ∪ t) := by
  rw [← Set.sUnion_pair]
  apply Set.Finite.isKLindelof_sUnion hreg (by simp)
  rintro x (rfl | rfl) <;> assumption

protected theorem IsKLindelof.insert (hreg : κ.IsRegular) (hs : IsKLindelof κ s) (a) :
    IsKLindelof κ (insert a s) :=
  isKLindelof_singleton.union hreg hs

/-- If `X` has a basis consisting of `κ`-Lindelöf opens, then an open set in `X` is `κ`-Lindelöf
open iff it is a union of less than `κ` elements in the basis -/
theorem isLindelof_open_iff_eq_cardinal_iUnion_of_isTopologicalBasis (b : ι → Set X)
    (hb : IsTopologicalBasis (Set.range b)) (hreg : κ.IsRegular)
    (hb' : ∀ i, IsKLindelof κ (b i)) (U : Set X) :
    IsKLindelof κ U ∧ IsOpen U ↔ ∃ s : Set ι, (#s < κ) ∧ U = ⋃ i ∈ s, b i := by
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨Y, f, rfl, hf⟩ := hb.open_eq_iUnion h₂
    choose f' hf' using hf
    have : b ∘ f' = f := funext hf'
    subst this
    obtain ⟨t, ht⟩ :=
      h₁.elim_cardinal_subcover hreg (b ∘ f') (fun i => hb.isOpen (Set.mem_range_self _)) Subset.rfl
    refine ⟨t.image f', lt_of_le_of_lt mk_image_le ht.1, le_antisymm ?_ ?_⟩
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
    · exact cardinal_isKLindelof_biUnion_of_isRegular hreg hs fun i _ => hb' i
    · exact isOpen_biUnion fun i _ => hb.isOpen (Set.mem_range_self _)

/--`Filter.coKLindelof` is the filter generated by complements to κ-Lindelöf sets. -/
def Filter.coKLindelof (κ : Cardinal.{u}) (X : Type u) [TopologicalSpace X] : Filter X :=
  --`Filter.coKLindelof` is the filter generated by complements to κ-Lindelöf sets.
  ⨅ (s : Set X) (_ : IsKLindelof κ s), 𝓟 sᶜ

theorem hasBasis_coKLindelof (hreg : κ.IsRegular) :
    (coKLindelof κ X).HasBasis (IsKLindelof κ) compl :=
  hasBasis_biInf_principal'
    (fun s hs t ht =>
      ⟨s ∪ t, hs.union hreg ht, compl_subset_compl.2 (subset_union_left s t),
        compl_subset_compl.2 (subset_union_right s t)⟩)
    ⟨∅, isKLindelof_empty⟩

theorem mem_coKLindelof (hreg : κ.IsRegular) :
    s ∈ coKLindelof κ X ↔ ∃ t, IsKLindelof κ t ∧ tᶜ ⊆ s :=
  (hasBasis_coKLindelof hreg).mem_iff

theorem mem_coKLindelof' (hreg : κ.IsRegular) :
    s ∈ coKLindelof κ X ↔ ∃ t, IsKLindelof κ t ∧ sᶜ ⊆ t :=
  (mem_coKLindelof hreg).trans <| exists_congr fun _ => and_congr_right fun _ => compl_subset_comm

theorem _root_.IsKLindelof.compl_mem_coKLindelof (hreg : κ.IsRegular)
    (hs : IsKLindelof κ s) : sᶜ ∈ coKLindelof κ X :=
  (hasBasis_coKLindelof hreg).mem_of_mem hs

theorem coKLindelof_le_cofinite (hreg : κ.IsRegular) : coKLindelof κ X ≤ cofinite :=
  fun s hs => compl_compl s ▸ IsKLindelof.compl_mem_coKLindelof hreg (hs.isKLindelof hreg)

theorem Tendsto.isKLindelof_insert_range_of_coKLindelof {f : X → Y} {y}
    (hreg : κ.IsRegular) (hf : Tendsto f (coKLindelof κ X) (𝓝 y)) (hfc : Continuous f) :
    IsKLindelof κ (insert y (range f)) := by
  intro l hne _ hle
  by_cases hy : ClusterPt y l
  · exact ⟨y, Or.inl rfl, hy⟩
  simp only [clusterPt_iff, not_forall, ← not_disjoint_iff_nonempty_inter, not_not] at hy
  rcases hy with ⟨s, hsy, t, htl, hd⟩
  rcases (mem_coKLindelof hreg).1 (hf hsy) with ⟨K, hKc, hKs⟩
  have : f '' K ∈ l := by
    filter_upwards [htl, le_principal_iff.1 hle] with y hyt hyf
    rcases hyf with (rfl | ⟨x, rfl⟩)
    exacts [(hd.le_bot ⟨mem_of_mem_nhds hsy, hyt⟩).elim,
      mem_image_of_mem _ (not_not.1 fun hxK => hd.le_bot ⟨hKs hxK, hyt⟩)]
  rcases hKc.image hfc (le_principal_iff.2 this) with ⟨y, hy, hyl⟩
  exact ⟨y, Or.inr <| image_subset_range _ _ hy, hyl⟩

/-- `Filter.coclosedKLindelof` is the filter generated by complements to closed `κ`-Lindelof sets.-/
def Filter.coclosedKLindelof (κ : Cardinal.{u}) (X : Type u) [TopologicalSpace X] : Filter X :=
  -- `Filter.coclosedKLindelof` is the filter generated by complements to closed `κ`-Lindelof sets.
  ⨅ (s : Set X) (_ : IsClosed s) (_ : IsKLindelof κ s), 𝓟 sᶜ

theorem hasBasis_coclosedKLindelof (hreg : κ.IsRegular) :
    (Filter.coclosedKLindelof κ X).HasBasis (fun s => IsClosed s ∧ IsKLindelof κ s) compl := by
  simp only [Filter.coclosedKLindelof, iInf_and']
  refine hasBasis_biInf_principal' ?_ ⟨∅, isClosed_empty, isKLindelof_empty⟩
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  exact ⟨s ∪ t, ⟨⟨hs₁.union ht₁, hs₂.union hreg ht₂⟩, compl_subset_compl.2 (subset_union_left _ _),
    compl_subset_compl.2 (subset_union_right _ _)⟩⟩

theorem mem_coclosed_KLindelof (hreg : κ.IsRegular) : s ∈ coclosedKLindelof κ X ↔
    ∃ t, IsClosed t ∧ IsKLindelof κ t ∧ tᶜ ⊆ s := by
  simp only [(hasBasis_coclosedKLindelof hreg).mem_iff, and_assoc]

theorem mem_coclosed_KLindelof' (hreg : κ.IsRegular) : s ∈ coclosedKLindelof κ X ↔
    ∃ t, IsClosed t ∧ IsKLindelof κ t ∧ sᶜ ⊆ t := by
  simp only [mem_coclosed_KLindelof hreg, compl_subset_comm]

theorem coKLindelof_le_coclosedKLindelof : coKLindelof κ X ≤ coclosedKLindelof κ X :=
  iInf_mono fun _ => le_iInf fun _ => le_rfl

theorem IsKLindelof.compl_mem_coclosedKLindelof_of_isClosed (hreg : κ.IsRegular)
    (hs : IsKLindelof κ s) (hs' : IsClosed s) : sᶜ ∈ Filter.coclosedKLindelof κ X :=
  (hasBasis_coclosedKLindelof hreg).mem_of_mem ⟨hs', hs⟩

/-- X is a `κ`-Lindelöf space iff every open cover has a subcover of cardinality less than `κ`.-/
class KLindelofSpace (κ : Cardinal.{u}) (X : Type u) [TopologicalSpace X] : Prop where
  /-- In a `κ`Lindelöf space, `Set.univ` is a `κ`-Lindelöf set. -/
  isKLindelof_univ : IsKLindelof κ (univ : Set X)

instance (priority := 10) Subsingleton.kLindelofSpace [Subsingleton X] : KLindelofSpace κ X :=
  ⟨subsingleton_univ.isKLindelof⟩

theorem isKLindelof_univ_iff : IsKLindelof κ (univ : Set X) ↔ KLindelofSpace κ X :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

theorem isKLindelof_univ [h : KLindelofSpace κ X] : IsKLindelof κ (univ : Set X) :=
  h.isKLindelof_univ

theorem cluster_point_of_KLindelof [KLindelofSpace κ X] (f : Filter X) [NeBot f]
    [CardinalInterFilter f κ] : ∃ x, ClusterPt x f := by
  have b := @isKLindelof_univ X _ κ _
  rw [IsKLindelof] at b
  simp_all only [principal_univ, le_top, mem_univ, true_and]

theorem KLindelofSpace.elim_nhds_subcover [KLindelofSpace κ X] (hreg : κ.IsRegular)
    (U : X → Set X) (hU : ∀ x, U x ∈ 𝓝 x) : ∃ t : Set X, (#t < κ) ∧ ⋃ x ∈ t, U x = Set.univ := by
  obtain ⟨t, tc, -, s⟩ := IsKLindelof.elim_nhds_subcover hreg isKLindelof_univ U fun x _ => hU x
  use t, tc
  apply top_unique s

theorem kLindelofSpace_of_cardinal_subfamily_closed
    (h : ∀ {ι : Type u} (t : ι → Set X), (∀ i, IsClosed (t i)) → ⋂ i, t i = ∅ →
      ∃ u : Set ι, (#u < κ) ∧ ⋂ i ∈ u, t i = ∅) :
    KLindelofSpace κ X where
  isKLindelof_univ := isKLindelof_of_cardinal_subfamily_closed fun t => by simpa using h t

theorem IsClosed.isKLindelof [KLindelofSpace κ X] (h : IsClosed s) : IsKLindelof κ s :=
  isKLindelof_univ.of_isClosed_subset h (subset_univ _)

/-- A compact set `s` is `κ`-Lindelöf. -/
theorem IsCompact.isKLindelof (hs : IsCompact s) (κ : Cardinal.{u}) :
  IsKLindelof κ s := by tauto

/-- A `κ`-Lindelöf set `s` is compact for `κ` ≤ ℵ₀. -/
theorem IsKLindelof.isCompact (hκ : κ ≤ ℵ₀) (hs : IsKLindelof κ s) :
    IsCompact s := by
  rw [IsCompact]
  intro f hf hfs
  have := f.toCardinalInterFilter.of_cardinalInterFilter_of_le hκ
  exact hs hfs

theorem IsKLindelof_iff_isCompact : IsKLindelof ℵ₀ s ↔ IsCompact s :=
  ⟨fun h => h.isCompact (le_refl _), fun h => h.isKLindelof ℵ₀⟩

/-- A Lindelöf set `s` is `κ`-Lindelöf. -/
theorem IsLindelof.isKLindelof (hs : IsLindelof s) (hκ : ℵ₀ < κ) :
    IsKLindelof κ s := by
  rw [IsKLindelof]
  intro f _ _ hsub
  have : CountableInterFilter f := CardinalInterFilter.toCountableInterFilter f hκ
  exact hs hsub

/-- A σ-compact set `s` is `κ`-Lindelöf-/
theorem IsSigmaCompact.isKLindelof (hκ : ℵ₀ < κ) (hs : IsSigmaCompact s) :
    IsKLindelof κ s := IsLindelof.isKLindelof (IsSigmaCompact.isLindelof hs) hκ

/-- A compact space `X` is `κ`-Lindelöf. -/
instance (priority := 100) [CompactSpace X] : KLindelofSpace κ X :=
  { isKLindelof_univ := isCompact_univ.isKLindelof}

/-- A sigma-compact space `X` is `κ`-Lindelöf. -/
instance (priority := 100) [SigmaCompactSpace X] [hκ : Fact (ℵ₀ < κ)] : KLindelofSpace κ X :=
  { isKLindelof_univ := isSigmaCompact_univ.isKLindelof hκ.out}

/-- `X` is a non-`κ`-Lindelöf topological space if it is not a `κ`-Lindelöf space. -/
class NonKLindelofSpace (κ : Cardinal.{u}) (X : Type u) [TopologicalSpace X] : Prop where
  /-- In a non-`κ`-Lindelöf space, `Set.univ` is not a `κ`-Lindelöf set. -/
  nonKLindelof_univ : ¬IsKLindelof κ (univ : Set X)

lemma nonKLindelof_univ (X : Type u) [TopologicalSpace X]
    [NonKLindelofSpace κ X] : ¬IsKLindelof κ (univ : Set X) := NonKLindelofSpace.nonKLindelof_univ

theorem IsKLindelof.ne_univ [NonKLindelofSpace κ X] (hs : IsKLindelof κ s) : s ≠ univ := fun h ↦
  nonKLindelof_univ X (h ▸ hs)

instance [hreg : Fact κ.IsRegular] [NonKLindelofSpace κ X] : NeBot (Filter.coKLindelof κ X) := by
  refine (hasBasis_coKLindelof hreg.out).neBot_iff.2 fun {s} hs => ?_
  contrapose hs
  rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hs
  rw [hs]
  exact nonKLindelof_univ X

@[simp]
theorem Filter.coKLindelof_eq_bot (hreg : κ.IsRegular) [KLindelofSpace κ X] :
    Filter.coKLindelof κ X = ⊥ :=
  (hasBasis_coKLindelof hreg).eq_bot_iff.mpr ⟨Set.univ, isKLindelof_univ, Set.compl_univ⟩

instance [Fact κ.IsRegular] [NonKLindelofSpace κ X] :
    NeBot (Filter.coclosedKLindelof κ X) :=
  neBot_of_le coKLindelof_le_coclosedKLindelof

theorem nonKLindelofSpace_of_neBot (hreg : κ.IsRegular)
    (_ : NeBot (Filter.coKLindelof κ X)) : NonKLindelofSpace κ X :=
  ⟨fun h' => (Filter.nonempty_of_mem (h'.compl_mem_coKLindelof hreg)).ne_empty compl_univ⟩

theorem Filter.coKLindelof_neBot_iff (hreg : κ.IsRegular) :
    NeBot (Filter.coKLindelof κ X) ↔ NonKLindelofSpace κ X := by
  refine ⟨nonKLindelofSpace_of_neBot hreg, fun _ ↦ ?_⟩
  have : Fact (κ.IsRegular) := ⟨hreg⟩
  infer_instance

theorem not_KLindelofSpace_iff : ¬KLindelofSpace κ X ↔ NonKLindelofSpace κ X :=
  ⟨fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩, fun ⟨h₁⟩ ⟨h₂⟩ => h₁ h₂⟩

theorem cardinal_of_KLindelof_of_discrete_of_isRegular (hreg : κ.IsRegular)
    [KLindelofSpace κ X] [DiscreteTopology X] : #X < κ := by
  rw [← Cardinal.mk_univ]
  exact isKLindelof_univ.cardinal_of_discrete_of_isRegular hreg

theorem cardinal_cover_nhds_interior_of_isRegular (hreg : κ.IsRegular) [KLindelofSpace κ X]
    {U : X → Set X} (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Set X, (#t < κ) ∧ ⋃ x ∈ t, interior (U x) = Set.univ :=
  let ⟨t, ht⟩ := isKLindelof_univ.elim_cardinal_subcover hreg (fun x => interior (U x))
    (fun _ => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  ⟨t, ⟨ht.1, univ_subset_iff.1 ht.2⟩⟩

theorem cardinal_cover_nhds_of_isRegular (hreg : κ.IsRegular) [KLindelofSpace κ X]
    {U : X → Set X} (hU : ∀ x, U x ∈ 𝓝 x) : ∃ t : Set X, (#t < κ) ∧ ⋃ x ∈ t, U x = Set.univ :=
  let ⟨t, ht⟩ := cardinal_cover_nhds_interior_of_isRegular hreg hU
  ⟨t, ⟨ht.1, univ_subset_iff.1 <| ht.2.symm.subset.trans <|
    iUnion₂_mono fun _ _ => interior_subset⟩⟩

/-- The comap of the co-`κ`-Lindelöf filter on `Y` by a continuous function `f : X → Y` is less than
or equal to the co-`κ`-Lindelöf filter on `X`.
This is a reformulation of the fact that images of `κ`-Lindelöf sets are `κ`-Lindelöf. -/
theorem Filter.comap_coKLindelof_le_of_isRegular (hreg : Cardinal.IsRegular κ) {f : X → Y}
    (hf : Continuous f) : (Filter.coKLindelof κ Y).comap f ≤ Filter.coKLindelof κ X := by
  rw [((hasBasis_coKLindelof hreg).comap f).le_basis_iff (hasBasis_coKLindelof hreg)]
  intro t ht
  refine ⟨f '' t, ht.image hf, ?_⟩
  simpa using t.subset_preimage_image f

theorem isKLindelof_range [KLindelofSpace κ X] {f : X → Y} (hf : Continuous f) :
    IsKLindelof κ (range f) :=
  by rw [← image_univ]; exact isKLindelof_univ.image hf

theorem isKLindelof_diagonal [KLindelofSpace κ X] : IsKLindelof κ (diagonal X) :=
  @range_diag X ▸ isKLindelof_range (continuous_id.prod_mk continuous_id)

/-- If `f : X → Y` is an `Inducing` map, the image `f '' s` of a set `s` is `κ`-Lindelöf
  if and only if `s` is `κ`-Lindelöf. -/
theorem Inducing.isKLindelof_iff {f : X → Y} (hf : Inducing f) :
    IsKLindelof κ s ↔ IsKLindelof κ (f '' s) := by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot _ F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x ∈ s, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

/-- If `f : X → Y` is an `Embedding`, the image `f '' s` of a set `s` is `κ`-Lindelöf
  if and only if `s` is `κ`-Lindelöf. -/
theorem Embedding.isKLindelof_iff {f : X → Y} (hf : Embedding f) :
    IsKLindelof κ s ↔ IsKLindelof κ (f '' s) := hf.toInducing.isKLindelof_iff

/-- The preimage of a `κ`-Lindelöf set under an inducing map is a `κ`-Lindelöf set. -/
theorem Inducing.isKLindelof_preimage {f : X → Y} (hf : Inducing f) (hf' : IsClosed (range f))
    {K : Set Y} (hK : IsKLindelof κ K) : IsKLindelof κ (f ⁻¹' K) := by
  replace hK := hK.inter_right hf'
  rwa [hf.isKLindelof_iff, image_preimage_eq_inter_range]

/-- The preimage of a `κ`-Lindelöf set under a closed embedding is a `κ`-Lindelöf set. -/
theorem ClosedEmbedding.isKLindelof_preimage {f : X → Y} (hf : ClosedEmbedding f)
    {K : Set Y} (hK : IsKLindelof κ K) : IsKLindelof κ (f ⁻¹' K) :=
  hf.toInducing.isKLindelof_preimage (hf.isClosed_range) hK

/-- A closed embedding is proper, ie, inverse images of `κ`-Lindelöf sets are contained in
`κ`-Lindelöf sets. Moreover, the preimage of a Lindelöf set is Lindelöf, see
`ClosedEmbedding.isLindelof_preimage`. -/
theorem ClosedEmbedding.tendsto_coKLindelof (hreg : κ.IsRegular) {f : X → Y}
    (hf : ClosedEmbedding f) : Tendsto f (Filter.coKLindelof κ X) (Filter.coKLindelof κ Y) :=
  (hasBasis_coKLindelof hreg).tendsto_right_iff.mpr fun _K hK =>
    (hf.isKLindelof_preimage hK).compl_mem_coKLindelof hreg

/-- Sets of subtype are `κ`-Lindelöf iff the image under a coercion is. -/
theorem Subtype.isKLindelof_iff {p : X → Prop} {s : Set { x // p x }} :
    IsKLindelof κ s ↔ IsKLindelof κ ((↑) '' s : Set X) :=
  embedding_subtype_val.isKLindelof_iff

theorem isKLindelof_iff_isKLindelof_univ : IsKLindelof κ s ↔ IsKLindelof κ (univ : Set s) := by
  rw [Subtype.isKLindelof_iff, image_univ, Subtype.range_coe]

theorem isKLindelof_iff_KLindelofSpace : IsKLindelof κ s ↔ KLindelofSpace κ s :=
  isKLindelof_iff_isKLindelof_univ.trans isKLindelof_univ_iff

lemma IsKLindelof.of_coe [KLindelofSpace κ s] : IsKLindelof κ s :=
  isKLindelof_iff_KLindelofSpace.mpr ‹_›

theorem IsKLindelof.cardinality (hreg : κ.IsRegular) (hs : IsKLindelof κ s)
    (hs' : DiscreteTopology s) : #s < κ :=
  (@cardinal_of_KLindelof_of_discrete_of_isRegular
    _ _ κ hreg (isKLindelof_iff_KLindelofSpace.mp hs) hs')

protected theorem ClosedEmbedding.nonKLindelofSpace (hreg : κ.IsRegular) [NonKLindelofSpace κ X]
    {f : X → Y} (hf : ClosedEmbedding f) : NonKLindelofSpace κ Y := by
  have : Fact (κ.IsRegular) := ⟨hreg⟩
  have : NeBot (coKLindelof κ X) := inferInstance
  exact nonKLindelofSpace_of_neBot hreg (hf.tendsto_coKLindelof hreg).neBot

protected theorem ClosedEmbedding.KLindelofSpace [h : KLindelofSpace κ Y] {f : X → Y}
    (hf : ClosedEmbedding f) : KLindelofSpace κ X :=
  ⟨by rw [hf.toInducing.isKLindelof_iff, image_univ]; exact hf.isClosed_range.isKLindelof⟩

/-- The disjoint union of two `κ`-Lindelöf spaces is `κ`-Lindelöf. -/
instance [hreg : Fact κ.IsRegular] [KLindelofSpace κ X] [KLindelofSpace κ Y] :
    KLindelofSpace κ (X ⊕ Y) where
    isKLindelof_univ := by
      rw [← range_inl_union_range_inr]
      exact IsKLindelof.union hreg.out (isKLindelof_range continuous_inl)
        (isKLindelof_range continuous_inr)

instance [hreg : Fact κ.IsRegular] {X : ι → Type u} (hι : #ι < κ) [∀ i, TopologicalSpace (X i)]
    [∀ i, KLindelofSpace κ (X i)] : KLindelofSpace κ (Σi, X i) where
  isKLindelof_univ := by
    rw [Sigma.univ]
    exact isKLindelof_iUnion hreg.out hι fun i => isKLindelof_range continuous_sigmaMk

instance Quot.KLindelofSpace {r : X → X → Prop} [KLindelofSpace κ X] :
    KLindelofSpace κ (Quot r) where
  isKLindelof_univ := by
    rw [← range_quot_mk]
    exact isKLindelof_range continuous_quot_mk

instance Quotient.KLindelofSpace {s : Setoid X} [KLindelofSpace κ X] :
    KLindelofSpace κ (Quotient s) := Quot.KLindelofSpace

/-- A continuous image of a `κ`-Lindelöf set is a `κ`-Lindelöf set within the codomain. -/
theorem KLindelofSpace.of_continuous_surjective {f : X → Y} [KLindelofSpace κ X] (hf : Continuous f)
    (hsur : Function.Surjective f) : KLindelofSpace κ Y where
  isKLindelof_univ := by
    rw [← Set.image_univ_of_surjective hsur]
    exact IsKLindelof.image (isKLindelof_univ_iff.mpr ‹_›) hf

/-- A set `s` is Hereditarily `κ`-Lindelöf if every subset is a `κ`-Lindelof set. We require this
only for open sets in the definition, and then conclude that this holds for all sets by ADD. -/
def IsHereditarilyKLindelof (κ : Cardinal.{u}) (s : Set X) :=
  ∀ t ⊆ s, IsKLindelof κ t

lemma IsHereditarilyLindelof.isHereditarilyKLindelof (hs : IsHereditarilyLindelof s) (hκ : ℵ₀ < κ) :
    IsHereditarilyKLindelof κ s := fun t ht => IsLindelof.isKLindelof (hs t ht) hκ

/-- Type class for Hereditarily `κ`-Lindelöf spaces.  -/
class HereditarilyKLindelofSpace (κ : Cardinal.{u}) (X : Type u) [TopologicalSpace X] : Prop where
  /-- In a Hereditarily `κ`-Lindelöf space, `Set.univ` is a Hereditarily `κ`-Lindelöf set. -/
  isHereditarilyKLindelof_univ : IsHereditarilyKLindelof κ (univ : Set X)

lemma IsHereditarilyKLindelof.isKLindelof_subset (hs : IsHereditarilyKLindelof κ s) (ht : t ⊆ s) :
    IsKLindelof κ t := hs t ht

lemma IsHereditarilyKLindelof.isKLindelof (hs : IsHereditarilyKLindelof κ s) :
    IsKLindelof κ s := hs.isKLindelof_subset Subset.rfl

instance (priority := 100) HereditarilyKLindelof.to_KLindelof [HereditarilyKLindelofSpace κ X] :
    KLindelofSpace κ X where
  isKLindelof_univ := HereditarilyKLindelofSpace.isHereditarilyKLindelof_univ.isKLindelof

theorem HereditarilyKLindelof_KLindelofSets [HereditarilyKLindelofSpace κ X] (s : Set X):
    IsKLindelof κ s := by
  apply HereditarilyKLindelofSpace.isHereditarilyKLindelof_univ
  exact subset_univ s

lemma eq_open_union_cardinal (hreg : κ.IsRegular) [HereditarilyKLindelofSpace κ X] {ι : Type u}
    (U : ι → Set X) (h : ∀ i, IsOpen (U i)) : ∃ t : Set ι, (#t < κ) ∧ ⋃ i∈t, U i = ⋃ i, U i := by
  have : IsKLindelof κ (⋃ i, U i) := HereditarilyKLindelof_KLindelofSets (⋃ i, U i)
  rcases (isKLindelof_iff_cardinal_subcover hreg).mp this U h (Eq.subset rfl) with ⟨t, ⟨htc, htu⟩⟩
  use t, htc
  apply eq_of_subset_of_subset (iUnion₂_subset_iUnion (fun i ↦ i ∈ t) fun i ↦ U i) htu

instance HereditarilyKLindelof.kLindelofSpace_subtype [HereditarilyKLindelofSpace κ X]
    (p : X → Prop) : KLindelofSpace κ {x // p x} := by
  apply isKLindelof_iff_KLindelofSpace.mp
  exact HereditarilyKLindelof_KLindelofSets fun x ↦ p x

lemma HereditarilyLindelof.HereditarilyKLindelof (hs : HereditarilyLindelofSpace s) (hκ : ℵ₀ < κ) :
    HereditarilyKLindelofSpace κ s where isHereditarilyKLindelof_univ :=
  IsHereditarilyLindelof.isHereditarilyKLindelof hs.isHereditarilyLindelof_univ hκ
