/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Topology.Bases
import Mathlib.Order.Filter.CountableInter
import Mathlib.Topology.Compactness.Compact

/-!
# Lindelöf sets and Lindelöf spaces

## Main definitions

We define the following properties for sets in a topological space:

* `IsLindelof s`: every nontrivial filter on `s` with the countable intersection property has
  a clusterpoint.
* `LindelofSpace X`: `X` is Lindelöf iff every open cover has a countable subcover.
* `NonLindelofSpace`: a space that is not a Lindëlof space.

## Main results

* `isLindelof_iff_countable_subcover`: A set is Lindelöf iff every open cover has a
  countable subcover.
-/
open Set Filter Topology TopologicalSpace


universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Lindelof

/-- A set `s` is Lindelöf if for every nontrivial filter `f` with the countable intersection
  property that contains `s`, there exists `a ∈ s` such that every set of `f`
  meets every neighborhood of `a`. -/
def IsLindelof (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f] [CountableInterFilter f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f

/-- The complement to a Lindelöf set belongs to a filter `f` with the countable intersection
  property if it belongs to each filter `𝓝 x ⊓ f`, `x ∈ s`. -/
theorem IsLindelof.compl_mem_sets (hs : IsLindelof s) {f : Filter X} [CountableInterFilter f]
    (hf : ∀ x ∈ s, sᶜ ∈ 𝓝 x ⊓ f) : sᶜ ∈ f := by
  contrapose! hf
  simp only [not_mem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  apply @hs
  apply inf_le_right

/-- The complement to a Lindelöf set belongs to a filter `f` with the countable intersection
  property if each `x ∈ s` has a neighborhood `t` within `s` such that `tᶜ` belongs to `f`. -/
theorem IsLindelof.compl_mem_sets_of_nhdsWithin (hs : IsLindelof s) {f : Filter X}
    [CountableInterFilter f] (hf : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, tᶜ ∈ f) : sᶜ ∈ f := by
  refine hs.compl_mem_sets fun x hx ↦ ?_
  rcases hf x hx with ⟨t, ht, hst⟩
  replace ht := mem_inf_principal.1 ht
  apply mem_inf_of_inter ht hst
  exact fun x ⟨h₁, h₂⟩ hs ↦ h₂ (h₁ hs)

/-- If `p : Set X → Prop` is stable under restriction and union, and each point `x`
  of a Lindelöf set `s` has a neighborhood `t` within `s` such that `p t`, then `p s` holds. -/
@[elab_as_elim]
theorem IsLindelof.induction_on (hs : IsLindelof s) {p : Set X → Prop} (he : p ∅)
    (hmono : ∀ ⦃s t⦄, s ⊆ t → p t → p s)
    (hcountable_union : ∀ (S : Set (Set X)), S.Countable → (∀ s ∈ S, p s) → p (⋃ s ∈ S, s))
    (hnhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, p t) : p s := by
  let f : Filter X :=
    { sets := { t | p tᶜ }
      univ_sets := by simpa
      sets_of_superset := fun ht₁ ht ↦ hmono (compl_subset_compl.2 ht) ht₁
      inter_sets := by
        intro ht₁ ht₂
        simp only [mem_setOf_eq, compl_inter]
        intro p₁ p₂
        let Se : Set (Set X) := {ht₁ᶜ, ht₂ᶜ}
        have hSe : Se.Countable := by simp
        have : ∀ s ∈ Se, p s := by
          rintro _ ⟨rfl|_⟩
          · exact p₁
          · have h : _ = ht₂ᶜ := by
              assumption
            rw [h]
            exact p₂
        have := hcountable_union Se hSe this
        have : ⋃ s∈ Se, s = ht₁ᶜ ∪ ht₂ᶜ := by simp
        rwa [← this]
        }
  have : CountableInterFilter f := by
    apply CountableInterFilter.mk
    simp only [Filter.mem_mk, mem_setOf_eq, compl_sInter, sUnion_image]
    intro S hS hsp
    let f := fun (x : Set X) ↦ xᶜ
    let S' := f '' S
    have hsp : ∀ s ∈ S', p s := by simpa
    have hS' : S'.Countable := Countable.image hS _
    have : ⋃ s ∈ S, sᶜ = ⋃ s ∈ S', s := by simp
    rw [this]
    apply hcountable_union S' hS' hsp
  have : sᶜ ∈ f := hs.compl_mem_sets_of_nhdsWithin (by simpa using hnhds)
  rwa [← compl_compl s]

/-- The intersection of a Lindelöf set and a closed set is a Lindelöf set. -/
theorem IsLindelof.inter_right (hs : IsLindelof s) (ht : IsClosed t) : IsLindelof (s ∩ t) := by
  intro f hnf _ hstf
  obtain ⟨x, hsx, hx⟩ : ∃ x ∈ s, ClusterPt x f :=
    hs (le_trans hstf (le_principal_iff.2 (inter_subset_left _ _)))
  have : x ∈ t := ht.mem_of_nhdsWithin_neBot <|
    hx.mono <| le_trans hstf (le_principal_iff.2 (inter_subset_right _ _))
  exact ⟨x, ⟨hsx, this⟩, hx⟩

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
  Classical.by_cases mem_of_eq_bot fun (this : f ⊓ 𝓟 tᶜ ≠ ⊥) ↦
  have hinf : CountableInterFilter (f ⊓ 𝓟 tᶜ) := countableInterFilter_inf _ _
  let ⟨x, hx, (hfx : ClusterPt x <| f ⊓ 𝓟 tᶜ)⟩ := @hs _ ⟨this⟩ hinf <| inf_le_of_left_le hf₂
  have : x ∈ t := ht₂ x hx hfx.of_inf_left
  have : tᶜ ∩ t ∈ 𝓝[tᶜ] x := inter_mem_nhdsWithin _ (ht₁.mem_nhds this)
  have A : 𝓝[tᶜ] x = ⊥ := empty_mem_iff_bot.1 <| compl_inter_self t ▸ this
  have : 𝓝[tᶜ] x ≠ ⊥ := hfx.of_inf_right.ne
  absurd A this

/--For every open cover of a Lindelöf set, there exists a countable subcover. -/
theorem IsLindelof.elim_countable_subcover {ι : Type v} (hs : IsLindelof s) (U : ι → Set X)
    (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) :
    ∃ r : Set ι, r.Countable ∧ (s ⊆ ⋃ i ∈ r, U i) := by
  have he : ∃ r : Set ι, r.Countable ∧ ∅ ⊆ ⋃ i ∈ r, U i := by use ∅; simp
  have hmono : ∀ ⦃s t : Set X⦄, s ⊆ t → (∃ r : Set ι, r.Countable ∧ t ⊆ ⋃ i ∈ r, U i)
      → (∃ r : Set ι, r.Countable ∧ s ⊆ ⋃ i ∈ r, U i) := by
    intro _ _ hst ⟨r, ⟨hrcountable,hsub⟩⟩
    exact ⟨r,hrcountable,Subset.trans hst hsub⟩
  have hcountable_union : ∀ (S : Set (Set X)), S.Countable
      → (∀ s ∈ S, ∃ r : Set ι, r.Countable ∧ (s ⊆ ⋃ i ∈ r, U i))
      → ∃ r : Set ι, r.Countable ∧ (⋃ s ∈ S, s ⊆ ⋃ i ∈ r, U i) := by
    intro S hS hsr
    choose! r hr using hsr
    refine ⟨⋃ s ∈ S, r s, hS.biUnion_iff.mpr (fun s hs ↦ (hr s hs).1), ?_⟩
    refine iUnion₂_subset ?h.right.h
    simp only [mem_iUnion, exists_prop, iUnion_exists, biUnion_and']
    exact fun i is x hx ↦ mem_biUnion is ((hr i is).2 hx)
  have h_nhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∃ r : Set ι, r.Countable ∧ (t ⊆ ⋃ i ∈ r, U i) := by
    intro x hx
    let ⟨i, hi⟩ := mem_iUnion.1 (hsU hx)
    refine ⟨U i, mem_nhdsWithin_of_mem_nhds ((hUo i).mem_nhds hi),{i}, ?_⟩
    refine ⟨by simp, ?_⟩
    simp only [mem_singleton_iff, iUnion_iUnion_eq_left]
    exact Subset.refl _
  exact hs.induction_on he hmono hcountable_union h_nhds

theorem IsLindelof.elim_nhds_subcover' (hs : IsLindelof s) (U : ∀ x ∈ s, Set X)
    (hU : ∀ x (hx : x ∈ s), U x ‹x ∈ s› ∈ 𝓝 x) :
    ∃ t : Set s, t.Countable ∧ s ⊆ ⋃ x ∈ t, U (x : s) x.2 := by
  have := hs.elim_countable_subcover (fun x : s ↦ interior (U x x.2)) (fun _ ↦ isOpen_interior)
    fun x hx ↦
      mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 <| hU _ _⟩
  rcases this with ⟨r,⟨hr,hs⟩⟩
  use r, hr
  apply Subset.trans hs
  apply iUnion₂_subset
  intro i hi
  apply Subset.trans interior_subset
  refine subset_iUnion_of_subset i ?_
  refine subset_iUnion_of_subset hi ?_
  apply Subset.refl

theorem IsLindelof.elim_nhds_subcover (hs : IsLindelof s) (U : X → Set X)
    (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
    ∃ t : Set X, t.Countable ∧ (∀ x ∈ t, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x := by
  let ⟨t, ⟨htc,htsub⟩⟩ := hs.elim_nhds_subcover' (fun x _ ↦ U x) hU
  refine ⟨↑t, Countable.image htc Subtype.val,?_⟩
  constructor
  · intro _; simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right,
    forall_exists_index]; tauto
  · have : ⋃ x ∈ t, U ↑x = ⋃ x ∈ Subtype.val '' t, U x := biUnion_image.symm
    rw [← this]; assumption

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

/-- For every family of closed sets whose intersection avoids a Lindelö set,
there exists a countable subfamily whose intersection avoids this Lindelöf set. -/
theorem IsLindelof.elim_countable_subfamily_closed {ι : Type v} (hs : IsLindelof s)
    (t : ι → Set X) (htc : ∀ i, IsClosed (t i)) (hst : (s ∩ ⋂ i, t i) = ∅) :
    ∃ u : Set ι, u.Countable ∧ (s ∩ ⋂ i ∈ u, t i) = ∅ := by
    let U := tᶜ
    have hUo : ∀ i, IsOpen (U i) := by simp only [Pi.compl_apply, isOpen_compl_iff]; exact htc
    have hsU : s ⊆ ⋃ i, U i := by
      simp only [Pi.compl_apply]
      rw [← compl_iInter]
      apply disjoint_compl_left_iff_subset.mp
      simp only [compl_iInter, compl_iUnion, compl_compl]
      apply Disjoint.symm
      exact disjoint_iff_inter_eq_empty.mpr hst
    rcases hs.elim_countable_subcover U hUo hsU with ⟨u, ⟨hucount, husub⟩⟩
    use u, hucount
    rw [← disjoint_compl_left_iff_subset] at husub
    simp only [Pi.compl_apply, compl_iUnion, compl_compl] at husub
    exact disjoint_iff_inter_eq_empty.mp (Disjoint.symm husub)

/--To show that a Lindelöf set intersects the intersection of a family of closed sets,
  it is sufficient to show that it intersects every countable subfamily. -/
theorem IsLindelof.inter_iInter_nonempty {ι : Type v} (hs : IsLindelof s) (t : ι → Set X)
    (htc : ∀ i, IsClosed (t i)) (hst : ∀ u : Set ι, u.Countable ∧ (s ∩ ⋂ i ∈ u, t i).Nonempty) :
    (s ∩ ⋂ i, t i).Nonempty := by
  contrapose! hst
  rcases hs.elim_countable_subfamily_closed t htc hst with ⟨u, ⟨_, husub⟩⟩
  use u
  apply fun _ ↦ husub

/-- For every open cover of a Lindelöf set, there exists a countable subcover. -/
theorem IsLindelof.elim_countable_subcover_image {b : Set ι} {c : ι → Set X} (hs : IsLindelof s)
    (hc₁ : ∀ i ∈ b, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i ∈ b, c i) :
    ∃ b', b' ⊆ b ∧ Set.Countable b' ∧ s ⊆ ⋃ i ∈ b', c i := by
  simp only [Subtype.forall', biUnion_eq_iUnion] at hc₁ hc₂
  rcases hs.elim_countable_subcover (fun i ↦ c i : b → Set X) hc₁ hc₂ with ⟨d, hd⟩
  refine ⟨Subtype.val '' d, ?_, Countable.image hd.1 Subtype.val, ?_⟩-- d.image _, _⟩
  · simp
  · rw [biUnion_image]
    apply hd.2


/-- A set `s` is Lindelöf if for every open cover of `s`, there exists a countable subcover. -/
theorem isLindelof_of_countable_subcover
    (h : ∀ {ι : Type u} (U : ι → Set X), (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) →
    ∃ t : Set ι, t.Countable ∧ s ⊆ ⋃ i ∈ t, U i) :
    IsLindelof s := fun f hf hfs ↦ by
  contrapose! h
  simp only [ClusterPt, not_neBot, ← disjoint_iff, SetCoe.forall',
    (nhds_basis_opens _).disjoint_iff_left] at h
  choose fsub U hU hUf using h
  refine ⟨s, U, fun x ↦ (hU x).2, fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).1 ⟩, ?_ ⟩
  intro t ht h
  have uinf := f.sets_of_superset (le_principal_iff.1 fsub) h
  have uninf : ⋂ i ∈ t, (U i)ᶜ ∈ f := by refine (countable_bInter_mem ht).mpr (fun _ _ ↦ hUf _)
  rw [← compl_iUnion₂] at uninf
  have uninf := compl_not_mem uninf
  simp only [compl_compl] at uninf
  contradiction

/-- A set `s` is Lindelöf if for every family of closed sets whose intersection avoids `s`,
there exists a countable subfamily whose intersection avoids `s`. -/
theorem isLindelof_of_countable_subfamily_closed
    (h : ∀ {ι : Type u} (t : ι → Set X), (∀ i, IsClosed (t i)) → (s ∩ ⋂ i, t i) = ∅ →
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
theorem isLindelof_empty : IsLindelof (∅ : Set X) := fun _f hnf _ hsf↦
  Not.elim hnf.ne <| empty_mem_iff_bot.1 <| le_principal_iff.1 hsf

/-- A singleton set is a Lindelof set. -/
@[simp]
theorem isLindelof_singleton {x : X} : IsLindelof ({x} : Set X) := fun f hf _ hfa ↦
  ⟨x, rfl, ClusterPt.of_le_nhds'
    (hfa.trans <| by simpa only [principal_singleton] using pure_le_nhds x) hf⟩

theorem Set.Subsingleton.isLindelof (hs : s.Subsingleton) : IsLindelof s :=
  Subsingleton.induction_on hs isLindelof_empty fun _ ↦ isLindelof_singleton

/-- Type class for Lindelöf spaces.  -/
class LindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a Lindelöf space, `Set.univ` is a Lindelöf set. -/
  isLindelof_univ : IsLindelof (univ : Set X)

theorem isLindelof_univ_iff : IsLindelof (univ : Set X) ↔ LindelofSpace X :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

theorem isLindelof_univ [h : LindelofSpace X] : IsLindelof (univ : Set X) :=
  h.isLindelof_univ

/-- A compact set `s` is Lindelöf. -/
theorem IsCompact.isLindelof (hs : IsCompact s) :
    IsLindelof s := by tauto

/-- A compact space `X` is Lindelöf. SHOULD THIS BE AN INSTANCE? -/
instance [CompactSpace X] : LindelofSpace X := { isLindelof_univ := isCompact_univ.isLindelof}

/-- `X` is a non-Lindelöf topological space if it is not a Lindelöf space. -/
class NonLindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a non-Lindelöf space, `Set.univ` is not a Lindelöf set. -/
  nonLindelof_univ : ¬IsLindelof (univ : Set X)
