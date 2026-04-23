/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Constructions
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Prod
import Mathlib.Init
import Mathlib.Order.BoundedOrder.Lattice
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.Map
import Mathlib.Order.Filter.Prod
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Closure
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsSet

/-!
# Neighborhoods relative to a subset

This file develops API on the relative versions `nhdsWithin` and `nhdsSetWithin` of `nhds` and
`nhdsSet`, which are defined in previous definition files.

Their basic properties studied in this file include the relationship between neighborhood filters
relative to a set and neighborhood filters in the corresponding subtype, and are in later files used
to develop relative versions `ContinuousOn` and `ContinuousWithinAt` of `Continuous` and
`ContinuousAt`.

## Notation

* `𝓝 x`: the filter of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;
* `𝓝[s] x`: the filter `nhdsWithin x s` of neighborhoods of a point `x` within a set `s`;
* `𝓝ˢ[t] s`: the filter `nhdsSetWithin s t` of neighborhoods of a set `s` within a set `t`.

-/

@[expose] public section

open Set Filter Function Topology

variable {α β γ δ : Type*} [TopologicalSpace α]

/-!
## Properties of the neighborhood-within filter
-/

@[simp]
theorem nhds_bind_nhdsWithin {a : α} {s : Set α} : ((𝓝 a).bind fun x => 𝓝[s] x) = 𝓝[s] a :=
  bind_inf_principal.trans <| congr_arg₂ _ nhds_bind_nhds rfl

@[simp]
theorem eventually_nhds_nhdsWithin {a : α} {s : Set α} {p : α → Prop} :
    (∀ᶠ y in 𝓝 a, ∀ᶠ x in 𝓝[s] y, p x) ↔ ∀ᶠ x in 𝓝[s] a, p x :=
  Filter.ext_iff.1 nhds_bind_nhdsWithin { x | p x }

theorem eventually_nhdsWithin_iff {a : α} {s : Set α} {p : α → Prop} :
    (∀ᶠ x in 𝓝[s] a, p x) ↔ ∀ᶠ x in 𝓝 a, x ∈ s → p x :=
  eventually_inf_principal

theorem frequently_nhdsWithin_iff {z : α} {s : Set α} {p : α → Prop} :
    (∃ᶠ x in 𝓝[s] z, p x) ↔ ∃ᶠ x in 𝓝 z, p x ∧ x ∈ s :=
  frequently_inf_principal.trans <| by simp only [and_comm]

theorem mem_closure_ne_iff_frequently_within {z : α} {s : Set α} :
    z ∈ closure (s \ {z}) ↔ ∃ᶠ x in 𝓝[≠] z, x ∈ s := by
  simp [mem_closure_iff_frequently, frequently_nhdsWithin_iff]

@[simp]
theorem eventually_eventually_nhdsWithin {a : α} {s : Set α} {p : α → Prop} :
    (∀ᶠ y in 𝓝[s] a, ∀ᶠ x in 𝓝[s] y, p x) ↔ ∀ᶠ x in 𝓝[s] a, p x := by
  refine ⟨fun h => ?_, fun h => (eventually_nhds_nhdsWithin.2 h).filter_mono inf_le_left⟩
  simp only [eventually_nhdsWithin_iff] at h ⊢
  exact h.mono fun x hx hxs => (hx hxs).self_of_nhds hxs

@[simp]
theorem eventually_mem_nhdsWithin_iff {x : α} {s t : Set α} :
    (∀ᶠ x' in 𝓝[s] x, t ∈ 𝓝[s] x') ↔ t ∈ 𝓝[s] x :=
  eventually_eventually_nhdsWithin

theorem nhdsWithin_eq (a : α) (s : Set α) :
    𝓝[s] a = ⨅ t ∈ { t : Set α | a ∈ t ∧ IsOpen t }, 𝓟 (t ∩ s) :=
  ((nhds_basis_opens a).inf_principal s).eq_biInf

@[simp] lemma nhdsWithin_univ (a : α) : 𝓝[Set.univ] a = 𝓝 a := by
  rw [nhdsWithin, principal_univ, inf_top_eq]

theorem nhdsWithin_hasBasis {ι : Sort*} {p : ι → Prop} {s : ι → Set α} {a : α}
    (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p fun i => s i ∩ t :=
  h.inf_principal t

theorem nhdsWithin_basis_open (a : α) (t : Set α) :
    (𝓝[t] a).HasBasis (fun u => a ∈ u ∧ IsOpen u) fun u => u ∩ t :=
  nhdsWithin_hasBasis (nhds_basis_opens a) t

theorem mem_nhdsWithin {t : Set α} {a : α} {s : Set α} :
    t ∈ 𝓝[s] a ↔ ∃ u, IsOpen u ∧ a ∈ u ∧ u ∩ s ⊆ t := by
  simpa only [and_assoc, and_left_comm] using (nhdsWithin_basis_open a s).mem_iff

theorem mem_nhdsWithin_iff_exists_mem_nhds_inter {t : Set α} {a : α} {s : Set α} :
    t ∈ 𝓝[s] a ↔ ∃ u ∈ 𝓝 a, u ∩ s ⊆ t :=
  (nhdsWithin_hasBasis (𝓝 a).basis_sets s).mem_iff

theorem diff_mem_nhdsWithin_compl {x : α} {s : Set α} (hs : s ∈ 𝓝 x) (t : Set α) :
    s \ t ∈ 𝓝[tᶜ] x :=
  diff_mem_inf_principal_compl hs t

theorem diff_mem_nhdsWithin_diff {x : α} {s t : Set α} (hs : s ∈ 𝓝[t] x) (t' : Set α) :
    s \ t' ∈ 𝓝[t \ t'] x := by
  rw [nhdsWithin, diff_eq, diff_eq, ← inf_principal, ← inf_assoc]
  exact inter_mem_inf hs (mem_principal_self _)

theorem nhds_of_nhdsWithin_of_nhds {s t : Set α} {a : α} (h1 : s ∈ 𝓝 a) (h2 : t ∈ 𝓝[s] a) :
    t ∈ 𝓝 a := by
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h2 with ⟨_, Hw, hw⟩
  exact (𝓝 a).sets_of_superset ((𝓝 a).inter_sets Hw h1) hw

theorem mem_nhdsWithin_iff_eventually {s t : Set α} {x : α} :
    t ∈ 𝓝[s] x ↔ ∀ᶠ y in 𝓝 x, y ∈ s → y ∈ t :=
  eventually_inf_principal

theorem mem_nhdsWithin_iff_eventuallyEq {s t : Set α} {x : α} :
    t ∈ 𝓝[s] x ↔ s =ᶠ[𝓝 x] (s ∩ t : Set α) := by
  simp_rw [mem_nhdsWithin_iff_eventually, eventuallyEq_set, mem_inter_iff, iff_self_and]

lemma mem_nhdsWithin_inter_self {s t : Set α} {x : α} : t ∈ 𝓝[s ∩ t] x :=
  mem_nhdsWithin_iff_eventuallyEq.mpr <| by simp [inter_assoc]

lemma mem_nhdsWithin_self_inter {s t : Set α} {x : α} : s ∈ 𝓝[s ∩ t] x :=
  mem_nhdsWithin_iff_eventuallyEq.mpr <| by simp [inter_comm s t, inter_assoc]

theorem nhdsWithin_eq_iff_eventuallyEq {s t : Set α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t :=
  set_eventuallyEq_iff_inf_principal.symm

theorem nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x ≤ 𝓝[t] x ↔ t ∈ 𝓝[s] x :=
  set_eventuallyLE_iff_inf_principal_le.symm.trans set_eventuallyLE_iff_mem_inf_principal

theorem preimage_nhdsWithin_coinduced' {X : α → β} {s : Set β} {t : Set α} {a : α} (h : a ∈ t)
    (hs : s ∈ @nhds β (.coinduced (fun x : t => X x) inferInstance) (X a)) :
    X ⁻¹' s ∈ 𝓝[t] a := by
  lift a to t using h
  replace hs : (fun x : t => X x) ⁻¹' s ∈ 𝓝 a := preimage_nhds_coinduced hs
  rwa [← map_nhds_subtype_val, mem_map]

theorem mem_nhdsWithin_of_mem_nhds {s t : Set α} {a : α} (h : s ∈ 𝓝 a) : s ∈ 𝓝[t] a :=
  mem_inf_of_left h

theorem self_mem_nhdsWithin {a : α} {s : Set α} : s ∈ 𝓝[s] a :=
  mem_inf_of_right (mem_principal_self s)

theorem eventually_mem_nhdsWithin {a : α} {s : Set α} : ∀ᶠ x in 𝓝[s] a, x ∈ s :=
  self_mem_nhdsWithin

theorem inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : α} (h : t ∈ 𝓝 a) : s ∩ t ∈ 𝓝[s] a :=
  inter_mem self_mem_nhdsWithin (mem_inf_of_left h)

theorem pure_le_nhdsWithin {a : α} {s : Set α} (ha : a ∈ s) : pure a ≤ 𝓝[s] a :=
  le_inf (pure_le_nhds a) (le_principal_iff.2 ha)

theorem mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha : a ∈ s) (ht : t ∈ 𝓝[s] a) : a ∈ t :=
  pure_le_nhdsWithin ha ht

theorem Filter.Eventually.self_of_nhdsWithin {p : α → Prop} {s : Set α} {x : α}
    (h : ∀ᶠ y in 𝓝[s] x, p y) (hx : x ∈ s) : p x :=
  mem_of_mem_nhdsWithin hx h

theorem tendsto_const_nhdsWithin {l : Filter β} {s : Set α} {a : α} (ha : a ∈ s) :
    Tendsto (fun _ : β => a) l (𝓝[s] a) :=
  tendsto_const_pure.mono_right <| pure_le_nhdsWithin ha

theorem nhdsWithin_restrict'' {a : α} (s : Set α) {t : Set α} (h : t ∈ 𝓝[s] a) :
    𝓝[s] a = 𝓝[s ∩ t] a :=
  le_antisymm (le_inf inf_le_left (le_principal_iff.mpr (inter_mem self_mem_nhdsWithin h)))
    (inf_le_inf_left _ (principal_mono.mpr Set.inter_subset_left))

theorem nhdsWithin_restrict' {a : α} (s : Set α) {t : Set α} (h : t ∈ 𝓝 a) : 𝓝[s] a = 𝓝[s ∩ t] a :=
  nhdsWithin_restrict'' s <| mem_inf_of_left h

theorem nhdsWithin_restrict {a : α} (s : Set α) {t : Set α} (h₀ : a ∈ t) (h₁ : IsOpen t) :
    𝓝[s] a = 𝓝[s ∩ t] a :=
  nhdsWithin_restrict' s (IsOpen.mem_nhds h₁ h₀)

theorem nhdsWithin_le_of_mem {a : α} {s t : Set α} (h : s ∈ 𝓝[t] a) : 𝓝[t] a ≤ 𝓝[s] a :=
  nhdsWithin_le_iff.mpr h

theorem nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a ≤ 𝓝 a := by
  rw [← nhdsWithin_univ]
  apply nhdsWithin_le_of_mem
  exact univ_mem

theorem nhdsWithin_eq_nhdsWithin' {a : α} {s t u : Set α} (hs : s ∈ 𝓝 a) (h₂ : t ∩ s = u ∩ s) :
    𝓝[t] a = 𝓝[u] a := by rw [nhdsWithin_restrict' t hs, nhdsWithin_restrict' u hs, h₂]

theorem nhdsWithin_eq_nhdsWithin {a : α} {s t u : Set α} (h₀ : a ∈ s) (h₁ : IsOpen s)
    (h₂ : t ∩ s = u ∩ s) : 𝓝[t] a = 𝓝[u] a := by
  rw [nhdsWithin_restrict t h₀ h₁, nhdsWithin_restrict u h₀ h₁, h₂]

@[simp] theorem nhdsWithin_eq_nhds {a : α} {s : Set α} : 𝓝[s] a = 𝓝 a ↔ s ∈ 𝓝 a :=
  inf_eq_left.trans le_principal_iff

theorem IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOpen s) (ha : a ∈ s) : 𝓝[s] a = 𝓝 a :=
  nhdsWithin_eq_nhds.2 <| h.mem_nhds ha

theorem preimage_nhds_within_coinduced {X : α → β} {s : Set β} {t : Set α} {a : α} (h : a ∈ t)
    (ht : IsOpen t)
    (hs : s ∈ @nhds β (.coinduced (fun x : t => X x) inferInstance) (X a)) :
    X ⁻¹' s ∈ 𝓝 a := by
  rw [← ht.nhdsWithin_eq h]
  exact preimage_nhdsWithin_coinduced' h hs

@[simp]
theorem nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥ := by rw [nhdsWithin, principal_empty, inf_bot_eq]

theorem nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s ∪ t] a = 𝓝[s] a ⊔ 𝓝[t] a := by
  delta nhdsWithin
  rw [← inf_sup_left, sup_principal]

theorem nhds_eq_nhdsWithin_sup_nhdsWithin (b : α) {I₁ I₂ : Set α} (hI : Set.univ = I₁ ∪ I₂) :
    nhds b = nhdsWithin b I₁ ⊔ nhdsWithin b I₂ := by
  rw [← nhdsWithin_univ b, hI, nhdsWithin_union]

lemma inter_mem_nhdsWithin_inter {a b c d : Set α} {x : α} (h : a ∈ 𝓝[b] x) (h' : c ∈ 𝓝[d] x) :
    a ∩ c ∈ 𝓝[b ∩ d] x :=
  inter_mem (nhdsWithin_mono _ inter_subset_left h) (nhdsWithin_mono _ inter_subset_right h')

/-- If `L` and `R` are neighborhoods of `b` within sets whose union is `Set.univ`, then
`L ∪ R` is a neighborhood of `b`. -/
theorem union_mem_nhds_of_mem_nhdsWithin {b : α}
    {I₁ I₂ : Set α} (h : Set.univ = I₁ ∪ I₂)
    {L : Set α} (hL : L ∈ nhdsWithin b I₁)
    {R : Set α} (hR : R ∈ nhdsWithin b I₂) : L ∪ R ∈ nhds b := by
  rw [← nhdsWithin_univ b, h, nhdsWithin_union]
  exact ⟨mem_of_superset hL (by simp), mem_of_superset hR (by simp)⟩


/-- Writing a punctured neighborhood filter as a sup of left and right filters. -/
lemma punctured_nhds_eq_nhdsWithin_sup_nhdsWithin [LinearOrder α] {x : α} :
    𝓝[≠] x = 𝓝[<] x ⊔ 𝓝[>] x := by
  rw [← Iio_union_Ioi, nhdsWithin_union]


/-- Obtain a "predictably-sided" neighborhood of `b` from two one-sided neighborhoods. -/
theorem nhds_of_Ici_Iic [LinearOrder α] {b : α}
    {L : Set α} (hL : L ∈ 𝓝[≤] b)
    {R : Set α} (hR : R ∈ 𝓝[≥] b) : L ∩ Iic b ∪ R ∩ Ici b ∈ 𝓝 b :=
  union_mem_nhds_of_mem_nhdsWithin Iic_union_Ici.symm
    (inter_mem hL self_mem_nhdsWithin) (inter_mem hR self_mem_nhdsWithin)

theorem nhdsWithin_biUnion {ι} {I : Set ι} (hI : I.Finite) (s : ι → Set α) (a : α) :
    𝓝[⋃ i ∈ I, s i] a = ⨆ i ∈ I, 𝓝[s i] a := by
  induction I, hI using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hT => simp only [hT, nhdsWithin_union, iSup_insert, biUnion_insert]

theorem nhdsWithin_sUnion {S : Set (Set α)} (hS : S.Finite) (a : α) :
    𝓝[⋃₀ S] a = ⨆ s ∈ S, 𝓝[s] a := by
  rw [sUnion_eq_biUnion, nhdsWithin_biUnion hS]

theorem nhdsWithin_iUnion {ι} [Finite ι] (s : ι → Set α) (a : α) :
    𝓝[⋃ i, s i] a = ⨆ i, 𝓝[s i] a := by
  rw [← sUnion_range, nhdsWithin_sUnion (finite_range s), iSup_range]

theorem nhdsWithin_inter (a : α) (s t : Set α) : 𝓝[s ∩ t] a = 𝓝[s] a ⊓ 𝓝[t] a := by
  delta nhdsWithin
  rw [inf_left_comm, inf_assoc, inf_principal, ← inf_assoc, inf_idem]

theorem nhdsWithin_inter' (a : α) (s t : Set α) : 𝓝[s ∩ t] a = 𝓝[s] a ⊓ 𝓟 t := by
  delta nhdsWithin
  rw [← inf_principal, inf_assoc]

theorem nhdsWithin_inter_of_mem {a : α} {s t : Set α} (h : s ∈ 𝓝[t] a) : 𝓝[s ∩ t] a = 𝓝[t] a := by
  rw [nhdsWithin_inter, inf_eq_right]
  exact nhdsWithin_le_of_mem h

theorem nhdsWithin_inter_of_mem' {a : α} {s t : Set α} (h : t ∈ 𝓝[s] a) : 𝓝[s ∩ t] a = 𝓝[s] a := by
  rw [inter_comm, nhdsWithin_inter_of_mem h]

@[simp]
theorem nhdsWithin_singleton (a : α) : 𝓝[{a}] a = pure a := by
  rw [nhdsWithin, principal_singleton, inf_eq_right.2 (pure_le_nhds a)]

@[simp]
theorem nhdsWithin_insert (a : α) (s : Set α) : 𝓝[insert a s] a = pure a ⊔ 𝓝[s] a := by
  rw [← singleton_union, nhdsWithin_union, nhdsWithin_singleton]

theorem mem_nhdsWithin_insert {a : α} {s t : Set α} : t ∈ 𝓝[insert a s] a ↔ a ∈ t ∧ t ∈ 𝓝[s] a := by
  simp

theorem insert_mem_nhdsWithin_insert {a : α} {s t : Set α} (h : t ∈ 𝓝[s] a) :
    insert a t ∈ 𝓝[insert a s] a := by simp [mem_of_superset h]

theorem insert_mem_nhds_iff {a : α} {s : Set α} : insert a s ∈ 𝓝 a ↔ s ∈ 𝓝[≠] a := by
  simp only [nhdsWithin, mem_inf_principal, mem_compl_iff, mem_singleton_iff, or_iff_not_imp_left,
    insert_def]

@[simp]
theorem nhdsNE_sup_pure (a : α) : 𝓝[≠] a ⊔ pure a = 𝓝 a := by
  rw [← nhdsWithin_singleton, ← nhdsWithin_union, compl_union_self, nhdsWithin_univ]

@[simp]
theorem pure_sup_nhdsNE (a : α) : pure a ⊔ 𝓝[≠] a = 𝓝 a := by rw [← sup_comm, nhdsNE_sup_pure]

lemma continuousAt_iff_punctured_nhds [TopologicalSpace β] {f : α → β} {a : α} :
    ContinuousAt f a ↔ Tendsto f (𝓝[≠] a) (𝓝 (f a)) := by
  simp [ContinuousAt, -pure_sup_nhdsNE, ← pure_sup_nhdsNE a, tendsto_pure_nhds]

theorem nhdsWithin_prod [TopologicalSpace β]
    {s u : Set α} {t v : Set β} {a : α} {b : β} (hu : u ∈ 𝓝[s] a) (hv : v ∈ 𝓝[t] b) :
    u ×ˢ v ∈ 𝓝[s ×ˢ t] (a, b) := by
  rw [nhdsWithin_prod_eq]
  exact prod_mem_prod hu hv

lemma Filter.EventuallyEq.mem_interior {x : α} {s t : Set α} (hst : s =ᶠ[𝓝 x] t)
    (h : x ∈ interior s) : x ∈ interior t := by
  rw [← nhdsWithin_eq_iff_eventuallyEq] at hst
  simpa [mem_interior_iff_mem_nhds, ← nhdsWithin_eq_nhds, hst] using h

lemma Filter.EventuallyEq.mem_interior_iff {x : α} {s t : Set α} (hst : s =ᶠ[𝓝 x] t) :
    x ∈ interior s ↔ x ∈ interior t :=
  ⟨fun h ↦ hst.mem_interior h, fun h ↦ hst.symm.mem_interior h⟩

section Pi

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

theorem nhdsWithin_pi_eq' {I : Set ι} (hI : I.Finite) (s : ∀ i, Set (X i)) (x : ∀ i, X i) :
    𝓝[pi I s] x = ⨅ i, comap (fun x => x i) (𝓝 (x i) ⊓ ⨅ (_ : i ∈ I), 𝓟 (s i)) := by
  simp only [nhdsWithin, nhds_pi, Filter.pi, comap_inf, comap_iInf, pi_def, comap_principal, ←
    iInf_principal_finite hI, ← iInf_inf_eq]

theorem nhdsWithin_pi_eq {I : Set ι} (hI : I.Finite) (s : ∀ i, Set (X i)) (x : ∀ i, X i) :
    𝓝[pi I s] x =
      (⨅ i ∈ I, comap (fun x => x i) (𝓝[s i] x i)) ⊓
        ⨅ (i) (_ : i ∉ I), comap (fun x => x i) (𝓝 (x i)) := by
  simp only [nhdsWithin, nhds_pi, Filter.pi, pi_def, ← iInf_principal_finite hI, comap_inf,
    comap_principal]
  rw [iInf_split _ fun i => i ∈ I, inf_right_comm]
  simp only [iInf_inf_eq]

theorem nhdsWithin_pi_univ_eq [Finite ι] (s : ∀ i, Set (X i)) (x : ∀ i, X i) :
    𝓝[pi univ s] x = ⨅ i, comap (fun x => x i) (𝓝[s i] x i) := by
  simpa [nhdsWithin] using nhdsWithin_pi_eq finite_univ s x

theorem nhdsWithin_pi_eq_bot {I : Set ι} {s : ∀ i, Set (X i)} {x : ∀ i, X i} :
    𝓝[pi I s] x = ⊥ ↔ ∃ i ∈ I, 𝓝[s i] x i = ⊥ := by
  simp only [nhdsWithin, nhds_pi, pi_inf_principal_pi_eq_bot]

theorem nhdsWithin_pi_neBot {I : Set ι} {s : ∀ i, Set (X i)} {x : ∀ i, X i} :
    (𝓝[pi I s] x).NeBot ↔ ∀ i ∈ I, (𝓝[s i] x i).NeBot := by
  simp [neBot_iff, nhdsWithin_pi_eq_bot]

instance instNeBotNhdsWithinUnivPi {s : ∀ i, Set (X i)} {x : ∀ i, X i}
    [∀ i, (𝓝[s i] x i).NeBot] : (𝓝[pi univ s] x).NeBot := by
  simpa [nhdsWithin_pi_neBot]

instance Pi.instNeBotNhdsWithinIio [Nonempty ι] [∀ i, Preorder (X i)] {x : ∀ i, X i}
    [∀ i, (𝓝[<] x i).NeBot] : (𝓝[<] x).NeBot :=
  have : (𝓝[pi univ fun i ↦ Iio (x i)] x).NeBot := inferInstance
  this.mono <| nhdsWithin_mono _ fun _y hy ↦ lt_of_strongLT fun i ↦ hy i trivial

instance Pi.instNeBotNhdsWithinIoi [Nonempty ι] [∀ i, Preorder (X i)] {x : ∀ i, X i}
    [∀ i, (𝓝[>] x i).NeBot] : (𝓝[>] x).NeBot :=
  Pi.instNeBotNhdsWithinIio (X := fun i ↦ (X i)ᵒᵈ) (x := fun i ↦ OrderDual.toDual (x i))

end Pi

theorem Filter.Tendsto.piecewise_nhdsWithin {f g : α → β} {t : Set α} [∀ x, Decidable (x ∈ t)]
    {a : α} {s : Set α} {l : Filter β} (h₀ : Tendsto f (𝓝[s ∩ t] a) l)
    (h₁ : Tendsto g (𝓝[s ∩ tᶜ] a) l) : Tendsto (piecewise t f g) (𝓝[s] a) l := by
  apply Tendsto.piecewise <;> rwa [← nhdsWithin_inter']

theorem Filter.Tendsto.if_nhdsWithin {f g : α → β} {p : α → Prop} [DecidablePred p] {a : α}
    {s : Set α} {l : Filter β} (h₀ : Tendsto f (𝓝[s ∩ { x | p x }] a) l)
    (h₁ : Tendsto g (𝓝[s ∩ { x | ¬p x }] a) l) :
    Tendsto (fun x => if p x then f x else g x) (𝓝[s] a) l :=
  h₀.piecewise_nhdsWithin h₁

theorem map_nhdsWithin (f : α → β) (a : α) (s : Set α) :
    map f (𝓝[s] a) = ⨅ t ∈ { t : Set α | a ∈ t ∧ IsOpen t }, 𝓟 (f '' (t ∩ s)) :=
  ((nhdsWithin_basis_open a s).map f).eq_biInf

theorem tendsto_nhdsWithin_mono_left {f : α → β} {a : α} {s t : Set α} {l : Filter β} (hst : s ⊆ t)
    (h : Tendsto f (𝓝[t] a) l) : Tendsto f (𝓝[s] a) l :=
  h.mono_left <| nhdsWithin_mono a hst

theorem tendsto_nhdsWithin_mono_right {f : β → α} {l : Filter β} {a : α} {s t : Set α} (hst : s ⊆ t)
    (h : Tendsto f l (𝓝[s] a)) : Tendsto f l (𝓝[t] a) :=
  h.mono_right (nhdsWithin_mono a hst)

theorem tendsto_nhdsWithin_of_tendsto_nhds {f : α → β} {a : α} {s : Set α} {l : Filter β}
    (h : Tendsto f (𝓝 a) l) : Tendsto f (𝓝[s] a) l :=
  h.mono_left inf_le_left

theorem eventually_mem_of_tendsto_nhdsWithin {f : β → α} {a : α} {s : Set α} {l : Filter β}
    (h : Tendsto f l (𝓝[s] a)) : ∀ᶠ i in l, f i ∈ s := by
  simp_rw [nhdsWithin_eq, tendsto_iInf, mem_setOf_eq, tendsto_principal, mem_inter_iff,
    eventually_and] at h
  exact (h univ ⟨mem_univ a, isOpen_univ⟩).2

theorem tendsto_nhds_of_tendsto_nhdsWithin {f : β → α} {a : α} {s : Set α} {l : Filter β}
    (h : Tendsto f l (𝓝[s] a)) : Tendsto f l (𝓝 a) :=
  h.mono_right nhdsWithin_le_nhds

theorem nhdsWithin_neBot_of_mem {s : Set α} {x : α} (hx : x ∈ s) : NeBot (𝓝[s] x) :=
  mem_closure_iff_nhdsWithin_neBot.1 <| subset_closure hx

theorem IsClosed.mem_of_nhdsWithin_neBot {s : Set α} (hs : IsClosed s) {x : α}
    (hx : NeBot <| 𝓝[s] x) : x ∈ s :=
  hs.closure_eq ▸ mem_closure_iff_nhdsWithin_neBot.2 hx

theorem DenseRange.nhdsWithin_neBot {ι : Type*} {f : ι → α} (h : DenseRange f) (x : α) :
    NeBot (𝓝[range f] x) :=
  mem_closure_iff_clusterPt.1 (h x)

theorem mem_closure_pi {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)] {I : Set ι}
    {s : ∀ i, Set (α i)} {x : ∀ i, α i} : x ∈ closure (pi I s) ↔ ∀ i ∈ I, x i ∈ closure (s i) := by
  simp only [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_pi_neBot]

theorem closure_pi_set {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)] (I : Set ι)
    (s : ∀ i, Set (α i)) : closure (pi I s) = pi I fun i => closure (s i) :=
  Set.ext fun _ => mem_closure_pi

theorem dense_pi {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)] {s : ∀ i, Set (α i)}
    (I : Set ι) (hs : ∀ i ∈ I, Dense (s i)) : Dense (pi I s) := by
  simp only [dense_iff_closure_eq, closure_pi_set, pi_congr rfl fun i hi => (hs i hi).closure_eq,
    pi_univ]

theorem DenseRange.piMap {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    {f : (i : ι) → (X i) → (Y i)} (hf : ∀ i, DenseRange (f i)) :
    DenseRange (Pi.map f) := by
  rw [DenseRange, Set.range_piMap]
  exact dense_pi Set.univ (fun i _ => hf i)

theorem eventuallyEq_nhdsWithin_iff {f g : α → β} {s : Set α} {a : α} :
    f =ᶠ[𝓝[s] a] g ↔ ∀ᶠ x in 𝓝 a, x ∈ s → f x = g x :=
  mem_inf_principal

/-- Two functions agree on a neighborhood of `x` if they agree at `x` and in a punctured
neighborhood. -/
theorem eventuallyEq_nhds_of_eventuallyEq_nhdsNE {f g : α → β} {a : α} (h₁ : f =ᶠ[𝓝[≠] a] g)
    (h₂ : f a = g a) :
    f =ᶠ[𝓝 a] g := by
  filter_upwards [eventually_nhdsWithin_iff.1 h₁]
  grind

theorem eventuallyEq_nhdsWithin_of_eqOn {f g : α → β} {s : Set α} {a : α} (h : EqOn f g s) :
    f =ᶠ[𝓝[s] a] g :=
  mem_inf_of_right h

theorem Set.EqOn.eventuallyEq_nhdsWithin {f g : α → β} {s : Set α} {a : α} (h : EqOn f g s) :
    f =ᶠ[𝓝[s] a] g :=
  eventuallyEq_nhdsWithin_of_eqOn h

theorem tendsto_nhdsWithin_congr {f g : α → β} {s : Set α} {a : α} {l : Filter β}
    (hfg : ∀ x ∈ s, f x = g x) (hf : Tendsto f (𝓝[s] a) l) : Tendsto g (𝓝[s] a) l :=
  (tendsto_congr' <| eventuallyEq_nhdsWithin_of_eqOn hfg).1 hf

theorem eventually_nhdsWithin_of_forall {s : Set α} {a : α} {p : α → Prop} (h : ∀ x ∈ s, p x) :
    ∀ᶠ x in 𝓝[s] a, p x :=
  mem_inf_of_right h

theorem tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α}
    (f : β → α) (h1 : Tendsto f l (𝓝 a)) (h2 : ∀ᶠ x in l, f x ∈ s) : Tendsto f l (𝓝[s] a) :=
  tendsto_inf.2 ⟨h1, tendsto_principal.2 h2⟩

theorem tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s : Set α} {f : β → α} :
    Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ ∀ᶠ n in l, f n ∈ s :=
  ⟨fun h => ⟨tendsto_nhds_of_tendsto_nhdsWithin h, eventually_mem_of_tendsto_nhdsWithin h⟩, fun h =>
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h.1 h.2⟩

@[simp]
theorem tendsto_nhdsWithin_range {a : α} {l : Filter β} {f : β → α} :
    Tendsto f l (𝓝[range f] a) ↔ Tendsto f l (𝓝 a) :=
  ⟨fun h => h.mono_right inf_le_left, fun h =>
    tendsto_inf.2 ⟨h, tendsto_principal.2 <| Eventually.of_forall mem_range_self⟩⟩

theorem Filter.EventuallyEq.eq_of_nhdsWithin {s : Set α} {f g : α → β} {a : α} (h : f =ᶠ[𝓝[s] a] g)
    (hmem : a ∈ s) : f a = g a :=
  h.self_of_nhdsWithin hmem

theorem eventually_nhdsWithin_of_eventually_nhds {s : Set α}
    {a : α} {p : α → Prop} (h : ∀ᶠ x in 𝓝 a, p x) : ∀ᶠ x in 𝓝[s] a, p x :=
  mem_nhdsWithin_of_mem_nhds h

lemma Set.MapsTo.preimage_mem_nhdsWithin {f : α → β} {s : Set α} {t : Set β} {x : α}
    (hst : MapsTo f s t) : f ⁻¹' t ∈ 𝓝[s] x :=
  Filter.mem_of_superset self_mem_nhdsWithin hst

/-!
### `nhdsWithin` and subtypes
-/

theorem mem_nhdsWithin_subtype {s : Set α} {a : { x // x ∈ s }} {t u : Set { x // x ∈ s }} :
    t ∈ 𝓝[u] a ↔ t ∈ comap ((↑) : s → α) (𝓝[(↑) '' u] a) := by
  rw [nhdsWithin, nhds_subtype, principal_subtype, ← comap_inf, ← nhdsWithin]

theorem nhdsWithin_subtype (s : Set α) (a : { x // x ∈ s }) (t : Set { x // x ∈ s }) :
    𝓝[t] a = comap ((↑) : s → α) (𝓝[(↑) '' t] a) :=
  Filter.ext fun _ => mem_nhdsWithin_subtype

theorem nhdsWithin_eq_map_subtype_coe {s : Set α} {a : α} (h : a ∈ s) :
    𝓝[s] a = map ((↑) : s → α) (𝓝 ⟨a, h⟩) :=
  (map_nhds_subtype_val ⟨a, h⟩).symm

theorem mem_nhds_subtype_iff_nhdsWithin {s : Set α} {a : s} {t : Set s} :
    t ∈ 𝓝 a ↔ (↑) '' t ∈ 𝓝[s] (a : α) := by
  rw [← map_nhds_subtype_val, image_mem_map_iff Subtype.val_injective]

theorem preimage_coe_mem_nhds_subtype {s t : Set α} {a : s} : (↑) ⁻¹' t ∈ 𝓝 a ↔ t ∈ 𝓝[s] ↑a := by
  rw [← map_nhds_subtype_val, mem_map]

theorem eventually_nhds_subtype_iff (s : Set α) (a : s) (P : α → Prop) :
    (∀ᶠ x : s in 𝓝 a, P x) ↔ ∀ᶠ x in 𝓝[s] a, P x :=
  preimage_coe_mem_nhds_subtype

theorem frequently_nhds_subtype_iff (s : Set α) (a : s) (P : α → Prop) :
    (∃ᶠ x : s in 𝓝 a, P x) ↔ ∃ᶠ x in 𝓝[s] a, P x :=
  eventually_nhds_subtype_iff s a (¬ P ·) |>.not

theorem tendsto_nhdsWithin_iff_subtype {s : Set α} {a : α} (h : a ∈ s) (f : α → β) (l : Filter β) :
    Tendsto f (𝓝[s] a) l ↔ Tendsto (s.restrict f) (𝓝 ⟨a, h⟩) l := by
  rw [nhdsWithin_eq_map_subtype_coe h, tendsto_map'_iff]; rfl

theorem clusterPt_principal_subtype_iff_frequently {s t : Set α} (hst : s ⊆ t) {J : Set s} {a : s} :
    ClusterPt a (Filter.principal J) ↔ ∃ᶠ x in nhdsWithin a t, ∃ h : x ∈ s, (⟨x, h⟩ : s) ∈ J := by
  rw [nhdsWithin_eq_map_subtype_coe (hst a.prop), Filter.frequently_map,
    clusterPt_principal_iff_frequently,
    Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.frequently_comap,
    Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.frequently_comap, Subtype.coe_mk]
  apply frequently_congr
  apply Eventually.of_forall
  intro x
  simp only [SetCoe.exists, exists_and_left, exists_eq_left]
  exact ⟨fun ⟨h, hx⟩ => ⟨hst h, h, hx⟩, fun ⟨_, hx⟩ => hx⟩

/-!
## The `nhdsSetWithin`-filter
-/

variable [TopologicalSpace β]

@[gcongr, mono]
lemma nhdsSetWithin_mono_left {s s' t : Set α} (h : s ⊆ s') : 𝓝ˢ[t] s ≤ 𝓝ˢ[t] s' :=
  inf_le_inf_right _ <| nhdsSet_mono h

@[gcongr, mono]
lemma nhdsSetWithin_mono_right {s t t' : Set α} (h : t ⊆ t') : 𝓝ˢ[t] s ≤ 𝓝ˢ[t'] s :=
  inf_le_inf_left _ <| principal_mono.2 h

lemma nhdsSetWithin_hasBasis {ι : Sort*} {p : ι → Prop} {s' : ι → Set α} {s : Set α}
    (h : (𝓝ˢ s).HasBasis p s') (t : Set α) : (𝓝ˢ[t] s).HasBasis p fun i => s' i ∩ t :=
  h.inf_principal t

lemma nhdsSetWithin_basis_open (s t : Set α) :
    (𝓝ˢ[t] s).HasBasis (fun u => IsOpen u ∧ s ⊆ u) fun u => u ∩ t :=
  nhdsSetWithin_hasBasis (hasBasis_nhdsSet s) t

lemma mem_nhdsSetWithin {s t u : Set α} : u ∈ 𝓝ˢ[t] s ↔ ∃ v, IsOpen v ∧ s ⊆ v ∧ v ∩ t ⊆ u := by
  simpa [and_assoc] using (nhdsSetWithin_basis_open s t).mem_iff

@[simp]
lemma nhdsSetWithin_singleton {x : α} {s : Set α} : 𝓝ˢ[s] {x} = 𝓝[s] x := by
  simp [nhdsSetWithin, nhdsWithin]

@[simp]
lemma nhdsSetWithin_univ {s : Set α} : 𝓝ˢ[univ] s = 𝓝ˢ s := by
  simp [nhdsSetWithin]

theorem mem_nhdsSet {s t : Set α} : s ∈ 𝓝ˢ t ↔ ∃ u ⊆ s, IsOpen u ∧ t ⊆ u := by
  simp [← nhdsSetWithin_univ, mem_nhdsSetWithin, and_comm, and_assoc]

@[simp]
lemma nhdsSetWithin_univ' {s : Set α} : 𝓝ˢ[s] univ = 𝓟 s := by
  simp [nhdsSetWithin]

@[simp]
lemma nhdsSetWithin_self {s : Set α} : 𝓝ˢ[s] s = 𝓟 s := by
  simp [nhdsSetWithin, principal_le_nhdsSet]

lemma nhdsSetWithin_eq_principal_of_subset {s t : Set α} (h : t ⊆ s) : 𝓝ˢ[t] s = 𝓟 t := by
  simp [nhdsSetWithin, (principal_mono.2 h).trans principal_le_nhdsSet]

@[simp]
lemma nhdsSetWithin_empty {s : Set α} : 𝓝ˢ[∅] s = ⊥ := by
  simp [nhdsSetWithin]

@[simp]
lemma nhdsSetWithin_empty' {s : Set α} : 𝓝ˢ[s] ∅ = ⊥ := by
  simp [nhdsSetWithin]

lemma principal_inter_le_nhdsSetWithin {s t : Set α} : 𝓟 (s ∩ t) ≤ 𝓝ˢ[t] s := by
  simpa [nhdsSetWithin] using inf_le_of_left_le (b := 𝓟 t) <| principal_le_nhdsSet

lemma nhdsSetWithin_prod_le {s s' : Set α} {t t' : Set β} :
    𝓝ˢ[s' ×ˢ t'] (s ×ˢ t) ≤ 𝓝ˢ[s'] s ×ˢ 𝓝ˢ[t'] t := by
  simpa [nhdsSetWithin, ← prod_inf_prod] using inf_le_of_left_le <| nhdsSet_prod_le _ _

lemma mem_nhdsSet_induced {α β : Type*} {t : TopologicalSpace β} (f : α → β) (s u : Set α) :
    u ∈ @nhdsSet α (t.induced f) s ↔ ∃ v ∈ 𝓝ˢ (f '' s), f ⁻¹' v ⊆ u := by
  letI := t.induced f
  simp_rw [mem_nhdsSet_iff_exists, isOpen_induced_iff]
  refine ⟨fun ⟨v, ⟨v', hv'⟩, hv⟩ ↦ ?_, fun ⟨v, ⟨v', hv'⟩, hv⟩ ↦ ?_⟩
  · refine ⟨v', ⟨v', hv'.1, ?_, subset_rfl⟩, hv'.2.trans_subset hv.2⟩
    exact (image_mono hv.1).trans (by simp [hv'])
  · exact ⟨f ⁻¹' v', ⟨v', hv'.1, rfl⟩, image_subset_iff.1 hv'.2.1, (preimage_mono hv'.2.2).trans hv⟩

lemma nhdsSet_induced {α β : Type*} {t : TopologicalSpace β} (f : α → β) (s : Set α) :
    @nhdsSet α (t.induced f) s = comap f (𝓝ˢ (f '' s)) := by
  ext s
  rw [mem_nhdsSet_induced, mem_comap]

lemma map_nhdsSet_induced_eq {α β : Type*} {t : TopologicalSpace β} {f : α → β} (s : Set α) :
    map f (@nhdsSet α (t.induced f) s) = 𝓝ˢ[range f] (f '' s) := by
  rw [nhdsSet_induced, Filter.map_comap, nhdsSetWithin]

lemma Topology.IsInducing.map_nhdsSet_eq {f : α → β} (hf : IsInducing f) (s : Set α) :
    (𝓝ˢ s).map f = 𝓝ˢ[range f] (f '' s) :=
  hf.eq_induced ▸ map_nhdsSet_induced_eq s

lemma map_nhdsSet_subtype_val {s : Set α} (t : Set s) :
    map (↑) (𝓝ˢ t) = 𝓝ˢ[s] ((↑) '' t) := by
  rw [IsInducing.subtypeVal.map_nhdsSet_eq, Subtype.range_val]

lemma mem_nhdsSet_subtype_iff_nhdsSetWithin {s : Set α} {t u : Set s} :
    u ∈ 𝓝ˢ t ↔ (↑) '' u ∈ 𝓝ˢ[s] ((↑) '' t) := by
  rw [← map_nhdsSet_subtype_val, image_mem_map_iff Subtype.val_injective]
