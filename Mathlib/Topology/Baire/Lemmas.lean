/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Topology.GDelta

#align_import topology.metric_space.baire from "leanprover-community/mathlib"@"b9e46fe101fc897fb2e7edaf0bf1f09ea49eb81a"

/-!
# Baire spaces

A topological space is called a *Baire space*
if a countable intersection of dense open subsets is dense.
Baire theorems say that all completely metrizable spaces
and all locally compact regular spaces are Baire spaces.
We prove the theorems in `Mathlib/Topology/Baire/CompleteMetrizable`
and `Mathlib/Topology/Baire/LocallyCompactRegular`.

In this file we prove various corollaries of Baire theorems.

The good concept underlying the theorems is that of a Gδ set, i.e., a countable intersection
of open sets. Then Baire theorem can also be formulated as the fact that a countable
intersection of dense Gδ sets is a dense Gδ set. We deduce this version from Baire property.
We also prove the important consequence that, if the space is
covered by a countable union of closed sets, then the union of their interiors is dense.

We also prove that in Baire spaces, the `residual` sets are exactly those containing a dense Gδ set.
-/


noncomputable section

open scoped Topology
open Filter Set TopologicalSpace

variable {X α : Type*} {ι : Sort*}

section BaireTheorem

variable [TopologicalSpace X] [BaireSpace X]

/-- Definition of a Baire space. -/
theorem dense_iInter_of_isOpen_nat {f : ℕ → Set X} (ho : ∀ n, IsOpen (f n))
    (hd : ∀ n, Dense (f n)) : Dense (⋂ n, f n) :=
  BaireSpace.baire_property f ho hd
#align dense_Inter_of_open_nat dense_iInter_of_isOpen_nat

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with ⋂₀. -/
theorem dense_sInter_of_isOpen {S : Set (Set X)} (ho : ∀ s ∈ S, IsOpen s) (hS : S.Countable)
    (hd : ∀ s ∈ S, Dense s) : Dense (⋂₀ S) := by
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h]
  · rcases hS.exists_eq_range h with ⟨f, rfl⟩
    exact dense_iInter_of_isOpen_nat (forall_mem_range.1 ho) (forall_mem_range.1 hd)
#align dense_sInter_of_open dense_sInter_of_isOpen

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with
an index set which is a countable set in any type. -/
theorem dense_biInter_of_isOpen {S : Set α} {f : α → Set X} (ho : ∀ s ∈ S, IsOpen (f s))
    (hS : S.Countable) (hd : ∀ s ∈ S, Dense (f s)) : Dense (⋂ s ∈ S, f s) := by
  rw [← sInter_image]
  refine dense_sInter_of_isOpen ?_ (hS.image _) ?_ <;> rwa [forall_mem_image]
#align dense_bInter_of_open dense_biInter_of_isOpen

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with
an index set which is a countable type. -/
theorem dense_iInter_of_isOpen [Countable ι] {f : ι → Set X} (ho : ∀ i, IsOpen (f i))
    (hd : ∀ i, Dense (f i)) : Dense (⋂ s, f s) :=
  dense_sInter_of_isOpen (forall_mem_range.2 ho) (countable_range _) (forall_mem_range.2 hd)
#align dense_Inter_of_open dense_iInter_of_isOpen

/-- A set is residual (comeagre) if and only if it includes a dense `Gδ` set. -/
theorem mem_residual {s : Set X} : s ∈ residual X ↔ ∃ t ⊆ s, IsGδ t ∧ Dense t := by
  constructor
  · rw [mem_residual_iff]
    rintro ⟨S, hSo, hSd, Sct, Ss⟩
    refine ⟨_, Ss, ⟨_, fun t ht => hSo _ ht, Sct, rfl⟩, ?_⟩
    exact dense_sInter_of_isOpen hSo Sct hSd
  rintro ⟨t, ts, ho, hd⟩
  exact mem_of_superset (residual_of_dense_Gδ ho hd) ts
#align mem_residual mem_residual

/-- A property holds on a residual (comeagre) set if and only if it holds on some dense `Gδ` set. -/
theorem eventually_residual {p : X → Prop} :
    (∀ᶠ x in residual X, p x) ↔ ∃ t : Set X, IsGδ t ∧ Dense t ∧ ∀ x ∈ t, p x := by
  simp only [Filter.Eventually, mem_residual, subset_def, mem_setOf_eq]
  tauto
#align eventually_residual eventually_residual

theorem dense_of_mem_residual {s : Set X} (hs : s ∈ residual X) : Dense s :=
  let ⟨_, hts, _, hd⟩ := mem_residual.1 hs
  hd.mono hts
#align dense_of_mem_residual dense_of_mem_residual

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with ⋂₀. -/
theorem dense_sInter_of_Gδ {S : Set (Set X)} (ho : ∀ s ∈ S, IsGδ s) (hS : S.Countable)
    (hd : ∀ s ∈ S, Dense s) : Dense (⋂₀ S) :=
  dense_of_mem_residual ((countable_sInter_mem hS).mpr
    (fun _ hs => residual_of_dense_Gδ (ho _ hs) (hd _ hs)))
set_option linter.uppercaseLean3 false in
#align dense_sInter_of_Gδ dense_sInter_of_Gδ

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is a countable type. -/
theorem dense_iInter_of_Gδ [Countable ι] {f : ι → Set X} (ho : ∀ s, IsGδ (f s))
    (hd : ∀ s, Dense (f s)) : Dense (⋂ s, f s) :=
  dense_sInter_of_Gδ (forall_mem_range.2 ‹_›) (countable_range _) (forall_mem_range.2 ‹_›)
set_option linter.uppercaseLean3 false in
#align dense_Inter_of_Gδ dense_iInter_of_Gδ

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is a countable set in any type. -/
theorem dense_biInter_of_Gδ {S : Set α} {f : ∀ x ∈ S, Set X} (ho : ∀ s (H : s ∈ S), IsGδ (f s H))
    (hS : S.Countable) (hd : ∀ s (H : s ∈ S), Dense (f s H)) : Dense (⋂ s ∈ S, f s ‹_›) := by
  rw [biInter_eq_iInter]
  haveI := hS.to_subtype
  exact dense_iInter_of_Gδ (fun s => ho s s.2) fun s => hd s s.2
set_option linter.uppercaseLean3 false in
#align dense_bInter_of_Gδ dense_biInter_of_Gδ

/-- Baire theorem: the intersection of two dense Gδ sets is dense. -/
theorem Dense.inter_of_Gδ {s t : Set X} (hs : IsGδ s) (ht : IsGδ t) (hsc : Dense s)
    (htc : Dense t) : Dense (s ∩ t) := by
  rw [inter_eq_iInter]
  apply dense_iInter_of_Gδ <;> simp [Bool.forall_bool, *]
set_option linter.uppercaseLean3 false in
#align dense.inter_of_Gδ Dense.inter_of_Gδ

/-- If a countable family of closed sets cover a dense `Gδ` set, then the union of their interiors
is dense. Formulated here with `⋃`. -/
theorem IsGδ.dense_iUnion_interior_of_closed [Countable ι] {s : Set X} (hs : IsGδ s) (hd : Dense s)
    {f : ι → Set X} (hc : ∀ i, IsClosed (f i)) (hU : s ⊆ ⋃ i, f i) :
    Dense (⋃ i, interior (f i)) := by
  let g i := (frontier (f i))ᶜ
  have hgo : ∀ i, IsOpen (g i) := fun i => isClosed_frontier.isOpen_compl
  have hgd : Dense (⋂ i, g i) := by
    refine dense_iInter_of_isOpen hgo fun i x => ?_
    rw [closure_compl, interior_frontier (hc _)]
    exact id
  refine (hd.inter_of_Gδ hs (.iInter_of_isOpen fun i => (hgo i)) hgd).mono ?_
  rintro x ⟨hxs, hxg⟩
  rw [mem_iInter] at hxg
  rcases mem_iUnion.1 (hU hxs) with ⟨i, hi⟩
  exact mem_iUnion.2 ⟨i, self_diff_frontier (f i) ▸ ⟨hi, hxg _⟩⟩
set_option linter.uppercaseLean3 false in
#align is_Gδ.dense_Union_interior_of_closed IsGδ.dense_iUnion_interior_of_closed

/-- If a countable family of closed sets cover a dense `Gδ` set, then the union of their interiors
is dense. Formulated here with a union over a countable set in any type. -/
theorem IsGδ.dense_biUnion_interior_of_closed {t : Set α} {s : Set X} (hs : IsGδ s) (hd : Dense s)
    (ht : t.Countable) {f : α → Set X} (hc : ∀ i ∈ t, IsClosed (f i)) (hU : s ⊆ ⋃ i ∈ t, f i) :
    Dense (⋃ i ∈ t, interior (f i)) := by
  haveI := ht.to_subtype
  simp only [biUnion_eq_iUnion, SetCoe.forall'] at *
  exact hs.dense_iUnion_interior_of_closed hd hc hU
set_option linter.uppercaseLean3 false in
#align is_Gδ.dense_bUnion_interior_of_closed IsGδ.dense_biUnion_interior_of_closed

/-- If a countable family of closed sets cover a dense `Gδ` set, then the union of their interiors
is dense. Formulated here with `⋃₀`. -/
theorem IsGδ.dense_sUnion_interior_of_closed {T : Set (Set X)} {s : Set X} (hs : IsGδ s)
    (hd : Dense s) (hc : T.Countable) (hc' : ∀ t ∈ T, IsClosed t) (hU : s ⊆ ⋃₀ T) :
    Dense (⋃ t ∈ T, interior t) :=
  hs.dense_biUnion_interior_of_closed hd hc hc' <| by rwa [← sUnion_eq_biUnion]
set_option linter.uppercaseLean3 false in
#align is_Gδ.dense_sUnion_interior_of_closed IsGδ.dense_sUnion_interior_of_closed

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with an index set which is a countable set in any type. -/
theorem dense_biUnion_interior_of_closed {S : Set α} {f : α → Set X} (hc : ∀ s ∈ S, IsClosed (f s))
    (hS : S.Countable) (hU : ⋃ s ∈ S, f s = univ) : Dense (⋃ s ∈ S, interior (f s)) :=
  IsGδ.univ.dense_biUnion_interior_of_closed dense_univ hS hc hU.ge
#align dense_bUnion_interior_of_closed dense_biUnion_interior_of_closed

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with `⋃₀`. -/
theorem dense_sUnion_interior_of_closed {S : Set (Set X)} (hc : ∀ s ∈ S, IsClosed s)
    (hS : S.Countable) (hU : ⋃₀ S = univ) : Dense (⋃ s ∈ S, interior s) :=
  IsGδ.univ.dense_sUnion_interior_of_closed dense_univ hS hc hU.ge
#align dense_sUnion_interior_of_closed dense_sUnion_interior_of_closed

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with an index set which is a countable type. -/
theorem dense_iUnion_interior_of_closed [Countable ι] {f : ι → Set X} (hc : ∀ i, IsClosed (f i))
    (hU : ⋃ i, f i = univ) : Dense (⋃ i, interior (f i)) :=
  IsGδ.univ.dense_iUnion_interior_of_closed dense_univ hc hU.ge
#align dense_Union_interior_of_closed dense_iUnion_interior_of_closed

/-- One of the most useful consequences of Baire theorem: if a countable union of closed sets
covers the space, then one of the sets has nonempty interior. -/
theorem nonempty_interior_of_iUnion_of_closed [Nonempty X] [Countable ι] {f : ι → Set X}
    (hc : ∀ i, IsClosed (f i)) (hU : ⋃ i, f i = univ) : ∃ i, (interior <| f i).Nonempty := by
  simpa using (dense_iUnion_interior_of_closed hc hU).nonempty
#align nonempty_interior_of_Union_of_closed nonempty_interior_of_iUnion_of_closed

end BaireTheorem
