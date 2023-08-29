/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.Separation
import Mathlib.Order.Filter.CountableInter

#align_import topology.G_delta from "leanprover-community/mathlib"@"b9e46fe101fc897fb2e7edaf0bf1f09ea49eb81a"

/-!
# `Gδ` sets

In this file we define `Gδ` sets and prove their basic properties.

## Main definitions

* `IsGδ`: a set `s` is a `Gδ` set if it can be represented as an intersection
  of countably many open sets;

* `residual`: the σ-filter of residual sets. A set `s` is called *residual* if it includes a
  countable intersection of dense open sets.

## Main results

We prove that finite or countable intersections of Gδ sets is a Gδ set. We also prove that the
continuity set of a function from a topological space to an (e)metric space is a Gδ set.

## Tags

Gδ set, residual set
-/


noncomputable section

open Topology TopologicalSpace Filter Encodable Set

variable {α β γ ι : Type*}

set_option linter.uppercaseLean3 false

section IsGδ

variable [TopologicalSpace α]

/-- A Gδ set is a countable intersection of open sets. -/
def IsGδ (s : Set α) : Prop :=
  ∃ T : Set (Set α), (∀ t ∈ T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T
#align is_Gδ IsGδ

/-- An open set is a Gδ set. -/
theorem IsOpen.isGδ {s : Set α} (h : IsOpen s) : IsGδ s :=
  ⟨{s}, by simp [h], countable_singleton _, (Set.sInter_singleton _).symm⟩
           -- 🎉 no goals
#align is_open.is_Gδ IsOpen.isGδ

@[simp]
theorem isGδ_empty : IsGδ (∅ : Set α) :=
  isOpen_empty.isGδ
#align is_Gδ_empty isGδ_empty

@[simp]
theorem isGδ_univ : IsGδ (univ : Set α) :=
  isOpen_univ.isGδ
#align is_Gδ_univ isGδ_univ

theorem isGδ_biInter_of_open {I : Set ι} (hI : I.Countable) {f : ι → Set α}
    (hf : ∀ i ∈ I, IsOpen (f i)) : IsGδ (⋂ i ∈ I, f i) :=
  ⟨f '' I, by rwa [ball_image_iff], hI.image _, by rw [sInter_image]⟩
              -- 🎉 no goals
                                                   -- 🎉 no goals
#align is_Gδ_bInter_of_open isGδ_biInter_of_open

-- porting note: TODO: generalize to `Sort*` + `Countable _`
theorem isGδ_iInter_of_open [Encodable ι] {f : ι → Set α} (hf : ∀ i, IsOpen (f i)) :
    IsGδ (⋂ i, f i) :=
  ⟨range f, by rwa [forall_range_iff], countable_range _, by rw [sInter_range]⟩
               -- 🎉 no goals
                                                             -- 🎉 no goals
#align is_Gδ_Inter_of_open isGδ_iInter_of_open

-- porting note: TODO: generalize to `Sort*` + `Countable _`
/-- The intersection of an encodable family of Gδ sets is a Gδ set. -/
theorem isGδ_iInter [Encodable ι] {s : ι → Set α} (hs : ∀ i, IsGδ (s i)) : IsGδ (⋂ i, s i) := by
  choose T hTo hTc hTs using hs
  -- ⊢ IsGδ (⋂ (i : ι), s i)
  obtain rfl : s = fun i => ⋂₀ T i := funext hTs
  -- ⊢ IsGδ (⋂ (i : ι), (fun i => ⋂₀ T i) i)
  refine' ⟨⋃ i, T i, _, countable_iUnion hTc, (sInter_iUnion _).symm⟩
  -- ⊢ ∀ (t : Set α), t ∈ ⋃ (i : ι), T i → IsOpen t
  simpa [@forall_swap ι] using hTo
  -- 🎉 no goals
#align is_Gδ_Inter isGδ_iInter

theorem isGδ_biInter {s : Set ι} (hs : s.Countable) {t : ∀ i ∈ s, Set α}
    (ht : ∀ (i) (hi : i ∈ s), IsGδ (t i hi)) : IsGδ (⋂ i ∈ s, t i ‹_›) := by
  rw [biInter_eq_iInter]
  -- ⊢ IsGδ (⋂ (x : ↑s), t ↑x (_ : ↑x ∈ s))
  haveI := hs.toEncodable
  -- ⊢ IsGδ (⋂ (x : ↑s), t ↑x (_ : ↑x ∈ s))
  exact isGδ_iInter fun x => ht x x.2
  -- 🎉 no goals
#align is_Gδ_bInter isGδ_biInter

/-- A countable intersection of Gδ sets is a Gδ set. -/
theorem isGδ_sInter {S : Set (Set α)} (h : ∀ s ∈ S, IsGδ s) (hS : S.Countable) : IsGδ (⋂₀ S) := by
  simpa only [sInter_eq_biInter] using isGδ_biInter hS h
  -- 🎉 no goals
#align is_Gδ_sInter isGδ_sInter

theorem IsGδ.inter {s t : Set α} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∩ t) := by
  rw [inter_eq_iInter]
  -- ⊢ IsGδ (⋂ (b : Bool), bif b then s else t)
  exact isGδ_iInter (Bool.forall_bool.2 ⟨ht, hs⟩)
  -- 🎉 no goals
#align is_Gδ.inter IsGδ.inter

/-- The union of two Gδ sets is a Gδ set. -/
theorem IsGδ.union {s t : Set α} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∪ t) := by
  rcases hs with ⟨S, Sopen, Scount, rfl⟩
  -- ⊢ IsGδ (⋂₀ S ∪ t)
  rcases ht with ⟨T, Topen, Tcount, rfl⟩
  -- ⊢ IsGδ (⋂₀ S ∪ ⋂₀ T)
  rw [sInter_union_sInter]
  -- ⊢ IsGδ (⋂ (p : Set α × Set α) (_ : p ∈ S ×ˢ T), p.fst ∪ p.snd)
  apply isGδ_biInter_of_open (Scount.prod Tcount)
  -- ⊢ ∀ (i : Set α × Set α), i ∈ S ×ˢ T → IsOpen (i.fst ∪ i.snd)
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  -- ⊢ IsOpen ((a, b).fst ∪ (a, b).snd)
  exact (Sopen a ha).union (Topen b hb)
  -- 🎉 no goals
#align is_Gδ.union IsGδ.union

-- porting note: TODO: add `iUnion` and `sUnion` versions
/-- The union of finitely many Gδ sets is a Gδ set. -/
theorem isGδ_biUnion {s : Set ι} (hs : s.Finite) {f : ι → Set α} (h : ∀ i ∈ s, IsGδ (f i)) :
    IsGδ (⋃ i ∈ s, f i) := by
  refine' Finite.induction_on hs (by simp) _ h
  -- ⊢ ∀ {a : ι} {s : Set ι}, ¬a ∈ s → Set.Finite s → ((∀ (i : ι), i ∈ s → IsGδ (f  …
  simp only [ball_insert_iff, biUnion_insert]
  -- ⊢ ∀ {a : ι} {s : Set ι}, ¬a ∈ s → Set.Finite s → ((∀ (i : ι), i ∈ s → IsGδ (f  …
  exact fun _ _ ihs H => H.1.union (ihs H.2)
  -- 🎉 no goals
#align is_Gδ_bUnion isGδ_biUnion

-- Porting note: Did not recognize notation 𝓤 α, needed to replace with uniformity α
theorem IsClosed.isGδ {α} [UniformSpace α] [IsCountablyGenerated (uniformity α)] {s : Set α}
    (hs : IsClosed s) : IsGδ s := by
  rcases(@uniformity_hasBasis_open α _).exists_antitone_subbasis with ⟨U, hUo, hU, -⟩
  -- ⊢ IsGδ s
  rw [← hs.closure_eq, ← hU.biInter_biUnion_ball]
  -- ⊢ IsGδ (⋂ (i : ℕ) (_ : True), ⋃ (x : α) (_ : x ∈ s), UniformSpace.ball x (id ( …
  refine' isGδ_biInter (to_countable _) fun n _ => IsOpen.isGδ _
  -- ⊢ IsOpen (⋃ (x : α) (_ : x ∈ s), UniformSpace.ball x (id (U n)))
  exact isOpen_biUnion fun x _ => UniformSpace.isOpen_ball _ (hUo _).2
  -- 🎉 no goals
#align is_closed.is_Gδ IsClosed.isGδ

section T1Space

variable [T1Space α]

theorem isGδ_compl_singleton (a : α) : IsGδ ({a}ᶜ : Set α) :=
  isOpen_compl_singleton.isGδ
#align is_Gδ_compl_singleton isGδ_compl_singleton

theorem Set.Countable.isGδ_compl {s : Set α} (hs : s.Countable) : IsGδ sᶜ := by
  rw [← biUnion_of_singleton s, compl_iUnion₂]
  -- ⊢ IsGδ (⋂ (i : α) (_ : i ∈ s), {i}ᶜ)
  exact isGδ_biInter hs fun x _ => isGδ_compl_singleton x
  -- 🎉 no goals
#align set.countable.is_Gδ_compl Set.Countable.isGδ_compl

theorem Set.Finite.isGδ_compl {s : Set α} (hs : s.Finite) : IsGδ sᶜ :=
  hs.countable.isGδ_compl
#align set.finite.is_Gδ_compl Set.Finite.isGδ_compl

theorem Set.Subsingleton.isGδ_compl {s : Set α} (hs : s.Subsingleton) : IsGδ sᶜ :=
  hs.finite.isGδ_compl
#align set.subsingleton.is_Gδ_compl Set.Subsingleton.isGδ_compl

theorem Finset.isGδ_compl (s : Finset α) : IsGδ (sᶜ : Set α) :=
  s.finite_toSet.isGδ_compl
#align finset.is_Gδ_compl Finset.isGδ_compl

variable [FirstCountableTopology α]

theorem isGδ_singleton (a : α) : IsGδ ({a} : Set α) := by
  rcases (nhds_basis_opens a).exists_antitone_subbasis with ⟨U, hU, h_basis⟩
  -- ⊢ IsGδ {a}
  rw [← biInter_basis_nhds h_basis.toHasBasis]
  -- ⊢ IsGδ (⋂ (i : ℕ) (_ : True), U i)
  exact isGδ_biInter (to_countable _) fun n _ => (hU n).2.isGδ
  -- 🎉 no goals
#align is_Gδ_singleton isGδ_singleton

theorem Set.Finite.isGδ {s : Set α} (hs : s.Finite) : IsGδ s :=
  Finite.induction_on hs isGδ_empty fun _ _ hs => (isGδ_singleton _).union hs
#align set.finite.is_Gδ Set.Finite.isGδ

end T1Space

end IsGδ

section ContinuousAt

variable [TopologicalSpace α]

/-- The set of points where a function is continuous is a Gδ set. -/
theorem isGδ_setOf_continuousAt [UniformSpace β] [IsCountablyGenerated (uniformity β)] (f : α → β) :
    IsGδ { x | ContinuousAt f x } := by
  obtain ⟨U, _, hU⟩ := (@uniformity_hasBasis_open_symmetric β _).exists_antitone_subbasis
  -- ⊢ IsGδ {x | ContinuousAt f x}
  simp only [Uniform.continuousAt_iff_prod, nhds_prod_eq]
  -- ⊢ IsGδ {x | Tendsto (fun x => (f x.fst, f x.snd)) (𝓝 x ×ˢ 𝓝 x) (uniformity β)}
  simp only [(nhds_basis_opens _).prod_self.tendsto_iff hU.toHasBasis, forall_prop_of_true,
    setOf_forall, id]
  refine' isGδ_iInter fun k => IsOpen.isGδ <| isOpen_iff_mem_nhds.2 fun x => _
  -- ⊢ x ∈ {x | ∃ ia, (x ∈ ia ∧ IsOpen ia) ∧ ∀ (x : α × α), x ∈ ia ×ˢ ia → (f x.fst …
  rintro ⟨s, ⟨hsx, hso⟩, hsU⟩
  -- ⊢ {x | ∃ ia, (x ∈ ia ∧ IsOpen ia) ∧ ∀ (x : α × α), x ∈ ia ×ˢ ia → (f x.fst, f  …
  filter_upwards [IsOpen.mem_nhds hso hsx]with _ hy using⟨s, ⟨hy, hso⟩, hsU⟩
  -- 🎉 no goals
#align is_Gδ_set_of_continuous_at isGδ_setOf_continuousAt

end ContinuousAt

section residual

variable [TopologicalSpace α]

/-- A set `s` is called *residual* if it includes a countable intersection of dense open sets. -/
def residual (α : Type*) [TopologicalSpace α] : Filter α :=
  Filter.countableGenerate { t | IsOpen t ∧ Dense t }
#align residual residual

instance countableInterFilter_residual : CountableInterFilter (residual α) := by
  rw [residual]; infer_instance
  -- ⊢ CountableInterFilter (countableGenerate {t | IsOpen t ∧ Dense t})
                 -- 🎉 no goals
#align countable_Inter_filter_residual countableInterFilter_residual

/-- Dense open sets are residual. -/
theorem residual_of_dense_open {s : Set α} (ho : IsOpen s) (hd : Dense s) : s ∈ residual α :=
  CountableGenerateSets.basic ⟨ho, hd⟩
#align residual_of_dense_open residual_of_dense_open

/-- Dense Gδ sets are residual. -/
theorem residual_of_dense_Gδ {s : Set α} (ho : IsGδ s) (hd : Dense s) : s ∈ residual α := by
  rcases ho with ⟨T, To, Tct, rfl⟩
  -- ⊢ ⋂₀ T ∈ residual α
  exact
    (countable_sInter_mem Tct).mpr fun t tT =>
      residual_of_dense_open (To t tT) (hd.mono (sInter_subset_of_mem tT))
#align residual_of_dense_Gδ residual_of_dense_Gδ

/-- A set is residual iff it includes a countable intersection of dense open sets. -/
theorem mem_residual_iff {s : Set α} :
    s ∈ residual α ↔
      ∃ S : Set (Set α), (∀ t ∈ S, IsOpen t) ∧ (∀ t ∈ S, Dense t) ∧ S.Countable ∧ ⋂₀ S ⊆ s :=
  mem_countableGenerate_iff.trans <| by simp_rw [subset_def, mem_setOf, forall_and, and_assoc]
                                        -- 🎉 no goals
#align mem_residual_iff mem_residual_iff

end residual
