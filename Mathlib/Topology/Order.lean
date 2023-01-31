/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module topology.order
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Tactic

/-!
# Ordering on topologies and (co)induced topologies

Topologies on a fixed type `α` are ordered, by reverse inclusion.
That is, for topologies `t₁` and `t₂` on `α`, we write `t₁ ≤ t₂`
if every set open in `t₂` is also open in `t₁`.
(One also calls `t₁` finer than `t₂`, and `t₂` coarser than `t₁`.)

Any function `f : α → β` induces
       `induced f : topological_space β → topological_space α`
and  `coinduced f : topological_space α → topological_space β`.
Continuity, the ordering on topologies and (co)induced topologies are
related as follows:
* The identity map (α, t₁) → (α, t₂) is continuous iff t₁ ≤ t₂.
* A map f : (α, t) → (β, u) is continuous
    iff             t ≤ induced f u   (`continuous_iff_le_induced`)
    iff coinduced f t ≤ u             (`continuous_iff_coinduced_le`).

Topologies on α form a complete lattice, with ⊥ the discrete topology
and ⊤ the indiscrete topology.

For a function f : α → β, (coinduced f, induced f) is a Galois connection
between topologies on α and topologies on β.

## Implementation notes

There is a Galois insertion between topologies on α (with the inclusion ordering)
and all collections of sets in α. The complete lattice structure on topologies
on α is defined as the reverse of the one obtained via this Galois insertion.

## Tags

finer, coarser, induced topology, coinduced topology

-/


open Function Set Filter

open Topology Filter

universe u v w

namespace TopologicalSpace

variable {α : Type u}

/-- The open sets of the least topology containing a collection of basic sets. -/
inductive GenerateOpen (g : Set (Set α)) : Set α → Prop
  | basic : ∀ s ∈ g, generate_open s
  | univ : generate_open univ
  | inter : ∀ s t, generate_open s → generate_open t → generate_open (s ∩ t)
  | sUnion : ∀ k, (∀ s ∈ k, generate_open s) → generate_open (⋃₀ k)
#align topological_space.generate_open TopologicalSpace.GenerateOpen

/-- The smallest topological space containing the collection `g` of basic sets -/
def generateFrom (g : Set (Set α)) : TopologicalSpace α
    where
  IsOpen := GenerateOpen g
  is_open_univ := GenerateOpen.univ
  is_open_inter := GenerateOpen.inter
  is_open_sUnion := GenerateOpen.sUnion
#align topological_space.generate_from TopologicalSpace.generateFrom

theorem isOpen_generateFrom_of_mem {g : Set (Set α)} {s : Set α} (hs : s ∈ g) :
    is_open[generateFrom g] s :=
  GenerateOpen.basic s hs
#align topological_space.is_open_generate_from_of_mem TopologicalSpace.isOpen_generateFrom_of_mem

theorem nhds_generateFrom {g : Set (Set α)} {a : α} :
    @nhds α (generateFrom g) a = ⨅ s ∈ { s | a ∈ s ∧ s ∈ g }, 𝓟 s :=
  by
  rw [nhds_def]
  refine' le_antisymm (binfᵢ_mono fun s ⟨as, sg⟩ => ⟨as, generate_open.basic _ sg⟩) _
  refine' le_infᵢ₂ fun s hs => _; cases' hs with ha hs
  induction hs
  case basic s hs => exact infᵢ₂_le _ ⟨ha, hs⟩
  case univ => exact le_top.trans_eq principal_univ.symm
  case inter s t hs' ht' hs ht => exact (le_inf (hs ha.1) (ht ha.2)).trans_eq inf_principal
  case sUnion S hS' hS =>
    rcases ha with ⟨t, htS, hat⟩
    exact (hS t htS hat).trans (principal_mono.2 <| subset_sUnion_of_mem htS)
#align topological_space.nhds_generate_from TopologicalSpace.nhds_generateFrom

theorem tendsto_nhds_generateFrom {β : Type _} {m : α → β} {f : Filter α} {g : Set (Set β)} {b : β}
    (h : ∀ s ∈ g, b ∈ s → m ⁻¹' s ∈ f) : Tendsto m f (@nhds β (generateFrom g) b) := by
  rw [nhds_generate_from] <;>
    exact
      tendsto_infi.2 fun s => tendsto_infi.2 fun ⟨hbs, hsg⟩ => tendsto_principal.2 <| h s hsg hbs
#align topological_space.tendsto_nhds_generate_from TopologicalSpace.tendsto_nhds_generateFrom

/-- Construct a topology on α given the filter of neighborhoods of each point of α. -/
protected def mkOfNhds (n : α → Filter α) : TopologicalSpace α
    where
  IsOpen s := ∀ a ∈ s, s ∈ n a
  is_open_univ x h := univ_mem
  is_open_inter := fun s t hs ht x ⟨hxs, hxt⟩ => inter_mem (hs x hxs) (ht x hxt)
  is_open_sUnion := fun s hs a ⟨x, hx, hxa⟩ =>
    mem_of_superset (hs x hx _ hxa) (Set.subset_unionₛ_of_mem hx)
#align topological_space.mk_of_nhds TopologicalSpace.mkOfNhds

theorem nhds_mkOfNhds (n : α → Filter α) (a : α) (h₀ : pure ≤ n)
    (h₁ : ∀ a s, s ∈ n a → ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a') :
    @nhds α (TopologicalSpace.mkOfNhds n) a = n a :=
  by
  letI := TopologicalSpace.mkOfNhds n
  refine' le_antisymm (fun s hs => _) fun s hs => _
  · have h₀ : { b | s ∈ n b } ⊆ s := fun b hb => mem_pure.1 <| h₀ b hb
    have h₁ : { b | s ∈ n b } ∈ 𝓝 a :=
      by
      refine' IsOpen.mem_nhds (fun b (hb : s ∈ n b) => _) hs
      rcases h₁ _ _ hb with ⟨t, ht, hts, h⟩
      exact mem_of_superset ht h
    exact mem_of_superset h₁ h₀
  · rcases(@mem_nhds_iff α (TopologicalSpace.mkOfNhds n) _ _).1 hs with ⟨t, hts, ht, hat⟩
    exact (n a).sets_of_superset (ht _ hat) hts
#align topological_space.nhds_mk_of_nhds TopologicalSpace.nhds_mkOfNhds

theorem nhds_mkOfNhds_single [DecidableEq α] {a₀ : α} {l : Filter α} (h : pure a₀ ≤ l) (b : α) :
    @nhds α (TopologicalSpace.mkOfNhds <| update pure a₀ l) b =
      (update pure a₀ l : α → Filter α) b :=
  by
  refine' nhds_mk_of_nhds _ _ (le_update_iff.mpr ⟨h, fun _ _ => le_rfl⟩) fun a s hs => _
  rcases eq_or_ne a a₀ with (rfl | ha)
  · refine' ⟨s, hs, subset.rfl, fun b hb => _⟩
    rcases eq_or_ne b a with (rfl | hb)
    · exact hs
    · rwa [update_noteq hb]
  · have hs' := hs
    rw [update_noteq ha] at hs⊢
    exact ⟨{a}, rfl, singleton_subset_iff.mpr hs, forall_eq.2 hs'⟩
#align topological_space.nhds_mk_of_nhds_single TopologicalSpace.nhds_mkOfNhds_single

theorem nhds_mkOfNhds_filterBasis (B : α → FilterBasis α) (a : α) (h₀ : ∀ (x), ∀ n ∈ B x, x ∈ n)
    (h₁ : ∀ (x), ∀ n ∈ B x, ∃ n₁ ∈ B x, n₁ ⊆ n ∧ ∀ x' ∈ n₁, ∃ n₂ ∈ B x', n₂ ⊆ n) :
    @nhds α (TopologicalSpace.mkOfNhds fun x => (B x).filter) a = (B a).filter :=
  by
  rw [TopologicalSpace.nhds_mkOfNhds] <;> intro x n hn <;>
    obtain ⟨m, hm₁, hm₂⟩ := (B x).mem_filter_iff.mp hn
  · exact hm₂ (h₀ _ _ hm₁)
  · obtain ⟨n₁, hn₁, hn₂, hn₃⟩ := h₁ x m hm₁
    refine'
      ⟨n₁, (B x).mem_filter_of_mem hn₁, hn₂.trans hm₂, fun x' hx' => (B x').mem_filter_iff.mp _⟩
    obtain ⟨n₂, hn₄, hn₅⟩ := hn₃ x' hx'
    exact ⟨n₂, hn₄, hn₅.trans hm₂⟩
#align topological_space.nhds_mk_of_nhds_filter_basis TopologicalSpace.nhds_mkOfNhds_filterBasis

section Lattice

/-- The ordering on topologies on the type `α`. `t ≤ s` if every set open in `s` is also open in `t`
(`t` is finer than `s`). -/
instance : PartialOrder (TopologicalSpace α) :=
  { PartialOrder.lift (fun s => OrderDual.toDual is_open[s]) fun _ _ => topologicalSpace_eq with
    le := fun s t => ∀ U, is_open[t] U → is_open[s] U }

protected theorem le_def {α} {t s : TopologicalSpace α} : t ≤ s ↔ is_open[s] ≤ is_open[t] :=
  Iff.rfl
#align topological_space.le_def TopologicalSpace.le_def

theorem le_generateFrom_iff_subset_isOpen {g : Set (Set α)} {t : TopologicalSpace α} :
    t ≤ TopologicalSpace.generateFrom g ↔ g ⊆ { s | is_open[t] s } :=
  ⟨fun ht s hs => ht _ <| GenerateOpen.basic s hs, fun hg s hs =>
    hs.recOn (fun v hv => hg hv) t.is_open_univ (fun u v _ _ => t.is_open_inter u v) fun k _ =>
      t.is_open_sUnion k⟩
#align topological_space.le_generate_from_iff_subset_is_open TopologicalSpace.le_generateFrom_iff_subset_isOpen

/-- If `s` equals the collection of open sets in the topology it generates, then `s` defines a
topology. -/
protected def mkOfClosure (s : Set (Set α)) (hs : { u | GenerateOpen s u } = s) : TopologicalSpace α
    where
  IsOpen u := u ∈ s
  is_open_univ := hs ▸ TopologicalSpace.GenerateOpen.univ
  is_open_inter := hs ▸ TopologicalSpace.GenerateOpen.inter
  is_open_sUnion := hs ▸ TopologicalSpace.GenerateOpen.sUnion
#align topological_space.mk_of_closure TopologicalSpace.mkOfClosure

theorem mkOfClosure_sets {s : Set (Set α)} {hs : { u | GenerateOpen s u } = s} :
    TopologicalSpace.mkOfClosure s hs = TopologicalSpace.generateFrom s :=
  topologicalSpace_eq hs.symm
#align topological_space.mk_of_closure_sets TopologicalSpace.mkOfClosure_sets

theorem gc_generateFrom (α) :
    GaloisConnection (fun t : TopologicalSpace α => OrderDual.toDual { s | is_open[t] s })
      (generate_from ∘ OrderDual.ofDual) :=
  fun _ _ => le_generateFrom_iff_subset_isOpen.symm
#align topological_space.gc_generate_from TopologicalSpace.gc_generateFrom

/-- The Galois coinsertion between `topological_space α` and `(set (set α))ᵒᵈ` whose lower part
  sends a topology to its collection of open subsets, and whose upper part sends a collection of
  subsets of α to the topology they generate. -/
def gciGenerateFrom (α : Type _) :
    GaloisCoinsertion (fun t : TopologicalSpace α => OrderDual.toDual { s | is_open[t] s })
      (generate_from ∘ OrderDual.ofDual)
    where
  gc := gc_generateFrom α
  u_l_le ts s hs := GenerateOpen.basic s hs
  choice g hg :=
    TopologicalSpace.mkOfClosure g
      (Subset.antisymm hg <| le_generateFrom_iff_subset_isOpen.1 <| le_rfl)
  choice_eq s hs := mkOfClosure_sets
#align topological_space.gci_generate_from TopologicalSpace.gciGenerateFrom

/-- Topologies on `α` form a complete lattice, with `⊥` the discrete topology
  and `⊤` the indiscrete topology. The infimum of a collection of topologies
  is the topology generated by all their open sets, while the supremum is the
  topology whose open sets are those sets open in every member of the collection. -/
instance : CompleteLattice (TopologicalSpace α) :=
  (gciGenerateFrom α).liftCompleteLattice

@[mono]
theorem generateFrom_anti {α} {g₁ g₂ : Set (Set α)} (h : g₁ ⊆ g₂) :
    generateFrom g₂ ≤ generateFrom g₁ :=
  (gc_generateFrom _).monotone_u h
#align topological_space.generate_from_anti TopologicalSpace.generateFrom_anti

theorem generateFrom_setOf_isOpen (t : TopologicalSpace α) :
    generateFrom { s | is_open[t] s } = t :=
  (gciGenerateFrom α).u_l_eq t
#align topological_space.generate_from_set_of_is_open TopologicalSpace.generateFrom_setOf_isOpen

theorem leftInverse_generateFrom :
    LeftInverse generateFrom fun t : TopologicalSpace α => { s | is_open[t] s } :=
  (gciGenerateFrom α).u_l_left_inverse
#align topological_space.left_inverse_generate_from TopologicalSpace.leftInverse_generateFrom

theorem generateFrom_surjective : Surjective (generateFrom : Set (Set α) → TopologicalSpace α) :=
  (gciGenerateFrom α).u_surjective
#align topological_space.generate_from_surjective TopologicalSpace.generateFrom_surjective

theorem setOf_isOpen_injective : Injective fun t : TopologicalSpace α => { s | is_open[t] s } :=
  (gciGenerateFrom α).l_injective
#align topological_space.set_of_is_open_injective TopologicalSpace.setOf_isOpen_injective

end Lattice

end TopologicalSpace

section Lattice

variable {α : Type u} {β : Type v}

theorem IsOpen.mono {α} {t₁ t₂ : TopologicalSpace α} {s : Set α} (hs : is_open[t₂] s)
    (h : t₁ ≤ t₂) : is_open[t₁] s :=
  h s hs
#align is_open.mono IsOpen.mono

theorem IsClosed.mono {α} {t₁ t₂ : TopologicalSpace α} {s : Set α} (hs : is_closed[t₂] s)
    (h : t₁ ≤ t₂) : is_closed[t₁] s :=
  (@isOpen_compl_iff α t₁ s).mp <| hs.is_open_compl.mono h
#align is_closed.mono IsClosed.mono

theorem isOpen_implies_isOpen_iff {a b : TopologicalSpace α} :
    (∀ s, is_open[a] s → is_open[b] s) ↔ b ≤ a :=
  Iff.rfl
#align is_open_implies_is_open_iff isOpen_implies_isOpen_iff

/-- The only open sets in the indiscrete topology are the empty set and the whole space. -/
theorem TopologicalSpace.isOpen_top_iff {α} (U : Set α) : is_open[⊤] U ↔ U = ∅ ∨ U = univ :=
  ⟨fun h => by
    induction' h with V h _ _ _ _ ih₁ ih₂ _ _ ih
    · cases h; · exact Or.inr rfl
    · obtain ⟨rfl | rfl, rfl | rfl⟩ := ih₁, ih₂ <;> simp
    · rw [sUnion_eq_empty, or_iff_not_imp_left]
      intro h
      push_neg  at h
      obtain ⟨U, hU, hne⟩ := h
      have := (ih U hU).resolve_left hne
      subst this
      refine' sUnion_eq_univ_iff.2 fun a => ⟨_, hU, trivial⟩,
    by
    rintro (rfl | rfl)
    exacts[@isOpen_empty _ ⊤, @isOpen_univ _ ⊤]⟩
#align topological_space.is_open_top_iff TopologicalSpace.isOpen_top_iff

/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`eq_bot] [] -/
/-- A topological space is discrete if every set is open, that is,
  its topology equals the discrete topology `⊥`. -/
class DiscreteTopology (α : Type _) [t : TopologicalSpace α] : Prop where
  eq_bot : t = ⊥
#align discrete_topology DiscreteTopology

theorem discreteTopology_bot (α : Type _) : @DiscreteTopology α ⊥ :=
  @DiscreteTopology.mk α ⊥ rfl
#align discrete_topology_bot discreteTopology_bot

@[simp]
theorem isOpen_discrete [TopologicalSpace α] [DiscreteTopology α] (s : Set α) : IsOpen s :=
  (DiscreteTopology.eq_bot α).symm ▸ trivial
#align is_open_discrete isOpen_discrete

@[simp]
theorem isClosed_discrete [TopologicalSpace α] [DiscreteTopology α] (s : Set α) : IsClosed s :=
  isOpen_compl_iff.1 <| isOpen_discrete _
#align is_closed_discrete isClosed_discrete

@[nontriviality]
theorem continuous_of_discreteTopology [TopologicalSpace α] [DiscreteTopology α]
    [TopologicalSpace β] {f : α → β} : Continuous f :=
  continuous_def.2 fun s hs => isOpen_discrete _
#align continuous_of_discrete_topology continuous_of_discreteTopology

@[simp]
theorem nhds_discrete (α : Type _) [TopologicalSpace α] [DiscreteTopology α] : @nhds α _ = pure :=
  le_antisymm (fun _ s hs => (isOpen_discrete s).mem_nhds hs) pure_le_nhds
#align nhds_discrete nhds_discrete

theorem mem_nhds_discrete [TopologicalSpace α] [DiscreteTopology α] {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ x ∈ s := by rw [nhds_discrete, mem_pure]
#align mem_nhds_discrete mem_nhds_discrete

theorem le_of_nhds_le_nhds {t₁ t₂ : TopologicalSpace α} (h : ∀ x, @nhds α t₁ x ≤ @nhds α t₂ x) :
    t₁ ≤ t₂ := by
  intro s
  rw [@isOpen_iff_mem_nhds _ t₁, @isOpen_iff_mem_nhds α t₂]
  exact fun hs a ha => h _ (hs _ ha)
#align le_of_nhds_le_nhds le_of_nhds_le_nhds

theorem eq_of_nhds_eq_nhds {t₁ t₂ : TopologicalSpace α} (h : ∀ x, @nhds α t₁ x = @nhds α t₂ x) :
    t₁ = t₂ :=
  le_antisymm (le_of_nhds_le_nhds fun x => le_of_eq <| h x)
    (le_of_nhds_le_nhds fun x => le_of_eq <| (h x).symm)
#align eq_of_nhds_eq_nhds eq_of_nhds_eq_nhds

theorem eq_bot_of_singletons_open {t : TopologicalSpace α} (h : ∀ x, is_open[t] {x}) : t = ⊥ :=
  bot_unique fun s hs => bunionᵢ_of_singleton s ▸ isOpen_bunionᵢ fun x _ => h x
#align eq_bot_of_singletons_open eq_bot_of_singletons_open

theorem forall_open_iff_discrete {X : Type _} [TopologicalSpace X] :
    (∀ s : Set X, IsOpen s) ↔ DiscreteTopology X :=
  ⟨fun h => ⟨eq_bot_of_singletons_open fun _ => h _⟩, @isOpen_discrete _ _⟩
#align forall_open_iff_discrete forall_open_iff_discrete

theorem singletons_open_iff_discrete {X : Type _} [TopologicalSpace X] :
    (∀ a : X, IsOpen ({a} : Set X)) ↔ DiscreteTopology X :=
  ⟨fun h => ⟨eq_bot_of_singletons_open h⟩, fun a _ => @isOpen_discrete _ _ a _⟩
#align singletons_open_iff_discrete singletons_open_iff_discrete

theorem discreteTopology_iff_singleton_mem_nhds [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ x : α, {x} ∈ 𝓝 x := by
  simp only [← singletons_open_iff_discrete, isOpen_iff_mem_nhds, mem_singleton_iff, forall_eq]
#align discrete_topology_iff_singleton_mem_nhds discreteTopology_iff_singleton_mem_nhds

/-- This lemma characterizes discrete topological spaces as those whose singletons are
neighbourhoods. -/
theorem discreteTopology_iff_nhds [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ x : α, 𝓝 x = pure x := by
  simp only [discreteTopology_iff_singleton_mem_nhds, ← nhds_ne_bot.le_pure_iff, le_pure_iff]
#align discrete_topology_iff_nhds discreteTopology_iff_nhds

theorem discreteTopology_iff_nhds_ne [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ x : α, 𝓝[≠] x = ⊥ := by
  simp only [discreteTopology_iff_singleton_mem_nhds, nhdsWithin, inf_principal_eq_bot, compl_compl]
#align discrete_topology_iff_nhds_ne discreteTopology_iff_nhds_ne

end Lattice

section GaloisConnection

variable {α : Type _} {β : Type _} {γ : Type _}

/-- Given `f : α → β` and a topology on `β`, the induced topology on `α` is the collection of
  sets that are preimages of some open set in `β`. This is the coarsest topology that
  makes `f` continuous. -/
def TopologicalSpace.induced {α : Type u} {β : Type v} (f : α → β) (t : TopologicalSpace β) :
    TopologicalSpace α where
  IsOpen s := ∃ s', IsOpen s' ∧ f ⁻¹' s' = s
  is_open_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  is_open_inter := by
    rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩ <;>
      exact ⟨s'₁ ∩ s'₂, hs₁.inter hs₂, preimage_inter⟩
  is_open_sUnion s h := by
    simp only [Classical.skolem] at h
    cases' h with f hf
    apply Exists.intro (⋃ (x : Set α) (h : x ∈ s), f x h)
    simp only [sUnion_eq_bUnion, preimage_Union, fun x h => (hf x h).right]; refine' ⟨_, rfl⟩
    exact
      @isOpen_unionᵢ β _ t _ fun i =>
        show IsOpen (⋃ h, f i h) from @isOpen_unionᵢ β _ t _ fun h => (hf i h).left
#align topological_space.induced TopologicalSpace.induced

theorem isOpen_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α → β} :
    is_open[t.induced f] s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s :=
  Iff.rfl
#align is_open_induced_iff isOpen_induced_iff

theorem isClosed_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α → β} :
    is_closed[t.induced f] s ↔ ∃ t, IsClosed t ∧ f ⁻¹' t = s :=
  by
  simp only [← isOpen_compl_iff, isOpen_induced_iff]
  exact compl_surjective.exists.trans (by simp only [preimage_compl, compl_inj_iff])
#align is_closed_induced_iff isClosed_induced_iff

/-- Given `f : α → β` and a topology on `α`, the coinduced topology on `β` is defined
  such that `s:set β` is open if the preimage of `s` is open. This is the finest topology that
  makes `f` continuous. -/
def TopologicalSpace.coinduced {α : Type u} {β : Type v} (f : α → β) (t : TopologicalSpace α) :
    TopologicalSpace β where
  IsOpen s := is_open[t] (f ⁻¹' s)
  is_open_univ := t.is_open_univ
  is_open_inter _ _ h₁ h₂ := h₁.inter h₂
  is_open_sUnion s h := by simpa only [preimage_sUnion] using isOpen_bunionᵢ h
#align topological_space.coinduced TopologicalSpace.coinduced

theorem isOpen_coinduced {t : TopologicalSpace α} {s : Set β} {f : α → β} :
    is_open[t.coinduced f] s ↔ IsOpen (f ⁻¹' s) :=
  Iff.rfl
#align is_open_coinduced isOpen_coinduced

theorem preimage_nhds_coinduced [TopologicalSpace α] {π : α → β} {s : Set β} {a : α}
    (hs : s ∈ @nhds β (TopologicalSpace.coinduced π ‹_›) (π a)) : π ⁻¹' s ∈ 𝓝 a :=
  by
  letI := TopologicalSpace.coinduced π ‹_›
  rcases mem_nhds_iff.mp hs with ⟨V, hVs, V_op, mem_V⟩
  exact mem_nhds_iff.mpr ⟨π ⁻¹' V, Set.preimage_mono hVs, V_op, mem_V⟩
#align preimage_nhds_coinduced preimage_nhds_coinduced

variable {t t₁ t₂ : TopologicalSpace α} {t' : TopologicalSpace β} {f : α → β} {g : β → α}

theorem Continuous.coinduced_le (h : @Continuous α β t t' f) : t.coinduced f ≤ t' := fun s hs =>
  (continuous_def.1 h s hs : _)
#align continuous.coinduced_le Continuous.coinduced_le

theorem coinduced_le_iff_le_induced {f : α → β} {tα : TopologicalSpace α}
    {tβ : TopologicalSpace β} : tα.coinduced f ≤ tβ ↔ tα ≤ tβ.induced f :=
  ⟨fun h s ⟨t, ht, hst⟩ => hst ▸ h _ ht, fun h s hs => h _ ⟨s, hs, rfl⟩⟩
#align coinduced_le_iff_le_induced coinduced_le_iff_le_induced

theorem Continuous.le_induced (h : @Continuous α β t t' f) : t ≤ t'.induced f :=
  coinduced_le_iff_le_induced.1 h.coinduced_le
#align continuous.le_induced Continuous.le_induced

theorem gc_coinduced_induced (f : α → β) :
    GaloisConnection (TopologicalSpace.coinduced f) (TopologicalSpace.induced f) := fun f g =>
  coinduced_le_iff_le_induced
#align gc_coinduced_induced gc_coinduced_induced

theorem induced_mono (h : t₁ ≤ t₂) : t₁.induced g ≤ t₂.induced g :=
  (gc_coinduced_induced g).monotone_u h
#align induced_mono induced_mono

theorem coinduced_mono (h : t₁ ≤ t₂) : t₁.coinduced f ≤ t₂.coinduced f :=
  (gc_coinduced_induced f).monotone_l h
#align coinduced_mono coinduced_mono

@[simp]
theorem induced_top : (⊤ : TopologicalSpace α).induced g = ⊤ :=
  (gc_coinduced_induced g).u_top
#align induced_top induced_top

@[simp]
theorem induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induced g :=
  (gc_coinduced_induced g).u_inf
#align induced_inf induced_inf

@[simp]
theorem induced_infᵢ {ι : Sort w} {t : ι → TopologicalSpace α} :
    (⨅ i, t i).induced g = ⨅ i, (t i).induced g :=
  (gc_coinduced_induced g).u_infi
#align induced_infi induced_infᵢ

@[simp]
theorem coinduced_bot : (⊥ : TopologicalSpace α).coinduced f = ⊥ :=
  (gc_coinduced_induced f).l_bot
#align coinduced_bot coinduced_bot

@[simp]
theorem coinduced_sup : (t₁ ⊔ t₂).coinduced f = t₁.coinduced f ⊔ t₂.coinduced f :=
  (gc_coinduced_induced f).l_sup
#align coinduced_sup coinduced_sup

@[simp]
theorem coinduced_supᵢ {ι : Sort w} {t : ι → TopologicalSpace α} :
    (⨆ i, t i).coinduced f = ⨆ i, (t i).coinduced f :=
  (gc_coinduced_induced f).l_supr
#align coinduced_supr coinduced_supᵢ

theorem induced_id [t : TopologicalSpace α] : t.induced id = t :=
  topologicalSpace_eq <|
    funext fun s => propext <| ⟨fun ⟨s', hs, h⟩ => h ▸ hs, fun hs => ⟨s, hs, rfl⟩⟩
#align induced_id induced_id

theorem induced_compose [tγ : TopologicalSpace γ] {f : α → β} {g : β → γ} :
    (tγ.induced g).induced f = tγ.induced (g ∘ f) :=
  topologicalSpace_eq <|
    funext fun s =>
      propext <|
        ⟨fun ⟨s', ⟨s, hs, h₂⟩, h₁⟩ => h₁ ▸ h₂ ▸ ⟨s, hs, rfl⟩, fun ⟨s, hs, h⟩ =>
          ⟨preimage g s, ⟨s, hs, rfl⟩, h ▸ rfl⟩⟩
#align induced_compose induced_compose

theorem induced_const [t : TopologicalSpace α] {x : α} : (t.induced fun y : β => x) = ⊤ :=
  le_antisymm le_top (@continuous_const β α ⊤ t x).le_induced
#align induced_const induced_const

theorem coinduced_id [t : TopologicalSpace α] : t.coinduced id = t :=
  topologicalSpace_eq rfl
#align coinduced_id coinduced_id

theorem coinduced_compose [tα : TopologicalSpace α] {f : α → β} {g : β → γ} :
    (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f) :=
  topologicalSpace_eq rfl
#align coinduced_compose coinduced_compose

theorem Equiv.induced_symm {α β : Type _} (e : α ≃ β) :
    TopologicalSpace.induced e.symm = TopologicalSpace.coinduced e :=
  by
  ext (t U)
  constructor
  · rintro ⟨V, hV, rfl⟩
    rwa [isOpen_coinduced, e.preimage_symm_preimage]
  · exact fun hU => ⟨e ⁻¹' U, hU, e.symm_preimage_preimage _⟩
#align equiv.induced_symm Equiv.induced_symm

theorem Equiv.coinduced_symm {α β : Type _} (e : α ≃ β) :
    TopologicalSpace.coinduced e.symm = TopologicalSpace.induced e := by
  rw [← e.symm.induced_symm, e.symm_symm]
#align equiv.coinduced_symm Equiv.coinduced_symm

end GaloisConnection

-- constructions using the complete lattice structure
section Constructions

open TopologicalSpace

variable {α : Type u} {β : Type v}

instance inhabitedTopologicalSpace {α : Type u} : Inhabited (TopologicalSpace α) :=
  ⟨⊥⟩
#align inhabited_topological_space inhabitedTopologicalSpace

instance (priority := 100) Subsingleton.uniqueTopologicalSpace [Subsingleton α] :
    Unique (TopologicalSpace α) where
  default := ⊥
  uniq t :=
    eq_bot_of_singletons_open fun x =>
      Subsingleton.set_cases (@isOpen_empty _ t) (@isOpen_univ _ t) ({x} : Set α)
#align subsingleton.unique_topological_space Subsingleton.uniqueTopologicalSpace

instance (priority := 100) Subsingleton.discreteTopology [t : TopologicalSpace α] [Subsingleton α] :
    DiscreteTopology α :=
  ⟨Unique.eq_default t⟩
#align subsingleton.discrete_topology Subsingleton.discreteTopology

instance : TopologicalSpace Empty :=
  ⊥

instance : DiscreteTopology Empty :=
  ⟨rfl⟩

instance : TopologicalSpace PEmpty :=
  ⊥

instance : DiscreteTopology PEmpty :=
  ⟨rfl⟩

instance : TopologicalSpace PUnit :=
  ⊥

instance : DiscreteTopology PUnit :=
  ⟨rfl⟩

instance : TopologicalSpace Bool :=
  ⊥

instance : DiscreteTopology Bool :=
  ⟨rfl⟩

instance : TopologicalSpace ℕ :=
  ⊥

instance : DiscreteTopology ℕ :=
  ⟨rfl⟩

instance : TopologicalSpace ℤ :=
  ⊥

instance : DiscreteTopology ℤ :=
  ⟨rfl⟩

instance {n} : TopologicalSpace (Fin n) :=
  ⊥

instance {n} : DiscreteTopology (Fin n) :=
  ⟨rfl⟩

instance sierpinskiSpace : TopologicalSpace Prop :=
  generateFrom {{True}}
#align sierpinski_space sierpinskiSpace

theorem continuous_empty_function [TopologicalSpace α] [TopologicalSpace β] [IsEmpty β]
    (f : α → β) : Continuous f :=
  letI := Function.isEmpty f
  continuous_of_discreteTopology
#align continuous_empty_function continuous_empty_function

theorem le_generateFrom {t : TopologicalSpace α} {g : Set (Set α)} (h : ∀ s ∈ g, IsOpen s) :
    t ≤ generateFrom g :=
  le_generateFrom_iff_subset_isOpen.2 h
#align le_generate_from le_generateFrom

theorem induced_generateFrom_eq {α β} {b : Set (Set β)} {f : α → β} :
    (generateFrom b).induced f = TopologicalSpace.generateFrom (preimage f '' b) :=
  le_antisymm (le_generateFrom <| ball_image_iff.2 fun s hs => ⟨s, GenerateOpen.basic _ hs, rfl⟩)
    (coinduced_le_iff_le_induced.1 <|
      le_generateFrom fun s hs => GenerateOpen.basic _ <| mem_image_of_mem _ hs)
#align induced_generate_from_eq induced_generateFrom_eq

theorem le_induced_generateFrom {α β} [t : TopologicalSpace α] {b : Set (Set β)} {f : α → β}
    (h : ∀ a : Set β, a ∈ b → IsOpen (f ⁻¹' a)) : t ≤ induced f (generateFrom b) :=
  by
  rw [induced_generateFrom_eq]
  apply le_generateFrom
  simp only [mem_image, and_imp, forall_apply_eq_imp_iff₂, exists_imp]
  exact h
#align le_induced_generate_from le_induced_generateFrom

/-- This construction is left adjoint to the operation sending a topology on `α`
  to its neighborhood filter at a fixed point `a : α`. -/
def nhdsAdjoint (a : α) (f : Filter α) : TopologicalSpace α
    where
  IsOpen s := a ∈ s → s ∈ f
  is_open_univ s := univ_mem
  is_open_inter := fun s t hs ht ⟨has, hat⟩ => inter_mem (hs has) (ht hat)
  is_open_sUnion := fun k hk ⟨u, hu, hau⟩ => mem_of_superset (hk u hu hau) (subset_unionₛ_of_mem hu)
#align nhds_adjoint nhdsAdjoint

theorem gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nhds α t a := fun f t =>
  by
  rw [le_nhds_iff]
  exact ⟨fun H s hs has => H _ has hs, fun H s has hs => H _ hs has⟩
#align gc_nhds gc_nhds

theorem nhds_mono {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ ≤ t₂) :
    @nhds α t₁ a ≤ @nhds α t₂ a :=
  (gc_nhds a).monotone_u h
#align nhds_mono nhds_mono

theorem le_iff_nhds {α : Type _} (t t' : TopologicalSpace α) :
    t ≤ t' ↔ ∀ x, @nhds α t x ≤ @nhds α t' x :=
  ⟨fun h x => nhds_mono h, le_of_nhds_le_nhds⟩
#align le_iff_nhds le_iff_nhds

theorem nhdsAdjoint_nhds {α : Type _} (a : α) (f : Filter α) :
    @nhds α (nhdsAdjoint a f) a = pure a ⊔ f :=
  by
  ext U
  rw [mem_nhds_iff]
  constructor
  · rintro ⟨t, htU, ht, hat⟩
    exact ⟨htU hat, mem_of_superset (ht hat) htU⟩
  · rintro ⟨haU, hU⟩
    exact ⟨U, subset.rfl, fun h => hU, haU⟩
#align nhds_adjoint_nhds nhdsAdjoint_nhds

theorem nhdsAdjoint_nhds_of_ne {α : Type _} (a : α) (f : Filter α) {b : α} (h : b ≠ a) :
    @nhds α (nhdsAdjoint a f) b = pure b :=
  by
  apply le_antisymm
  · intro U hU
    rw [mem_nhds_iff]
    use {b}
    simp only [and_true_iff, singleton_subset_iff, mem_singleton]
    refine' ⟨hU, fun ha => (h.symm ha).elim⟩
  · exact @pure_le_nhds α (nhdsAdjoint a f) b
#align nhds_adjoint_nhds_of_ne nhdsAdjoint_nhds_of_ne

theorem isOpen_singleton_nhdsAdjoint {α : Type _} {a b : α} (f : Filter α) (hb : b ≠ a) :
    is_open[nhdsAdjoint a f] {b} :=
  by
  rw [isOpen_singleton_iff_nhds_eq_pure]
  exact nhdsAdjoint_nhds_of_ne a f hb
#align is_open_singleton_nhds_adjoint isOpen_singleton_nhdsAdjoint

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr ≠ » a) -/
theorem le_nhdsAdjoint_iff' {α : Type _} (a : α) (f : Filter α) (t : TopologicalSpace α) :
    t ≤ nhdsAdjoint a f ↔ @nhds α t a ≤ pure a ⊔ f ∧ ∀ (b) (_ : b ≠ a), @nhds α t b = pure b :=
  by
  rw [le_iff_nhds]
  constructor
  · intro h
    constructor
    · specialize h a
      rwa [nhdsAdjoint_nhds] at h
    · intro b hb
      apply le_antisymm _ (pure_le_nhds b)
      specialize h b
      rwa [nhdsAdjoint_nhds_of_ne a f hb] at h
  · rintro ⟨h, h'⟩ b
    by_cases hb : b = a
    · rwa [hb, nhdsAdjoint_nhds]
    · simp [nhdsAdjoint_nhds_of_ne a f hb, h' b hb]
#align le_nhds_adjoint_iff' le_nhdsAdjoint_iff'

theorem le_nhdsAdjoint_iff {α : Type _} (a : α) (f : Filter α) (t : TopologicalSpace α) :
    t ≤ nhdsAdjoint a f ↔ @nhds α t a ≤ pure a ⊔ f ∧ ∀ b, b ≠ a → is_open[t] {b} :=
  by
  change _ ↔ _ ∧ ∀ b : α, b ≠ a → IsOpen {b}
  rw [le_nhdsAdjoint_iff', and_congr_right_iff]
  apply fun h => forall_congr' fun b => _
  rw [@isOpen_singleton_iff_nhds_eq_pure α t b]
#align le_nhds_adjoint_iff le_nhdsAdjoint_iff

theorem nhds_infᵢ {ι : Sort _} {t : ι → TopologicalSpace α} {a : α} :
    @nhds α (infᵢ t) a = ⨅ i, @nhds α (t i) a :=
  (gc_nhds a).u_infi
#align nhds_infi nhds_infᵢ

theorem nhds_infₛ {s : Set (TopologicalSpace α)} {a : α} :
    @nhds α (infₛ s) a = ⨅ t ∈ s, @nhds α t a :=
  (gc_nhds a).u_Inf
#align nhds_Inf nhds_infₛ

theorem nhds_inf {t₁ t₂ : TopologicalSpace α} {a : α} :
    @nhds α (t₁ ⊓ t₂) a = @nhds α t₁ a ⊓ @nhds α t₂ a :=
  (gc_nhds a).u_inf
#align nhds_inf nhds_inf

theorem nhds_top {a : α} : @nhds α ⊤ a = ⊤ :=
  (gc_nhds a).u_top
#align nhds_top nhds_top

theorem isOpen_sup {t₁ t₂ : TopologicalSpace α} {s : Set α} :
    is_open[t₁ ⊔ t₂] s ↔ is_open[t₁] s ∧ is_open[t₂] s :=
  Iff.rfl
#align is_open_sup isOpen_sup

-- mathport name: exprcont
local notation "cont" => @Continuous _ _

-- mathport name: exprtspace
local notation "tspace" => TopologicalSpace

open TopologicalSpace

variable {γ : Type _} {f : α → β} {ι : Sort _}

theorem continuous_iff_coinduced_le {t₁ : tspace α} {t₂ : tspace β} :
    cont t₁ t₂ f ↔ coinduced f t₁ ≤ t₂ :=
  continuous_def.trans Iff.rfl
#align continuous_iff_coinduced_le continuous_iff_coinduced_le

theorem continuous_iff_le_induced {t₁ : tspace α} {t₂ : tspace β} :
    cont t₁ t₂ f ↔ t₁ ≤ induced f t₂ :=
  Iff.trans continuous_iff_coinduced_le (gc_coinduced_induced f _ _)
#align continuous_iff_le_induced continuous_iff_le_induced

theorem continuous_generated_from {t : tspace α} {b : Set (Set β)} (h : ∀ s ∈ b, IsOpen (f ⁻¹' s)) :
    cont t (generateFrom b) f :=
  continuous_iff_coinduced_le.2 <| le_generateFrom h
#align continuous_generated_from continuous_generated_from

@[continuity]
theorem continuous_induced_dom {t : tspace β} : cont (induced f t) t f :=
  by
  rw [continuous_def]
  intro s h
  exact ⟨_, h, rfl⟩
#align continuous_induced_dom continuous_induced_dom

theorem continuous_induced_rng {g : γ → α} {t₂ : tspace β} {t₁ : tspace γ} :
    cont t₁ (induced f t₂) g ↔ cont t₁ t₂ (f ∘ g) := by
  simp only [continuous_iff_le_induced, induced_compose]
#align continuous_induced_rng continuous_induced_rng

theorem continuous_coinduced_rng {t : tspace α} : cont t (coinduced f t) f :=
  by
  rw [continuous_def]
  intro s h
  exact h
#align continuous_coinduced_rng continuous_coinduced_rng

theorem continuous_coinduced_dom {g : β → γ} {t₁ : tspace α} {t₂ : tspace γ} :
    cont (coinduced f t₁) t₂ g ↔ cont t₁ t₂ (g ∘ f) := by
  simp only [continuous_iff_coinduced_le, coinduced_compose]
#align continuous_coinduced_dom continuous_coinduced_dom

theorem continuous_le_dom {t₁ t₂ : tspace α} {t₃ : tspace β} (h₁ : t₂ ≤ t₁) (h₂ : cont t₁ t₃ f) :
    cont t₂ t₃ f := by
  rw [continuous_def] at h₂⊢
  intro s h
  exact h₁ _ (h₂ s h)
#align continuous_le_dom continuous_le_dom

theorem continuous_le_rng {t₁ : tspace α} {t₂ t₃ : tspace β} (h₁ : t₂ ≤ t₃) (h₂ : cont t₁ t₂ f) :
    cont t₁ t₃ f := by
  rw [continuous_def] at h₂⊢
  intro s h
  exact h₂ s (h₁ s h)
#align continuous_le_rng continuous_le_rng

theorem continuous_sup_dom {t₁ t₂ : tspace α} {t₃ : tspace β} :
    cont (t₁ ⊔ t₂) t₃ f ↔ cont t₁ t₃ f ∧ cont t₂ t₃ f := by
  simp only [continuous_iff_le_induced, sup_le_iff]
#align continuous_sup_dom continuous_sup_dom

theorem continuous_sup_rng_left {t₁ : tspace α} {t₃ t₂ : tspace β} :
    cont t₁ t₂ f → cont t₁ (t₂ ⊔ t₃) f :=
  continuous_le_rng le_sup_left
#align continuous_sup_rng_left continuous_sup_rng_left

theorem continuous_sup_rng_right {t₁ : tspace α} {t₃ t₂ : tspace β} :
    cont t₁ t₃ f → cont t₁ (t₂ ⊔ t₃) f :=
  continuous_le_rng le_sup_right
#align continuous_sup_rng_right continuous_sup_rng_right

theorem continuous_supₛ_dom {T : Set (tspace α)} {t₂ : tspace β} :
    cont (supₛ T) t₂ f ↔ ∀ t ∈ T, cont t t₂ f := by
  simp only [continuous_iff_le_induced, supₛ_le_iff]
#align continuous_Sup_dom continuous_supₛ_dom

theorem continuous_supₛ_rng {t₁ : tspace α} {t₂ : Set (tspace β)} {t : tspace β} (h₁ : t ∈ t₂)
    (hf : cont t₁ t f) : cont t₁ (supₛ t₂) f :=
  continuous_iff_coinduced_le.2 <| le_supₛ_of_le h₁ <| continuous_iff_coinduced_le.1 hf
#align continuous_Sup_rng continuous_supₛ_rng

theorem continuous_supᵢ_dom {t₁ : ι → tspace α} {t₂ : tspace β} :
    cont (supᵢ t₁) t₂ f ↔ ∀ i, cont (t₁ i) t₂ f := by
  simp only [continuous_iff_le_induced, supᵢ_le_iff]
#align continuous_supr_dom continuous_supᵢ_dom

theorem continuous_supᵢ_rng {t₁ : tspace α} {t₂ : ι → tspace β} {i : ι} (h : cont t₁ (t₂ i) f) :
    cont t₁ (supᵢ t₂) f :=
  continuous_supₛ_rng ⟨i, rfl⟩ h
#align continuous_supr_rng continuous_supᵢ_rng

theorem continuous_inf_rng {t₁ : tspace α} {t₂ t₃ : tspace β} :
    cont t₁ (t₂ ⊓ t₃) f ↔ cont t₁ t₂ f ∧ cont t₁ t₃ f := by
  simp only [continuous_iff_coinduced_le, le_inf_iff]
#align continuous_inf_rng continuous_inf_rng

theorem continuous_inf_dom_left {t₁ t₂ : tspace α} {t₃ : tspace β} :
    cont t₁ t₃ f → cont (t₁ ⊓ t₂) t₃ f :=
  continuous_le_dom inf_le_left
#align continuous_inf_dom_left continuous_inf_dom_left

theorem continuous_inf_dom_right {t₁ t₂ : tspace α} {t₃ : tspace β} :
    cont t₂ t₃ f → cont (t₁ ⊓ t₂) t₃ f :=
  continuous_le_dom inf_le_right
#align continuous_inf_dom_right continuous_inf_dom_right

theorem continuous_infₛ_dom {t₁ : Set (tspace α)} {t₂ : tspace β} {t : tspace α} (h₁ : t ∈ t₁) :
    cont t t₂ f → cont (infₛ t₁) t₂ f :=
  continuous_le_dom <| infₛ_le h₁
#align continuous_Inf_dom continuous_infₛ_dom

theorem continuous_infₛ_rng {t₁ : tspace α} {T : Set (tspace β)} :
    cont t₁ (infₛ T) f ↔ ∀ t ∈ T, cont t₁ t f := by
  simp only [continuous_iff_coinduced_le, le_infₛ_iff]
#align continuous_Inf_rng continuous_infₛ_rng

theorem continuous_infᵢ_dom {t₁ : ι → tspace α} {t₂ : tspace β} {i : ι} :
    cont (t₁ i) t₂ f → cont (infᵢ t₁) t₂ f :=
  continuous_le_dom <| infᵢ_le _ _
#align continuous_infi_dom continuous_infᵢ_dom

theorem continuous_infᵢ_rng {t₁ : tspace α} {t₂ : ι → tspace β} :
    cont t₁ (infᵢ t₂) f ↔ ∀ i, cont t₁ (t₂ i) f := by
  simp only [continuous_iff_coinduced_le, le_infᵢ_iff]
#align continuous_infi_rng continuous_infᵢ_rng

@[continuity]
theorem continuous_bot {t : tspace β} : cont ⊥ t f :=
  continuous_iff_le_induced.2 <| bot_le
#align continuous_bot continuous_bot

@[continuity]
theorem continuous_top {t : tspace α} : cont t ⊤ f :=
  continuous_iff_coinduced_le.2 <| le_top
#align continuous_top continuous_top

theorem continuous_id_iff_le {t t' : tspace α} : cont t t' id ↔ t ≤ t' :=
  @continuous_def _ _ t t' id
#align continuous_id_iff_le continuous_id_iff_le

theorem continuous_id_of_le {t t' : tspace α} (h : t ≤ t') : cont t t' id :=
  continuous_id_iff_le.2 h
#align continuous_id_of_le continuous_id_of_le

-- 𝓝 in the induced topology
theorem mem_nhds_induced [T : TopologicalSpace α] (f : β → α) (a : β) (s : Set β) :
    s ∈ @nhds β (TopologicalSpace.induced f T) a ↔ ∃ u ∈ 𝓝 (f a), f ⁻¹' u ⊆ s :=
  by
  simp only [mem_nhds_iff, isOpen_induced_iff, exists_prop, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, usub, ⟨v, openv, ueq⟩, au⟩
    exact ⟨v, ⟨v, Set.Subset.refl v, openv, by rwa [← ueq] at au⟩, by rw [ueq] <;> exact usub⟩
  rintro ⟨u, ⟨v, vsubu, openv, amem⟩, finvsub⟩
  exact ⟨f ⁻¹' v, Set.Subset.trans (Set.preimage_mono vsubu) finvsub, ⟨⟨v, openv, rfl⟩, amem⟩⟩
#align mem_nhds_induced mem_nhds_induced

theorem nhds_induced [T : TopologicalSpace α] (f : β → α) (a : β) :
    @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a)) :=
  by
  ext s
  rw [mem_nhds_induced, mem_comap]
#align nhds_induced nhds_induced

theorem induced_iff_nhds_eq [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : β → α) :
    tβ = tα.induced f ↔ ∀ b, 𝓝 b = comap f (𝓝 <| f b) :=
  ⟨fun h a => h.symm ▸ nhds_induced f a, fun h =>
    eq_of_nhds_eq_nhds fun x => by rw [h, nhds_induced]⟩
#align induced_iff_nhds_eq induced_iff_nhds_eq

theorem map_nhds_induced_of_surjective [T : TopologicalSpace α] {f : β → α} (hf : Surjective f)
    (a : β) : map f (@nhds β (TopologicalSpace.induced f T) a) = 𝓝 (f a) := by
  rw [nhds_induced, map_comap_of_surjective hf]
#align map_nhds_induced_of_surjective map_nhds_induced_of_surjective

end Constructions

section Induced

open TopologicalSpace

variable {α : Type _} {β : Type _}

variable [t : TopologicalSpace β] {f : α → β}

theorem isOpen_induced_eq {s : Set α} :
    is_open[induced f t] s ↔ s ∈ preimage f '' { s | IsOpen s } :=
  Iff.rfl
#align is_open_induced_eq isOpen_induced_eq

theorem isOpen_induced {s : Set β} (h : IsOpen s) : is_open[induced f t] (f ⁻¹' s) :=
  ⟨s, h, rfl⟩
#align is_open_induced isOpen_induced

theorem map_nhds_induced_eq (a : α) : map f (@nhds α (induced f t) a) = 𝓝[range f] f a := by
  rw [nhds_induced, Filter.map_comap, nhdsWithin]
#align map_nhds_induced_eq map_nhds_induced_eq

theorem map_nhds_induced_of_mem {a : α} (h : range f ∈ 𝓝 (f a)) :
    map f (@nhds α (induced f t) a) = 𝓝 (f a) := by rw [nhds_induced, Filter.map_comap_of_mem h]
#align map_nhds_induced_of_mem map_nhds_induced_of_mem

theorem closure_induced [t : TopologicalSpace β] {f : α → β} {a : α} {s : Set α} :
    a ∈ @closure α (TopologicalSpace.induced f t) s ↔ f a ∈ closure (f '' s) := by
  simp only [mem_closure_iff_frequently, nhds_induced, frequently_comap, mem_image, and_comm']
#align closure_induced closure_induced

theorem isClosed_induced_iff' [t : TopologicalSpace β] {f : α → β} {s : Set α} :
    is_closed[t.induced f] s ↔ ∀ a, f a ∈ closure (f '' s) → a ∈ s := by
  simp only [← closure_subset_iff_isClosed, subset_def, closure_induced]
#align is_closed_induced_iff' isClosed_induced_iff'

end Induced

section Sierpinski

variable {α : Type _} [TopologicalSpace α]

@[simp]
theorem isOpen_singleton_true : IsOpen ({True} : Set Prop) :=
  TopologicalSpace.GenerateOpen.basic _ (mem_singleton _)
#align is_open_singleton_true isOpen_singleton_true

@[simp]
theorem nhds_true : 𝓝 True = pure True :=
  le_antisymm (le_pure_iff.2 <| isOpen_singleton_true.mem_nhds <| mem_singleton _) (pure_le_nhds _)
#align nhds_true nhds_true

@[simp]
theorem nhds_false : 𝓝 False = ⊤ :=
  TopologicalSpace.nhds_generateFrom.trans <| by simp [@and_comm (_ ∈ _)]
#align nhds_false nhds_false

theorem continuous_Prop {p : α → Prop} : Continuous p ↔ IsOpen { x | p x } :=
  ⟨fun h : Continuous p =>
    by
    have : IsOpen (p ⁻¹' {True}) := isOpen_singleton_true.Preimage h
    simpa [preimage, eq_true_iff] using this, fun h : IsOpen { x | p x } =>
    continuous_generated_from fun s (hs : s = {True}) => by simp [hs, preimage, eq_true_iff, h]⟩
#align continuous_Prop continuous_Prop

theorem isOpen_iff_continuous_mem {s : Set α} : IsOpen s ↔ Continuous fun x => x ∈ s :=
  continuous_Prop.symm
#align is_open_iff_continuous_mem isOpen_iff_continuous_mem

end Sierpinski

section infᵢ

variable {α : Type u} {ι : Sort v}

theorem generateFrom_union (a₁ a₂ : Set (Set α)) :
    TopologicalSpace.generateFrom (a₁ ∪ a₂) =
      TopologicalSpace.generateFrom a₁ ⊓ TopologicalSpace.generateFrom a₂ :=
  (TopologicalSpace.gc_generateFrom α).u_inf
#align generate_from_union generateFrom_union

theorem setOf_isOpen_sup (t₁ t₂ : TopologicalSpace α) :
    { s | is_open[t₁ ⊔ t₂] s } = { s | is_open[t₁] s } ∩ { s | is_open[t₂] s } :=
  rfl
#align set_of_is_open_sup setOf_isOpen_sup

theorem generateFrom_unionᵢ {f : ι → Set (Set α)} :
    TopologicalSpace.generateFrom (⋃ i, f i) = ⨅ i, TopologicalSpace.generateFrom (f i) :=
  (TopologicalSpace.gc_generateFrom α).u_infi
#align generate_from_Union generateFrom_unionᵢ

theorem setOf_isOpen_supᵢ {t : ι → TopologicalSpace α} :
    { s | is_open[⨆ i, t i] s } = ⋂ i, { s | is_open[t i] s } :=
  (TopologicalSpace.gc_generateFrom α).l_supr
#align set_of_is_open_supr setOf_isOpen_supᵢ

theorem generateFrom_unionₛ {S : Set (Set (Set α))} :
    TopologicalSpace.generateFrom (⋃₀ S) = ⨅ s ∈ S, TopologicalSpace.generateFrom s :=
  (TopologicalSpace.gc_generateFrom α).u_Inf
#align generate_from_sUnion generateFrom_unionₛ

theorem setOf_isOpen_supₛ {T : Set (TopologicalSpace α)} :
    { s | is_open[supₛ T] s } = ⋂ t ∈ T, { s | is_open[t] s } :=
  (TopologicalSpace.gc_generateFrom α).l_Sup
#align set_of_is_open_Sup setOf_isOpen_supₛ

theorem generateFrom_union_isOpen (a b : TopologicalSpace α) :
    TopologicalSpace.generateFrom ({ s | is_open[a] s } ∪ { s | is_open[b] s }) = a ⊓ b :=
  (TopologicalSpace.gciGenerateFrom α).u_inf_l a b
#align generate_from_union_is_open generateFrom_union_isOpen

theorem generateFrom_unionᵢ_isOpen (f : ι → TopologicalSpace α) :
    TopologicalSpace.generateFrom (⋃ i, { s | is_open[f i] s }) = ⨅ i, f i :=
  (TopologicalSpace.gciGenerateFrom α).u_infi_l f
#align generate_from_Union_is_open generateFrom_unionᵢ_isOpen

theorem generateFrom_inter (a b : TopologicalSpace α) :
    TopologicalSpace.generateFrom ({ s | is_open[a] s } ∩ { s | is_open[b] s }) = a ⊔ b :=
  (TopologicalSpace.gciGenerateFrom α).u_sup_l a b
#align generate_from_inter generateFrom_inter

theorem generateFrom_interᵢ (f : ι → TopologicalSpace α) :
    TopologicalSpace.generateFrom (⋂ i, { s | is_open[f i] s }) = ⨆ i, f i :=
  (TopologicalSpace.gciGenerateFrom α).u_supr_l f
#align generate_from_Inter generateFrom_interᵢ

theorem generateFrom_interᵢ_of_generateFrom_eq_self (f : ι → Set (Set α))
    (hf : ∀ i, { s | is_open[TopologicalSpace.generateFrom (f i)] s } = f i) :
    TopologicalSpace.generateFrom (⋂ i, f i) = ⨆ i, TopologicalSpace.generateFrom (f i) :=
  (TopologicalSpace.gciGenerateFrom α).u_supr_of_lu_eq_self f hf
#align generate_from_Inter_of_generate_from_eq_self generateFrom_interᵢ_of_generateFrom_eq_self

variable {t : ι → TopologicalSpace α}

theorem isOpen_supᵢ_iff {s : Set α} : is_open[⨆ i, t i] s ↔ ∀ i, is_open[t i] s :=
  show s ∈ setOf is_open[supᵢ t] ↔ s ∈ { x : Set α | ∀ i : ι, is_open[t i] x } by
    simp [setOf_isOpen_supᵢ]
#align is_open_supr_iff isOpen_supᵢ_iff

theorem isClosed_supᵢ_iff {s : Set α} : is_closed[⨆ i, t i] s ↔ ∀ i, is_closed[t i] s := by
  simp [← isOpen_compl_iff, isOpen_supᵢ_iff]
#align is_closed_supr_iff isClosed_supᵢ_iff

end infᵢ

