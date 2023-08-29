/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Topology.Basic

#align_import topology.order from "leanprover-community/mathlib"@"bcfa726826abd57587355b4b5b7e78ad6527b7e4"

/-!
# Ordering on topologies and (co)induced topologies

Topologies on a fixed type `α` are ordered, by reverse inclusion.  That is, for topologies `t₁` and
`t₂` on `α`, we write `t₁ ≤ t₂` if every set open in `t₂` is also open in `t₁`.  (One also calls
`t₁` *finer* than `t₂`, and `t₂` *coarser* than `t₁`.)

Any function `f : α → β` induces

* `TopologicalSpace.induced f : TopologicalSpace β → TopologicalSpace α`;
* `TopologicalSpace.coinduced f : TopologicalSpace α → TopologicalSpace β`.

Continuity, the ordering on topologies and (co)induced topologies are related as follows:

* The identity map `(α, t₁) → (α, t₂)` is continuous iff `t₁ ≤ t₂`.
* A map `f : (α, t) → (β, u)` is continuous
  * iff `t ≤ TopologicalSpace.induced f u` (`continuous_iff_le_induced`)
  * iff `TopologicalSpace.coinduced f t ≤ u` (`continuous_iff_coinduced_le`).

Topologies on `α` form a complete lattice, with `⊥` the discrete topology and `⊤` the indiscrete
topology.

For a function `f : α → β`, `(TopologicalSpace.coinduced f, TopologicalSpace.induced f)` is a Galois
connection between topologies on `α` and topologies on `β`.

## Implementation notes

There is a Galois insertion between topologies on `α` (with the inclusion ordering) and all
collections of sets in `α`. The complete lattice structure on topologies on `α` is defined as the
reverse of the one obtained via this Galois insertion. More precisely, we use the corresponding
Galois coinsertion between topologies on `α` (with the reversed inclusion ordering) and collections
of sets in `α` (with the reversed inclusion ordering).

## Tags

finer, coarser, induced topology, coinduced topology
-/

set_option autoImplicit true


open Function Set Filter Topology

universe u v w

namespace TopologicalSpace

variable {α : Type u}

/-- The open sets of the least topology containing a collection of basic sets. -/
inductive GenerateOpen (g : Set (Set α)) : Set α → Prop
  | basic : ∀ s ∈ g, GenerateOpen g s
  | univ : GenerateOpen g univ
  | inter : ∀ s t, GenerateOpen g s → GenerateOpen g t → GenerateOpen g (s ∩ t)
  | sUnion : ∀ S : Set (Set α), (∀ s ∈ S, GenerateOpen g s) → GenerateOpen g (⋃₀ S)
#align topological_space.generate_open TopologicalSpace.GenerateOpen

/-- The smallest topological space containing the collection `g` of basic sets -/
def generateFrom (g : Set (Set α)) : TopologicalSpace α where
  IsOpen := GenerateOpen g
  isOpen_univ := GenerateOpen.univ
  isOpen_inter := GenerateOpen.inter
  isOpen_sUnion := GenerateOpen.sUnion
#align topological_space.generate_from TopologicalSpace.generateFrom

theorem isOpen_generateFrom_of_mem {g : Set (Set α)} {s : Set α} (hs : s ∈ g) :
    IsOpen[generateFrom g] s :=
  GenerateOpen.basic s hs
#align topological_space.is_open_generate_from_of_mem TopologicalSpace.isOpen_generateFrom_of_mem

theorem nhds_generateFrom {g : Set (Set α)} {a : α} :
    @nhds α (generateFrom g) a = ⨅ s ∈ { s | a ∈ s ∧ s ∈ g }, 𝓟 s := by
  letI := generateFrom g
  -- ⊢ 𝓝 a = ⨅ (s : Set α) (_ : s ∈ {s | a ∈ s ∧ s ∈ g}), 𝓟 s
  rw [nhds_def]
  -- ⊢ ⨅ (s : Set α) (_ : s ∈ {s | a ∈ s ∧ IsOpen s}), 𝓟 s = ⨅ (s : Set α) (_ : s ∈ …
  refine le_antisymm (biInf_mono fun s ⟨as, sg⟩ => ⟨as, .basic _ sg⟩) ?_
  -- ⊢ ⨅ (s : Set α) (_ : s ∈ {s | a ∈ s ∧ s ∈ g}), 𝓟 s ≤ ⨅ (s : Set α) (_ : s ∈ {s …
  refine le_iInf₂ fun s ⟨ha, hs⟩ => ?_; clear ‹s ∈ { s | a ∈ s ∧ IsOpen s }›
  -- ⊢ ⨅ (s : Set α) (_ : s ∈ {s | a ∈ s ∧ s ∈ g}), 𝓟 s ≤ 𝓟 s
                                        -- ⊢ ⨅ (s : Set α) (_ : s ∈ {s | a ∈ s ∧ s ∈ g}), 𝓟 s ≤ 𝓟 s
  induction hs with
  | basic _ hs => exact iInf₂_le _ ⟨ha, hs⟩
  | univ => exact le_top.trans_eq principal_univ.symm
  | inter _ _ _ _ hs ht => exact (le_inf (hs ha.1) (ht ha.2)).trans_eq inf_principal
  | sUnion _ _ hS =>
    let ⟨t, htS, hat⟩ := ha
    exact (hS t htS hat).trans (principal_mono.2 <| subset_sUnion_of_mem htS)
#align topological_space.nhds_generate_from TopologicalSpace.nhds_generateFrom

theorem tendsto_nhds_generateFrom {β : Type*} {m : α → β} {f : Filter α} {g : Set (Set β)} {b : β}
    (h : ∀ s ∈ g, b ∈ s → m ⁻¹' s ∈ f) : Tendsto m f (@nhds β (generateFrom g) b) := by
  rw [nhds_generateFrom]
  -- ⊢ Tendsto m f (⨅ (s : Set β) (_ : s ∈ {s | b ∈ s ∧ s ∈ g}), 𝓟 s)
  exact tendsto_iInf.2 fun s => tendsto_iInf.2 fun ⟨hbs, hsg⟩ => tendsto_principal.2 <| h s hsg hbs
  -- 🎉 no goals
#align topological_space.tendsto_nhds_generate_from TopologicalSpace.tendsto_nhds_generateFrom

/-- Construct a topology on α given the filter of neighborhoods of each point of α. -/
protected def mkOfNhds (n : α → Filter α) : TopologicalSpace α where
  IsOpen s := ∀ a ∈ s, s ∈ n a
  isOpen_univ _ _ := univ_mem
  isOpen_inter := fun _s _t hs ht x ⟨hxs, hxt⟩ => inter_mem (hs x hxs) (ht x hxt)
  isOpen_sUnion := fun _s hs _a ⟨x, hx, hxa⟩ =>
    mem_of_superset (hs x hx _ hxa) (subset_sUnion_of_mem hx)
#align topological_space.mk_of_nhds TopologicalSpace.mkOfNhds

theorem nhds_mkOfNhds (n : α → Filter α) (a : α) (h₀ : pure ≤ n)
    (h₁ : ∀ a s, s ∈ n a → ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a') :
    @nhds α (TopologicalSpace.mkOfNhds n) a = n a := by
  letI := TopologicalSpace.mkOfNhds n
  -- ⊢ 𝓝 a = n a
  apply le_antisymm <;> intros s hs
  -- ⊢ 𝓝 a ≤ n a
                        -- ⊢ s ∈ 𝓝 a
                        -- ⊢ s ∈ n a
  · have h₀ : { b | s ∈ n b } ⊆ s := fun b hb => mem_pure.1 <| h₀ b hb
    -- ⊢ s ∈ 𝓝 a
    have h₁ : { b | s ∈ n b } ∈ 𝓝 a := by
      refine' IsOpen.mem_nhds (fun b (hb : s ∈ n b) => _) hs
      rcases h₁ _ _ hb with ⟨t, ht, -, h⟩
      exact mem_of_superset ht h
    exact mem_of_superset h₁ h₀
    -- 🎉 no goals
  · rcases mem_nhds_iff.1 hs with ⟨t, hts, ht, hat⟩
    -- ⊢ s ∈ n a
    exact (n a).sets_of_superset (ht _ hat) hts
    -- 🎉 no goals
#align topological_space.nhds_mk_of_nhds TopologicalSpace.nhds_mkOfNhds

theorem nhds_mkOfNhds_single [DecidableEq α] {a₀ : α} {l : Filter α} (h : pure a₀ ≤ l) (b : α) :
    @nhds α (TopologicalSpace.mkOfNhds (update pure a₀ l)) b =
      (update pure a₀ l : α → Filter α) b := by
  refine' nhds_mkOfNhds _ _ (le_update_iff.mpr ⟨h, fun _ _ => le_rfl⟩) fun a s hs => _
  -- ⊢ ∃ t, t ∈ update pure a₀ l a ∧ t ⊆ s ∧ ∀ (a' : α), a' ∈ t → s ∈ update pure a …
  rcases eq_or_ne a a₀ with (rfl | ha)
  -- ⊢ ∃ t, t ∈ update pure a l a ∧ t ⊆ s ∧ ∀ (a' : α), a' ∈ t → s ∈ update pure a  …
  · refine' ⟨s, hs, Subset.rfl, fun b hb => _⟩
    -- ⊢ s ∈ update pure a l b
    rcases eq_or_ne b a with (rfl | hb)
    -- ⊢ s ∈ update pure b l b
    · exact hs
      -- 🎉 no goals
    · rwa [update_noteq hb]
      -- 🎉 no goals
  · have hs' := hs
    -- ⊢ ∃ t, t ∈ update pure a₀ l a ∧ t ⊆ s ∧ ∀ (a' : α), a' ∈ t → s ∈ update pure a …
    rw [update_noteq ha] at hs ⊢
    -- ⊢ ∃ t, t ∈ pure a ∧ t ⊆ s ∧ ∀ (a' : α), a' ∈ t → s ∈ update pure a₀ l a'
    exact ⟨{a}, rfl, singleton_subset_iff.mpr hs, forall_eq.2 hs'⟩
    -- 🎉 no goals
#align topological_space.nhds_mk_of_nhds_single TopologicalSpace.nhds_mkOfNhds_single

theorem nhds_mkOfNhds_filterBasis (B : α → FilterBasis α) (a : α) (h₀ : ∀ (x), ∀ n ∈ B x, x ∈ n)
    (h₁ : ∀ (x), ∀ n ∈ B x, ∃ n₁ ∈ B x, n₁ ⊆ n ∧ ∀ x' ∈ n₁, ∃ n₂ ∈ B x', n₂ ⊆ n) :
    @nhds α (TopologicalSpace.mkOfNhds fun x => (B x).filter) a = (B a).filter := by
  rw [TopologicalSpace.nhds_mkOfNhds] <;> intro x n hn <;>
  -- ⊢ pure ≤ fun x => FilterBasis.filter (B x)
                                          -- ⊢ n ∈ pure x
                                          -- ⊢ ∃ t, t ∈ FilterBasis.filter (B x) ∧ t ⊆ n ∧ ∀ (a' : α), a' ∈ t → n ∈ FilterB …
    obtain ⟨m, hm₁, hm₂⟩ := (B x).mem_filter_iff.mp hn
    -- ⊢ n ∈ pure x
    -- ⊢ ∃ t, t ∈ FilterBasis.filter (B x) ∧ t ⊆ n ∧ ∀ (a' : α), a' ∈ t → n ∈ FilterB …
  · exact hm₂ (h₀ _ _ hm₁)
    -- 🎉 no goals
  · obtain ⟨n₁, hn₁, hn₂, hn₃⟩ := h₁ x m hm₁
    -- ⊢ ∃ t, t ∈ FilterBasis.filter (B x) ∧ t ⊆ n ∧ ∀ (a' : α), a' ∈ t → n ∈ FilterB …
    refine'
      ⟨n₁, (B x).mem_filter_of_mem hn₁, hn₂.trans hm₂, fun x' hx' => (B x').mem_filter_iff.mp _⟩
    obtain ⟨n₂, hn₄, hn₅⟩ := hn₃ x' hx'
    -- ⊢ n ∈ FilterBasis.filter (B x')
    exact ⟨n₂, hn₄, hn₅.trans hm₂⟩
    -- 🎉 no goals
#align topological_space.nhds_mk_of_nhds_filter_basis TopologicalSpace.nhds_mkOfNhds_filterBasis

section Lattice

variable {α : Type u} {β : Type v}

/-- The ordering on topologies on the type `α`. `t ≤ s` if every set open in `s` is also open in `t`
(`t` is finer than `s`). -/
instance : PartialOrder (TopologicalSpace α) :=
  { PartialOrder.lift (fun t => OrderDual.toDual IsOpen[t]) (fun _ _ => TopologicalSpace.ext) with
    le := fun s t => ∀ U, IsOpen[t] U → IsOpen[s] U }

protected theorem le_def {α} {t s : TopologicalSpace α} : t ≤ s ↔ IsOpen[s] ≤ IsOpen[t] :=
  Iff.rfl
#align topological_space.le_def TopologicalSpace.le_def

theorem le_generateFrom_iff_subset_isOpen {g : Set (Set α)} {t : TopologicalSpace α} :
    t ≤ generateFrom g ↔ g ⊆ { s | IsOpen[t] s } :=
  ⟨fun ht s hs => ht _ <| .basic s hs, fun hg _s hs =>
    hs.recOn (fun _ h => hg h) isOpen_univ (fun _ _ _ _ => IsOpen.inter) fun _ _ => isOpen_sUnion⟩
#align topological_space.le_generate_from_iff_subset_is_open TopologicalSpace.le_generateFrom_iff_subset_isOpen

/-- If `s` equals the collection of open sets in the topology it generates, then `s` defines a
topology. -/
protected def mkOfClosure (s : Set (Set α)) (hs : { u | GenerateOpen s u } = s) :
    TopologicalSpace α where
  IsOpen u := u ∈ s
  isOpen_univ := hs ▸ TopologicalSpace.GenerateOpen.univ
  isOpen_inter := hs ▸ TopologicalSpace.GenerateOpen.inter
  isOpen_sUnion := hs ▸ TopologicalSpace.GenerateOpen.sUnion
#align topological_space.mk_of_closure TopologicalSpace.mkOfClosure

theorem mkOfClosure_sets {s : Set (Set α)} {hs : { u | GenerateOpen s u } = s} :
    TopologicalSpace.mkOfClosure s hs = generateFrom s :=
  TopologicalSpace.ext hs.symm
#align topological_space.mk_of_closure_sets TopologicalSpace.mkOfClosure_sets

theorem gc_generateFrom (α) :
    GaloisConnection (fun t : TopologicalSpace α => OrderDual.toDual { s | IsOpen[t] s })
      (generateFrom ∘ OrderDual.ofDual) := fun _ _ =>
  le_generateFrom_iff_subset_isOpen.symm

/-- The Galois coinsertion between `TopologicalSpace α` and `(Set (Set α))ᵒᵈ` whose lower part sends
  a topology to its collection of open subsets, and whose upper part sends a collection of subsets
  of `α` to the topology they generate. -/
def gciGenerateFrom (α : Type*) :
    GaloisCoinsertion (fun t : TopologicalSpace α => OrderDual.toDual { s | IsOpen[t] s })
      (generateFrom ∘ OrderDual.ofDual) where
  gc := gc_generateFrom α
  u_l_le _ s hs := TopologicalSpace.GenerateOpen.basic s hs
  choice g hg := TopologicalSpace.mkOfClosure g
    (Subset.antisymm hg <| le_generateFrom_iff_subset_isOpen.1 <| le_rfl)
  choice_eq _ _ := mkOfClosure_sets
#align gi_generate_from TopologicalSpace.gciGenerateFrom

/-- Topologies on `α` form a complete lattice, with `⊥` the discrete topology
  and `⊤` the indiscrete topology. The infimum of a collection of topologies
  is the topology generated by all their open sets, while the supremum is the
  topology whose open sets are those sets open in every member of the collection. -/
instance : CompleteLattice (TopologicalSpace α) := (gciGenerateFrom α).liftCompleteLattice

@[mono]
theorem generateFrom_anti {α} {g₁ g₂ : Set (Set α)} (h : g₁ ⊆ g₂) :
    generateFrom g₂ ≤ generateFrom g₁ :=
  (gc_generateFrom _).monotone_u h
#align topological_space.generate_from_anti TopologicalSpace.generateFrom_anti

theorem generateFrom_setOf_isOpen (t : TopologicalSpace α) :
    generateFrom { s | IsOpen[t] s } = t :=
  (gciGenerateFrom α).u_l_eq t
#align topological_space.generate_from_set_of_is_open TopologicalSpace.generateFrom_setOf_isOpen

theorem leftInverse_generateFrom :
    LeftInverse generateFrom fun t : TopologicalSpace α => { s | IsOpen[t] s } :=
  (gciGenerateFrom α).u_l_leftInverse
#align topological_space.left_inverse_generate_from TopologicalSpace.leftInverse_generateFrom

theorem generateFrom_surjective : Surjective (generateFrom : Set (Set α) → TopologicalSpace α) :=
  (gciGenerateFrom α).u_surjective
#align topological_space.generate_from_surjective TopologicalSpace.generateFrom_surjective

theorem setOf_isOpen_injective : Injective fun t : TopologicalSpace α => { s | IsOpen[t] s } :=
  (gciGenerateFrom α).l_injective
#align topological_space.set_of_is_open_injective TopologicalSpace.setOf_isOpen_injective

end Lattice

end TopologicalSpace

section Lattice

variable {t t₁ t₂ : TopologicalSpace α} {s : Set α}

theorem IsOpen.mono (hs : IsOpen[t₂] s) (h : t₁ ≤ t₂) : IsOpen[t₁] s := h s hs
#align is_open.mono IsOpen.mono

theorem IsClosed.mono (hs : IsClosed[t₂] s) (h : t₁ ≤ t₂) : IsClosed[t₁] s :=
  (@isOpen_compl_iff α t₁ s).mp <| hs.isOpen_compl.mono h
#align is_closed.mono IsClosed.mono

theorem closure.mono (h : t₁ ≤ t₂) : closure[t₁] s ⊆ closure[t₂] s :=
  @closure_minimal _ t₁ s (@closure _ t₂ s) subset_closure (IsClosed.mono isClosed_closure h)

theorem isOpen_implies_isOpen_iff : (∀ s, IsOpen[t₁] s → IsOpen[t₂] s) ↔ t₂ ≤ t₁ :=
  Iff.rfl
#align is_open_implies_is_open_iff isOpen_implies_isOpen_iff

/-- The only open sets in the indiscrete topology are the empty set and the whole space. -/
theorem TopologicalSpace.isOpen_top_iff {α} (U : Set α) : IsOpen[⊤] U ↔ U = ∅ ∨ U = univ :=
  ⟨fun h => by
    induction h with
    | basic _ h => exact False.elim h
    | univ => exact .inr rfl
    | inter _ _ _ _ h₁ h₂ =>
      rcases h₁ with (rfl | rfl) <;> rcases h₂ with (rfl | rfl) <;> simp
    | sUnion _ _ ih => exact sUnion_mem_empty_univ ih, by
      rintro (rfl | rfl)
      -- ⊢ IsOpen ∅
      exacts [@isOpen_empty _ ⊤, @isOpen_univ _ ⊤]⟩
      -- 🎉 no goals
#align topological_space.is_open_top_iff TopologicalSpace.isOpen_top_iff

/-- A topological space is discrete if every set is open, that is,
  its topology equals the discrete topology `⊥`. -/
class DiscreteTopology (α : Type*) [t : TopologicalSpace α] : Prop where
  /-- The `TopologicalSpace` structure on a type with discrete topology is equal to `⊥`. -/
  eq_bot : t = ⊥
#align discrete_topology DiscreteTopology

theorem discreteTopology_bot (α : Type*) : @DiscreteTopology α ⊥ :=
  @DiscreteTopology.mk α ⊥ rfl
#align discrete_topology_bot discreteTopology_bot

section DiscreteTopology

variable [TopologicalSpace α] [DiscreteTopology α]

@[simp]
theorem isOpen_discrete (s : Set α) : IsOpen s := (@DiscreteTopology.eq_bot α _).symm ▸ trivial
#align is_open_discrete isOpen_discrete

@[simp] theorem isClosed_discrete (s : Set α) : IsClosed s := ⟨isOpen_discrete _⟩
#align is_closed_discrete isClosed_discrete

@[simp] theorem closure_discrete (s : Set α) : closure s = s := (isClosed_discrete _).closure_eq

@[simp] theorem dense_discrete {s : Set α} : Dense s ↔ s = univ := by simp [dense_iff_closure_eq]
                                                                      -- 🎉 no goals

@[simp]
theorem denseRange_discrete {f : ι → α} : DenseRange f ↔ Surjective f := by
  rw [DenseRange, dense_discrete, range_iff_surjective]
  -- 🎉 no goals

@[nontriviality, continuity]
theorem continuous_of_discreteTopology [TopologicalSpace β] {f : α → β} : Continuous f :=
  continuous_def.2 fun _ _ => isOpen_discrete _
#align continuous_of_discrete_topology continuous_of_discreteTopology

@[simp]
theorem nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteTopology α] : @nhds α _ = pure :=
  le_antisymm (fun _ s hs => (isOpen_discrete s).mem_nhds hs) pure_le_nhds
#align nhds_discrete nhds_discrete

theorem mem_nhds_discrete {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ x ∈ s := by rw [nhds_discrete, mem_pure]
                          -- 🎉 no goals
#align mem_nhds_discrete mem_nhds_discrete

end DiscreteTopology

theorem le_of_nhds_le_nhds (h : ∀ x, @nhds α t₁ x ≤ @nhds α t₂ x) : t₁ ≤ t₂ := fun s => by
  rw [@isOpen_iff_mem_nhds _ t₁, @isOpen_iff_mem_nhds α t₂]
  -- ⊢ (∀ (a : α), a ∈ s → s ∈ 𝓝 a) → ∀ (a : α), a ∈ s → s ∈ 𝓝 a
  exact fun hs a ha => h _ (hs _ ha)
  -- 🎉 no goals
#align le_of_nhds_le_nhds le_of_nhds_le_nhds

theorem eq_of_nhds_eq_nhds (h : ∀ x, @nhds α t₁ x = @nhds α t₂ x) : t₁ = t₂ :=
  le_antisymm (le_of_nhds_le_nhds fun x => (h x).le)
    (le_of_nhds_le_nhds fun x => (h x).ge)
#align eq_of_nhds_eq_nhds eq_of_nhds_eq_nhds

theorem eq_bot_of_singletons_open {t : TopologicalSpace α} (h : ∀ x, IsOpen[t] {x}) : t = ⊥ :=
  bot_unique fun s _ => biUnion_of_singleton s ▸ isOpen_biUnion fun x _ => h x
#align eq_bot_of_singletons_open eq_bot_of_singletons_open

theorem forall_open_iff_discrete {X : Type*} [TopologicalSpace X] :
    (∀ s : Set X, IsOpen s) ↔ DiscreteTopology X :=
  ⟨fun h => ⟨eq_bot_of_singletons_open fun _ => h _⟩, @isOpen_discrete _ _⟩
#align forall_open_iff_discrete forall_open_iff_discrete

theorem discreteTopology_iff_forall_isClosed [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ s : Set α, IsClosed s :=
  forall_open_iff_discrete.symm.trans <| compl_surjective.forall.trans <| forall_congr' fun _ ↦
    isOpen_compl_iff

theorem singletons_open_iff_discrete {X : Type*} [TopologicalSpace X] :
    (∀ a : X, IsOpen ({a} : Set X)) ↔ DiscreteTopology X :=
  ⟨fun h => ⟨eq_bot_of_singletons_open h⟩, fun a _ => @isOpen_discrete _ _ a _⟩
#align singletons_open_iff_discrete singletons_open_iff_discrete

theorem discreteTopology_iff_singleton_mem_nhds [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ x : α, {x} ∈ 𝓝 x := by
  simp only [← singletons_open_iff_discrete, isOpen_iff_mem_nhds, mem_singleton_iff, forall_eq]
  -- 🎉 no goals
#align discrete_topology_iff_singleton_mem_nhds discreteTopology_iff_singleton_mem_nhds

/-- This lemma characterizes discrete topological spaces as those whose singletons are
neighbourhoods. -/
theorem discreteTopology_iff_nhds [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ x : α, 𝓝 x = pure x := by
  simp only [discreteTopology_iff_singleton_mem_nhds, ← nhds_neBot.le_pure_iff, le_pure_iff]
  -- 🎉 no goals
#align discrete_topology_iff_nhds discreteTopology_iff_nhds

theorem discreteTopology_iff_nhds_ne [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ x : α, 𝓝[≠] x = ⊥ := by
  simp only [discreteTopology_iff_singleton_mem_nhds, nhdsWithin, inf_principal_eq_bot, compl_compl]
  -- 🎉 no goals
#align discrete_topology_iff_nhds_ne discreteTopology_iff_nhds_ne

end Lattice

section GaloisConnection

variable {α β γ : Type*}

/-- Given `f : α → β` and a topology on `β`, the induced topology on `α` is the collection of
  sets that are preimages of some open set in `β`. This is the coarsest topology that
  makes `f` continuous. -/
def TopologicalSpace.induced {α : Type u} {β : Type v} (f : α → β) (t : TopologicalSpace β) :
    TopologicalSpace α where
  IsOpen s := ∃ s', IsOpen s' ∧ f ⁻¹' s' = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
    rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩
    -- ⊢ ∃ s', IsOpen s' ∧ f ⁻¹' s' = f ⁻¹' s'₁ ∩ f ⁻¹' s'₂
    exact ⟨s'₁ ∩ s'₂, hs₁.inter hs₂, preimage_inter⟩
    -- 🎉 no goals
  isOpen_sUnion S h := by
    choose! g hgo hfg using h
    -- ⊢ ∃ s', IsOpen s' ∧ f ⁻¹' s' = ⋃₀ S
    refine ⟨⋃ s ∈ S, g s, isOpen_biUnion fun s hs => hgo s hs, ?_⟩
    -- ⊢ f ⁻¹' ⋃ (s : Set α) (_ : s ∈ S), g s = ⋃₀ S
    rw [preimage_iUnion₂, sUnion_eq_biUnion]
    -- ⊢ ⋃ (i : Set α) (_ : i ∈ S), f ⁻¹' g i = ⋃ (i : Set α) (_ : i ∈ S), i
    exact iUnion₂_congr hfg
    -- 🎉 no goals
#align topological_space.induced TopologicalSpace.induced

theorem isOpen_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α → β} :
    IsOpen[t.induced f] s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s :=
  Iff.rfl
#align is_open_induced_iff isOpen_induced_iff

theorem isClosed_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α → β} :
    IsClosed[t.induced f] s ↔ ∃ t, IsClosed t ∧ f ⁻¹' t = s := by
  letI := t.induced f
  -- ⊢ IsClosed s ↔ ∃ t_1, IsClosed t_1 ∧ f ⁻¹' t_1 = s
  simp only [← isOpen_compl_iff, isOpen_induced_iff]
  -- ⊢ (∃ t_1, IsOpen t_1 ∧ f ⁻¹' t_1 = sᶜ) ↔ ∃ t_1, IsOpen t_1ᶜ ∧ f ⁻¹' t_1 = s
  exact compl_surjective.exists.trans (by simp only [preimage_compl, compl_inj_iff])
  -- 🎉 no goals
#align is_closed_induced_iff isClosed_induced_iff

/-- Given `f : α → β` and a topology on `α`, the coinduced topology on `β` is defined
  such that `s : Set β` is open if the preimage of `s` is open. This is the finest topology that
  makes `f` continuous. -/
def TopologicalSpace.coinduced {α : Type u} {β : Type v} (f : α → β) (t : TopologicalSpace α) :
    TopologicalSpace β where
  IsOpen s := IsOpen[t] (f ⁻¹' s)
  isOpen_univ := t.isOpen_univ
  isOpen_inter s₁ s₂ h₁ h₂ := h₁.inter h₂
  isOpen_sUnion s h := by simpa only [preimage_sUnion] using isOpen_biUnion h
                          -- 🎉 no goals
#align topological_space.coinduced TopologicalSpace.coinduced

theorem isOpen_coinduced {t : TopologicalSpace α} {s : Set β} {f : α → β} :
    IsOpen[t.coinduced f] s ↔ IsOpen (f ⁻¹' s) :=
  Iff.rfl
#align is_open_coinduced isOpen_coinduced

theorem preimage_nhds_coinduced [TopologicalSpace α] {π : α → β} {s : Set β} {a : α}
    (hs : s ∈ @nhds β (TopologicalSpace.coinduced π ‹_›) (π a)) : π ⁻¹' s ∈ 𝓝 a := by
  letI := TopologicalSpace.coinduced π ‹_›
  -- ⊢ π ⁻¹' s ∈ 𝓝 a
  rcases mem_nhds_iff.mp hs with ⟨V, hVs, V_op, mem_V⟩
  -- ⊢ π ⁻¹' s ∈ 𝓝 a
  exact mem_nhds_iff.mpr ⟨π ⁻¹' V, Set.preimage_mono hVs, V_op, mem_V⟩
  -- 🎉 no goals
#align preimage_nhds_coinduced preimage_nhds_coinduced

variable {t t₁ t₂ : TopologicalSpace α} {t' : TopologicalSpace β} {f : α → β} {g : β → α}

theorem Continuous.coinduced_le (h : Continuous[t, t'] f) : t.coinduced f ≤ t' :=
  (@continuous_def α β t t').1 h
#align continuous.coinduced_le Continuous.coinduced_le

theorem coinduced_le_iff_le_induced {f : α → β} {tα : TopologicalSpace α}
    {tβ : TopologicalSpace β} : tα.coinduced f ≤ tβ ↔ tα ≤ tβ.induced f :=
  ⟨fun h _s ⟨_t, ht, hst⟩ => hst ▸ h _ ht, fun h s hs => h _ ⟨s, hs, rfl⟩⟩
#align coinduced_le_iff_le_induced coinduced_le_iff_le_induced

theorem Continuous.le_induced (h : Continuous[t, t'] f) : t ≤ t'.induced f :=
  coinduced_le_iff_le_induced.1 h.coinduced_le
#align continuous.le_induced Continuous.le_induced

theorem gc_coinduced_induced (f : α → β) :
    GaloisConnection (TopologicalSpace.coinduced f) (TopologicalSpace.induced f) := fun _ _ =>
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
theorem induced_iInf {ι : Sort w} {t : ι → TopologicalSpace α} :
    (⨅ i, t i).induced g = ⨅ i, (t i).induced g :=
  (gc_coinduced_induced g).u_iInf
#align induced_infi induced_iInf

@[simp]
theorem coinduced_bot : (⊥ : TopologicalSpace α).coinduced f = ⊥ :=
  (gc_coinduced_induced f).l_bot
#align coinduced_bot coinduced_bot

@[simp]
theorem coinduced_sup : (t₁ ⊔ t₂).coinduced f = t₁.coinduced f ⊔ t₂.coinduced f :=
  (gc_coinduced_induced f).l_sup
#align coinduced_sup coinduced_sup

@[simp]
theorem coinduced_iSup {ι : Sort w} {t : ι → TopologicalSpace α} :
    (⨆ i, t i).coinduced f = ⨆ i, (t i).coinduced f :=
  (gc_coinduced_induced f).l_iSup
#align coinduced_supr coinduced_iSup

theorem induced_id [t : TopologicalSpace α] : t.induced id = t :=
  TopologicalSpace.ext <|
    funext fun s => propext <| ⟨fun ⟨_, hs, h⟩ => h ▸ hs, fun hs => ⟨s, hs, rfl⟩⟩
#align induced_id induced_id

theorem induced_compose [tγ : TopologicalSpace γ] {f : α → β} {g : β → γ} :
    (tγ.induced g).induced f = tγ.induced (g ∘ f) :=
  TopologicalSpace.ext <|
    funext fun _ => propext
      ⟨fun ⟨_, ⟨s, hs, h₂⟩, h₁⟩ => h₁ ▸ h₂ ▸ ⟨s, hs, rfl⟩,
        fun ⟨s, hs, h⟩ => ⟨preimage g s, ⟨s, hs, rfl⟩, h ▸ rfl⟩⟩
#align induced_compose induced_compose

theorem induced_const [t : TopologicalSpace α] {x : α} : (t.induced fun _ : β => x) = ⊤ :=
  le_antisymm le_top (@continuous_const β α ⊤ t x).le_induced
#align induced_const induced_const

theorem coinduced_id [t : TopologicalSpace α] : t.coinduced id = t :=
  TopologicalSpace.ext rfl
#align coinduced_id coinduced_id

theorem coinduced_compose [tα : TopologicalSpace α] {f : α → β} {g : β → γ} :
    (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f) :=
  TopologicalSpace.ext rfl
#align coinduced_compose coinduced_compose

theorem Equiv.induced_symm {α β : Type*} (e : α ≃ β) :
    TopologicalSpace.induced e.symm = TopologicalSpace.coinduced e := by
  ext t U
  -- ⊢ IsOpen U ↔ IsOpen U
  rw [isOpen_induced_iff, isOpen_coinduced]
  -- ⊢ (∃ t_1, IsOpen t_1 ∧ ↑e.symm ⁻¹' t_1 = U) ↔ IsOpen (↑e ⁻¹' U)
  simp only [e.symm.preimage_eq_iff_eq_image, exists_eq_right, ← preimage_equiv_eq_image_symm]
  -- 🎉 no goals
#align equiv.induced_symm Equiv.induced_symm

theorem Equiv.coinduced_symm {α β : Type*} (e : α ≃ β) :
    TopologicalSpace.coinduced e.symm = TopologicalSpace.induced e :=
  e.symm.induced_symm.symm
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

instance : TopologicalSpace Empty := ⊥
instance : DiscreteTopology Empty := ⟨rfl⟩

instance : TopologicalSpace PEmpty := ⊥
instance : DiscreteTopology PEmpty := ⟨rfl⟩

instance : TopologicalSpace PUnit := ⊥
instance : DiscreteTopology PUnit := ⟨rfl⟩

instance : TopologicalSpace Bool := ⊥
instance : DiscreteTopology Bool := ⟨rfl⟩

instance : TopologicalSpace ℕ := ⊥
instance : DiscreteTopology ℕ := ⟨rfl⟩

instance : TopologicalSpace ℤ := ⊥
instance : DiscreteTopology ℤ := ⟨rfl⟩

instance {n} : TopologicalSpace (Fin n) := ⊥
instance {n} : DiscreteTopology (Fin n) := ⟨rfl⟩

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
    (generateFrom b).induced f = generateFrom (preimage f '' b) :=
  le_antisymm (le_generateFrom <| ball_image_iff.2 fun s hs => ⟨s, GenerateOpen.basic _ hs, rfl⟩)
    (coinduced_le_iff_le_induced.1 <| le_generateFrom fun _s hs => .basic _ (mem_image_of_mem _ hs))
#align induced_generate_from_eq induced_generateFrom_eq

theorem le_induced_generateFrom {α β} [t : TopologicalSpace α] {b : Set (Set β)} {f : α → β}
    (h : ∀ a : Set β, a ∈ b → IsOpen (f ⁻¹' a)) : t ≤ induced f (generateFrom b) := by
  rw [induced_generateFrom_eq]
  -- ⊢ t ≤ generateFrom (preimage f '' b)
  apply le_generateFrom
  -- ⊢ ∀ (s : Set α), s ∈ preimage f '' b → IsOpen s
  simp only [mem_image, and_imp, forall_apply_eq_imp_iff₂, exists_imp]
  -- ⊢ ∀ (a : Set β), a ∈ b → IsOpen (f ⁻¹' a)
  exact h
  -- 🎉 no goals
#align le_induced_generate_from le_induced_generateFrom

/-- This construction is left adjoint to the operation sending a topology on `α`
  to its neighborhood filter at a fixed point `a : α`. -/
def nhdsAdjoint (a : α) (f : Filter α) : TopologicalSpace α where
  IsOpen s := a ∈ s → s ∈ f
  isOpen_univ _ := univ_mem
  isOpen_inter := fun _s _t hs ht ⟨has, hat⟩ => inter_mem (hs has) (ht hat)
  isOpen_sUnion := fun _k hk ⟨u, hu, hau⟩ => mem_of_superset (hk u hu hau) (subset_sUnion_of_mem hu)
#align nhds_adjoint nhdsAdjoint

theorem gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nhds α t a := fun f t => by
  rw [le_nhds_iff]
  -- ⊢ nhdsAdjoint a f ≤ t ↔ ∀ (s : Set α), a ∈ s → IsOpen s → s ∈ f
  exact ⟨fun H s hs has => H _ has hs, fun H s has hs => H _ hs has⟩
  -- 🎉 no goals
#align gc_nhds gc_nhds

theorem nhds_mono {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ ≤ t₂) :
    @nhds α t₁ a ≤ @nhds α t₂ a :=
  (gc_nhds a).monotone_u h
#align nhds_mono nhds_mono

theorem le_iff_nhds {α : Type*} (t t' : TopologicalSpace α) :
    t ≤ t' ↔ ∀ x, @nhds α t x ≤ @nhds α t' x :=
  ⟨fun h _ => nhds_mono h, le_of_nhds_le_nhds⟩
#align le_iff_nhds le_iff_nhds

theorem nhdsAdjoint_nhds {α : Type*} (a : α) (f : Filter α) :
    @nhds α (nhdsAdjoint a f) a = pure a ⊔ f := by
  letI := nhdsAdjoint a f
  -- ⊢ 𝓝 a = pure a ⊔ f
  ext U
  -- ⊢ U ∈ 𝓝 a ↔ U ∈ pure a ⊔ f
  rw [mem_nhds_iff]
  -- ⊢ (∃ t, t ⊆ U ∧ IsOpen t ∧ a ∈ t) ↔ U ∈ pure a ⊔ f
  constructor
  -- ⊢ (∃ t, t ⊆ U ∧ IsOpen t ∧ a ∈ t) → U ∈ pure a ⊔ f
  · rintro ⟨t, htU, ht, hat⟩
    -- ⊢ U ∈ pure a ⊔ f
    exact ⟨htU hat, mem_of_superset (ht hat) htU⟩
    -- 🎉 no goals
  · rintro ⟨haU, hU⟩
    -- ⊢ ∃ t, t ⊆ U ∧ IsOpen t ∧ a ∈ t
    exact ⟨U, Subset.rfl, fun _ => hU, haU⟩
    -- 🎉 no goals
#align nhds_adjoint_nhds nhdsAdjoint_nhds

theorem nhdsAdjoint_nhds_of_ne {α : Type*} (a : α) (f : Filter α) {b : α} (h : b ≠ a) :
    @nhds α (nhdsAdjoint a f) b = pure b := by
  letI := nhdsAdjoint a f
  -- ⊢ 𝓝 b = pure b
  apply le_antisymm
  -- ⊢ 𝓝 b ≤ pure b
  · intro U hU
    -- ⊢ U ∈ 𝓝 b
    rw [mem_nhds_iff]
    -- ⊢ ∃ t, t ⊆ U ∧ IsOpen t ∧ b ∈ t
    use {b}
    -- ⊢ {b} ⊆ U ∧ IsOpen {b} ∧ b ∈ {b}
    simp only [and_true_iff, singleton_subset_iff, mem_singleton]
    -- ⊢ b ∈ U ∧ IsOpen {b}
    refine' ⟨hU, fun ha => (h.symm ha).elim⟩
    -- 🎉 no goals
  · exact @pure_le_nhds α (nhdsAdjoint a f) b
    -- 🎉 no goals
#align nhds_adjoint_nhds_of_ne nhdsAdjoint_nhds_of_ne

theorem isOpen_singleton_nhdsAdjoint {α : Type*} {a b : α} (f : Filter α) (hb : b ≠ a) :
    IsOpen[nhdsAdjoint a f] {b} := by
  letI := nhdsAdjoint a f
  -- ⊢ IsOpen {b}
  rw [isOpen_singleton_iff_nhds_eq_pure]
  -- ⊢ 𝓝 b = pure b
  exact nhdsAdjoint_nhds_of_ne a f hb
  -- 🎉 no goals
#align is_open_singleton_nhds_adjoint isOpen_singleton_nhdsAdjoint

theorem le_nhdsAdjoint_iff' {α : Type*} (a : α) (f : Filter α) (t : TopologicalSpace α) :
    t ≤ nhdsAdjoint a f ↔ @nhds α t a ≤ pure a ⊔ f ∧ ∀ b, b ≠ a → @nhds α t b = pure b := by
  rw [le_iff_nhds]
  -- ⊢ (∀ (x : α), 𝓝 x ≤ 𝓝 x) ↔ 𝓝 a ≤ pure a ⊔ f ∧ ∀ (b : α), b ≠ a → 𝓝 b = pure b
  constructor
  -- ⊢ (∀ (x : α), 𝓝 x ≤ 𝓝 x) → 𝓝 a ≤ pure a ⊔ f ∧ ∀ (b : α), b ≠ a → 𝓝 b = pure b
  · intro h
    -- ⊢ 𝓝 a ≤ pure a ⊔ f ∧ ∀ (b : α), b ≠ a → 𝓝 b = pure b
    constructor
    -- ⊢ 𝓝 a ≤ pure a ⊔ f
    · specialize h a
      -- ⊢ 𝓝 a ≤ pure a ⊔ f
      rwa [nhdsAdjoint_nhds] at h
      -- 🎉 no goals
    · intro b hb
      -- ⊢ 𝓝 b = pure b
      apply le_antisymm _ (pure_le_nhds b)
      -- ⊢ 𝓝 b ≤ pure b
      specialize h b
      -- ⊢ 𝓝 b ≤ pure b
      rwa [nhdsAdjoint_nhds_of_ne a f hb] at h
      -- 🎉 no goals
  · rintro ⟨h, h'⟩ b
    -- ⊢ 𝓝 b ≤ 𝓝 b
    by_cases hb : b = a
    -- ⊢ 𝓝 b ≤ 𝓝 b
    · rwa [hb, nhdsAdjoint_nhds]
      -- 🎉 no goals
    · simp [nhdsAdjoint_nhds_of_ne a f hb, h' b hb]
      -- 🎉 no goals
#align le_nhds_adjoint_iff' le_nhdsAdjoint_iff'

theorem le_nhdsAdjoint_iff {α : Type*} (a : α) (f : Filter α) (t : TopologicalSpace α) :
    t ≤ nhdsAdjoint a f ↔ @nhds α t a ≤ pure a ⊔ f ∧ ∀ b, b ≠ a → IsOpen[t] {b} := by
  change _ ↔ _ ∧ ∀ b : α, b ≠ a → IsOpen {b}
  -- ⊢ t ≤ nhdsAdjoint a f ↔ 𝓝 a ≤ pure a ⊔ f ∧ ∀ (b : α), b ≠ a → IsOpen {b}
  rw [le_nhdsAdjoint_iff', and_congr_right_iff]
  -- ⊢ 𝓝 a ≤ pure a ⊔ f → ((∀ (b : α), b ≠ a → 𝓝 b = pure b) ↔ ∀ (b : α), b ≠ a → I …
  refine fun _ => forall_congr' fun b => ?_
  -- ⊢ b ≠ a → 𝓝 b = pure b ↔ b ≠ a → IsOpen {b}
  rw [@isOpen_singleton_iff_nhds_eq_pure α t b]
  -- 🎉 no goals
#align le_nhds_adjoint_iff le_nhdsAdjoint_iff

theorem nhds_iInf {ι : Sort*} {t : ι → TopologicalSpace α} {a : α} :
    @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a :=
  (gc_nhds a).u_iInf
#align nhds_infi nhds_iInf

theorem nhds_sInf {s : Set (TopologicalSpace α)} {a : α} :
    @nhds α (sInf s) a = ⨅ t ∈ s, @nhds α t a :=
  (gc_nhds a).u_sInf
#align nhds_Inf nhds_sInf

-- porting note: todo: timeouts without `b₁ := t₁`
theorem nhds_inf {t₁ t₂ : TopologicalSpace α} {a : α} :
    @nhds α (t₁ ⊓ t₂) a = @nhds α t₁ a ⊓ @nhds α t₂ a :=
  GaloisConnection.u_inf (b₁ := t₁) (gc_nhds a)
#align nhds_inf nhds_inf

theorem nhds_top {a : α} : @nhds α ⊤ a = ⊤ :=
  (gc_nhds a).u_top
#align nhds_top nhds_top

theorem isOpen_sup {t₁ t₂ : TopologicalSpace α} {s : Set α} :
    IsOpen[t₁ ⊔ t₂] s ↔ IsOpen[t₁] s ∧ IsOpen[t₂] s :=
  Iff.rfl
#align is_open_sup isOpen_sup

open TopologicalSpace

variable {γ : Type*} {f : α → β} {ι : Sort*}

theorem continuous_iff_coinduced_le {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace β} :
    Continuous[t₁, t₂] f ↔ coinduced f t₁ ≤ t₂ :=
  continuous_def
#align continuous_iff_coinduced_le continuous_iff_coinduced_le

theorem continuous_iff_le_induced {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace β} :
    Continuous[t₁, t₂] f ↔ t₁ ≤ induced f t₂ :=
  Iff.trans continuous_iff_coinduced_le (gc_coinduced_induced f _ _)
#align continuous_iff_le_induced continuous_iff_le_induced

theorem continuous_generateFrom {t : TopologicalSpace α} {b : Set (Set β)}
    (h : ∀ s ∈ b, IsOpen (f ⁻¹' s)) :
    Continuous[t, generateFrom b] f :=
  continuous_iff_coinduced_le.2 <| le_generateFrom h
#align continuous_generated_from continuous_generateFrom

@[continuity]
theorem continuous_induced_dom {t : TopologicalSpace β} : Continuous[induced f t, t] f :=
  continuous_iff_le_induced.2 le_rfl
#align continuous_induced_dom continuous_induced_dom

theorem continuous_induced_rng {g : γ → α} {t₂ : TopologicalSpace β} {t₁ : TopologicalSpace γ} :
    Continuous[t₁, induced f t₂] g ↔ Continuous[t₁, t₂] (f ∘ g) := by
  simp only [continuous_iff_le_induced, induced_compose]
  -- 🎉 no goals
#align continuous_induced_rng continuous_induced_rng

theorem continuous_coinduced_rng {t : TopologicalSpace α} :
    Continuous[t, coinduced f t] f :=
  continuous_iff_coinduced_le.2 le_rfl
#align continuous_coinduced_rng continuous_coinduced_rng

theorem continuous_coinduced_dom {g : β → γ} {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace γ} :
    Continuous[coinduced f t₁, t₂] g ↔ Continuous[t₁, t₂] (g ∘ f) := by
  simp only [continuous_iff_coinduced_le, coinduced_compose]
  -- 🎉 no goals
#align continuous_coinduced_dom continuous_coinduced_dom

theorem continuous_le_dom {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} (h₁ : t₂ ≤ t₁)
    (h₂ : Continuous[t₁, t₃] f) : Continuous[t₂, t₃] f := by
  rw [continuous_iff_le_induced] at h₂ ⊢
  -- ⊢ t₂ ≤ induced f t₃
  exact le_trans h₁ h₂
  -- 🎉 no goals
#align continuous_le_dom continuous_le_dom

theorem continuous_le_rng {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β} (h₁ : t₂ ≤ t₃)
    (h₂ : Continuous[t₁, t₂] f) : Continuous[t₁, t₃] f := by
  rw [continuous_iff_coinduced_le] at h₂ ⊢
  -- ⊢ coinduced f t₁ ≤ t₃
  exact le_trans h₂ h₁
  -- 🎉 no goals
#align continuous_le_rng continuous_le_rng

theorem continuous_sup_dom {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} :
    Continuous[t₁ ⊔ t₂, t₃] f ↔ Continuous[t₁, t₃] f ∧ Continuous[t₂, t₃] f := by
  simp only [continuous_iff_le_induced, sup_le_iff]
  -- 🎉 no goals
#align continuous_sup_dom continuous_sup_dom

theorem continuous_sup_rng_left {t₁ : TopologicalSpace α} {t₃ t₂ : TopologicalSpace β} :
    Continuous[t₁, t₂] f → Continuous[t₁, t₂ ⊔ t₃] f :=
  continuous_le_rng le_sup_left
#align continuous_sup_rng_left continuous_sup_rng_left

theorem continuous_sup_rng_right {t₁ : TopologicalSpace α} {t₃ t₂ : TopologicalSpace β} :
    Continuous[t₁, t₃] f → Continuous[t₁, t₂ ⊔ t₃] f :=
  continuous_le_rng le_sup_right
#align continuous_sup_rng_right continuous_sup_rng_right

theorem continuous_sSup_dom {T : Set (TopologicalSpace α)} {t₂ : TopologicalSpace β} :
    Continuous[sSup T, t₂] f ↔ ∀ t ∈ T, Continuous[t, t₂] f := by
  simp only [continuous_iff_le_induced, sSup_le_iff]
  -- 🎉 no goals
#align continuous_Sup_dom continuous_sSup_dom

theorem continuous_sSup_rng {t₁ : TopologicalSpace α} {t₂ : Set (TopologicalSpace β)}
    {t : TopologicalSpace β} (h₁ : t ∈ t₂) (hf : Continuous[t₁, t] f) :
    Continuous[t₁, sSup t₂] f :=
  continuous_iff_coinduced_le.2 <| le_sSup_of_le h₁ <| continuous_iff_coinduced_le.1 hf
#align continuous_Sup_rng continuous_sSup_rng

theorem continuous_iSup_dom {t₁ : ι → TopologicalSpace α} {t₂ : TopologicalSpace β} :
    Continuous[iSup t₁, t₂] f ↔ ∀ i, Continuous[t₁ i, t₂] f := by
  simp only [continuous_iff_le_induced, iSup_le_iff]
  -- 🎉 no goals
#align continuous_supr_dom continuous_iSup_dom

theorem continuous_iSup_rng {t₁ : TopologicalSpace α} {t₂ : ι → TopologicalSpace β} {i : ι}
    (h : Continuous[t₁, t₂ i] f) : Continuous[t₁, iSup t₂] f :=
  continuous_sSup_rng ⟨i, rfl⟩ h
#align continuous_supr_rng continuous_iSup_rng

theorem continuous_inf_rng {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β} :
    Continuous[t₁, t₂ ⊓ t₃] f ↔ Continuous[t₁, t₂] f ∧ Continuous[t₁, t₃] f := by
  simp only [continuous_iff_coinduced_le, le_inf_iff]
  -- 🎉 no goals
#align continuous_inf_rng continuous_inf_rng

theorem continuous_inf_dom_left {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} :
    Continuous[t₁, t₃] f → Continuous[t₁ ⊓ t₂, t₃] f :=
  continuous_le_dom inf_le_left
#align continuous_inf_dom_left continuous_inf_dom_left

theorem continuous_inf_dom_right {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} :
    Continuous[t₂, t₃] f → Continuous[t₁ ⊓ t₂, t₃] f :=
  continuous_le_dom inf_le_right
#align continuous_inf_dom_right continuous_inf_dom_right

theorem continuous_sInf_dom {t₁ : Set (TopologicalSpace α)} {t₂ : TopologicalSpace β}
    {t : TopologicalSpace α} (h₁ : t ∈ t₁) :
    Continuous[t, t₂] f → Continuous[sInf t₁, t₂] f :=
  continuous_le_dom <| sInf_le h₁
#align continuous_Inf_dom continuous_sInf_dom

theorem continuous_sInf_rng {t₁ : TopologicalSpace α} {T : Set (TopologicalSpace β)} :
    Continuous[t₁, sInf T] f ↔ ∀ t ∈ T, Continuous[t₁, t] f := by
  simp only [continuous_iff_coinduced_le, le_sInf_iff]
  -- 🎉 no goals
#align continuous_Inf_rng continuous_sInf_rng

theorem continuous_iInf_dom {t₁ : ι → TopologicalSpace α} {t₂ : TopologicalSpace β} {i : ι} :
    Continuous[t₁ i, t₂] f → Continuous[iInf t₁, t₂] f :=
  continuous_le_dom <| iInf_le _ _
#align continuous_infi_dom continuous_iInf_dom

theorem continuous_iInf_rng {t₁ : TopologicalSpace α} {t₂ : ι → TopologicalSpace β} :
    Continuous[t₁, iInf t₂] f ↔ ∀ i, Continuous[t₁, t₂ i] f := by
  simp only [continuous_iff_coinduced_le, le_iInf_iff]
  -- 🎉 no goals
#align continuous_infi_rng continuous_iInf_rng

@[continuity]
theorem continuous_bot {t : TopologicalSpace β} : Continuous[⊥, t] f :=
  continuous_iff_le_induced.2 bot_le
#align continuous_bot continuous_bot

@[continuity]
theorem continuous_top {t : TopologicalSpace α} : Continuous[t, ⊤] f :=
  continuous_iff_coinduced_le.2 le_top
#align continuous_top continuous_top

theorem continuous_id_iff_le {t t' : TopologicalSpace α} : Continuous[t, t'] id ↔ t ≤ t' :=
  @continuous_def _ _ t t' id
#align continuous_id_iff_le continuous_id_iff_le

theorem continuous_id_of_le {t t' : TopologicalSpace α} (h : t ≤ t') : Continuous[t, t'] id :=
  continuous_id_iff_le.2 h
#align continuous_id_of_le continuous_id_of_le

-- 𝓝 in the induced topology
theorem mem_nhds_induced [T : TopologicalSpace α] (f : β → α) (a : β) (s : Set β) :
    s ∈ @nhds β (TopologicalSpace.induced f T) a ↔ ∃ u ∈ 𝓝 (f a), f ⁻¹' u ⊆ s := by
  letI := T.induced f
  -- ⊢ s ∈ 𝓝 a ↔ ∃ u, u ∈ 𝓝 (f a) ∧ f ⁻¹' u ⊆ s
  simp only [mem_nhds_iff, isOpen_induced_iff, exists_prop, Set.mem_setOf_eq]
  -- ⊢ (∃ t, t ⊆ s ∧ (∃ t_1, IsOpen t_1 ∧ f ⁻¹' t_1 = t) ∧ a ∈ t) ↔ ∃ u, (∃ t, t ⊆  …
  constructor
  -- ⊢ (∃ t, t ⊆ s ∧ (∃ t_1, IsOpen t_1 ∧ f ⁻¹' t_1 = t) ∧ a ∈ t) → ∃ u, (∃ t, t ⊆  …
  · rintro ⟨u, usub, ⟨v, openv, rfl⟩, au⟩
    -- ⊢ ∃ u, (∃ t, t ⊆ u ∧ IsOpen t ∧ f a ∈ t) ∧ f ⁻¹' u ⊆ s
    exact ⟨v, ⟨v, Subset.rfl, openv, au⟩, usub⟩
    -- 🎉 no goals
  · rintro ⟨u, ⟨v, vsubu, openv, amem⟩, finvsub⟩
    -- ⊢ ∃ t, t ⊆ s ∧ (∃ t_1, IsOpen t_1 ∧ f ⁻¹' t_1 = t) ∧ a ∈ t
    exact ⟨f ⁻¹' v, (Set.preimage_mono vsubu).trans finvsub, ⟨⟨v, openv, rfl⟩, amem⟩⟩
    -- 🎉 no goals
#align mem_nhds_induced mem_nhds_induced

theorem nhds_induced [T : TopologicalSpace α] (f : β → α) (a : β) :
    @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a)) := by
  ext s
  -- ⊢ s ∈ 𝓝 a ↔ s ∈ comap f (𝓝 (f a))
  rw [mem_nhds_induced, mem_comap]
  -- 🎉 no goals
#align nhds_induced nhds_induced

theorem induced_iff_nhds_eq [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : β → α) :
    tβ = tα.induced f ↔ ∀ b, 𝓝 b = comap f (𝓝 <| f b) :=
  ⟨fun h a => h.symm ▸ nhds_induced f a, fun h =>
    eq_of_nhds_eq_nhds fun x => by rw [h, nhds_induced]⟩
                                   -- 🎉 no goals
#align induced_iff_nhds_eq induced_iff_nhds_eq

theorem map_nhds_induced_of_surjective [T : TopologicalSpace α] {f : β → α} (hf : Surjective f)
    (a : β) : map f (@nhds β (TopologicalSpace.induced f T) a) = 𝓝 (f a) := by
  rw [nhds_induced, map_comap_of_surjective hf]
  -- 🎉 no goals
#align map_nhds_induced_of_surjective map_nhds_induced_of_surjective

end Constructions

section Induced

open TopologicalSpace

variable {α : Type*} {β : Type*}

variable [t : TopologicalSpace β] {f : α → β}

theorem isOpen_induced_eq {s : Set α} :
    IsOpen[induced f t] s ↔ s ∈ preimage f '' { s | IsOpen s } :=
  Iff.rfl
#align is_open_induced_eq isOpen_induced_eq

theorem isOpen_induced {s : Set β} (h : IsOpen s) : IsOpen[induced f t] (f ⁻¹' s) :=
  ⟨s, h, rfl⟩
#align is_open_induced isOpen_induced

theorem map_nhds_induced_eq (a : α) : map f (@nhds α (induced f t) a) = 𝓝[range f] f a := by
  rw [nhds_induced, Filter.map_comap, nhdsWithin]
  -- 🎉 no goals
#align map_nhds_induced_eq map_nhds_induced_eq

theorem map_nhds_induced_of_mem {a : α} (h : range f ∈ 𝓝 (f a)) :
    map f (@nhds α (induced f t) a) = 𝓝 (f a) := by rw [nhds_induced, Filter.map_comap_of_mem h]
                                                    -- 🎉 no goals
#align map_nhds_induced_of_mem map_nhds_induced_of_mem

theorem closure_induced [t : TopologicalSpace β] {f : α → β} {a : α} {s : Set α} :
    a ∈ @closure α (t.induced f) s ↔ f a ∈ closure (f '' s) := by
  letI := t.induced f
  -- ⊢ a ∈ closure s ↔ f a ∈ closure (f '' s)
  simp only [mem_closure_iff_frequently, nhds_induced, frequently_comap, mem_image, and_comm]
  -- 🎉 no goals
#align closure_induced closure_induced

theorem isClosed_induced_iff' [t : TopologicalSpace β] {f : α → β} {s : Set α} :
    IsClosed[t.induced f] s ↔ ∀ a, f a ∈ closure (f '' s) → a ∈ s := by
  letI := t.induced f
  -- ⊢ IsClosed s ↔ ∀ (a : α), f a ∈ closure (f '' s) → a ∈ s
  simp only [← closure_subset_iff_isClosed, subset_def, closure_induced]
  -- 🎉 no goals
#align is_closed_induced_iff' isClosed_induced_iff'

end Induced

section Sierpinski

variable {α : Type*} [TopologicalSpace α]

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
                                                 -- 🎉 no goals
#align nhds_false nhds_false

theorem tendsto_nhds_true {l : Filter α} {p : α → Prop} :
    Tendsto p l (𝓝 True) ↔ ∀ᶠ x in l, p x := by simp
                                                -- 🎉 no goals

theorem tendsto_nhds_Prop {l : Filter α} {p : α → Prop} {q : Prop} :
    Tendsto p l (𝓝 q) ↔ (q → ∀ᶠ x in l, p x) := by
  by_cases q <;> simp [*]
  -- ⊢ Tendsto p l (𝓝 q) ↔ q → ∀ᶠ (x : α) in l, p x
  -- ⊢ Tendsto p l (𝓝 q) ↔ q → ∀ᶠ (x : α) in l, p x
                 -- 🎉 no goals
                 -- 🎉 no goals

theorem continuous_Prop {p : α → Prop} : Continuous p ↔ IsOpen { x | p x } := by
  simp only [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_Prop, isOpen_iff_mem_nhds]; rfl
  -- ⊢ (∀ (x : α), p x → ∀ᶠ (x : α) in 𝓝 x, p x) ↔ ∀ (a : α), a ∈ {x | p x} → {x |  …
                                                                                                 -- 🎉 no goals
#align continuous_Prop continuous_Prop

theorem isOpen_iff_continuous_mem {s : Set α} : IsOpen s ↔ Continuous (· ∈ s) :=
  continuous_Prop.symm
#align is_open_iff_continuous_mem isOpen_iff_continuous_mem

end Sierpinski

section iInf

open TopologicalSpace

variable {α : Type u} {ι : Sort v}

theorem generateFrom_union (a₁ a₂ : Set (Set α)) :
    generateFrom (a₁ ∪ a₂) = generateFrom a₁ ⊓ generateFrom a₂ :=
  (gc_generateFrom α).u_inf
#align generate_from_union generateFrom_union

theorem setOf_isOpen_sup (t₁ t₂ : TopologicalSpace α) :
    { s | IsOpen[t₁ ⊔ t₂] s } = { s | IsOpen[t₁] s } ∩ { s | IsOpen[t₂] s } :=
  rfl
#align set_of_is_open_sup setOf_isOpen_sup

theorem generateFrom_iUnion {f : ι → Set (Set α)} :
    generateFrom (⋃ i, f i) = ⨅ i, generateFrom (f i) :=
  (gc_generateFrom α).u_iInf
#align generate_from_Union generateFrom_iUnion

theorem setOf_isOpen_iSup {t : ι → TopologicalSpace α} :
    { s | IsOpen[⨆ i, t i] s } = ⋂ i, { s | IsOpen[t i] s } :=
  (gc_generateFrom α).l_iSup
#align set_of_is_open_supr setOf_isOpen_iSup

theorem generateFrom_sUnion {S : Set (Set (Set α))} :
    generateFrom (⋃₀ S) = ⨅ s ∈ S, generateFrom s :=
  (gc_generateFrom α).u_sInf
#align generate_from_sUnion generateFrom_sUnion

theorem setOf_isOpen_sSup {T : Set (TopologicalSpace α)} :
    { s | IsOpen[sSup T] s } = ⋂ t ∈ T, { s | IsOpen[t] s } :=
  (gc_generateFrom α).l_sSup
#align set_of_is_open_Sup setOf_isOpen_sSup

theorem generateFrom_union_isOpen (a b : TopologicalSpace α) :
    generateFrom ({ s | IsOpen[a] s } ∪ { s | IsOpen[b] s }) = a ⊓ b :=
  (gciGenerateFrom α).u_inf_l _ _
#align generate_from_union_is_open generateFrom_union_isOpen

theorem generateFrom_iUnion_isOpen (f : ι → TopologicalSpace α) :
    generateFrom (⋃ i, { s | IsOpen[f i] s }) = ⨅ i, f i :=
  (gciGenerateFrom α).u_iInf_l _
#align generate_from_Union_is_open generateFrom_iUnion_isOpen

theorem generateFrom_inter (a b : TopologicalSpace α) :
    generateFrom ({ s | IsOpen[a] s } ∩ { s | IsOpen[b] s }) = a ⊔ b :=
  (gciGenerateFrom α).u_sup_l _ _
#align generate_from_inter generateFrom_inter

theorem generateFrom_iInter (f : ι → TopologicalSpace α) :
    generateFrom (⋂ i, { s | IsOpen[f i] s }) = ⨆ i, f i :=
  (gciGenerateFrom α).u_iSup_l _
#align generate_from_Inter generateFrom_iInter

theorem generateFrom_iInter_of_generateFrom_eq_self (f : ι → Set (Set α))
    (hf : ∀ i, { s | IsOpen[generateFrom (f i)] s } = f i) :
    generateFrom (⋂ i, f i) = ⨆ i, generateFrom (f i) :=
  (gciGenerateFrom α).u_iSup_of_lu_eq_self f hf
#align generate_from_Inter_of_generate_from_eq_self generateFrom_iInter_of_generateFrom_eq_self

variable {t : ι → TopologicalSpace α}

theorem isOpen_iSup_iff {s : Set α} : IsOpen[⨆ i, t i] s ↔ ∀ i, IsOpen[t i] s :=
  show s ∈ {s | IsOpen[iSup t] s} ↔ s ∈ { x : Set α | ∀ i : ι, IsOpen[t i] x } by
    simp [setOf_isOpen_iSup]
    -- 🎉 no goals
#align is_open_supr_iff isOpen_iSup_iff

theorem isClosed_iSup_iff {s : Set α} : IsClosed[⨆ i, t i] s ↔ ∀ i, IsClosed[t i] s := by
  simp [← @isOpen_compl_iff _ (⨆ i, t i), ← @isOpen_compl_iff _ (t _), isOpen_iSup_iff]
  -- 🎉 no goals
#align is_closed_supr_iff isClosed_iSup_iff

end iInf
