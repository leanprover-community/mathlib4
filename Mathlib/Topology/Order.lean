/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Induced

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

@[expose] public section

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

/-- The smallest topological space containing the collection `g` of basic sets -/
def generateFrom (g : Set (Set α)) : TopologicalSpace α where
  IsOpen := GenerateOpen g
  isOpen_univ := GenerateOpen.univ
  isOpen_inter := GenerateOpen.inter
  isOpen_sUnion := GenerateOpen.sUnion

theorem isOpen_generateFrom_of_mem {g : Set (Set α)} {s : Set α} (hs : s ∈ g) :
    IsOpen[generateFrom g] s :=
  GenerateOpen.basic s hs

theorem nhds_generateFrom {g : Set (Set α)} {a : α} :
    @nhds α (generateFrom g) a = ⨅ s ∈ { s | a ∈ s ∧ s ∈ g }, 𝓟 s := by
  letI := generateFrom g
  rw [nhds_def]
  refine le_antisymm (biInf_mono fun s ⟨as, sg⟩ => ⟨as, .basic _ sg⟩) <| le_iInf₂ ?_
  rintro s ⟨ha, hs⟩
  induction hs with
  | basic _ hs => exact iInf₂_le _ ⟨ha, hs⟩
  | univ => exact le_top.trans_eq principal_univ.symm
  | inter _ _ _ _ hs ht => exact (le_inf (hs ha.1) (ht ha.2)).trans_eq inf_principal
  | sUnion _ _ hS =>
    let ⟨t, htS, hat⟩ := ha
    exact (hS t htS hat).trans (principal_mono.2 <| subset_sUnion_of_mem htS)

lemma tendsto_nhds_generateFrom_iff {β : Type*} {m : α → β} {f : Filter α} {g : Set (Set β)}
    {b : β} : Tendsto m f (@nhds β (generateFrom g) b) ↔ ∀ s ∈ g, b ∈ s → m ⁻¹' s ∈ f := by
  simp only [nhds_generateFrom, @forall_swap (b ∈ _), tendsto_iInf, mem_setOf_eq, and_imp,
    tendsto_principal]; rfl

/-- Construct a topology on α given the filter of neighborhoods of each point of α. -/
protected def mkOfNhds (n : α → Filter α) : TopologicalSpace α where
  IsOpen s := ∀ a ∈ s, s ∈ n a
  isOpen_univ _ _ := univ_mem
  isOpen_inter := fun _s _t hs ht x ⟨hxs, hxt⟩ => inter_mem (hs x hxs) (ht x hxt)
  isOpen_sUnion := fun _s hs _a ⟨x, hx, hxa⟩ =>
    mem_of_superset (hs x hx _ hxa) (subset_sUnion_of_mem hx)

theorem nhds_mkOfNhds_of_hasBasis {n : α → Filter α} {ι : α → Sort*} {p : ∀ a, ι a → Prop}
    {s : ∀ a, ι a → Set α} (hb : ∀ a, (n a).HasBasis (p a) (s a))
    (hpure : ∀ a i, p a i → a ∈ s a i) (hopen : ∀ a i, p a i → ∀ᶠ x in n a, s a i ∈ n x) (a : α) :
    @nhds α (.mkOfNhds n) a = n a := by
  let t : TopologicalSpace α := .mkOfNhds n
  apply le_antisymm
  · intro U hU
    replace hpure : pure ≤ n := fun x ↦ (hb x).ge_iff.2 (hpure x)
    refine mem_nhds_iff.2 ⟨{x | U ∈ n x}, fun x hx ↦ hpure x hx, fun x hx ↦ ?_, hU⟩
    rcases (hb x).mem_iff.1 hx with ⟨i, hpi, hi⟩
    exact (hopen x i hpi).mono fun y hy ↦ mem_of_superset hy hi
  · exact (nhds_basis_opens a).ge_iff.2 fun U ⟨haU, hUo⟩ ↦ hUo a haU

theorem nhds_mkOfNhds (n : α → Filter α) (a : α) (h₀ : pure ≤ n)
    (h₁ : ∀ a, ∀ s ∈ n a, ∀ᶠ y in n a, s ∈ n y) :
    @nhds α (TopologicalSpace.mkOfNhds n) a = n a :=
  nhds_mkOfNhds_of_hasBasis (fun a ↦ (n a).basis_sets) h₀ h₁ _

theorem nhds_mkOfNhds_single [DecidableEq α] {a₀ : α} {l : Filter α} (h : pure a₀ ≤ l) (b : α) :
    @nhds α (TopologicalSpace.mkOfNhds (update pure a₀ l)) b =
      (update pure a₀ l : α → Filter α) b := by
  refine nhds_mkOfNhds _ _ (le_update_iff.mpr ⟨h, fun _ _ => le_rfl⟩) fun a s hs => ?_
  rcases eq_or_ne a a₀ with (rfl | ha)
  · filter_upwards [hs] with b hb
    rcases eq_or_ne b a with (rfl | hb)
    · exact hs
    · rwa [update_of_ne hb]
  · simpa only [update_of_ne ha, mem_pure, eventually_pure] using hs

theorem nhds_mkOfNhds_filterBasis (B : α → FilterBasis α) (a : α) (h₀ : ∀ x, ∀ n ∈ B x, x ∈ n)
    (h₁ : ∀ x, ∀ n ∈ B x, ∃ n₁ ∈ B x, ∀ x' ∈ n₁, ∃ n₂ ∈ B x', n₂ ⊆ n) :
    @nhds α (TopologicalSpace.mkOfNhds fun x => (B x).filter) a = (B a).filter :=
  nhds_mkOfNhds_of_hasBasis (fun a ↦ (B a).hasBasis) h₀ h₁ a

section Lattice

variable {α : Type u} {β : Type v}

/-- The ordering on topologies on the type `α`. `t ≤ s` if every set open in `s` is also open in `t`
(`t` is finer than `s`). -/
instance : PartialOrder (TopologicalSpace α) :=
  { PartialOrder.lift (fun t => OrderDual.toDual IsOpen[t]) (fun _ _ => TopologicalSpace.ext) with
    le := fun s t => ∀ U, IsOpen[t] U → IsOpen[s] U }

protected theorem le_def {α} {t s : TopologicalSpace α} : t ≤ s ↔ IsOpen[s] ≤ IsOpen[t] :=
  Iff.rfl

theorem le_generateFrom_iff_subset_isOpen {g : Set (Set α)} {t : TopologicalSpace α} :
    t ≤ generateFrom g ↔ g ⊆ { s | IsOpen[t] s } :=
  ⟨fun ht s hs => ht _ <| .basic s hs, fun hg _s hs =>
    hs.recOn (fun _ h => hg h) isOpen_univ (fun _ _ _ _ => IsOpen.inter) fun _ _ => isOpen_sUnion⟩

/-- If `s` equals the collection of open sets in the topology it generates, then `s` defines a
topology. -/
protected def mkOfClosure (s : Set (Set α)) (hs : { u | GenerateOpen s u } = s) :
    TopologicalSpace α where
  IsOpen u := u ∈ s
  isOpen_univ := hs ▸ TopologicalSpace.GenerateOpen.univ
  isOpen_inter := hs ▸ TopologicalSpace.GenerateOpen.inter
  isOpen_sUnion := hs ▸ TopologicalSpace.GenerateOpen.sUnion

theorem mkOfClosure_sets {s : Set (Set α)} {hs : { u | GenerateOpen s u } = s} :
    TopologicalSpace.mkOfClosure s hs = generateFrom s :=
  TopologicalSpace.ext hs.symm

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

/-- Topologies on `α` form a complete lattice, with `⊥` the discrete topology
  and `⊤` the indiscrete topology. The infimum of a collection of topologies
  is the topology generated by all their open sets, while the supremum is the
  topology whose open sets are those sets open in every member of the collection. -/
instance : CompleteLattice (TopologicalSpace α) := (gciGenerateFrom α).liftCompleteLattice

@[mono, gcongr]
theorem generateFrom_anti {α} {g₁ g₂ : Set (Set α)} (h : g₁ ⊆ g₂) :
    generateFrom g₂ ≤ generateFrom g₁ :=
  (gc_generateFrom _).monotone_u h

theorem generateFrom_setOf_isOpen (t : TopologicalSpace α) :
    generateFrom { s | IsOpen[t] s } = t :=
  (gciGenerateFrom α).u_l_eq t

theorem leftInverse_generateFrom :
    LeftInverse generateFrom fun t : TopologicalSpace α => { s | IsOpen[t] s } :=
  (gciGenerateFrom α).u_l_leftInverse

theorem generateFrom_surjective : Surjective (generateFrom : Set (Set α) → TopologicalSpace α) :=
  (gciGenerateFrom α).u_surjective

theorem setOf_isOpen_injective : Injective fun t : TopologicalSpace α => { s | IsOpen[t] s } :=
  (gciGenerateFrom α).l_injective

end Lattice

end TopologicalSpace

section Lattice

variable {α : Type*} {t t₁ t₂ : TopologicalSpace α} {s : Set α}

theorem IsOpen.mono (hs : IsOpen[t₂] s) (h : t₁ ≤ t₂) : IsOpen[t₁] s := h s hs

theorem IsClosed.mono (hs : IsClosed[t₂] s) (h : t₁ ≤ t₂) : IsClosed[t₁] s :=
  (@isOpen_compl_iff α s t₁).mp <| hs.isOpen_compl.mono h

theorem closure.mono (h : t₁ ≤ t₂) : closure[t₁] s ⊆ closure[t₂] s :=
  @closure_minimal _ t₁ s (@closure _ t₂ s) subset_closure (IsClosed.mono isClosed_closure h)

theorem isOpen_implies_isOpen_iff : (∀ s, IsOpen[t₁] s → IsOpen[t₂] s) ↔ t₂ ≤ t₁ :=
  Iff.rfl

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
      exacts [@isOpen_empty _ ⊤, @isOpen_univ _ ⊤]⟩

/-- A topological space is discrete if every set is open, that is,
  its topology equals the discrete topology `⊥`. -/
class DiscreteTopology (α : Type*) [t : TopologicalSpace α] : Prop where
  /-- The `TopologicalSpace` structure on a type with discrete topology is equal to `⊥`. -/
  eq_bot : t = ⊥

theorem discreteTopology_bot (α : Type*) : @DiscreteTopology α ⊥ :=
  @DiscreteTopology.mk α ⊥ rfl

section DiscreteTopology

variable [TopologicalSpace α] [DiscreteTopology α] {β : Type*}

@[simp]
theorem isOpen_discrete (s : Set α) : IsOpen s := (@DiscreteTopology.eq_bot α _).symm ▸ trivial

@[simp] theorem isClosed_discrete (s : Set α) : IsClosed s := ⟨isOpen_discrete _⟩

theorem closure_discrete (s : Set α) : closure s = s := (isClosed_discrete _).closure_eq

@[simp] theorem dense_discrete {s : Set α} : Dense s ↔ s = univ := by simp [dense_iff_closure_eq]

@[simp]
theorem denseRange_discrete {ι : Type*} {f : ι → α} : DenseRange f ↔ Surjective f := by
  rw [DenseRange, dense_discrete, range_eq_univ]

@[nontriviality, continuity, fun_prop]
theorem continuous_of_discreteTopology [TopologicalSpace β] {f : α → β} : Continuous f :=
  continuous_def.2 fun _ _ => isOpen_discrete _

/-- A function to a discrete topological space is continuous if and only if the preimage of every
singleton is open. -/
theorem continuous_discrete_rng {α} [TopologicalSpace α] [TopologicalSpace β] [DiscreteTopology β]
    {f : α → β} : Continuous f ↔ ∀ b : β, IsOpen (f ⁻¹' {b}) :=
  ⟨fun h _ => (isOpen_discrete _).preimage h, fun h => ⟨fun s _ => by
    rw [← biUnion_of_singleton s, preimage_iUnion₂]
    exact isOpen_biUnion fun _ _ => h _⟩⟩

@[simp]
theorem nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteTopology α] : @nhds α _ = pure :=
  le_antisymm (fun _ s hs => (isOpen_discrete s).mem_nhds hs) pure_le_nhds

theorem mem_nhds_discrete {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ x ∈ s := by rw [nhds_discrete, mem_pure]

end DiscreteTopology

theorem le_of_nhds_le_nhds (h : ∀ x, @nhds α t₁ x ≤ @nhds α t₂ x) : t₁ ≤ t₂ := fun s => by
  rw [@isOpen_iff_mem_nhds _ t₁, @isOpen_iff_mem_nhds _ t₂]
  exact fun hs a ha => h _ (hs _ ha)

theorem eq_bot_of_singletons_open {t : TopologicalSpace α} (h : ∀ x, IsOpen[t] {x}) : t = ⊥ :=
  bot_unique fun s _ => biUnion_of_singleton s ▸ isOpen_biUnion fun x _ => h x

theorem discreteTopology_iff_forall_isOpen [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ s : Set α, IsOpen s :=
  ⟨@isOpen_discrete _ _, fun h ↦ ⟨eq_bot_of_singletons_open fun _ ↦ h _⟩⟩

@[deprecated discreteTopology_iff_forall_isOpen (since := "2025-10-10")]
theorem forall_open_iff_discrete {X : Type*} [TopologicalSpace X] :
    (∀ s : Set X, IsOpen s) ↔ DiscreteTopology X :=
  discreteTopology_iff_forall_isOpen.symm

theorem discreteTopology_iff_forall_isClosed [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ s : Set α, IsClosed s :=
  discreteTopology_iff_forall_isOpen.trans <| compl_surjective.forall.trans <| forall_congr' fun _ ↦
    isOpen_compl_iff

theorem discreteTopology_iff_isOpen_singleton [TopologicalSpace α] :
    DiscreteTopology α ↔ (∀ a : α, IsOpen ({a} : Set α)):=
  ⟨fun _ _ ↦ isOpen_discrete _, fun h ↦ ⟨eq_bot_of_singletons_open h⟩⟩

@[deprecated discreteTopology_iff_isOpen_singleton (since := "2025-10-10")]
theorem singletons_open_iff_discrete {X : Type*} [TopologicalSpace X] :
    (∀ a : X, IsOpen ({a} : Set X)) ↔ DiscreteTopology X :=
  discreteTopology_iff_isOpen_singleton.symm

theorem DiscreteTopology.of_finite_of_isClosed_singleton [TopologicalSpace α] [Finite α]
    (h : ∀ a : α, IsClosed {a}) : DiscreteTopology α :=
  discreteTopology_iff_forall_isClosed.mpr fun s ↦
    s.iUnion_of_singleton_coe ▸ isClosed_iUnion_of_finite fun _ ↦ h _

theorem discreteTopology_iff_singleton_mem_nhds [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ x : α, {x} ∈ 𝓝 x := by
  simp only [discreteTopology_iff_isOpen_singleton,
    isOpen_iff_mem_nhds, mem_singleton_iff, forall_eq]

/-- This lemma characterizes discrete topological spaces as those whose singletons are
neighbourhoods. -/
theorem discreteTopology_iff_nhds [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ x : α, 𝓝 x = pure x := by
  simp only [discreteTopology_iff_singleton_mem_nhds]
  apply forall_congr' (fun x ↦ ?_)
  simp [le_antisymm_iff, pure_le_nhds x]

theorem discreteTopology_iff_nhds_ne [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ x : α, 𝓝[≠] x = ⊥ := by
  simp only [discreteTopology_iff_singleton_mem_nhds, nhdsWithin, inf_principal_eq_bot, compl_compl]

/-- If the codomain of a continuous injective function has discrete topology,
then so does the domain.

See also `Embedding.discreteTopology` for an important special case. -/
theorem DiscreteTopology.of_continuous_injective
    {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [DiscreteTopology β] {f : α → β}
    (hc : Continuous f) (hinj : Injective f) : DiscreteTopology α :=
  discreteTopology_iff_forall_isOpen.2 fun s ↦
    hinj.preimage_image s ▸ (isOpen_discrete _).preimage hc

end Lattice

section GaloisConnection

variable {α β γ : Type*}

theorem isOpen_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α → β} :
    IsOpen[t.induced f] s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s :=
  Iff.rfl

theorem isClosed_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α → β} :
    IsClosed[t.induced f] s ↔ ∃ t, IsClosed t ∧ f ⁻¹' t = s := by
  letI := t.induced f
  simp only [← isOpen_compl_iff, isOpen_induced_iff]
  exact compl_surjective.exists.trans (by simp only [preimage_compl, compl_inj_iff])

theorem isOpen_coinduced {t : TopologicalSpace α} {s : Set β} {f : α → β} :
    IsOpen[t.coinduced f] s ↔ IsOpen (f ⁻¹' s) :=
  Iff.rfl

theorem isClosed_coinduced {t : TopologicalSpace α} {s : Set β} {f : α → β} :
    IsClosed[t.coinduced f] s ↔ IsClosed (f ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_coinduced (f := f), preimage_compl]

theorem preimage_nhds_coinduced [TopologicalSpace α] {π : α → β} {s : Set β} {a : α}
    (hs : s ∈ @nhds β (TopologicalSpace.coinduced π ‹_›) (π a)) : π ⁻¹' s ∈ 𝓝 a := by
  letI := TopologicalSpace.coinduced π ‹_›
  rcases mem_nhds_iff.mp hs with ⟨V, hVs, V_op, mem_V⟩
  exact mem_nhds_iff.mpr ⟨π ⁻¹' V, Set.preimage_mono hVs, V_op, mem_V⟩

variable {t t₁ t₂ : TopologicalSpace α} {t' : TopologicalSpace β} {f : α → β} {g : β → α}

theorem Continuous.coinduced_le (h : Continuous[t, t'] f) : t.coinduced f ≤ t' :=
  (@continuous_def α β t t').1 h

theorem coinduced_le_iff_le_induced {f : α → β} {tα : TopologicalSpace α}
    {tβ : TopologicalSpace β} : tα.coinduced f ≤ tβ ↔ tα ≤ tβ.induced f :=
  ⟨fun h _s ⟨_t, ht, hst⟩ => hst ▸ h _ ht, fun h s hs => h _ ⟨s, hs, rfl⟩⟩

theorem Continuous.le_induced (h : Continuous[t, t'] f) : t ≤ t'.induced f :=
  coinduced_le_iff_le_induced.1 h.coinduced_le

theorem gc_coinduced_induced (f : α → β) :
    GaloisConnection (TopologicalSpace.coinduced f) (TopologicalSpace.induced f) := fun _ _ =>
  coinduced_le_iff_le_induced

@[gcongr]
theorem induced_mono (h : t₁ ≤ t₂) : t₁.induced g ≤ t₂.induced g :=
  (gc_coinduced_induced g).monotone_u h

@[gcongr]
theorem coinduced_mono (h : t₁ ≤ t₂) : t₁.coinduced f ≤ t₂.coinduced f :=
  (gc_coinduced_induced f).monotone_l h

@[simp]
theorem induced_top : (⊤ : TopologicalSpace α).induced g = ⊤ :=
  (gc_coinduced_induced g).u_top

@[simp]
theorem induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induced g :=
  (gc_coinduced_induced g).u_inf

@[simp]
theorem induced_iInf {ι : Sort w} {t : ι → TopologicalSpace α} :
    (⨅ i, t i).induced g = ⨅ i, (t i).induced g :=
  (gc_coinduced_induced g).u_iInf

@[simp]
theorem induced_sInf {s : Set (TopologicalSpace α)} :
    TopologicalSpace.induced g (sInf s) = sInf (TopologicalSpace.induced g '' s) := by
  rw [sInf_eq_iInf', sInf_image', induced_iInf]

@[simp]
theorem coinduced_bot : (⊥ : TopologicalSpace α).coinduced f = ⊥ :=
  (gc_coinduced_induced f).l_bot

@[simp]
theorem coinduced_sup : (t₁ ⊔ t₂).coinduced f = t₁.coinduced f ⊔ t₂.coinduced f :=
  (gc_coinduced_induced f).l_sup

@[simp]
theorem coinduced_iSup {ι : Sort w} {t : ι → TopologicalSpace α} :
    (⨆ i, t i).coinduced f = ⨆ i, (t i).coinduced f :=
  (gc_coinduced_induced f).l_iSup

@[simp]
theorem coinduced_sSup {s : Set (TopologicalSpace α)} :
    TopologicalSpace.coinduced f (sSup s) = sSup ((TopologicalSpace.coinduced f) '' s) := by
  rw [sSup_eq_iSup', sSup_image', coinduced_iSup]

theorem induced_id [t : TopologicalSpace α] : t.induced id = t :=
  TopologicalSpace.ext <|
    funext fun s => propext <| ⟨fun ⟨_, hs, h⟩ => h ▸ hs, fun hs => ⟨s, hs, rfl⟩⟩

theorem induced_compose {tγ : TopologicalSpace γ} {f : α → β} {g : β → γ} :
    (tγ.induced g).induced f = tγ.induced (g ∘ f) :=
  TopologicalSpace.ext <|
    funext fun _ => propext
      ⟨fun ⟨_, ⟨s, hs, h₂⟩, h₁⟩ => h₁ ▸ h₂ ▸ ⟨s, hs, rfl⟩,
        fun ⟨s, hs, h⟩ => ⟨preimage g s, ⟨s, hs, rfl⟩, h ▸ rfl⟩⟩

theorem induced_const [t : TopologicalSpace α] {x : α} : (t.induced fun _ : β => x) = ⊤ :=
  le_antisymm le_top (@Continuous.const β α ⊤ t x).le_induced

theorem coinduced_id [t : TopologicalSpace α] : t.coinduced id = t :=
  TopologicalSpace.ext rfl

theorem coinduced_compose [tα : TopologicalSpace α] {f : α → β} {g : β → γ} :
    (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f) :=
  TopologicalSpace.ext rfl

theorem Equiv.induced_symm {α β : Type*} (e : α ≃ β) :
    TopologicalSpace.induced e.symm = TopologicalSpace.coinduced e := by
  ext t U
  rw [isOpen_induced_iff, isOpen_coinduced]
  simp only [e.symm.preimage_eq_iff_eq_image, exists_eq_right, Equiv.image_symm_eq_preimage]

theorem Equiv.coinduced_symm {α β : Type*} (e : α ≃ β) :
    TopologicalSpace.coinduced e.symm = TopologicalSpace.induced e :=
  e.symm.induced_symm.symm

end GaloisConnection

-- constructions using the complete lattice structure
section Constructions

open TopologicalSpace

variable {α : Type u} {β : Type v}

instance inhabitedTopologicalSpace {α : Type u} : Inhabited (TopologicalSpace α) :=
  ⟨⊥⟩

instance (priority := 100) Subsingleton.uniqueTopologicalSpace [Subsingleton α] :
    Unique (TopologicalSpace α) where
  default := ⊥
  uniq t :=
    eq_bot_of_singletons_open fun x =>
      Subsingleton.set_cases (@isOpen_empty _ t) (@isOpen_univ _ t) ({x} : Set α)

instance (priority := 100) Subsingleton.discreteTopology [t : TopologicalSpace α] [Subsingleton α] :
    DiscreteTopology α :=
  ⟨Unique.eq_default t⟩

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

lemma Nat.cast_continuous {R : Type*} [NatCast R] [TopologicalSpace R] :
    Continuous (Nat.cast (R := R)) :=
  continuous_of_discreteTopology

lemma Int.cast_continuous {R : Type*} [IntCast R] [TopologicalSpace R] :
    Continuous (Int.cast (R := R)) :=
  continuous_of_discreteTopology

instance sierpinskiSpace : TopologicalSpace Prop :=
  generateFrom {{True}}

/-- See also `continuous_of_discreteTopology`, which works for `IsEmpty α`. -/
theorem continuous_empty_function [TopologicalSpace α] [TopologicalSpace β] [IsEmpty β]
    (f : α → β) : Continuous f :=
  letI := Function.isEmpty f
  continuous_of_discreteTopology

theorem le_generateFrom {t : TopologicalSpace α} {g : Set (Set α)} (h : ∀ s ∈ g, IsOpen s) :
    t ≤ generateFrom g :=
  le_generateFrom_iff_subset_isOpen.2 h

theorem induced_generateFrom_eq {α β} {b : Set (Set β)} {f : α → β} :
    (generateFrom b).induced f = generateFrom (preimage f '' b) :=
  le_antisymm (le_generateFrom <| forall_mem_image.2 fun s hs => ⟨s, GenerateOpen.basic _ hs, rfl⟩)
    (coinduced_le_iff_le_induced.1 <| le_generateFrom fun _s hs => .basic _ (mem_image_of_mem _ hs))

theorem le_induced_generateFrom {α β} [t : TopologicalSpace α] {b : Set (Set β)} {f : α → β}
    (h : ∀ a : Set β, a ∈ b → IsOpen (f ⁻¹' a)) : t ≤ induced f (generateFrom b) := by
  rw [induced_generateFrom_eq]
  apply le_generateFrom
  simp only [mem_image, and_imp, forall_apply_eq_imp_iff₂, exists_imp]
  exact h

lemma generateFrom_insert_of_generateOpen {α : Type*} {s : Set (Set α)} {t : Set α}
    (ht : GenerateOpen s t) : generateFrom (insert t s) = generateFrom s := by
  refine le_antisymm (generateFrom_anti <| subset_insert t s) (le_generateFrom ?_)
  rintro t (rfl | h)
  · exact ht
  · exact isOpen_generateFrom_of_mem h

@[simp]
lemma generateFrom_insert_univ {α : Type*} {s : Set (Set α)} :
    generateFrom (insert univ s) = generateFrom s :=
  generateFrom_insert_of_generateOpen .univ

@[simp]
lemma generateFrom_insert_empty {α : Type*} {s : Set (Set α)} :
    generateFrom (insert ∅ s) = generateFrom s := by
  rw [← sUnion_empty]
  exact generateFrom_insert_of_generateOpen (.sUnion ∅ (fun s_1 a ↦ False.elim a))

/-- This construction is left adjoint to the operation sending a topology on `α`
  to its neighborhood filter at a fixed point `a : α`. -/
def nhdsAdjoint (a : α) (f : Filter α) : TopologicalSpace α where
  IsOpen s := a ∈ s → s ∈ f
  isOpen_univ _ := univ_mem
  isOpen_inter := fun _s _t hs ht ⟨has, hat⟩ => inter_mem (hs has) (ht hat)
  isOpen_sUnion := fun _k hk ⟨u, hu, hau⟩ => mem_of_superset (hk u hu hau) (subset_sUnion_of_mem hu)

theorem gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nhds α t a := fun f t => by
  rw [le_nhds_iff]
  exact ⟨fun H s hs has => H _ has hs, fun H s has hs => H _ hs has⟩

theorem nhds_mono {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ ≤ t₂) :
    @nhds α t₁ a ≤ @nhds α t₂ a :=
  (gc_nhds a).monotone_u h

theorem le_iff_nhds {α : Type*} (t t' : TopologicalSpace α) :
    t ≤ t' ↔ ∀ x, @nhds α t x ≤ @nhds α t' x :=
  ⟨fun h _ => nhds_mono h, le_of_nhds_le_nhds⟩

theorem isOpen_singleton_nhdsAdjoint {α : Type*} {a b : α} (f : Filter α) (hb : b ≠ a) :
    IsOpen[nhdsAdjoint a f] {b} := fun h ↦
  absurd h hb.symm

theorem nhds_nhdsAdjoint_same (a : α) (f : Filter α) :
    @nhds α (nhdsAdjoint a f) a = pure a ⊔ f := by
  let _ := nhdsAdjoint a f
  apply le_antisymm
  · rintro t ⟨hat : a ∈ t, htf : t ∈ f⟩
    exact IsOpen.mem_nhds (fun _ ↦ htf) hat
  · exact sup_le (pure_le_nhds _) ((gc_nhds a).le_u_l f)

theorem nhds_nhdsAdjoint_of_ne {a b : α} (f : Filter α) (h : b ≠ a) :
    @nhds α (nhdsAdjoint a f) b = pure b :=
  let _ := nhdsAdjoint a f
  (isOpen_singleton_iff_nhds_eq_pure _).1 <| isOpen_singleton_nhdsAdjoint f h

theorem nhds_nhdsAdjoint [DecidableEq α] (a : α) (f : Filter α) :
    @nhds α (nhdsAdjoint a f) = update pure a (pure a ⊔ f) :=
  eq_update_iff.2 ⟨nhds_nhdsAdjoint_same .., fun _ ↦ nhds_nhdsAdjoint_of_ne _⟩

theorem le_nhdsAdjoint_iff' {a : α} {f : Filter α} {t : TopologicalSpace α} :
    t ≤ nhdsAdjoint a f ↔ @nhds α t a ≤ pure a ⊔ f ∧ ∀ b ≠ a, @nhds α t b = pure b := by
  classical
  simp_rw [le_iff_nhds, nhds_nhdsAdjoint, forall_update_iff, (pure_le_nhds _).ge_iff_eq']

theorem le_nhdsAdjoint_iff {α : Type*} (a : α) (f : Filter α) (t : TopologicalSpace α) :
    t ≤ nhdsAdjoint a f ↔ @nhds α t a ≤ pure a ⊔ f ∧ ∀ b ≠ a, IsOpen[t] {b} := by
  simp only [le_nhdsAdjoint_iff', @isOpen_singleton_iff_nhds_eq_pure α t]

theorem nhds_iInf {ι : Sort*} {t : ι → TopologicalSpace α} {a : α} :
    @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a :=
  (gc_nhds a).u_iInf

theorem nhds_sInf {s : Set (TopologicalSpace α)} {a : α} :
    @nhds α (sInf s) a = ⨅ t ∈ s, @nhds α t a :=
  (gc_nhds a).u_sInf

-- Porting note: type error without `b₁ := t₁`
theorem nhds_inf {t₁ t₂ : TopologicalSpace α} {a : α} :
    @nhds α (t₁ ⊓ t₂) a = @nhds α t₁ a ⊓ @nhds α t₂ a :=
  (gc_nhds a).u_inf (b₁ := t₁)

theorem nhds_top {a : α} : @nhds α ⊤ a = ⊤ :=
  (gc_nhds a).u_top

theorem isOpen_sup {t₁ t₂ : TopologicalSpace α} {s : Set α} :
    IsOpen[t₁ ⊔ t₂] s ↔ IsOpen[t₁] s ∧ IsOpen[t₂] s :=
  Iff.rfl

/-- In the trivial topology no points are separable.

The corresponding `bot` lemma is handled more generally by `inseparable_iff_eq`. -/
@[simp]
theorem inseparable_top (x y : α) : @Inseparable α ⊤ x y := nhds_top.trans nhds_top.symm

theorem TopologicalSpace.eq_top_iff_forall_inseparable {t : TopologicalSpace α} :
    t = ⊤ ↔ (∀ x y : α, Inseparable x y) where
  mp h := h ▸ inseparable_top
  mpr h := ext_nhds fun x => nhds_top ▸ top_unique fun _ hs a => mem_of_mem_nhds <| h x a ▸ hs

theorem TopologicalSpace.ne_top_iff_exists_not_inseparable {t : TopologicalSpace α} :
    t ≠ ⊤ ↔ ∃ x y : α, ¬Inseparable x y := by
  simpa using eq_top_iff_forall_inseparable.not

open TopologicalSpace

variable {γ : Type*} {f : α → β} {ι : Sort*}

theorem continuous_iff_coinduced_le {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace β} :
    Continuous[t₁, t₂] f ↔ coinduced f t₁ ≤ t₂ :=
  continuous_def

theorem continuous_iff_le_induced {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace β} :
    Continuous[t₁, t₂] f ↔ t₁ ≤ induced f t₂ :=
  Iff.trans continuous_iff_coinduced_le (gc_coinduced_induced f _ _)

lemma continuous_generateFrom_iff {t : TopologicalSpace α} {b : Set (Set β)} :
    Continuous[t, generateFrom b] f ↔ ∀ s ∈ b, IsOpen (f ⁻¹' s) := by
  rw [continuous_iff_coinduced_le, le_generateFrom_iff_subset_isOpen]
  simp only [isOpen_coinduced, preimage_id', subset_def, mem_setOf]

@[continuity, fun_prop]
theorem continuous_induced_dom {t : TopologicalSpace β} : Continuous[induced f t, t] f :=
  continuous_iff_le_induced.2 le_rfl

theorem continuous_induced_rng {g : γ → α} {t₂ : TopologicalSpace β} {t₁ : TopologicalSpace γ} :
    Continuous[t₁, induced f t₂] g ↔ Continuous[t₁, t₂] (f ∘ g) := by
  simp only [continuous_iff_le_induced, induced_compose]

theorem continuous_coinduced_rng {t : TopologicalSpace α} :
    Continuous[t, coinduced f t] f :=
  continuous_iff_coinduced_le.2 le_rfl

theorem continuous_coinduced_dom {g : β → γ} {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace γ} :
    Continuous[coinduced f t₁, t₂] g ↔ Continuous[t₁, t₂] (g ∘ f) := by
  simp only [continuous_iff_coinduced_le, coinduced_compose]

theorem continuous_le_dom {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} (h₁ : t₂ ≤ t₁)
    (h₂ : Continuous[t₁, t₃] f) : Continuous[t₂, t₃] f := by
  rw [continuous_iff_le_induced] at h₂ ⊢
  exact le_trans h₁ h₂

theorem continuous_le_rng {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β} (h₁ : t₂ ≤ t₃)
    (h₂ : Continuous[t₁, t₂] f) : Continuous[t₁, t₃] f := by
  rw [continuous_iff_coinduced_le] at h₂ ⊢
  exact le_trans h₂ h₁

theorem continuous_sup_dom {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} :
    Continuous[t₁ ⊔ t₂, t₃] f ↔ Continuous[t₁, t₃] f ∧ Continuous[t₂, t₃] f := by
  simp only [continuous_iff_le_induced, sup_le_iff]

theorem continuous_sup_rng_left {t₁ : TopologicalSpace α} {t₃ t₂ : TopologicalSpace β} :
    Continuous[t₁, t₂] f → Continuous[t₁, t₂ ⊔ t₃] f :=
  continuous_le_rng le_sup_left

theorem continuous_sup_rng_right {t₁ : TopologicalSpace α} {t₃ t₂ : TopologicalSpace β} :
    Continuous[t₁, t₃] f → Continuous[t₁, t₂ ⊔ t₃] f :=
  continuous_le_rng le_sup_right

theorem continuous_sSup_dom {T : Set (TopologicalSpace α)} {t₂ : TopologicalSpace β} :
    Continuous[sSup T, t₂] f ↔ ∀ t ∈ T, Continuous[t, t₂] f := by
  simp only [continuous_iff_le_induced, sSup_le_iff]

theorem continuous_sSup_rng {t₁ : TopologicalSpace α} {t₂ : Set (TopologicalSpace β)}
    {t : TopologicalSpace β} (h₁ : t ∈ t₂) (hf : Continuous[t₁, t] f) :
    Continuous[t₁, sSup t₂] f :=
  continuous_iff_coinduced_le.2 <| le_sSup_of_le h₁ <| continuous_iff_coinduced_le.1 hf

theorem continuous_iSup_dom {t₁ : ι → TopologicalSpace α} {t₂ : TopologicalSpace β} :
    Continuous[iSup t₁, t₂] f ↔ ∀ i, Continuous[t₁ i, t₂] f := by
  simp only [continuous_iff_le_induced, iSup_le_iff]

theorem continuous_iSup_rng {t₁ : TopologicalSpace α} {t₂ : ι → TopologicalSpace β} {i : ι}
    (h : Continuous[t₁, t₂ i] f) : Continuous[t₁, iSup t₂] f :=
  continuous_sSup_rng ⟨i, rfl⟩ h

theorem continuous_inf_rng {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β} :
    Continuous[t₁, t₂ ⊓ t₃] f ↔ Continuous[t₁, t₂] f ∧ Continuous[t₁, t₃] f := by
  simp only [continuous_iff_coinduced_le, le_inf_iff]

theorem continuous_inf_dom_left {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} :
    Continuous[t₁, t₃] f → Continuous[t₁ ⊓ t₂, t₃] f :=
  continuous_le_dom inf_le_left

theorem continuous_inf_dom_right {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} :
    Continuous[t₂, t₃] f → Continuous[t₁ ⊓ t₂, t₃] f :=
  continuous_le_dom inf_le_right

theorem continuous_sInf_dom {t₁ : Set (TopologicalSpace α)} {t₂ : TopologicalSpace β}
    {t : TopologicalSpace α} (h₁ : t ∈ t₁) :
    Continuous[t, t₂] f → Continuous[sInf t₁, t₂] f :=
  continuous_le_dom <| sInf_le h₁

theorem continuous_sInf_rng {t₁ : TopologicalSpace α} {T : Set (TopologicalSpace β)} :
    Continuous[t₁, sInf T] f ↔ ∀ t ∈ T, Continuous[t₁, t] f := by
  simp only [continuous_iff_coinduced_le, le_sInf_iff]

theorem continuous_iInf_dom {t₁ : ι → TopologicalSpace α} {t₂ : TopologicalSpace β} {i : ι} :
    Continuous[t₁ i, t₂] f → Continuous[iInf t₁, t₂] f :=
  continuous_le_dom <| iInf_le _ _

theorem continuous_iInf_rng {t₁ : TopologicalSpace α} {t₂ : ι → TopologicalSpace β} :
    Continuous[t₁, iInf t₂] f ↔ ∀ i, Continuous[t₁, t₂ i] f := by
  simp only [continuous_iff_coinduced_le, le_iInf_iff]

@[continuity, fun_prop]
theorem continuous_bot {t : TopologicalSpace β} : Continuous[⊥, t] f :=
  continuous_iff_le_induced.2 bot_le

@[continuity, fun_prop]
theorem continuous_top {t : TopologicalSpace α} : Continuous[t, ⊤] f :=
  continuous_iff_coinduced_le.2 le_top

theorem continuous_id_iff_le {t t' : TopologicalSpace α} : Continuous[t, t'] id ↔ t ≤ t' :=
  @continuous_def _ _ t t' id

theorem continuous_id_of_le {t t' : TopologicalSpace α} (h : t ≤ t') : Continuous[t, t'] id :=
  continuous_id_iff_le.2 h

-- 𝓝 in the induced topology
theorem mem_nhds_induced [T : TopologicalSpace α] (f : β → α) (a : β) (s : Set β) :
    s ∈ @nhds β (TopologicalSpace.induced f T) a ↔ ∃ u ∈ 𝓝 (f a), f ⁻¹' u ⊆ s := by
  letI := T.induced f
  simp_rw [mem_nhds_iff, isOpen_induced_iff]
  constructor
  · rintro ⟨u, usub, ⟨v, openv, rfl⟩, au⟩
    exact ⟨v, ⟨v, Subset.rfl, openv, au⟩, usub⟩
  · rintro ⟨u, ⟨v, vsubu, openv, amem⟩, finvsub⟩
    exact ⟨f ⁻¹' v, (Set.preimage_mono vsubu).trans finvsub, ⟨⟨v, openv, rfl⟩, amem⟩⟩

theorem nhds_induced [T : TopologicalSpace α] (f : β → α) (a : β) :
    @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a)) := by
  ext s
  rw [mem_nhds_induced, mem_comap]

theorem induced_iff_nhds_eq [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : β → α) :
    tβ = tα.induced f ↔ ∀ b, 𝓝 b = comap f (𝓝 <| f b) := by
  simp only [ext_iff_nhds, nhds_induced]

theorem map_nhds_induced_of_surjective [T : TopologicalSpace α] {f : β → α} (hf : Surjective f)
    (a : β) : map f (@nhds β (TopologicalSpace.induced f T) a) = 𝓝 (f a) := by
  rw [nhds_induced, map_comap_of_surjective hf]

theorem continuous_nhdsAdjoint_dom [TopologicalSpace β] {f : α → β} {a : α} {l : Filter α} :
    Continuous[nhdsAdjoint a l, _] f ↔ Tendsto f l (𝓝 (f a)) := by
  simp_rw [continuous_iff_le_induced, gc_nhds _ _, nhds_induced, tendsto_iff_comap]

theorem coinduced_nhdsAdjoint (f : α → β) (a : α) (l : Filter α) :
    coinduced f (nhdsAdjoint a l) = nhdsAdjoint (f a) (map f l) :=
  eq_of_forall_ge_iff fun _ ↦ by
    rw [gc_nhds, ← continuous_iff_coinduced_le, continuous_nhdsAdjoint_dom, Tendsto]

end Constructions

section Induced

open TopologicalSpace

variable {α : Type*} {β : Type*}
variable [t : TopologicalSpace β] {f : α → β}

theorem isOpen_induced_eq {s : Set α} :
    IsOpen[induced f t] s ↔ s ∈ preimage f '' { s | IsOpen s } :=
  Iff.rfl

theorem isOpen_induced {s : Set β} (h : IsOpen s) : IsOpen[induced f t] (f ⁻¹' s) :=
  ⟨s, h, rfl⟩

theorem isClosed_induced {s : Set β} (h : IsClosed s) : IsClosed[induced f t] (f ⁻¹' s) := by
  simp_rw [← isOpen_compl_iff]
  exact isOpen_induced h.isOpen_compl

theorem map_nhds_induced_eq (a : α) : map f (@nhds α (induced f t) a) = 𝓝[range f] f a := by
  rw [nhds_induced, Filter.map_comap, nhdsWithin]

theorem map_nhds_induced_of_mem {a : α} (h : range f ∈ 𝓝 (f a)) :
    map f (@nhds α (induced f t) a) = 𝓝 (f a) := by rw [nhds_induced, Filter.map_comap_of_mem h]

theorem closure_induced {f : α → β} {a : α} {s : Set α} :
    a ∈ @closure α (t.induced f) s ↔ f a ∈ closure (f '' s) := by
  simp only [mem_closure_iff_frequently, nhds_induced, frequently_comap, mem_image, and_comm]

theorem isClosed_induced_iff' {f : α → β} {s : Set α} :
    IsClosed[t.induced f] s ↔ ∀ a, f a ∈ closure (f '' s) → a ∈ s := by
  simp only [← closure_subset_iff_isClosed, subset_def, closure_induced]

end Induced

section Sierpinski

variable {α : Type*}

@[simp]
theorem isOpen_singleton_true : IsOpen ({True} : Set Prop) :=
  TopologicalSpace.GenerateOpen.basic _ (mem_singleton _)

@[simp]
theorem nhds_true : 𝓝 True = pure True :=
  le_antisymm (le_pure_iff.2 <| isOpen_singleton_true.mem_nhds <| mem_singleton _) (pure_le_nhds _)

@[simp]
theorem nhds_false : 𝓝 False = ⊤ :=
  TopologicalSpace.nhds_generateFrom.trans <| by simp [@and_comm (_ ∈ _)]

theorem tendsto_nhds_true {l : Filter α} {p : α → Prop} :
    Tendsto p l (𝓝 True) ↔ ∀ᶠ x in l, p x := by simp

theorem tendsto_nhds_Prop {l : Filter α} {p : α → Prop} {q : Prop} :
    Tendsto p l (𝓝 q) ↔ (q → ∀ᶠ x in l, p x) := by
  by_cases q <;> simp [*]

variable [TopologicalSpace α]

theorem continuous_Prop {p : α → Prop} : Continuous p ↔ IsOpen { x | p x } := by
  simp only [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_Prop, isOpen_iff_mem_nhds]; rfl

theorem isOpen_iff_continuous_mem {s : Set α} : IsOpen s ↔ Continuous (· ∈ s) :=
  continuous_Prop.symm

end Sierpinski

section iInf

open TopologicalSpace

variable {α : Type u} {ι : Sort v}

theorem generateFrom_union (a₁ a₂ : Set (Set α)) :
    generateFrom (a₁ ∪ a₂) = generateFrom a₁ ⊓ generateFrom a₂ :=
  (gc_generateFrom α).u_inf

theorem setOf_isOpen_sup (t₁ t₂ : TopologicalSpace α) :
    { s | IsOpen[t₁ ⊔ t₂] s } = { s | IsOpen[t₁] s } ∩ { s | IsOpen[t₂] s } :=
  rfl

theorem generateFrom_iUnion {f : ι → Set (Set α)} :
    generateFrom (⋃ i, f i) = ⨅ i, generateFrom (f i) :=
  (gc_generateFrom α).u_iInf

theorem setOf_isOpen_iSup {t : ι → TopologicalSpace α} :
    { s | IsOpen[⨆ i, t i] s } = ⋂ i, { s | IsOpen[t i] s } :=
  (gc_generateFrom α).l_iSup

theorem generateFrom_sUnion {S : Set (Set (Set α))} :
    generateFrom (⋃₀ S) = ⨅ s ∈ S, generateFrom s :=
  (gc_generateFrom α).u_sInf

theorem setOf_isOpen_sSup {T : Set (TopologicalSpace α)} :
    { s | IsOpen[sSup T] s } = ⋂ t ∈ T, { s | IsOpen[t] s } :=
  (gc_generateFrom α).l_sSup

theorem generateFrom_union_isOpen (a b : TopologicalSpace α) :
    generateFrom ({ s | IsOpen[a] s } ∪ { s | IsOpen[b] s }) = a ⊓ b :=
  (gciGenerateFrom α).u_inf_l _ _

theorem generateFrom_iUnion_isOpen (f : ι → TopologicalSpace α) :
    generateFrom (⋃ i, { s | IsOpen[f i] s }) = ⨅ i, f i :=
  (gciGenerateFrom α).u_iInf_l _

theorem generateFrom_inter (a b : TopologicalSpace α) :
    generateFrom ({ s | IsOpen[a] s } ∩ { s | IsOpen[b] s }) = a ⊔ b :=
  (gciGenerateFrom α).u_sup_l _ _

theorem generateFrom_iInter (f : ι → TopologicalSpace α) :
    generateFrom (⋂ i, { s | IsOpen[f i] s }) = ⨆ i, f i :=
  (gciGenerateFrom α).u_iSup_l _

theorem generateFrom_iInter_of_generateFrom_eq_self (f : ι → Set (Set α))
    (hf : ∀ i, { s | IsOpen[generateFrom (f i)] s } = f i) :
    generateFrom (⋂ i, f i) = ⨆ i, generateFrom (f i) :=
  (gciGenerateFrom α).u_iSup_of_lu_eq_self f hf

variable {t : ι → TopologicalSpace α}

theorem isOpen_iSup_iff {s : Set α} : IsOpen[⨆ i, t i] s ↔ ∀ i, IsOpen[t i] s :=
  show s ∈ {s | IsOpen[iSup t] s} ↔ s ∈ { x : Set α | ∀ i : ι, IsOpen[t i] x } by
    simp [setOf_isOpen_iSup]

theorem isOpen_sSup_iff {s : Set α} {T : Set (TopologicalSpace α)} :
    IsOpen[sSup T] s ↔ ∀ t ∈ T, IsOpen[t] s := by
  simp only [sSup_eq_iSup, isOpen_iSup_iff]

theorem isClosed_iSup_iff {s : Set α} : IsClosed[⨆ i, t i] s ↔ ∀ i, IsClosed[t i] s := by
  simp only [← @isOpen_compl_iff _ _ (⨆ i, t i), ← @isOpen_compl_iff _ _ (t _), isOpen_iSup_iff]

theorem isClosed_sSup_iff {s : Set α} {T : Set (TopologicalSpace α)} :
    IsClosed[sSup T] s ↔ ∀ t ∈ T, IsClosed[t] s := by
  simp only [sSup_eq_iSup, isClosed_iSup_iff]

end iInf
