/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.Separation.SeparatedNhds
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Bases
public import Mathlib.Tactic.StacksAttribute

/-!
# Separation properties of topological spaces

This file defines some of the weaker separation axioms (under the Kolmogorov classification),
notably T₀, R₀, T₁ and R₁ spaces. For T₂ (Hausdorff) spaces and other stronger
conditions, see the file `Mathlib/Topology/Separation/Hausdorff.lean`.

## Main definitions

* `SeparatedNhds`: Two `Set`s are separated by neighbourhoods if they are contained in disjoint
  open sets.
* `HasSeparatingCover`: A set has a countable cover that can be used with
  `hasSeparatingCovers_iff_separatedNhds` to witness when two `Set`s have `SeparatedNhds`.
* `T0Space`: A T₀/Kolmogorov space is a space where, for every two points `x ≠ y`,
  there is an open set that contains one, but not the other.
* `R0Space`: An R₀ space (sometimes called a *symmetric space*) is a topological space
  such that the `Specializes` relation is symmetric.
* `T1Space`: A T₁/Fréchet space is a space where every singleton set is closed.
  This is equivalent to, for every pair `x ≠ y`, there existing an open set containing `x`
  but not `y` (`t1Space_iff_exists_open` shows that these conditions are equivalent.)
  T₁ iff T₀ and R₀.
* `R1Space`: An R₁/preregular space is a space where any two topologically distinguishable points
  have disjoint neighbourhoods. R₁ implies R₀.

Note that `mathlib` adopts the modern convention that `m ≤ n` if and only if `T_m → T_n`, but
occasionally the literature swaps definitions for e.g. T₃ and regular.

## Main results

### T₀ spaces

* `IsClosed.exists_closed_singleton`: Given a closed set `S` in a compact T₀ space,
  there is some `x ∈ S` such that `{x}` is closed.
* `exists_isOpen_singleton_of_isOpen_finite`: Given an open finite set `S` in a T₀ space,
  there is some `x ∈ S` such that `{x}` is open.

### T₁ spaces

* `isClosedMap_const`: The constant map is a closed map.
* `Finite.instDiscreteTopology`: A finite T₁ space must have the discrete topology.

## References

* <https://en.wikipedia.org/wiki/Separation_axiom>
* [Willard's *General Topology*][zbMATH02107988]
-/

@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

/-- A T₀ space, also known as a Kolmogorov space, is a topological space such that for every pair
`x ≠ y`, there is an open set containing one but not the other. We formulate the definition in terms
of the `Inseparable` relation. -/
@[stacks 004X "(2)"]
class T0Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Two inseparable points in a T₀ space are equal. -/
  t0 : ∀ ⦃x y : X⦄, Inseparable x y → x = y

theorem t0Space_iff_inseparable (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ ∀ x y : X, Inseparable x y → x = y :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem t0Space_iff_not_inseparable (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Pairwise fun x y : X => ¬Inseparable x y := by
  simp only [t0Space_iff_inseparable, Ne, not_imp_not, Pairwise]

theorem Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x y) : x = y :=
  T0Space.t0 h

/-- A topology inducing map from a T₀ space is injective. -/
protected theorem Topology.IsInducing.injective [TopologicalSpace Y] [T0Space X] {f : X → Y}
    (hf : IsInducing f) : Injective f := fun _ _ h =>
  (hf.inseparable_iff.1 <| .of_eq h).eq

/-- A topology inducing map from a T₀ space is a topological embedding. -/
protected theorem Topology.IsInducing.isEmbedding [TopologicalSpace Y] [T0Space X] {f : X → Y}
    (hf : IsInducing f) : IsEmbedding f :=
  ⟨hf, hf.injective⟩

lemma isEmbedding_iff_isInducing [TopologicalSpace Y] [T0Space X] {f : X → Y} :
    IsEmbedding f ↔ IsInducing f :=
  ⟨IsEmbedding.isInducing, IsInducing.isEmbedding⟩

theorem t0Space_iff_nhds_injective (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Injective (𝓝 : X → Filter X) :=
  t0Space_iff_inseparable X

theorem nhds_injective [T0Space X] : Injective (𝓝 : X → Filter X) :=
  (t0Space_iff_nhds_injective X).1 ‹_›

theorem inseparable_iff_eq [T0Space X] {x y : X} : Inseparable x y ↔ x = y :=
  nhds_injective.eq_iff

@[simp]
theorem nhds_eq_nhds_iff [T0Space X] {a b : X} : 𝓝 a = 𝓝 b ↔ a = b :=
  nhds_injective.eq_iff

@[simp]
theorem inseparable_eq_eq [T0Space X] : Inseparable = @Eq X :=
  funext₂ fun _ _ => propext inseparable_iff_eq

theorem TopologicalSpace.IsTopologicalBasis.inseparable_iff {b : Set (Set X)}
    (hb : IsTopologicalBasis b) {x y : X} : Inseparable x y ↔ ∀ s ∈ b, (x ∈ s ↔ y ∈ s) :=
  ⟨fun h _ hs ↦ inseparable_iff_forall_isOpen.1 h _ (hb.isOpen hs),
    fun h ↦ hb.nhds_hasBasis.eq_of_same_basis <| by
      convert hb.nhds_hasBasis using 2
      exact and_congr_right (h _)⟩

theorem TopologicalSpace.IsTopologicalBasis.eq_iff [T0Space X] {b : Set (Set X)}
    (hb : IsTopologicalBasis b) {x y : X} : x = y ↔ ∀ s ∈ b, (x ∈ s ↔ y ∈ s) :=
  inseparable_iff_eq.symm.trans hb.inseparable_iff

theorem t0Space_iff_exists_isOpen_xor_mem (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Pairwise fun x y => ∃ U : Set X, IsOpen U ∧ Xor (x ∈ U) (y ∈ U) := by
  simp only [t0Space_iff_not_inseparable, xor_iff_not_iff, not_forall, exists_prop,
    inseparable_iff_forall_isOpen, Pairwise]

@[deprecated (since := "2026-04-24")] alias t0Space_iff_exists_isOpen_xor'_mem :=
  t0Space_iff_exists_isOpen_xor_mem

theorem exists_isOpen_xor_mem [T0Space X] {x y : X} (h : x ≠ y) :
    ∃ U : Set X, IsOpen U ∧ Xor (x ∈ U) (y ∈ U) :=
  (t0Space_iff_exists_isOpen_xor_mem X).1 ‹_› h

@[deprecated (since := "2026-04-24")] alias exists_isOpen_xor'_mem :=
  exists_isOpen_xor_mem

/-- Specialization forms a partial order on a t0 topological space. -/
@[instance_reducible]
def specializationOrder (X) [TopologicalSpace X] [T0Space X] : PartialOrder X :=
  { specializationPreorder X, PartialOrder.lift (OrderDual.toDual ∘ 𝓝) nhds_injective with }

instance SeparationQuotient.instT0Space : T0Space (SeparationQuotient X) :=
  ⟨fun x y => Quotient.inductionOn₂' x y fun _ _ h =>
    SeparationQuotient.mk_eq_mk.2 <| SeparationQuotient.isInducing_mk.inseparable_iff.1 h⟩

theorem minimal_nonempty_closed_subsingleton [T0Space X] {s : Set X} (hs : IsClosed s)
    (hmin : ∀ t, t ⊆ s → t.Nonempty → IsClosed t → t = s) : s.Subsingleton := by
  refine fun x hx y hy => of_not_not fun hxy => ?_
  rcases exists_isOpen_xor_mem hxy with ⟨U, hUo, hU⟩
  wlog h : x ∈ U ∧ y ∉ U
  · refine this hs hmin y hy x hx (Ne.symm hxy) U hUo hU.symm (hU.resolve_left h)
  obtain ⟨hxU, hyU⟩ := h
  have : s \ U = s := hmin (s \ U) diff_subset ⟨y, hy, hyU⟩ (hs.sdiff hUo)
  exact (this.symm.subset hx).2 hxU

theorem minimal_nonempty_closed_eq_singleton [T0Space X] {s : Set X} (hs : IsClosed s)
    (hne : s.Nonempty) (hmin : ∀ t, t ⊆ s → t.Nonempty → IsClosed t → t = s) : ∃ x, s = {x} :=
  exists_eq_singleton_iff_nonempty_subsingleton.2
    ⟨hne, minimal_nonempty_closed_subsingleton hs hmin⟩

/-- Given a closed set `S` in a compact T₀ space, there is some `x ∈ S` such that `{x}` is
closed. -/
theorem IsClosed.exists_closed_singleton [T0Space X] [CompactSpace X] {S : Set X}
    (hS : IsClosed S) (hne : S.Nonempty) : ∃ x : X, x ∈ S ∧ IsClosed ({x} : Set X) := by
  obtain ⟨V, Vsub, Vne, Vcls, hV⟩ := hS.exists_minimal_nonempty_closed_subset hne
  rcases minimal_nonempty_closed_eq_singleton Vcls Vne hV with ⟨x, rfl⟩
  exact ⟨x, Vsub (mem_singleton x), Vcls⟩

theorem minimal_nonempty_open_subsingleton [T0Space X] {s : Set X} (hs : IsOpen s)
    (hmin : ∀ t, t ⊆ s → t.Nonempty → IsOpen t → t = s) : s.Subsingleton := by
  refine fun x hx y hy => of_not_not fun hxy => ?_
  rcases exists_isOpen_xor_mem hxy with ⟨U, hUo, hU⟩
  wlog h : x ∈ U ∧ y ∉ U
  · exact this hs hmin y hy x hx (Ne.symm hxy) U hUo hU.symm (hU.resolve_left h)
  obtain ⟨hxU, hyU⟩ := h
  have : s ∩ U = s := hmin (s ∩ U) inter_subset_left ⟨x, hx, hxU⟩ (hs.inter hUo)
  exact hyU (this.symm.subset hy).2

theorem minimal_nonempty_open_eq_singleton [T0Space X] {s : Set X} (hs : IsOpen s)
    (hne : s.Nonempty) (hmin : ∀ t, t ⊆ s → t.Nonempty → IsOpen t → t = s) : ∃ x, s = {x} :=
  exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨hne, minimal_nonempty_open_subsingleton hs hmin⟩

/-- Given an open finite set `S` in a T₀ space, there is some `x ∈ S` such that `{x}` is open. -/
theorem exists_isOpen_singleton_of_isOpen_finite [T0Space X] {s : Set X} (hfin : s.Finite)
    (hne : s.Nonempty) (ho : IsOpen s) : ∃ x ∈ s, IsOpen ({x} : Set X) := by
  lift s to Finset X using hfin
  induction s using Finset.strongInductionOn
  rename_i s ihs
  rcases em (∃ t, t ⊂ s ∧ t.Nonempty ∧ IsOpen (t : Set X)) with (⟨t, hts, htne, hto⟩ | ht)
  · rcases ihs t hts htne hto with ⟨x, hxt, hxo⟩
    exact ⟨x, hts.1 hxt, hxo⟩
  · -- Porting note: was `rcases minimal_nonempty_open_eq_singleton ho hne _ with ⟨x, hx⟩`
    --               https://github.com/leanprover-community/batteries/issues/116
    rsuffices ⟨x, hx⟩ : ∃ x, (s : Set X) = {x}
    · exact ⟨x, hx.symm ▸ rfl, hx ▸ ho⟩
    refine minimal_nonempty_open_eq_singleton ho hne ?_
    refine fun t hts htne hto => of_not_not fun hts' => ht ?_
    lift t to Finset X using s.finite_toSet.subset hts
    exact ⟨t, ssubset_iff_subset_ne.2 ⟨hts, mt Finset.coe_inj.2 hts'⟩, htne, hto⟩

theorem exists_open_singleton_of_finite [T0Space X] [Finite X] [Nonempty X] :
    ∃ x : X, IsOpen ({x} : Set X) :=
  let ⟨x, _, h⟩ := exists_isOpen_singleton_of_isOpen_finite (Set.toFinite _)
    univ_nonempty isOpen_univ
  ⟨x, h⟩

theorem t0Space_of_injective_of_continuous [TopologicalSpace Y] {f : X → Y}
    (hf : Function.Injective f) (hf' : Continuous f) [T0Space Y] : T0Space X :=
  ⟨fun _ _ h => hf <| (h.map hf').eq⟩

protected theorem Topology.IsEmbedding.t0Space [TopologicalSpace Y] [T0Space Y] {f : X → Y}
    (hf : IsEmbedding f) : T0Space X :=
  t0Space_of_injective_of_continuous hf.injective hf.continuous

protected theorem Homeomorph.t0Space [TopologicalSpace Y] [T0Space X] (h : X ≃ₜ Y) : T0Space Y :=
  h.symm.isEmbedding.t0Space

@[stacks 0B31 "part 1"]
instance Subtype.t0Space [T0Space X] {p : X → Prop} : T0Space (Subtype p) :=
  IsEmbedding.subtypeVal.t0Space

theorem t0Space_iff_or_notMem_closure (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Pairwise fun a b : X => a ∉ closure ({b} : Set X) ∨ b ∉ closure ({a} : Set X) := by
  simp only [t0Space_iff_not_inseparable, inseparable_iff_mem_closure, not_and_or]

instance Prod.instT0Space [TopologicalSpace Y] [T0Space X] [T0Space Y] : T0Space (X × Y) :=
  ⟨fun _ _ h => Prod.ext (h.map continuous_fst).eq (h.map continuous_snd).eq⟩

instance Pi.instT0Space {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, T0Space (X i)] :
    T0Space (∀ i, X i) :=
  ⟨fun _ _ h => funext fun i => (h.map (continuous_apply i)).eq⟩

instance ULift.instT0Space [T0Space X] : T0Space (ULift X) := IsEmbedding.uliftDown.t0Space

theorem T0Space.of_cover (h : ∀ x y, Inseparable x y → ∃ s : Set X, x ∈ s ∧ y ∈ s ∧ T0Space s) :
    T0Space X := by
  refine ⟨fun x y hxy => ?_⟩
  rcases h x y hxy with ⟨s, hxs, hys, hs⟩
  lift x to s using hxs; lift y to s using hys
  rw [← subtype_inseparable_iff] at hxy
  exact congr_arg Subtype.val hxy.eq

theorem T0Space.of_open_cover (h : ∀ x, ∃ s : Set X, x ∈ s ∧ IsOpen s ∧ T0Space s) : T0Space X :=
  T0Space.of_cover fun x _ hxy =>
    let ⟨s, hxs, hso, hs⟩ := h x
    ⟨s, hxs, (hxy.mem_open_iff hso).1 hxs, hs⟩

/-- A topological space is called an R₀ space, if `Specializes` relation is symmetric.

In other words, given two points `x y : X`,
if every neighborhood of `y` contains `x`, then every neighborhood of `x` contains `y`. -/
@[mk_iff]
class R0Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- In an R₀ space, the `Specializes` relation is symmetric. -/
  specializes_symmetric : Symmetric (Specializes : X → X → Prop)

export R0Space (specializes_symmetric)

section R0Space

variable [R0Space X] {x y : X}

/-- In an R₀ space, the `Specializes` relation is symmetric, dot notation version. -/
theorem Specializes.symm (h : x ⤳ y) : y ⤳ x := specializes_symmetric h

/-- In an R₀ space, the `Specializes` relation is symmetric, `Iff` version. -/
theorem specializes_comm : x ⤳ y ↔ y ⤳ x := ⟨Specializes.symm, Specializes.symm⟩

/-- In an R₀ space, `Specializes` is equivalent to `Inseparable`. -/
theorem specializes_iff_inseparable : x ⤳ y ↔ Inseparable x y :=
  ⟨fun h ↦ h.antisymm h.symm, Inseparable.specializes⟩

/-- In an R₀ space, `Specializes` implies `Inseparable`. -/
alias ⟨Specializes.inseparable, _⟩ := specializes_iff_inseparable

theorem Topology.IsInducing.r0Space [TopologicalSpace Y] {f : Y → X} (hf : IsInducing f) :
    R0Space Y where
  specializes_symmetric a b := by
    simpa only [← hf.specializes_iff] using Specializes.symm

instance {p : X → Prop} : R0Space {x // p x} := IsInducing.subtypeVal.r0Space

instance [TopologicalSpace Y] [R0Space Y] : R0Space (X × Y) where
  specializes_symmetric _ _ h := h.fst.symm.prod h.snd.symm

instance {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, R0Space (X i)] :
    R0Space (∀ i, X i) where
  specializes_symmetric _ _ h := specializes_pi.2 fun i ↦ (specializes_pi.1 h i).symm

lemma R0Space.closure_singleton (x : X) : closure {x} = (𝓝 x).ker := by
  ext; simp [ker_nhds_eq_specializes, ← specializes_iff_mem_closure, specializes_comm]

/-- In an R₀ space, the closure of a singleton is a compact set. -/
theorem isCompact_closure_singleton : IsCompact (closure {x}) := by
  refine isCompact_of_finite_subcover fun U hUo hxU ↦ ?_
  obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := mem_iUnion.1 <| hxU <| subset_closure rfl
  refine ⟨{i}, fun y hy ↦ ?_⟩
  rw [← specializes_iff_mem_closure, specializes_comm] at hy
  simpa using hy.mem_open (hUo i) hi

theorem Filter.coclosedCompact_le_cofinite : coclosedCompact X ≤ cofinite :=
  le_cofinite_iff_compl_singleton_mem.2 fun _ ↦
    compl_mem_coclosedCompact.2 isCompact_closure_singleton

variable (X) in
/-- In an R₀ space, relatively compact sets form a bornology.
Its cobounded filter is `Filter.coclosedCompact`.
See also `Bornology.inCompact` the bornology of sets contained in a compact set. -/
@[implicit_reducible]
def Bornology.relativelyCompact : Bornology X where
  cobounded := Filter.coclosedCompact X
  le_cofinite := Filter.coclosedCompact_le_cofinite

theorem Bornology.relativelyCompact.isBounded_iff {s : Set X} :
    @Bornology.IsBounded _ (Bornology.relativelyCompact X) s ↔ IsCompact (closure s) :=
  compl_mem_coclosedCompact

/-- In an R₀ space, the closure of a finite set is a compact set. -/
theorem Set.Finite.isCompact_closure {s : Set X} (hs : s.Finite) : IsCompact (closure s) :=
  let _ : Bornology X := .relativelyCompact X
  Bornology.relativelyCompact.isBounded_iff.1 hs.isBounded

end R0Space

/-- A T₁ space, also known as a Fréchet space, is a topological space
  where every singleton set is closed. Equivalently, for every pair
  `x ≠ y`, there is an open set containing `x` and not `y`. -/
class T1Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- A singleton in a T₁ space is a closed set. -/
  t1 : ∀ x, IsClosed ({x} : Set X)

theorem isClosed_singleton [T1Space X] {x : X} : IsClosed ({x} : Set X) :=
  T1Space.t1 x

theorem isOpen_compl_singleton [T1Space X] {x : X} : IsOpen ({x}ᶜ : Set X) :=
  isClosed_singleton.isOpen_compl

theorem isOpen_ne [T1Space X] {x : X} : IsOpen { y | y ≠ x } :=
  isOpen_compl_singleton

@[to_additive]
theorem Continuous.isOpen_mulSupport [T1Space X] [One X] [TopologicalSpace Y] {f : Y → X}
    (hf : Continuous f) : IsOpen (mulSupport f) :=
  isOpen_ne.preimage hf

theorem Ne.nhdsWithin_compl_singleton [T1Space X] {x y : X} (h : x ≠ y) : 𝓝[{y}ᶜ] x = 𝓝 x :=
  isOpen_ne.nhdsWithin_eq h

theorem Ne.nhdsWithin_diff_singleton [T1Space X] {x y : X} (h : x ≠ y) (s : Set X) :
    𝓝[s \ {y}] x = 𝓝[s] x := by
  rw [diff_eq, inter_comm, nhdsWithin_inter_of_mem]
  exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds h)

lemma nhdsWithin_compl_singleton_le [T1Space X] (x y : X) : 𝓝[{x}ᶜ] x ≤ 𝓝[{y}ᶜ] x := by
  rcases eq_or_ne x y with rfl | hy
  · exact Eq.le rfl
  · rw [Ne.nhdsWithin_compl_singleton hy]
    exact nhdsWithin_le_nhds

theorem isOpen_setOf_eventually_nhdsWithin [T1Space X] {p : X → Prop} :
    IsOpen { x | ∀ᶠ y in 𝓝[≠] x, p y } := by
  refine isOpen_iff_mem_nhds.mpr fun a ha => ?_
  filter_upwards [eventually_nhds_nhdsWithin.mpr ha] with b hb
  rcases eq_or_ne a b with rfl | h
  · exact hb
  · rw [h.symm.nhdsWithin_compl_singleton] at hb
    exact hb.filter_mono nhdsWithin_le_nhds

@[simp] protected lemma Set.Finite.isClosed [T1Space X] {s : Set X} (hs : s.Finite) :
    IsClosed s := by
  rw [← biUnion_of_singleton s]
  exact hs.isClosed_biUnion fun i _ => isClosed_singleton

theorem TopologicalSpace.IsTopologicalBasis.exists_mem_of_ne [T1Space X] {b : Set (Set X)}
    (hb : IsTopologicalBasis b) {x y : X} (h : x ≠ y) : ∃ a ∈ b, x ∈ a ∧ y ∉ a := by
  rcases hb.isOpen_iff.1 isOpen_ne x h with ⟨a, ab, xa, ha⟩
  exact ⟨a, ab, xa, fun h => ha h rfl⟩

protected theorem Finset.isClosed [T1Space X] (s : Finset X) : IsClosed (s : Set X) :=
  s.finite_toSet.isClosed

theorem t1Space_TFAE (X : Type u) [TopologicalSpace X] :
    List.TFAE [T1Space X,
      ∀ x, IsClosed ({ x } : Set X),
      ∀ x, IsOpen ({ x }ᶜ : Set X),
      Continuous (@CofiniteTopology.of X),
      ∀ ⦃x y : X⦄, x ≠ y → {y}ᶜ ∈ 𝓝 x,
      ∀ ⦃x y : X⦄, x ≠ y → ∃ s ∈ 𝓝 x, y ∉ s,
      ∀ ⦃x y : X⦄, x ≠ y → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ y ∉ U,
      ∀ ⦃x y : X⦄, x ≠ y → Disjoint (𝓝 x) (pure y),
      ∀ ⦃x y : X⦄, x ≠ y → Disjoint (pure x) (𝓝 y),
      ∀ ⦃x y : X⦄, x ⤳ y → x = y,
      T0Space X ∧ R0Space X] := by
  tfae_have 1 ↔ 2 := ⟨fun h => h.1, fun h => ⟨h⟩⟩
  tfae_have 2 ↔ 3 := by
    simp only [isOpen_compl_iff]
  tfae_have 5 ↔ 3 := by
    refine forall_comm.trans ?_
    simp only [isOpen_iff_mem_nhds, mem_compl_iff, mem_singleton_iff]
  tfae_have 5 ↔ 6 := by
    simp only [← subset_compl_singleton_iff, exists_mem_subset_iff]
  tfae_have 5 ↔ 7 := by
    simp only [(nhds_basis_opens _).mem_iff, subset_compl_singleton_iff, and_assoc,
      and_left_comm]
  tfae_have 5 ↔ 8 := by
    simp only [← principal_singleton, disjoint_principal_right]
  tfae_have 8 ↔ 9 := forall_comm.trans (by simp only [disjoint_comm, ne_comm])
  tfae_have 1 → 4 := by
    simp only [continuous_def, CofiniteTopology.isOpen_iff']
    rintro H s (rfl | hs)
    exacts [isOpen_empty, compl_compl s ▸ (@Set.Finite.isClosed _ _ H _ hs).isOpen_compl]
  tfae_have 4 → 2 :=
    fun h x => (CofiniteTopology.isClosed_iff.2 <| Or.inr (finite_singleton _)).preimage h
  tfae_have 2 ↔ 10 := by
    simp only [← closure_subset_iff_isClosed, specializes_iff_mem_closure, subset_def,
      mem_singleton_iff, eq_comm]
  tfae_have 10 ↔ 11 :=
    ⟨fun h => ⟨⟨fun _ _ h₂ => h h₂.specializes⟩, ⟨fun _ _ h₂ => specializes_of_eq (h h₂).symm⟩⟩,
      fun ⟨_, _⟩ _ _ h => (h.antisymm h.symm).eq⟩
  tfae_finish

theorem t1Space_iff_continuous_cofinite_of : T1Space X ↔ Continuous (@CofiniteTopology.of X) :=
  (t1Space_TFAE X).out 0 3

theorem CofiniteTopology.continuous_of [T1Space X] : Continuous (@CofiniteTopology.of X) :=
  t1Space_iff_continuous_cofinite_of.mp ‹_›

theorem t1Space_iff_exists_open :
    T1Space X ↔ Pairwise fun x y => ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ y ∉ U :=
  (t1Space_TFAE X).out 0 6

theorem t1Space_iff_disjoint_pure_nhds : T1Space X ↔ ∀ ⦃x y : X⦄, x ≠ y → Disjoint (pure x) (𝓝 y) :=
  (t1Space_TFAE X).out 0 8

theorem t1Space_iff_disjoint_nhds_pure : T1Space X ↔ ∀ ⦃x y : X⦄, x ≠ y → Disjoint (𝓝 x) (pure y) :=
  (t1Space_TFAE X).out 0 7

theorem t1Space_iff_specializes_imp_eq : T1Space X ↔ ∀ ⦃x y : X⦄, x ⤳ y → x = y :=
  (t1Space_TFAE X).out 0 9

theorem t1Space_iff_t0Space_and_r0Space : T1Space X ↔ T0Space X ∧ R0Space X :=
  (t1Space_TFAE X).out 0 10

theorem disjoint_pure_nhds [T1Space X] {x y : X} (h : x ≠ y) : Disjoint (pure x) (𝓝 y) :=
  t1Space_iff_disjoint_pure_nhds.mp ‹_› h

theorem disjoint_nhds_pure [T1Space X] {x y : X} (h : x ≠ y) : Disjoint (𝓝 x) (pure y) :=
  t1Space_iff_disjoint_nhds_pure.mp ‹_› h

theorem Specializes.eq [T1Space X] {x y : X} (h : x ⤳ y) : x = y :=
  t1Space_iff_specializes_imp_eq.1 ‹_› h

theorem specializes_iff_eq [T1Space X] {x y : X} : x ⤳ y ↔ x = y :=
  ⟨Specializes.eq, fun h => h ▸ specializes_rfl⟩

@[simp] theorem specializes_eq_eq [T1Space X] : (· ⤳ ·) = @Eq X :=
  funext₂ fun _ _ => propext specializes_iff_eq

@[simp]
theorem pure_le_nhds_iff [T1Space X] {a b : X} : pure a ≤ 𝓝 b ↔ a = b :=
  specializes_iff_pure.symm.trans specializes_iff_eq

@[simp]
theorem nhds_le_nhds_iff [T1Space X] {a b : X} : 𝓝 a ≤ 𝓝 b ↔ a = b :=
  specializes_iff_eq

instance (priority := 100) [T1Space X] : R0Space X :=
  (t1Space_iff_t0Space_and_r0Space.mp ‹T1Space X›).right

instance : T1Space (CofiniteTopology X) :=
  t1Space_iff_continuous_cofinite_of.mpr continuous_id

instance (priority := 80) [T0Space X] [R0Space X] : T1Space X :=
  t1Space_iff_t0Space_and_r0Space.mpr ⟨‹T0Space X›, ‹R0Space X›⟩

theorem t1Space_antitone {X} : Antitone (@T1Space X) := fun a _ h _ =>
  @T1Space.mk _ a fun x => (T1Space.t1 x).mono h

theorem continuousWithinAt_update_of_ne [T1Space X] [DecidableEq X] [TopologicalSpace Y] {f : X → Y}
    {s : Set X} {x x' : X} {y : Y} (hne : x' ≠ x) :
    ContinuousWithinAt (Function.update f x y) s x' ↔ ContinuousWithinAt f s x' :=
  EventuallyEq.congr_continuousWithinAt
    (mem_nhdsWithin_of_mem_nhds <| mem_of_superset (isOpen_ne.mem_nhds hne) fun _y' hy' =>
      Function.update_of_ne hy' _ _)
    (Function.update_of_ne hne ..)

theorem continuousAt_update_of_ne [T1Space X] [DecidableEq X] [TopologicalSpace Y]
    {f : X → Y} {x x' : X} {y : Y} (hne : x' ≠ x) :
    ContinuousAt (Function.update f x y) x' ↔ ContinuousAt f x' := by
  simp only [← continuousWithinAt_univ, continuousWithinAt_update_of_ne hne]

theorem continuousOn_update_iff [T1Space X] [DecidableEq X] [TopologicalSpace Y] {f : X → Y}
    {s : Set X} {x : X} {y : Y} :
    ContinuousOn (Function.update f x y) s ↔
      ContinuousOn f (s \ {x}) ∧ (x ∈ s → Tendsto f (𝓝[s \ {x}] x) (𝓝 y)) := by
  rw [ContinuousOn, ← and_forall_ne x, and_comm]
  refine and_congr ⟨fun H z hz => ?_, fun H z hzx hzs => ?_⟩ (forall_congr' fun _ => ?_)
  · specialize H z hz.2 hz.1
    rw [continuousWithinAt_update_of_ne hz.2] at H
    exact H.mono diff_subset
  · rw [continuousWithinAt_update_of_ne hzx]
    refine (H z ⟨hzs, hzx⟩).mono_of_mem_nhdsWithin (inter_mem_nhdsWithin _ ?_)
    exact isOpen_ne.mem_nhds hzx
  · exact continuousWithinAt_update_same

theorem t1Space_of_injective_of_continuous [TopologicalSpace Y] {f : X → Y}
    (hf : Function.Injective f) (hf' : Continuous f) [T1Space Y] : T1Space X :=
  t1Space_iff_specializes_imp_eq.2 fun _ _ h => hf (h.map hf').eq

protected theorem Topology.IsEmbedding.t1Space [TopologicalSpace Y] [T1Space Y] {f : X → Y}
    (hf : IsEmbedding f) : T1Space X :=
  t1Space_of_injective_of_continuous hf.injective hf.continuous

protected theorem Homeomorph.t1Space [TopologicalSpace Y] [T1Space X] (h : X ≃ₜ Y) : T1Space Y :=
  h.symm.isEmbedding.t1Space

instance Subtype.t1Space {X : Type u} [TopologicalSpace X] [T1Space X] {p : X → Prop} :
    T1Space (Subtype p) :=
  IsEmbedding.subtypeVal.t1Space

instance [TopologicalSpace Y] [T1Space X] [T1Space Y] : T1Space (X × Y) :=
  ⟨fun ⟨a, b⟩ => @singleton_prod_singleton _ _ a b ▸ isClosed_singleton.prod isClosed_singleton⟩

instance {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, T1Space (X i)] :
    T1Space (∀ i, X i) :=
  ⟨fun f => univ_pi_singleton f ▸ isClosed_set_pi fun _ _ => isClosed_singleton⟩

instance ULift.instT1Space [T1Space X] : T1Space (ULift X) :=
  IsEmbedding.uliftDown.t1Space

-- see Note [lower instance priority]
instance (priority := 100) T1Space.t0Space [T1Space X] : T0Space X :=
  (t1Space_iff_t0Space_and_r0Space.mp ‹T1Space X›).left

@[simp]
theorem compl_singleton_mem_nhds_iff [T1Space X] {x y : X} : {x}ᶜ ∈ 𝓝 y ↔ y ≠ x :=
  isOpen_compl_singleton.mem_nhds_iff

theorem compl_singleton_mem_nhds [T1Space X] {x y : X} (h : y ≠ x) : {x}ᶜ ∈ 𝓝 y :=
  compl_singleton_mem_nhds_iff.mpr h

theorem closure_singleton [T1Space X] {x : X} : closure ({x} : Set X) = {x} :=
  isClosed_singleton.closure_eq

lemma Set.Subsingleton.isClosed [T1Space X] {s : Set X} (hs : s.Subsingleton) : IsClosed s := by
  rcases hs.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
  · exact isClosed_empty
  · exact isClosed_singleton

theorem Set.Subsingleton.closure_eq [T1Space X] {s : Set X} (hs : s.Subsingleton) :
    closure s = s :=
  hs.isClosed.closure_eq

theorem Set.Subsingleton.closure [T1Space X] {s : Set X} (hs : s.Subsingleton) :
    (closure s).Subsingleton := by
  rwa [hs.closure_eq]

@[simp]
theorem subsingleton_closure [T1Space X] {s : Set X} : (closure s).Subsingleton ↔ s.Subsingleton :=
  ⟨fun h => h.anti subset_closure, fun h => h.closure⟩

theorem isClosedMap_const {X Y} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y] {y : Y} :
    IsClosedMap (Function.const X y) :=
  IsClosedMap.of_nonempty fun s _ h2s => by simp_rw [const, h2s.image_const, isClosed_singleton]

lemma isClosedMap_prodMk_left [TopologicalSpace Y] [T1Space X] (x : X) :
    IsClosedMap (fun y : Y ↦ Prod.mk x y) :=
  fun _K hK ↦ Set.singleton_prod ▸ isClosed_singleton.prod hK

lemma isClosedMap_prodMk_right [TopologicalSpace Y] [T1Space Y] (y : Y) :
    IsClosedMap (fun x : X ↦ Prod.mk x y) :=
  fun _K hK ↦ Set.prod_singleton ▸ hK.prod isClosed_singleton

theorem nhdsWithin_insert_of_ne [T1Space X] {x y : X} {s : Set X} (hxy : x ≠ y) :
    𝓝[insert y s] x = 𝓝[s] x := by
  refine le_antisymm (Filter.le_def.2 fun t ht => ?_) (nhdsWithin_mono x <| subset_insert y s)
  obtain ⟨o, ho, hxo, host⟩ := mem_nhdsWithin.mp ht
  refine mem_nhdsWithin.mpr ⟨o \ {y}, ho.sdiff isClosed_singleton, ⟨hxo, hxy⟩, ?_⟩
  rw [inter_insert_of_notMem <| notMem_diff_of_mem (mem_singleton y)]
  exact (inter_subset_inter diff_subset Subset.rfl).trans host

/-- If `t` is a subset of `s`, except for one point,
then `insert x s` is a neighborhood of `x` within `t`. -/
theorem insert_mem_nhdsWithin_of_subset_insert [T1Space X] {x y : X} {s t : Set X}
    (hu : t ⊆ insert y s) : insert x s ∈ 𝓝[t] x := by
  rcases eq_or_ne x y with (rfl | h)
  · exact mem_of_superset self_mem_nhdsWithin hu
  refine nhdsWithin_mono x hu ?_
  rw [nhdsWithin_insert_of_ne h]
  exact mem_of_superset self_mem_nhdsWithin (subset_insert x s)

lemma eventuallyEq_insert [T1Space X] {s t : Set X} {x y : X} (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    (insert x s : Set X) =ᶠ[𝓝 x] (insert x t : Set X) := by
  simp_rw [eventuallyEq_set] at h ⊢
  simp_rw [← union_singleton, ← nhdsWithin_univ, ← compl_union_self {x},
    nhdsWithin_union, eventually_sup, nhdsWithin_singleton,
    eventually_pure, union_singleton, mem_insert_iff, true_or, and_true]
  filter_upwards [nhdsWithin_compl_singleton_le x y h] with y using or_congr (Iff.rfl)

@[simp]
theorem ker_nhds [T1Space X] (x : X) : (𝓝 x).ker = {x} := by
  simp [ker_nhds_eq_specializes]

theorem biInter_basis_nhds [T1Space X] {ι : Sort*} {p : ι → Prop} {s : ι → Set X} {x : X}
    (h : (𝓝 x).HasBasis p s) : ⋂ (i) (_ : p i), s i = {x} := by
  rw [← h.ker, ker_nhds]

@[simp]
theorem compl_singleton_mem_nhdsSet_iff [T1Space X] {x : X} {s : Set X} : {x}ᶜ ∈ 𝓝ˢ s ↔ x ∉ s := by
  rw [isOpen_compl_singleton.mem_nhdsSet, subset_compl_singleton_iff]

@[simp]
theorem nhdsSet_le_iff [T1Space X] {s t : Set X} : 𝓝ˢ s ≤ 𝓝ˢ t ↔ s ⊆ t := by
  refine ⟨?_, fun h => monotone_nhdsSet h⟩
  simp_rw [Filter.le_def]; intro h x hx
  specialize h {x}ᶜ
  simp_rw [compl_singleton_mem_nhdsSet_iff] at h
  by_contra hxt
  exact h hxt hx

@[simp]
theorem nhdsSet_inj_iff [T1Space X] {s t : Set X} : 𝓝ˢ s = 𝓝ˢ t ↔ s = t := by
  simp_rw [le_antisymm_iff]
  exact and_congr nhdsSet_le_iff nhdsSet_le_iff

theorem injective_nhdsSet [T1Space X] : Function.Injective (𝓝ˢ : Set X → Filter X) := fun _ _ hst =>
  nhdsSet_inj_iff.mp hst

theorem strictMono_nhdsSet [T1Space X] : StrictMono (𝓝ˢ : Set X → Filter X) :=
  monotone_nhdsSet.strictMono_of_injective injective_nhdsSet

@[simp]
theorem nhds_le_nhdsSet_iff [T1Space X] {s : Set X} {x : X} : 𝓝 x ≤ 𝓝ˢ s ↔ x ∈ s := by
  rw [← nhdsSet_singleton, nhdsSet_le_iff, singleton_subset_iff]

/-- Removing a non-isolated point from a dense set, one still obtains a dense set. -/
theorem Dense.diff_singleton [T1Space X] {s : Set X} (hs : Dense s) (x : X) [NeBot (𝓝[≠] x)] :
    Dense (s \ {x}) :=
  hs.inter_of_isOpen_right (dense_compl_singleton x) isOpen_compl_singleton

/-- Removing a finset from a dense set in a space without isolated points, one still
obtains a dense set. -/
theorem Dense.diff_finset [T1Space X] [∀ x : X, NeBot (𝓝[≠] x)] {s : Set X} (hs : Dense s)
    (t : Finset X) : Dense (s \ t) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hs
  | insert _ _ _ ih =>
    rw [Finset.coe_insert, ← union_singleton, ← diff_diff]
    exact ih.diff_singleton _

/-- Removing a finite set from a dense set in a space without isolated points, one still
obtains a dense set. -/
theorem Dense.diff_finite [T1Space X] [∀ x : X, NeBot (𝓝[≠] x)] {s : Set X} (hs : Dense s)
    {t : Set X} (ht : t.Finite) : Dense (s \ t) := by
  convert hs.diff_finset ht.toFinset
  exact (Finite.coe_toFinset _).symm

/-- If a function to a `T1Space` tends to some limit `y` at some point `x`, then necessarily
`y = f x`. -/
theorem eq_of_tendsto_nhds [TopologicalSpace Y] [T1Space Y] {f : X → Y} {x : X} {y : Y}
    (h : Tendsto f (𝓝 x) (𝓝 y)) : f x = y :=
  by_contra fun hfa : f x ≠ y =>
    have fact₁ : {f x}ᶜ ∈ 𝓝 y := compl_singleton_mem_nhds hfa.symm
    have fact₂ : Tendsto f (pure x) (𝓝 y) := h.comp (tendsto_id'.2 <| pure_le_nhds x)
    fact₂ fact₁ (Eq.refl <| f x)

theorem Filter.Tendsto.eventually_ne {X} [TopologicalSpace Y] [T1Space Y] {g : X → Y}
    {l : Filter X} {b₁ b₂ : Y} (hg : Tendsto g l (𝓝 b₁)) (hb : b₁ ≠ b₂) : ∀ᶠ z in l, g z ≠ b₂ :=
  hg.eventually (isOpen_compl_singleton.eventually_mem hb)

theorem ContinuousAt.eventually_ne [TopologicalSpace Y] [T1Space Y] {g : X → Y} {x : X} {y : Y}
    (hg1 : ContinuousAt g x) (hg2 : g x ≠ y) : ∀ᶠ z in 𝓝 x, g z ≠ y :=
  hg1.tendsto.eventually_ne hg2

theorem eventually_ne_nhds [T1Space X] {a b : X} (h : a ≠ b) : ∀ᶠ x in 𝓝 a, x ≠ b :=
  IsOpen.eventually_mem isOpen_ne h

theorem eventually_ne_nhdsWithin [T1Space X] {a b : X} {s : Set X} (h : a ≠ b) :
    ∀ᶠ x in 𝓝[s] a, x ≠ b :=
  Filter.Eventually.filter_mono nhdsWithin_le_nhds <| eventually_ne_nhds h

theorem eventually_nhdsWithin_eventually_nhds_iff_of_isOpen {s : Set X} {a : X} {p : X → Prop}
    (hs : IsOpen s) : (∀ᶠ y in 𝓝[s] a, ∀ᶠ x in 𝓝 y, p x) ↔ ∀ᶠ x in 𝓝[s] a, p x := by
  nth_rw 2 [← eventually_eventually_nhdsWithin]
  constructor
  · intro h
    filter_upwards [h] with _ hy
    exact eventually_nhdsWithin_of_eventually_nhds hy
  · intro h
    filter_upwards [h, eventually_nhdsWithin_of_forall fun _ a ↦ a] with _ _ _
    simp_all [IsOpen.nhdsWithin_eq]

@[simp]
theorem eventually_nhdsNE_eventually_nhds_iff [T1Space X] {a : X} {p : X → Prop} :
    (∀ᶠ y in 𝓝[≠] a, ∀ᶠ x in 𝓝 y, p x) ↔ ∀ᶠ x in 𝓝[≠] a, p x :=
  eventually_nhdsWithin_eventually_nhds_iff_of_isOpen isOpen_ne

theorem continuousWithinAt_insert [TopologicalSpace Y] [T1Space X]
    {x y : X} {s : Set X} {f : X → Y} :
    ContinuousWithinAt f (insert y s) x ↔ ContinuousWithinAt f s x := by
  rcases eq_or_ne x y with (rfl | h)
  · exact continuousWithinAt_insert_self
  simp_rw [ContinuousWithinAt, nhdsWithin_insert_of_ne h]

alias ⟨ContinuousWithinAt.of_insert, ContinuousWithinAt.insert'⟩ := continuousWithinAt_insert

/-- See also `continuousWithinAt_diff_self` for the case `y = x` but not requiring `T1Space`. -/
theorem continuousWithinAt_diff_singleton [TopologicalSpace Y] [T1Space X]
    {x y : X} {s : Set X} {f : X → Y} :
    ContinuousWithinAt f (s \ {y}) x ↔ ContinuousWithinAt f s x := by
  rw [← continuousWithinAt_insert, insert_diff_singleton, continuousWithinAt_insert]

/-- If two sets coincide locally around `x`, except maybe at `y`, then it is equivalent to be
continuous at `x` within one set or the other. -/
theorem continuousWithinAt_congr_set' [TopologicalSpace Y] [T1Space X]
    {x : X} {s t : Set X} {f : X → Y} (y : X) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt f t x := by
  rw [← continuousWithinAt_insert_self (s := s), ← continuousWithinAt_insert_self (s := t)]
  exact continuousWithinAt_congr_set (eventuallyEq_insert h)

theorem ContinuousWithinAt.eq_const_of_mem_closure [TopologicalSpace Y] [T1Space Y]
    {f : X → Y} {s : Set X} {x : X} {c : Y} (h : ContinuousWithinAt f s x) (hx : x ∈ closure s)
    (ht : ∀ y ∈ s, f y = c) : f x = c := by
  rw [← Set.mem_singleton_iff, ← closure_singleton]
  exact h.mem_closure hx ht

theorem ContinuousWithinAt.eqOn_const_closure [TopologicalSpace Y] [T1Space Y]
    {f : X → Y} {s : Set X} {c : Y} (h : ∀ x ∈ closure s, ContinuousWithinAt f s x)
    (ht : s.EqOn f (fun _ ↦ c)) : (closure s).EqOn f (fun _ ↦ c) := by
  intro x hx
  apply ContinuousWithinAt.eq_const_of_mem_closure (h x hx) hx ht

/-- To prove a function to a `T1Space` is continuous at some point `x`, it suffices to prove that
`f` admits *some* limit at `x`. -/
theorem continuousAt_of_tendsto_nhds [TopologicalSpace Y] [T1Space Y] {f : X → Y} {x : X} {y : Y}
    (h : Tendsto f (𝓝 x) (𝓝 y)) : ContinuousAt f x := by
  rwa [ContinuousAt, eq_of_tendsto_nhds h]

@[simp]
theorem tendsto_const_nhds_iff [T1Space X] {l : Filter Y} [NeBot l] {c d : X} :
    Tendsto (fun _ => c) l (𝓝 d) ↔ c = d := by simp_rw [Tendsto, Filter.map_const, pure_le_nhds_iff]

/-- A point with a finite neighborhood has to be isolated. -/
theorem isOpen_singleton_of_finite_mem_nhds [T1Space X] (x : X)
    {s : Set X} (hs : s ∈ 𝓝 x) (hsf : s.Finite) : IsOpen ({x} : Set X) := by
  have A : {x} ⊆ s := by simp only [singleton_subset_iff, mem_of_mem_nhds hs]
  have B : IsClosed (s \ {x}) := (hsf.subset diff_subset).isClosed
  have C : (s \ {x})ᶜ ∈ 𝓝 x := B.isOpen_compl.mem_nhds fun h => h.2 rfl
  have D : {x} ∈ 𝓝 x := by simpa only [← diff_eq, diff_diff_cancel_left A] using inter_mem hs C
  rwa [← mem_interior_iff_mem_nhds, ← singleton_subset_iff, subset_interior_iff_isOpen] at D

/-- If the punctured neighborhoods of a point form a nontrivial filter, then any neighborhood is
infinite. -/
theorem infinite_of_mem_nhds {X} [TopologicalSpace X] [T1Space X] (x : X) [hx : NeBot (𝓝[≠] x)]
    {s : Set X} (hs : s ∈ 𝓝 x) : Set.Infinite s := by
  refine fun hsf => hx.1 ?_
  rw [← isOpen_singleton_iff_punctured_nhds]
  exact isOpen_singleton_of_finite_mem_nhds x hs hsf

instance (priority := low) [DiscreteTopology X] : T1Space X where t1 _ := isClosed_discrete _

instance Finite.instDiscreteTopology [T1Space X] [Finite X] : DiscreteTopology X :=
  discreteTopology_iff_forall_isClosed.mpr (·.toFinite.isClosed)

lemma Set.Finite.isDiscrete [T1Space X] {s : Set X} (hs : s.Finite) : IsDiscrete s :=
  ⟨@Finite.instDiscreteTopology _ _ _ hs.to_subtype⟩

theorem Set.Finite.continuousOn [T1Space X] [TopologicalSpace Y] {s : Set X} (hs : s.Finite)
    (f : X → Y) : ContinuousOn f s := by
  rw [continuousOn_iff_continuous_restrict]
  have : Finite s := hs
  fun_prop

theorem SeparationQuotient.t1Space_iff : T1Space (SeparationQuotient X) ↔ R0Space X := by
  rw [r0Space_iff, ((t1Space_TFAE (SeparationQuotient X)).out 0 9 :)]
  constructor
  · intro h x y xspecy
    rw [← IsInducing.specializes_iff isInducing_mk, h xspecy] at *
  · -- TODO is there are better way to do this,
    -- so the case split produces `SeparationQuotient.mk` directly, rather than `Quot.mk`?
    -- Currently we need the `change` statement to recover this.
    rintro h ⟨x⟩ ⟨y⟩ sxspecsy
    change mk _ = mk _
    have xspecy : x ⤳ y := isInducing_mk.specializes_iff.mp sxspecsy
    have yspecx : y ⤳ x := h xspecy
    rw [mk_eq_mk, inseparable_iff_specializes_and]
    exact ⟨xspecy, yspecx⟩

lemma isClosed_inter_singleton [T1Space X] {A : Set X} {a : X} : IsClosed (A ∩ {a}) :=
  Subsingleton.inter_singleton.isClosed

lemma isClosed_singleton_inter [T1Space X] {A : Set X} {a : X} : IsClosed ({a} ∩ A) :=
  Subsingleton.singleton_inter.isClosed

theorem singleton_mem_nhdsWithin_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X}
    (hx : x ∈ s) : {x} ∈ 𝓝[s] x := by
  rw [isDiscrete_iff_discreteTopology] at hs
  have : ({⟨x, hx⟩} : Set s) ∈ 𝓝 (⟨x, hx⟩ : s) := by simp [nhds_discrete]
  simpa only [nhdsWithin_eq_map_subtype_coe hx, image_singleton] using
    @image_mem_map _ _ _ ((↑) : s → X) _ this

/-- The neighbourhoods filter of `x` within `s`, under the discrete topology, is equal to
the pure `x` filter (which is the principal filter at the singleton `{x}`.) -/
theorem nhdsWithin_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x ∈ s) :
    𝓝[s] x = pure x :=
  (le_pure_iff.2 <| singleton_mem_nhdsWithin_of_mem_discrete hs hx).antisymm (pure_le_nhdsWithin hx)

theorem Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete {ι : Type*} {p : ι → Prop}
    {t : ι → Set X} {s : Set X} (hs : IsDiscrete s) {x : X} (hb : (𝓝 x).HasBasis p t)
    (hx : x ∈ s) : ∃ i, p i ∧ t i ∩ s = {x} := by
  rcases (nhdsWithin_hasBasis hb s).mem_iff.1 (singleton_mem_nhdsWithin_of_mem_discrete hs hx) with
    ⟨i, hi, hix⟩
  exact ⟨i, hi, hix.antisymm <| singleton_subset_iff.2 ⟨mem_of_mem_nhds <| hb.mem_of_mem hi, hx⟩⟩

/-- A point `x` in a discrete subset `s` of a topological space admits a neighbourhood
that only meets `s` at `x`. -/
theorem nhds_inter_eq_singleton_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X}
    (hx : x ∈ s) : ∃ U ∈ 𝓝 x, U ∩ s = {x} := by
  simpa using (𝓝 x).basis_sets.exists_inter_eq_singleton_of_mem_discrete hs hx

/-- Let `x` be a point in a discrete subset `s` of a topological space, then there exists an open
set that only meets `s` at `x`. -/
theorem isOpen_inter_eq_singleton_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X}
    (hx : x ∈ s) : ∃ U : Set X, IsOpen U ∧ U ∩ s = {x} := by
  obtain ⟨U, hU_nhds, hU_inter⟩ := nhds_inter_eq_singleton_of_mem_discrete hs hx
  obtain ⟨t, ht_sub, ht_open, ht_x⟩ := mem_nhds_iff.mp hU_nhds
  grind

/-- For point `x` in a discrete subset `s` of a topological space, there is a set `U`
such that
1. `U` is a punctured neighborhood of `x` (i.e. `U ∪ {x}` is a neighbourhood of `x`),
2. `U` is disjoint from `s`.
-/
theorem disjoint_nhdsWithin_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x ∈ s) :
    ∃ U ∈ 𝓝[≠] x, Disjoint U s :=
  let ⟨V, h, h'⟩ := nhds_inter_eq_singleton_of_mem_discrete hs hx
  ⟨{x}ᶜ ∩ V, inter_mem_nhdsWithin _ h,
    disjoint_iff_inter_eq_empty.mpr (by rw [inter_assoc, h', compl_inter_self])⟩

theorem isClosedEmbedding_update {ι : Type*} {β : ι → Type*}
    [DecidableEq ι] [(i : ι) → TopologicalSpace (β i)]
    (x : (i : ι) → β i) (i : ι) [(i : ι) → T1Space (β i)] :
    IsClosedEmbedding (update x i) := by
  refine .of_continuous_injective_isClosedMap (continuous_const.update i continuous_id)
    (update_injective x i) fun s hs ↦ ?_
  rw [update_image]
  apply isClosed_set_pi
  simp [forall_update_iff, hs]

lemma nhdsNE_le_cofinite {α : Type*} [TopologicalSpace α] [T1Space α] (a : α) :
    𝓝[≠] a ≤ cofinite := by
  refine le_cofinite_iff_compl_singleton_mem.mpr fun x ↦ ?_
  rcases eq_or_ne a x with rfl | hx
  exacts [self_mem_nhdsWithin, eventually_ne_nhdsWithin hx]

lemma Function.update_eventuallyEq_nhdsNE
    {α β : Type*} [TopologicalSpace α] [T1Space α] [DecidableEq α] (f : α → β) (a a' : α) (b : β) :
    Function.update f a b =ᶠ[𝓝[≠] a'] f :=
  (Function.update_eventuallyEq_cofinite f a b).filter_mono (nhdsNE_le_cofinite a')

/-! ### R₁ (preregular) spaces -/

section R1Space

/-- A topological space is called a *preregular* (a.k.a. R₁) space,
if any two topologically distinguishable points have disjoint neighbourhoods. -/
@[mk_iff r1Space_iff_specializes_or_disjoint_nhds]
class R1Space (X : Type*) [TopologicalSpace X] : Prop where
  specializes_or_disjoint_nhds (x y : X) : Specializes x y ∨ Disjoint (𝓝 x) (𝓝 y)

export R1Space (specializes_or_disjoint_nhds)

variable [R1Space X] {x y : X}

instance (priority := 100) : R0Space X where
  specializes_symmetric _ _ h := (specializes_or_disjoint_nhds _ _).resolve_right <| fun hd ↦
    h.not_disjoint hd.symm

theorem disjoint_nhds_nhds_iff_not_specializes : Disjoint (𝓝 x) (𝓝 y) ↔ ¬x ⤳ y :=
  ⟨fun hd hspec ↦ hspec.not_disjoint hd, (specializes_or_disjoint_nhds _ _).resolve_left⟩

theorem specializes_iff_not_disjoint : x ⤳ y ↔ ¬Disjoint (𝓝 x) (𝓝 y) :=
  disjoint_nhds_nhds_iff_not_specializes.not_left.symm

theorem disjoint_nhds_nhds_iff_not_inseparable : Disjoint (𝓝 x) (𝓝 y) ↔ ¬Inseparable x y := by
  rw [disjoint_nhds_nhds_iff_not_specializes, specializes_iff_inseparable]

theorem r1Space_iff_inseparable_or_disjoint_nhds {X : Type*} [TopologicalSpace X] :
    R1Space X ↔ ∀ x y : X, Inseparable x y ∨ Disjoint (𝓝 x) (𝓝 y) :=
  ⟨fun _h x y ↦ (specializes_or_disjoint_nhds x y).imp_left Specializes.inseparable, fun h ↦
    ⟨fun x y ↦ (h x y).imp_left Inseparable.specializes⟩⟩

theorem Inseparable.of_nhds_neBot {x y : X} (h : NeBot (𝓝 x ⊓ 𝓝 y)) :
    Inseparable x y :=
  (r1Space_iff_inseparable_or_disjoint_nhds.mp ‹_› _ _).resolve_right fun h' => h.ne h'.eq_bot

theorem r1_separation {x y : X} (h : ¬Inseparable x y) :
    ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v := by
  rw [← disjoint_nhds_nhds_iff_not_inseparable,
    (nhds_basis_opens x).disjoint_iff (nhds_basis_opens y)] at h
  obtain ⟨u, ⟨hxu, hu⟩, v, ⟨hyv, hv⟩, huv⟩ := h
  exact ⟨u, v, hu, hv, hxu, hyv, huv⟩

/-- Limits are unique up to separability.

A weaker version of `tendsto_nhds_unique` for `R1Space`. -/
theorem tendsto_nhds_unique_inseparable {f : Y → X} {l : Filter Y} {a b : X} [NeBot l]
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : Inseparable a b :=
  .of_nhds_neBot <| neBot_of_le <| le_inf ha hb

theorem isClosed_setOf_specializes : IsClosed { p : X × X | p.1 ⤳ p.2 } := by
  simp only [← isOpen_compl_iff, compl_setOf, ← disjoint_nhds_nhds_iff_not_specializes,
    isOpen_setOf_disjoint_nhds_nhds]

theorem isClosed_setOf_inseparable : IsClosed { p : X × X | Inseparable p.1 p.2 } := by
  simp only [← specializes_iff_inseparable, isClosed_setOf_specializes]

/-- In an R₁ space, a point belongs to the closure of a compact set `K`
if and only if it is topologically inseparable from some point of `K`. -/
theorem IsCompact.mem_closure_iff_exists_inseparable {K : Set X} (hK : IsCompact K) :
    y ∈ closure K ↔ ∃ x ∈ K, Inseparable x y := by
  refine ⟨fun hy ↦ ?_, fun ⟨x, hxK, hxy⟩ ↦
    (hxy.mem_closed_iff isClosed_closure).1 <| subset_closure hxK⟩
  contrapose! hy
  have : Disjoint (𝓝 y) (𝓝ˢ K) := hK.disjoint_nhdsSet_right.2 fun x hx ↦
    (disjoint_nhds_nhds_iff_not_inseparable.2 (hy x hx)).symm
  simpa only [disjoint_iff, notMem_closure_iff_nhdsWithin_eq_bot]
    using this.mono_right principal_le_nhdsSet

theorem IsCompact.closure_eq_biUnion_inseparable {K : Set X} (hK : IsCompact K) :
    closure K = ⋃ x ∈ K, {y | Inseparable x y} := by
  ext; simp [hK.mem_closure_iff_exists_inseparable]

/-- In an R₁ space, the closure of a compact set is the union of the closures of its points. -/
theorem IsCompact.closure_eq_biUnion_closure_singleton {K : Set X} (hK : IsCompact K) :
    closure K = ⋃ x ∈ K, closure {x} := by
  simp only [hK.closure_eq_biUnion_inseparable, ← specializes_iff_inseparable,
    specializes_iff_mem_closure, setOf_mem_eq]

/-- In an R₁ space, if a compact set `K` is contained in an open set `U`,
then its closure is also contained in `U`. -/
theorem IsCompact.closure_subset_of_isOpen {K : Set X} (hK : IsCompact K)
    {U : Set X} (hU : IsOpen U) (hKU : K ⊆ U) : closure K ⊆ U := by
  rw [hK.closure_eq_biUnion_inseparable, iUnion₂_subset_iff]
  exact fun x hx y hxy ↦ (hxy.mem_open_iff hU).1 (hKU hx)

/-- The closure of a compact set in an R₁ space is a compact set. -/
protected theorem IsCompact.closure {K : Set X} (hK : IsCompact K) : IsCompact (closure K) := by
  refine isCompact_of_finite_subcover fun U hUo hKU ↦ ?_
  rcases hK.elim_finite_subcover U hUo (subset_closure.trans hKU) with ⟨t, ht⟩
  exact ⟨t, hK.closure_subset_of_isOpen (isOpen_biUnion fun _ _ ↦ hUo _) ht⟩

theorem IsCompact.closure_of_subset {s K : Set X} (hK : IsCompact K) (h : s ⊆ K) :
    IsCompact (closure s) :=
  hK.closure.of_isClosed_subset isClosed_closure (closure_mono h)

@[simp]
theorem exists_isCompact_superset_iff {s : Set X} :
    (∃ K, IsCompact K ∧ s ⊆ K) ↔ IsCompact (closure s) :=
  ⟨fun ⟨_K, hK, hsK⟩ => hK.closure_of_subset hsK, fun h => ⟨closure s, h, subset_closure⟩⟩

/-- If `K` and `L` are disjoint compact sets in an R₁ topological space
and `L` is also closed, then `K` and `L` have disjoint neighborhoods. -/
theorem SeparatedNhds.of_isCompact_isCompact_isClosed {K L : Set X} (hK : IsCompact K)
    (hL : IsCompact L) (h'L : IsClosed L) (hd : Disjoint K L) : SeparatedNhds K L := by
  simp_rw [separatedNhds_iff_disjoint, hK.disjoint_nhdsSet_left, hL.disjoint_nhdsSet_right,
    disjoint_nhds_nhds_iff_not_inseparable]
  intro x hx y hy h
  exact absurd ((h.mem_closed_iff h'L).2 hy) <| disjoint_left.1 hd hx

/-- If a compact set is covered by two open sets, then we can cover it by two compact subsets. -/
theorem IsCompact.binary_compact_cover {K U V : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hV : IsOpen V) (h2K : K ⊆ U ∪ V) :
    ∃ K₁ K₂ : Set X, IsCompact K₁ ∧ IsCompact K₂ ∧ K₁ ⊆ U ∧ K₂ ⊆ V ∧ K = K₁ ∪ K₂ := by
  have hK' : IsCompact (closure K) := hK.closure
  have : SeparatedNhds (closure K \ U) (closure K \ V) := by
    apply SeparatedNhds.of_isCompact_isCompact_isClosed (hK'.diff hU) (hK'.diff hV)
      (isClosed_closure.sdiff hV)
    rw [disjoint_iff_inter_eq_empty, diff_inter_diff, diff_eq_empty]
    exact hK.closure_subset_of_isOpen (hU.union hV) h2K
  have : SeparatedNhds (K \ U) (K \ V) :=
    this.mono (diff_subset_diff_left (subset_closure)) (diff_subset_diff_left (subset_closure))
  rcases this with ⟨O₁, O₂, h1O₁, h1O₂, h2O₁, h2O₂, hO⟩
  exact ⟨K \ O₁, K \ O₂, hK.diff h1O₁, hK.diff h1O₂, diff_subset_comm.mp h2O₁,
    diff_subset_comm.mp h2O₂, by rw [← diff_inter, hO.inter_eq, diff_empty]⟩

/-- For every finite open cover `Uᵢ` of a compact set, there exists a compact cover `Kᵢ ⊆ Uᵢ`. -/
theorem IsCompact.finite_compact_cover {s : Set X} (hs : IsCompact s) {ι : Type*}
    (t : Finset ι) (U : ι → Set X) (hU : ∀ i ∈ t, IsOpen (U i)) (hsC : s ⊆ ⋃ i ∈ t, U i) :
    ∃ K : ι → Set X, (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ U i) ∧ s = ⋃ i ∈ t, K i := by
  classical
  induction t using Finset.induction generalizing U s with
  | empty =>
    refine ⟨fun _ => ∅, fun _ => isCompact_empty, fun i => empty_subset _, ?_⟩
    simpa only [subset_empty_iff, Finset.notMem_empty, iUnion_false, iUnion_empty] using hsC
  | insert x t hx ih =>
    simp only [Finset.set_biUnion_insert] at hsC
    simp only [Finset.forall_mem_insert] at hU
    have hU' : ∀ i ∈ t, IsOpen (U i) := fun i hi => hU.2 i hi
    rcases hs.binary_compact_cover hU.1 (isOpen_biUnion hU') hsC with
      ⟨K₁, K₂, h1K₁, h1K₂, h2K₁, h2K₂, hK⟩
    rcases ih h1K₂ U hU' h2K₂ with ⟨K, h1K, h2K, h3K⟩
    refine ⟨update K x K₁, ?_, ?_, ?_⟩
    · intro i
      rcases eq_or_ne i x with rfl | hi
      · simp only [update_self, h1K₁]
      · simp only [update_of_ne hi, h1K]
    · intro i
      rcases eq_or_ne i x with rfl | hi
      · simp only [update_self, h2K₁]
      · simp only [update_of_ne hi, h2K]
    · simp only [Finset.set_biUnion_insert_update _ hx, hK, h3K]

theorem R1Space.of_continuous_specializes_imp [TopologicalSpace Y] {f : Y → X} (hc : Continuous f)
    (hspec : ∀ x y, f x ⤳ f y → x ⤳ y) : R1Space Y where
  specializes_or_disjoint_nhds x y := (specializes_or_disjoint_nhds (f x) (f y)).imp (hspec x y) <|
    ((hc.tendsto _).disjoint · (hc.tendsto _))

theorem Topology.IsInducing.r1Space [TopologicalSpace Y] {f : Y → X} (hf : IsInducing f) :
    R1Space Y := .of_continuous_specializes_imp hf.continuous fun _ _ ↦ hf.specializes_iff.1

protected theorem R1Space.induced (f : Y → X) : @R1Space Y (.induced f ‹_›) :=
  @IsInducing.r1Space _ _ _ _ (.induced f _) f (.induced f)

instance (p : X → Prop) : R1Space (Subtype p) := .induced _

protected theorem R1Space.sInf {X : Type*} {T : Set (TopologicalSpace X)}
    (hT : ∀ t ∈ T, @R1Space X t) : @R1Space X (sInf T) := by
  let _ := sInf T
  refine ⟨fun x y ↦ ?_⟩
  simp only [Specializes, nhds_sInf]
  by_cases! hTd : ∃ t ∈ T, Disjoint (@nhds X t x) (@nhds X t y)
  · rcases hTd with ⟨t, htT, htd⟩
    exact .inr <| htd.mono (iInf₂_le t htT) (iInf₂_le t htT)
  · exact .inl <| iInf₂_mono fun t ht ↦ ((hT t ht).1 x y).resolve_right (hTd t ht)

protected theorem R1Space.iInf {ι X : Type*} {t : ι → TopologicalSpace X}
    (ht : ∀ i, @R1Space X (t i)) : @R1Space X (iInf t) :=
  .sInf <| forall_mem_range.2 ht

set_option backward.isDefEq.respectTransparency false in
protected theorem R1Space.inf {X : Type*} {t₁ t₂ : TopologicalSpace X}
    (h₁ : @R1Space X t₁) (h₂ : @R1Space X t₂) : @R1Space X (t₁ ⊓ t₂) := by
  rw [inf_eq_iInf]
  apply R1Space.iInf
  simp [*]

instance [TopologicalSpace Y] [R1Space Y] : R1Space (X × Y) :=
  .inf (.induced _) (.induced _)

instance {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, R1Space (X i)] :
    R1Space (∀ i, X i) :=
  .iInf fun _ ↦ .induced _

theorem exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [R1Space Y] {f : X → Y} {x : X}
    {K : Set X} {s : Set Y} (hf : Continuous f) (hs : s ∈ 𝓝 (f x)) (hKc : IsCompact K)
    (hKx : K ∈ 𝓝 x) : ∃ L ∈ 𝓝 x, IsCompact L ∧ MapsTo f L s := by
  have hc : IsCompact (f '' K \ interior s) := (hKc.image hf).diff isOpen_interior
  obtain ⟨U, V, Uo, Vo, hxU, hV, hd⟩ : SeparatedNhds {f x} (f '' K \ interior s) := by
    simp_rw [separatedNhds_iff_disjoint, nhdsSet_singleton, hc.disjoint_nhdsSet_right,
      disjoint_nhds_nhds_iff_not_inseparable]
    rintro y ⟨-, hys⟩ hxy
    refine hys <| (hxy.mem_open_iff isOpen_interior).1 ?_
    rwa [mem_interior_iff_mem_nhds]
  refine ⟨K \ f ⁻¹' V, diff_mem hKx ?_, hKc.diff <| Vo.preimage hf, fun y hy ↦ ?_⟩
  · filter_upwards [hf.continuousAt <| Uo.mem_nhds (hxU rfl)] with x hx
      using Set.disjoint_left.1 hd hx
  · by_contra hys
    exact hy.2 (hV ⟨mem_image_of_mem _ hy.1, notMem_subset interior_subset hys⟩)

instance (priority := 900) {X Y : Type*} [TopologicalSpace X] [WeaklyLocallyCompactSpace X]
    [TopologicalSpace Y] [R1Space Y] : LocallyCompactPair X Y where
  exists_mem_nhds_isCompact_mapsTo hf hs :=
    let ⟨_K, hKc, hKx⟩ := exists_compact_mem_nhds _
    exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds hf hs hKc hKx

/-- If a point in an R₁ space has a compact neighborhood,
then it has a basis of compact closed neighborhoods. -/
theorem IsCompact.isCompact_isClosed_basis_nhds {x : X} {L : Set X} (hLc : IsCompact L)
    (hxL : L ∈ 𝓝 x) : (𝓝 x).HasBasis (fun K ↦ K ∈ 𝓝 x ∧ IsCompact K ∧ IsClosed K) (·) :=
  hasBasis_self.2 fun _U hU ↦
    let ⟨K, hKx, hKc, hKU⟩ := exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds
      continuous_id (interior_mem_nhds.2 hU) hLc hxL
    ⟨closure K, mem_of_superset hKx subset_closure, ⟨hKc.closure, isClosed_closure⟩,
      (hKc.closure_subset_of_isOpen isOpen_interior hKU).trans interior_subset⟩

/-- In an R₁ space, the filters `coclosedCompact` and `cocompact` are equal. -/
@[simp]
theorem Filter.coclosedCompact_eq_cocompact : coclosedCompact X = cocompact X := by
  refine le_antisymm ?_ cocompact_le_coclosedCompact
  rw [hasBasis_coclosedCompact.le_basis_iff hasBasis_cocompact]
  exact fun K hK ↦ ⟨closure K, ⟨isClosed_closure, hK.closure⟩, compl_subset_compl.2 subset_closure⟩

/-- In an R₁ space, the bornologies `relativelyCompact` and `inCompact` are equal. -/
@[simp]
theorem Bornology.relativelyCompact_eq_inCompact :
    Bornology.relativelyCompact X = Bornology.inCompact X :=
  Bornology.ext _ _ Filter.coclosedCompact_eq_cocompact

/-!
### Lemmas about a weakly locally compact R₁ space

In fact, a space with these properties is locally compact and regular.
Some lemmas are formulated using the latter assumptions below.
-/

variable [WeaklyLocallyCompactSpace X]

/-- In a (weakly) locally compact R₁ space, compact closed neighborhoods of a point `x`
form a basis of neighborhoods of `x`. -/
theorem isCompact_isClosed_basis_nhds (x : X) :
    (𝓝 x).HasBasis (fun K => K ∈ 𝓝 x ∧ IsCompact K ∧ IsClosed K) (·) :=
  let ⟨_L, hLc, hLx⟩ := exists_compact_mem_nhds x
  hLc.isCompact_isClosed_basis_nhds hLx

/-- In a (weakly) locally compact R₁ space, each point admits a compact closed neighborhood. -/
theorem exists_mem_nhds_isCompact_isClosed (x : X) : ∃ K ∈ 𝓝 x, IsCompact K ∧ IsClosed K :=
  (isCompact_isClosed_basis_nhds x).ex_mem

-- see Note [lower instance priority]
/-- A weakly locally compact R₁ space is locally compact. -/
instance (priority := 80) WeaklyLocallyCompactSpace.locallyCompactSpace : LocallyCompactSpace X :=
  .of_hasBasis isCompact_isClosed_basis_nhds fun _ _ ⟨_, h, _⟩ ↦ h

/-- In a weakly locally compact R₁ space,
every compact set has an open neighborhood with compact closure. -/
theorem exists_isOpen_superset_and_isCompact_closure {K : Set X} (hK : IsCompact K) :
    ∃ V, IsOpen V ∧ K ⊆ V ∧ IsCompact (closure V) := by
  rcases exists_compact_superset hK with ⟨K', hK', hKK'⟩
  exact ⟨interior K', isOpen_interior, hKK', hK'.closure_of_subset interior_subset⟩

/-- In a weakly locally compact R₁ space,
every point has an open neighborhood with compact closure. -/
theorem exists_isOpen_mem_isCompact_closure (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsCompact (closure U) := by
  simpa only [singleton_subset_iff]
    using exists_isOpen_superset_and_isCompact_closure isCompact_singleton

end R1Space

end Separation
