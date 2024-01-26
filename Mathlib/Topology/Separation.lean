/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Inseparable

#align_import topology.separation from "leanprover-community/mathlib"@"d91e7f7a7f1c7e9f0e18fdb6bde4f652004c735d"

/-!
# Separation properties of topological spaces.

This file defines the predicate `SeparatedNhds`, and common separation axioms
(under the Kolmogorov classification).

## Main definitions

* `SeparatedNhds`: Two `Set`s are separated by neighbourhoods if they are contained in disjoint
  open sets.
* `T0Space`: A T₀/Kolmogorov space is a space where, for every two points `x ≠ y`,
  there is an open set that contains one, but not the other.
* `T1Space`: A T₁/Fréchet space is a space where every singleton set is closed.
  This is equivalent to, for every pair `x ≠ y`, there existing an open set containing `x`
  but not `y` (`t1Space_iff_exists_open` shows that these conditions are equivalent.)
* `T2Space`: A T₂/Hausdorff space is a space where, for every two points `x ≠ y`,
  there is two disjoint open sets, one containing `x`, and the other `y`.
* `T25Space`: A T₂.₅/Urysohn space is a space where, for every two points `x ≠ y`,
  there is two open sets, one containing `x`, and the other `y`, whose closures are disjoint.
* `RegularSpace`: A regular space is one where, given any closed `C` and `x ∉ C`,
  there are disjoint open sets containing `x` and `C` respectively. Such a space is not necessarily
  Hausdorff.
* `T3Space`: A T₃ space is a T0 regular space. In `mathlib`, T₃ implies T₂.₅.
* `NormalSpace`: A normal space, is one where given two disjoint closed sets,
  we can find two open sets that separate them.
* `T4Space`: A T₄ space is a normal T₁ space. T₄ implies T₃.
* `T5Space`: A T₅ space, also known as a *completely normal Hausdorff space*, is a space in which,
  given two sets `s` and `t` such that the closure of `s` is disjoint from `t`, and conversely,
  then `s` and `t` have disjoint neighborhoods.

## Main results

### T₀ spaces

* `IsClosed.exists_closed_singleton`: Given a closed set `S` in a compact T₀ space,
  there is some `x ∈ S` such that `{x}` is closed.
* `exists_open_singleton_of_open_finite`: Given an open finite set `S` in a T₀ space,
  there is some `x ∈ S` such that `{x}` is open.

### T₁ spaces

* `isClosedMap_const`: The constant map is a closed map.
* `discrete_of_t1_of_finite`: A finite T₁ space must have the discrete topology.

### T₂ spaces

* `t2_iff_nhds`: A space is T₂ iff the neighbourhoods of distinct points generate the bottom filter.
* `t2_iff_isClosed_diagonal`: A space is T₂ iff the `diagonal` of `X` (that is, the set of all
  points of the form `(a, a) : X × X`) is closed under the product topology.
* `separatedNhds_of_finset_finset`: Any two disjoint finsets are `SeparatedNhds`.
* Most topological constructions preserve Hausdorffness;
  these results are part of the typeclass inference system (e.g. `Embedding.t2Space`)
* `Set.EqOn.closure`: If two functions are equal on some set `s`, they are equal on its closure.
* `IsCompact.isClosed`: All compact sets are closed.
* `WeaklyLocallyCompactSpace.locallyCompactSpace`: If a topological space is both
  weakly locally compact (i.e., each point has a compact neighbourhood)
  and is T₂, then it is locally compact.
* `totallySeparatedSpace_of_t1_of_basis_clopen`: If `X` has a clopen basis, then
  it is a `TotallySeparatedSpace`.
* `loc_compact_t2_tot_disc_iff_tot_sep`: A locally compact T₂ space is totally disconnected iff
  it is totally separated.

If the space is also compact:

* `normalOfCompactT2`: A compact T₂ space is a `NormalSpace`.
* `connectedComponent_eq_iInter_isClopen`: The connected component of a point
  is the intersection of all its clopen neighbourhoods.
* `compact_t2_tot_disc_iff_tot_sep`: Being a `TotallyDisconnectedSpace`
  is equivalent to being a `TotallySeparatedSpace`.
* `ConnectedComponents.t2`: `ConnectedComponents X` is T₂ for `X` T₂ and compact.

### T₃ spaces

* `disjoint_nested_nhds`: Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and
  `y ∈ V₂ ⊆ U₂`, with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint.

## References

https://en.wikipedia.org/wiki/Separation_axiom
-/


open Function Set Filter Topology TopologicalSpace
open scoped Classical

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

/--
`SeparatedNhds` is a predicate on pairs of sub`Set`s of a topological space.  It holds if the two
sub`Set`s are contained in disjoint open sets.
-/
def SeparatedNhds : Set X → Set X → Prop := fun s t : Set X =>
  ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ s ⊆ U ∧ t ⊆ V ∧ Disjoint U V
#align separated_nhds SeparatedNhds

theorem separatedNhds_iff_disjoint {s t : Set X} : SeparatedNhds s t ↔ Disjoint (𝓝ˢ s) (𝓝ˢ t) := by
  simp only [(hasBasis_nhdsSet s).disjoint_iff (hasBasis_nhdsSet t), SeparatedNhds, exists_prop, ←
    exists_and_left, and_assoc, and_comm, and_left_comm]
#align separated_nhds_iff_disjoint separatedNhds_iff_disjoint

alias ⟨SeparatedNhds.disjoint_nhdsSet, _⟩ := separatedNhds_iff_disjoint

namespace SeparatedNhds

variable {s s₁ s₂ t t₁ t₂ u : Set X}

@[symm]
theorem symm : SeparatedNhds s t → SeparatedNhds t s := fun ⟨U, V, oU, oV, aU, bV, UV⟩ =>
  ⟨V, U, oV, oU, bV, aU, Disjoint.symm UV⟩
#align separated_nhds.symm SeparatedNhds.symm

theorem comm (s t : Set X) : SeparatedNhds s t ↔ SeparatedNhds t s :=
  ⟨symm, symm⟩
#align separated_nhds.comm SeparatedNhds.comm

theorem preimage [TopologicalSpace Y] {f : X → Y} {s t : Set Y} (h : SeparatedNhds s t)
    (hf : Continuous f) : SeparatedNhds (f ⁻¹' s) (f ⁻¹' t) :=
  let ⟨U, V, oU, oV, sU, tV, UV⟩ := h
  ⟨f ⁻¹' U, f ⁻¹' V, oU.preimage hf, oV.preimage hf, preimage_mono sU, preimage_mono tV,
    UV.preimage f⟩
#align separated_nhds.preimage SeparatedNhds.preimage

protected theorem disjoint (h : SeparatedNhds s t) : Disjoint s t :=
  let ⟨_, _, _, _, hsU, htV, hd⟩ := h; hd.mono hsU htV
#align separated_nhds.disjoint SeparatedNhds.disjoint

theorem disjoint_closure_left (h : SeparatedNhds s t) : Disjoint (closure s) t :=
  let ⟨_U, _V, _, hV, hsU, htV, hd⟩ := h
  (hd.closure_left hV).mono (closure_mono hsU) htV
#align separated_nhds.disjoint_closure_left SeparatedNhds.disjoint_closure_left

theorem disjoint_closure_right (h : SeparatedNhds s t) : Disjoint s (closure t) :=
  h.symm.disjoint_closure_left.symm
#align separated_nhds.disjoint_closure_right SeparatedNhds.disjoint_closure_right

@[simp] theorem empty_right (s : Set X) : SeparatedNhds s ∅ :=
  ⟨_, _, isOpen_univ, isOpen_empty, fun a _ => mem_univ a, Subset.rfl, disjoint_empty _⟩
#align separated_nhds.empty_right SeparatedNhds.empty_right

@[simp] theorem empty_left (s : Set X) : SeparatedNhds ∅ s :=
  (empty_right _).symm
#align separated_nhds.empty_left SeparatedNhds.empty_left

theorem mono (h : SeparatedNhds s₂ t₂) (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : SeparatedNhds s₁ t₁ :=
  let ⟨U, V, hU, hV, hsU, htV, hd⟩ := h
  ⟨U, V, hU, hV, hs.trans hsU, ht.trans htV, hd⟩
#align separated_nhds.mono SeparatedNhds.mono

theorem union_left : SeparatedNhds s u → SeparatedNhds t u → SeparatedNhds (s ∪ t) u := by
  simpa only [separatedNhds_iff_disjoint, nhdsSet_union, disjoint_sup_left] using And.intro
#align separated_nhds.union_left SeparatedNhds.union_left

theorem union_right (ht : SeparatedNhds s t) (hu : SeparatedNhds s u) : SeparatedNhds s (t ∪ u) :=
  (ht.symm.union_left hu.symm).symm
#align separated_nhds.union_right SeparatedNhds.union_right

end SeparatedNhds

/-- A T₀ space, also known as a Kolmogorov space, is a topological space such that for every pair
`x ≠ y`, there is an open set containing one but not the other. We formulate the definition in terms
of the `Inseparable` relation.  -/
class T0Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Two inseparable points in a T₀ space are equal. -/
  t0 : ∀ ⦃x y : X⦄, Inseparable x y → x = y
#align t0_space T0Space

theorem t0Space_iff_inseparable (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ ∀ x y : X, Inseparable x y → x = y :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
#align t0_space_iff_inseparable t0Space_iff_inseparable

theorem t0Space_iff_not_inseparable (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Pairwise fun x y : X => ¬Inseparable x y := by
  simp only [t0Space_iff_inseparable, Ne.def, not_imp_not, Pairwise]
#align t0_space_iff_not_inseparable t0Space_iff_not_inseparable

theorem Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x y) : x = y :=
  T0Space.t0 h
#align inseparable.eq Inseparable.eq

/-- A topology `Inducing` map from a T₀ space is injective. -/
protected theorem Inducing.injective [TopologicalSpace Y] [T0Space X] {f : X → Y}
    (hf : Inducing f) : Injective f := fun _ _ h =>
  (hf.inseparable_iff.1 <| .of_eq h).eq
#align inducing.injective Inducing.injective

/-- A topology `Inducing` map from a T₀ space is a topological embedding. -/
protected theorem Inducing.embedding [TopologicalSpace Y] [T0Space X] {f : X → Y}
    (hf : Inducing f) : Embedding f :=
  ⟨hf, hf.injective⟩
#align inducing.embedding Inducing.embedding

lemma embedding_iff_inducing [TopologicalSpace Y] [T0Space X] {f : X → Y} :
    Embedding f ↔ Inducing f :=
  ⟨Embedding.toInducing, Inducing.embedding⟩
#align embedding_iff_inducing embedding_iff_inducing

theorem t0Space_iff_nhds_injective (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Injective (𝓝 : X → Filter X) :=
  t0Space_iff_inseparable X
#align t0_space_iff_nhds_injective t0Space_iff_nhds_injective

theorem nhds_injective [T0Space X] : Injective (𝓝 : X → Filter X) :=
  (t0Space_iff_nhds_injective X).1 ‹_›
#align nhds_injective nhds_injective

theorem inseparable_iff_eq [T0Space X] {x y : X} : Inseparable x y ↔ x = y :=
  nhds_injective.eq_iff
#align inseparable_iff_eq inseparable_iff_eq

@[simp]
theorem nhds_eq_nhds_iff [T0Space X] {a b : X} : 𝓝 a = 𝓝 b ↔ a = b :=
  nhds_injective.eq_iff
#align nhds_eq_nhds_iff nhds_eq_nhds_iff

@[simp]
theorem inseparable_eq_eq [T0Space X] : Inseparable = @Eq X :=
  funext₂ fun _ _ => propext inseparable_iff_eq
#align inseparable_eq_eq inseparable_eq_eq

theorem TopologicalSpace.IsTopologicalBasis.inseparable_iff {b : Set (Set X)}
    (hb : IsTopologicalBasis b) {x y : X} : Inseparable x y ↔ ∀ s ∈ b, (x ∈ s ↔ y ∈ s) :=
  ⟨fun h s hs ↦ inseparable_iff_forall_open.1 h _ (hb.isOpen hs),
    fun h ↦ hb.nhds_hasBasis.eq_of_same_basis <| by
      convert hb.nhds_hasBasis using 2
      exact and_congr_right (h _)⟩

theorem TopologicalSpace.IsTopologicalBasis.eq_iff [T0Space X] {b : Set (Set X)}
    (hb : IsTopologicalBasis b) {x y : X} : x = y ↔ ∀ s ∈ b, (x ∈ s ↔ y ∈ s) :=
  inseparable_iff_eq.symm.trans hb.inseparable_iff

theorem t0Space_iff_exists_isOpen_xor'_mem (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Pairwise fun x y => ∃ U : Set X, IsOpen U ∧ Xor' (x ∈ U) (y ∈ U) := by
  simp only [t0Space_iff_not_inseparable, xor_iff_not_iff, not_forall, exists_prop,
    inseparable_iff_forall_open, Pairwise]
#align t0_space_iff_exists_is_open_xor_mem t0Space_iff_exists_isOpen_xor'_mem

theorem exists_isOpen_xor'_mem [T0Space X] {x y : X} (h : x ≠ y) :
    ∃ U : Set X, IsOpen U ∧ Xor' (x ∈ U) (y ∈ U) :=
  (t0Space_iff_exists_isOpen_xor'_mem X).1 ‹_› h
#align exists_is_open_xor_mem exists_isOpen_xor'_mem

/-- Specialization forms a partial order on a t0 topological space. -/
def specializationOrder (X) [TopologicalSpace X] [T0Space X] : PartialOrder X :=
  { specializationPreorder X, PartialOrder.lift (OrderDual.toDual ∘ 𝓝) nhds_injective with }
#align specialization_order specializationOrder

instance : T0Space (SeparationQuotient X) :=
  ⟨fun x y => Quotient.inductionOn₂' x y fun _ _ h =>
    SeparationQuotient.mk_eq_mk.2 <| SeparationQuotient.inducing_mk.inseparable_iff.1 h⟩

theorem minimal_nonempty_closed_subsingleton [T0Space X] {s : Set X} (hs : IsClosed s)
    (hmin : ∀ t, t ⊆ s → t.Nonempty → IsClosed t → t = s) : s.Subsingleton := by
  clear Y -- Porting note: added
  refine' fun x hx y hy => of_not_not fun hxy => _
  rcases exists_isOpen_xor'_mem hxy with ⟨U, hUo, hU⟩
  wlog h : x ∈ U ∧ y ∉ U
  · refine this hs hmin y hy x hx (Ne.symm hxy) U hUo hU.symm (hU.resolve_left h)
  cases' h with hxU hyU
  have : s \ U = s := hmin (s \ U) (diff_subset _ _) ⟨y, hy, hyU⟩ (hs.sdiff hUo)
  exact (this.symm.subset hx).2 hxU
#align minimal_nonempty_closed_subsingleton minimal_nonempty_closed_subsingleton

theorem minimal_nonempty_closed_eq_singleton [T0Space X] {s : Set X} (hs : IsClosed s)
    (hne : s.Nonempty) (hmin : ∀ t, t ⊆ s → t.Nonempty → IsClosed t → t = s) : ∃ x, s = {x} :=
  exists_eq_singleton_iff_nonempty_subsingleton.2
    ⟨hne, minimal_nonempty_closed_subsingleton hs hmin⟩
#align minimal_nonempty_closed_eq_singleton minimal_nonempty_closed_eq_singleton

/-- Given a closed set `S` in a compact T₀ space, there is some `x ∈ S` such that `{x}` is
closed. -/
theorem IsClosed.exists_closed_singleton [T0Space X] [CompactSpace X] {S : Set X}
    (hS : IsClosed S) (hne : S.Nonempty) : ∃ x : X, x ∈ S ∧ IsClosed ({x} : Set X) := by
  obtain ⟨V, Vsub, Vne, Vcls, hV⟩ := hS.exists_minimal_nonempty_closed_subset hne
  rcases minimal_nonempty_closed_eq_singleton Vcls Vne hV with ⟨x, rfl⟩
  exact ⟨x, Vsub (mem_singleton x), Vcls⟩
#align is_closed.exists_closed_singleton IsClosed.exists_closed_singleton

theorem minimal_nonempty_open_subsingleton [T0Space X] {s : Set X} (hs : IsOpen s)
    (hmin : ∀ t, t ⊆ s → t.Nonempty → IsOpen t → t = s) : s.Subsingleton := by
  clear Y -- Porting note: added
  refine' fun x hx y hy => of_not_not fun hxy => _
  rcases exists_isOpen_xor'_mem hxy with ⟨U, hUo, hU⟩
  wlog h : x ∈ U ∧ y ∉ U
  · exact this hs hmin y hy x hx (Ne.symm hxy) U hUo hU.symm (hU.resolve_left h)
  cases' h with hxU hyU
  have : s ∩ U = s := hmin (s ∩ U) (inter_subset_left _ _) ⟨x, hx, hxU⟩ (hs.inter hUo)
  exact hyU (this.symm.subset hy).2
#align minimal_nonempty_open_subsingleton minimal_nonempty_open_subsingleton

theorem minimal_nonempty_open_eq_singleton [T0Space X] {s : Set X} (hs : IsOpen s)
    (hne : s.Nonempty) (hmin : ∀ t, t ⊆ s → t.Nonempty → IsOpen t → t = s) : ∃ x, s = {x} :=
  exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨hne, minimal_nonempty_open_subsingleton hs hmin⟩
#align minimal_nonempty_open_eq_singleton minimal_nonempty_open_eq_singleton

/-- Given an open finite set `S` in a T₀ space, there is some `x ∈ S` such that `{x}` is open. -/
theorem exists_isOpen_singleton_of_isOpen_finite [T0Space X] {s : Set X} (hfin : s.Finite)
    (hne : s.Nonempty) (ho : IsOpen s) : ∃ x ∈ s, IsOpen ({x} : Set X) := by
  lift s to Finset X using hfin
  induction' s using Finset.strongInductionOn with s ihs
  rcases em (∃ t, t ⊂ s ∧ t.Nonempty ∧ IsOpen (t : Set X)) with (⟨t, hts, htne, hto⟩ | ht)
  · rcases ihs t hts htne hto with ⟨x, hxt, hxo⟩
    exact ⟨x, hts.1 hxt, hxo⟩
  · -- Porting note: was `rcases minimal_nonempty_open_eq_singleton ho hne _ with ⟨x, hx⟩`
    --               https://github.com/leanprover/std4/issues/116
    rsuffices ⟨x, hx⟩ : ∃ x, s.toSet = {x}
    · exact ⟨x, hx.symm ▸ rfl, hx ▸ ho⟩
    refine minimal_nonempty_open_eq_singleton ho hne ?_
    refine' fun t hts htne hto => of_not_not fun hts' => ht _
    lift t to Finset X using s.finite_toSet.subset hts
    exact ⟨t, ssubset_iff_subset_ne.2 ⟨hts, mt Finset.coe_inj.2 hts'⟩, htne, hto⟩
#align exists_open_singleton_of_open_finite exists_isOpen_singleton_of_isOpen_finite

theorem exists_open_singleton_of_finite [T0Space X] [Finite X] [Nonempty X] :
    ∃ x : X, IsOpen ({x} : Set X) :=
  let ⟨x, _, h⟩ := exists_isOpen_singleton_of_isOpen_finite (Set.toFinite _)
    univ_nonempty isOpen_univ
  ⟨x, h⟩
#align exists_open_singleton_of_fintype exists_open_singleton_of_finite

theorem t0Space_of_injective_of_continuous [TopologicalSpace Y] {f : X → Y}
    (hf : Function.Injective f) (hf' : Continuous f) [T0Space Y] : T0Space X :=
  ⟨fun _ _ h => hf <| (h.map hf').eq⟩
#align t0_space_of_injective_of_continuous t0Space_of_injective_of_continuous

protected theorem Embedding.t0Space [TopologicalSpace Y] [T0Space Y] {f : X → Y}
    (hf : Embedding f) : T0Space X :=
  t0Space_of_injective_of_continuous hf.inj hf.continuous
#align embedding.t0_space Embedding.t0Space

instance Subtype.t0Space [T0Space X] {p : X → Prop} : T0Space (Subtype p) :=
  embedding_subtype_val.t0Space
#align subtype.t0_space Subtype.t0Space

theorem t0Space_iff_or_not_mem_closure (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Pairwise fun a b : X => a ∉ closure ({b} : Set X) ∨ b ∉ closure ({a} : Set X) := by
  simp only [t0Space_iff_not_inseparable, inseparable_iff_mem_closure, not_and_or]
#align t0_space_iff_or_not_mem_closure t0Space_iff_or_not_mem_closure

instance Prod.instT0Space [TopologicalSpace Y] [T0Space X] [T0Space Y] : T0Space (X × Y) :=
  ⟨fun _ _ h => Prod.ext (h.map continuous_fst).eq (h.map continuous_snd).eq⟩

instance Pi.instT0Space {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, T0Space (X i)] :
    T0Space (∀ i, X i) :=
  ⟨fun _ _ h => funext fun i => (h.map (continuous_apply i)).eq⟩
#align pi.t0_space Pi.instT0Space

instance ULift.instT0Space [T0Space X] : T0Space (ULift X) :=
  embedding_uLift_down.t0Space

theorem T0Space.of_cover (h : ∀ x y, Inseparable x y → ∃ s : Set X, x ∈ s ∧ y ∈ s ∧ T0Space s) :
    T0Space X := by
  refine' ⟨fun x y hxy => _⟩
  rcases h x y hxy with ⟨s, hxs, hys, hs⟩
  lift x to s using hxs; lift y to s using hys
  rw [← subtype_inseparable_iff] at hxy
  exact congr_arg Subtype.val hxy.eq
#align t0_space.of_cover T0Space.of_cover

theorem T0Space.of_open_cover (h : ∀ x, ∃ s : Set X, x ∈ s ∧ IsOpen s ∧ T0Space s) : T0Space X :=
  T0Space.of_cover fun x _ hxy =>
    let ⟨s, hxs, hso, hs⟩ := h x
    ⟨s, hxs, (hxy.mem_open_iff hso).1 hxs, hs⟩
#align t0_space.of_open_cover T0Space.of_open_cover

/-- A T₁ space, also known as a Fréchet space, is a topological space
  where every singleton set is closed. Equivalently, for every pair
  `x ≠ y`, there is an open set containing `x` and not `y`. -/
class T1Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- A singleton in a T₁ space is a closed set. -/
  t1 : ∀ x, IsClosed ({x} : Set X)
#align t1_space T1Space

theorem isClosed_singleton [T1Space X] {x : X} : IsClosed ({x} : Set X) :=
  T1Space.t1 x
#align is_closed_singleton isClosed_singleton

theorem isOpen_compl_singleton [T1Space X] {x : X} : IsOpen ({x}ᶜ : Set X) :=
  isClosed_singleton.isOpen_compl
#align is_open_compl_singleton isOpen_compl_singleton

theorem isOpen_ne [T1Space X] {x : X} : IsOpen { y | y ≠ x } :=
  isOpen_compl_singleton
#align is_open_ne isOpen_ne

@[to_additive]
theorem Continuous.isOpen_mulSupport [T1Space X] [One X] [TopologicalSpace Y] {f : Y → X}
    (hf : Continuous f) : IsOpen (mulSupport f) :=
  isOpen_ne.preimage hf
#align continuous.is_open_mul_support Continuous.isOpen_mulSupport
#align continuous.is_open_support Continuous.isOpen_support

theorem Ne.nhdsWithin_compl_singleton [T1Space X] {x y : X} (h : x ≠ y) : 𝓝[{y}ᶜ] x = 𝓝 x :=
  isOpen_ne.nhdsWithin_eq h
#align ne.nhds_within_compl_singleton Ne.nhdsWithin_compl_singleton

theorem Ne.nhdsWithin_diff_singleton [T1Space X] {x y : X} (h : x ≠ y) (s : Set X) :
    𝓝[s \ {y}] x = 𝓝[s] x := by
  rw [diff_eq, inter_comm, nhdsWithin_inter_of_mem]
  exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds h)
#align ne.nhds_within_diff_singleton Ne.nhdsWithin_diff_singleton

lemma nhdsWithin_compl_singleton_le [T1Space X] (x y : X) : 𝓝[{x}ᶜ] x ≤ 𝓝[{y}ᶜ] x := by
  rcases eq_or_ne x y with rfl|hy
  · exact Eq.le rfl
  · rw [Ne.nhdsWithin_compl_singleton hy]
    exact nhdsWithin_le_nhds

theorem isOpen_setOf_eventually_nhdsWithin [T1Space X] {p : X → Prop} :
    IsOpen { x | ∀ᶠ y in 𝓝[≠] x, p y } := by
  refine' isOpen_iff_mem_nhds.mpr fun a ha => _
  filter_upwards [eventually_nhds_nhdsWithin.mpr ha] with b hb
  rcases eq_or_ne a b with rfl | h
  · exact hb
  · rw [h.symm.nhdsWithin_compl_singleton] at hb
    exact hb.filter_mono nhdsWithin_le_nhds
#align is_open_set_of_eventually_nhds_within isOpen_setOf_eventually_nhdsWithin

protected theorem Set.Finite.isClosed [T1Space X] {s : Set X} (hs : Set.Finite s) : IsClosed s := by
  rw [← biUnion_of_singleton s]
  exact hs.isClosed_biUnion fun i _ => isClosed_singleton
#align set.finite.is_closed Set.Finite.isClosed

theorem TopologicalSpace.IsTopologicalBasis.exists_mem_of_ne [T1Space X] {b : Set (Set X)}
    (hb : IsTopologicalBasis b) {x y : X} (h : x ≠ y) : ∃ a ∈ b, x ∈ a ∧ y ∉ a := by
  rcases hb.isOpen_iff.1 isOpen_ne x h with ⟨a, ab, xa, ha⟩
  exact ⟨a, ab, xa, fun h => ha h rfl⟩
#align topological_space.is_topological_basis.exists_mem_of_ne TopologicalSpace.IsTopologicalBasis.exists_mem_of_ne

theorem Filter.coclosedCompact_le_cofinite [T1Space X] :
    Filter.coclosedCompact X ≤ Filter.cofinite := fun s hs =>
  compl_compl s ▸ hs.isCompact.compl_mem_coclosedCompact_of_isClosed hs.isClosed
#align filter.coclosed_compact_le_cofinite Filter.coclosedCompact_le_cofinite

variable (X)

/-- In a `T1Space`, relatively compact sets form a bornology. Its cobounded filter is
`Filter.coclosedCompact`. See also `Bornology.inCompact` the bornology of sets contained
in a compact set. -/
def Bornology.relativelyCompact [T1Space X] : Bornology X where
  cobounded' := Filter.coclosedCompact X
  le_cofinite' := Filter.coclosedCompact_le_cofinite
#align bornology.relatively_compact Bornology.relativelyCompact

variable {X}

theorem Bornology.relativelyCompact.isBounded_iff [T1Space X] {s : Set X} :
    @Bornology.IsBounded _ (Bornology.relativelyCompact X) s ↔ IsCompact (closure s) := by
  change sᶜ ∈ Filter.coclosedCompact X ↔ _
  rw [Filter.mem_coclosedCompact]
  constructor
  · rintro ⟨t, ht₁, ht₂, hst⟩
    rw [compl_subset_compl] at hst
    exact ht₂.of_isClosed_subset isClosed_closure (closure_minimal hst ht₁)
  · intro h
    exact ⟨closure s, isClosed_closure, h, compl_subset_compl.mpr subset_closure⟩
#align bornology.relatively_compact.is_bounded_iff Bornology.relativelyCompact.isBounded_iff

protected theorem Finset.isClosed [T1Space X] (s : Finset X) : IsClosed (s : Set X) :=
  s.finite_toSet.isClosed
#align finset.is_closed Finset.isClosed

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
      ∀ ⦃x y : X⦄, x ⤳ y → x = y] := by
  tfae_have 1 ↔ 2
  · exact ⟨fun h => h.1, fun h => ⟨h⟩⟩
  tfae_have 2 ↔ 3
  · simp only [isOpen_compl_iff]
  tfae_have 5 ↔ 3
  · refine' forall_swap.trans _
    simp only [isOpen_iff_mem_nhds, mem_compl_iff, mem_singleton_iff]
  tfae_have 5 ↔ 6
  · simp only [← subset_compl_singleton_iff, exists_mem_subset_iff]
  tfae_have 5 ↔ 7
  · simp only [(nhds_basis_opens _).mem_iff, subset_compl_singleton_iff, exists_prop, and_assoc,
      and_left_comm]
  tfae_have 5 ↔ 8
  · simp only [← principal_singleton, disjoint_principal_right]
  tfae_have 8 ↔ 9
  · exact forall_swap.trans (by simp only [disjoint_comm, ne_comm])
  tfae_have 1 → 4
  · simp only [continuous_def, CofiniteTopology.isOpen_iff']
    rintro H s (rfl | hs)
    exacts [isOpen_empty, compl_compl s ▸ (@Set.Finite.isClosed _ _ H _ hs).isOpen_compl]
  tfae_have 4 → 2
  · exact fun h x => (CofiniteTopology.isClosed_iff.2 <| Or.inr (finite_singleton _)).preimage h
  tfae_have 2 ↔ 10
  · simp only [← closure_subset_iff_isClosed, specializes_iff_mem_closure, subset_def,
      mem_singleton_iff, eq_comm]
  tfae_finish
#align t1_space_tfae t1Space_TFAE

theorem t1Space_iff_continuous_cofinite_of : T1Space X ↔ Continuous (@CofiniteTopology.of X) :=
  (t1Space_TFAE X).out 0 3
#align t1_space_iff_continuous_cofinite_of t1Space_iff_continuous_cofinite_of

theorem CofiniteTopology.continuous_of [T1Space X] : Continuous (@CofiniteTopology.of X) :=
  t1Space_iff_continuous_cofinite_of.mp ‹_›
#align cofinite_topology.continuous_of CofiniteTopology.continuous_of

theorem t1Space_iff_exists_open :
    T1Space X ↔ Pairwise fun x y => ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ y ∉ U :=
  (t1Space_TFAE X).out 0 6
#align t1_space_iff_exists_open t1Space_iff_exists_open

theorem t1Space_iff_disjoint_pure_nhds : T1Space X ↔ ∀ ⦃x y : X⦄, x ≠ y → Disjoint (pure x) (𝓝 y) :=
  (t1Space_TFAE X).out 0 8
#align t1_space_iff_disjoint_pure_nhds t1Space_iff_disjoint_pure_nhds

theorem t1Space_iff_disjoint_nhds_pure : T1Space X ↔ ∀ ⦃x y : X⦄, x ≠ y → Disjoint (𝓝 x) (pure y) :=
  (t1Space_TFAE X).out 0 7
#align t1_space_iff_disjoint_nhds_pure t1Space_iff_disjoint_nhds_pure

theorem t1Space_iff_specializes_imp_eq : T1Space X ↔ ∀ ⦃x y : X⦄, x ⤳ y → x = y :=
  (t1Space_TFAE X).out 0 9
#align t1_space_iff_specializes_imp_eq t1Space_iff_specializes_imp_eq

theorem disjoint_pure_nhds [T1Space X] {x y : X} (h : x ≠ y) : Disjoint (pure x) (𝓝 y) :=
  t1Space_iff_disjoint_pure_nhds.mp ‹_› h
#align disjoint_pure_nhds disjoint_pure_nhds

theorem disjoint_nhds_pure [T1Space X] {x y : X} (h : x ≠ y) : Disjoint (𝓝 x) (pure y) :=
  t1Space_iff_disjoint_nhds_pure.mp ‹_› h
#align disjoint_nhds_pure disjoint_nhds_pure

theorem Specializes.eq [T1Space X] {x y : X} (h : x ⤳ y) : x = y :=
  t1Space_iff_specializes_imp_eq.1 ‹_› h
#align specializes.eq Specializes.eq

theorem specializes_iff_eq [T1Space X] {x y : X} : x ⤳ y ↔ x = y :=
  ⟨Specializes.eq, fun h => h ▸ specializes_rfl⟩
#align specializes_iff_eq specializes_iff_eq

@[simp] theorem specializes_eq_eq [T1Space X] : (· ⤳ ·) = @Eq X :=
  funext₂ fun _ _ => propext specializes_iff_eq
#align specializes_eq_eq specializes_eq_eq

@[simp]
theorem pure_le_nhds_iff [T1Space X] {a b : X} : pure a ≤ 𝓝 b ↔ a = b :=
  specializes_iff_pure.symm.trans specializes_iff_eq
#align pure_le_nhds_iff pure_le_nhds_iff

@[simp]
theorem nhds_le_nhds_iff [T1Space X] {a b : X} : 𝓝 a ≤ 𝓝 b ↔ a = b :=
  specializes_iff_eq
#align nhds_le_nhds_iff nhds_le_nhds_iff

instance : T1Space (CofiniteTopology X) :=
  t1Space_iff_continuous_cofinite_of.mpr continuous_id

theorem t1Space_antitone : Antitone (@T1Space X) := fun a _ h _ =>
  @T1Space.mk _ a fun x => (T1Space.t1 x).mono h
#align t1_space_antitone t1Space_antitone

theorem continuousWithinAt_update_of_ne [T1Space X] [DecidableEq X] [TopologicalSpace Y] {f : X → Y}
    {s : Set X} {x x' : X} {y : Y} (hne : x' ≠ x) :
    ContinuousWithinAt (Function.update f x y) s x' ↔ ContinuousWithinAt f s x' :=
  EventuallyEq.congr_continuousWithinAt
    (mem_nhdsWithin_of_mem_nhds <| mem_of_superset (isOpen_ne.mem_nhds hne) fun _y' hy' =>
      Function.update_noteq hy' _ _)
    (Function.update_noteq hne _ _)
#align continuous_within_at_update_of_ne continuousWithinAt_update_of_ne

theorem continuousAt_update_of_ne [T1Space X] [DecidableEq X] [TopologicalSpace Y]
    {f : X → Y} {x x' : X} {y : Y} (hne : x' ≠ x) :
    ContinuousAt (Function.update f x y) x' ↔ ContinuousAt f x' := by
  simp only [← continuousWithinAt_univ, continuousWithinAt_update_of_ne hne]
#align continuous_at_update_of_ne continuousAt_update_of_ne

theorem continuousOn_update_iff [T1Space X] [DecidableEq X] [TopologicalSpace Y] {f : X → Y}
    {s : Set X} {x : X} {y : Y} :
    ContinuousOn (Function.update f x y) s ↔
      ContinuousOn f (s \ {x}) ∧ (x ∈ s → Tendsto f (𝓝[s \ {x}] x) (𝓝 y)) := by
  rw [ContinuousOn, ← and_forall_ne x, and_comm]
  refine' and_congr ⟨fun H z hz => _, fun H z hzx hzs => _⟩ (forall_congr' fun _ => _)
  · specialize H z hz.2 hz.1
    rw [continuousWithinAt_update_of_ne hz.2] at H
    exact H.mono (diff_subset _ _)
  · rw [continuousWithinAt_update_of_ne hzx]
    refine' (H z ⟨hzs, hzx⟩).mono_of_mem (inter_mem_nhdsWithin _ _)
    exact isOpen_ne.mem_nhds hzx
  · exact continuousWithinAt_update_same
#align continuous_on_update_iff continuousOn_update_iff

theorem t1Space_of_injective_of_continuous [TopologicalSpace Y] {f : X → Y}
    (hf : Function.Injective f) (hf' : Continuous f) [T1Space Y] : T1Space X :=
  t1Space_iff_specializes_imp_eq.2 fun _ _ h => hf (h.map hf').eq
#align t1_space_of_injective_of_continuous t1Space_of_injective_of_continuous

protected theorem Embedding.t1Space [TopologicalSpace Y] [T1Space Y] {f : X → Y}
    (hf : Embedding f) : T1Space X :=
  t1Space_of_injective_of_continuous hf.inj hf.continuous
#align embedding.t1_space Embedding.t1Space

instance Subtype.t1Space {X : Type u} [TopologicalSpace X] [T1Space X] {p : X → Prop} :
    T1Space (Subtype p) :=
  embedding_subtype_val.t1Space
#align subtype.t1_space Subtype.t1Space

instance [TopologicalSpace Y] [T1Space X] [T1Space Y] : T1Space (X × Y) :=
  ⟨fun ⟨a, b⟩ => @singleton_prod_singleton _ _ a b ▸ isClosed_singleton.prod isClosed_singleton⟩

instance {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, T1Space (X i)] :
    T1Space (∀ i, X i) :=
  ⟨fun f => univ_pi_singleton f ▸ isClosed_set_pi fun _ _ => isClosed_singleton⟩

instance ULift.instT1Space [T1Space X] : T1Space (ULift X) :=
  embedding_uLift_down.t1Space

-- see Note [lower instance priority]
instance (priority := 100) T1Space.t0Space [T1Space X] : T0Space X :=
  ⟨fun _ _ h => h.specializes.eq⟩
#align t1_space.t0_space T1Space.t0Space

@[simp]
theorem compl_singleton_mem_nhds_iff [T1Space X] {x y : X} : {x}ᶜ ∈ 𝓝 y ↔ y ≠ x :=
  isOpen_compl_singleton.mem_nhds_iff
#align compl_singleton_mem_nhds_iff compl_singleton_mem_nhds_iff

theorem compl_singleton_mem_nhds [T1Space X] {x y : X} (h : y ≠ x) : {x}ᶜ ∈ 𝓝 y :=
  compl_singleton_mem_nhds_iff.mpr h
#align compl_singleton_mem_nhds compl_singleton_mem_nhds

@[simp]
theorem closure_singleton [T1Space X] {x : X} : closure ({x} : Set X) = {x} :=
  isClosed_singleton.closure_eq
#align closure_singleton closure_singleton

-- porting note: todo: the proof was `hs.induction_on (by simp) fun x => by simp`
theorem Set.Subsingleton.closure [T1Space X] {s : Set X} (hs : s.Subsingleton) :
    (closure s).Subsingleton := by
  rcases hs.eq_empty_or_singleton with (rfl | ⟨x, rfl⟩) <;> simp
#align set.subsingleton.closure Set.Subsingleton.closure

@[simp]
theorem subsingleton_closure [T1Space X] {s : Set X} : (closure s).Subsingleton ↔ s.Subsingleton :=
  ⟨fun h => h.anti subset_closure, fun h => h.closure⟩
#align subsingleton_closure subsingleton_closure

theorem isClosedMap_const {X Y} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y] {y : Y} :
    IsClosedMap (Function.const X y) :=
  IsClosedMap.of_nonempty fun s _ h2s => by simp_rw [const, h2s.image_const, isClosed_singleton]
#align is_closed_map_const isClosedMap_const

theorem nhdsWithin_insert_of_ne [T1Space X] {x y : X} {s : Set X} (hxy : x ≠ y) :
    𝓝[insert y s] x = 𝓝[s] x := by
  refine' le_antisymm (Filter.le_def.2 fun t ht => _) (nhdsWithin_mono x <| subset_insert y s)
  obtain ⟨o, ho, hxo, host⟩ := mem_nhdsWithin.mp ht
  refine' mem_nhdsWithin.mpr ⟨o \ {y}, ho.sdiff isClosed_singleton, ⟨hxo, hxy⟩, _⟩
  rw [inter_insert_of_not_mem <| not_mem_diff_of_mem (mem_singleton y)]
  exact (inter_subset_inter (diff_subset _ _) Subset.rfl).trans host
#align nhds_within_insert_of_ne nhdsWithin_insert_of_ne

/-- If `t` is a subset of `s`, except for one point,
then `insert x s` is a neighborhood of `x` within `t`. -/
theorem insert_mem_nhdsWithin_of_subset_insert [T1Space X] {x y : X} {s t : Set X}
    (hu : t ⊆ insert y s) : insert x s ∈ 𝓝[t] x := by
  rcases eq_or_ne x y with (rfl | h)
  · exact mem_of_superset self_mem_nhdsWithin hu
  refine' nhdsWithin_mono x hu _
  rw [nhdsWithin_insert_of_ne h]
  exact mem_of_superset self_mem_nhdsWithin (subset_insert x s)
#align insert_mem_nhds_within_of_subset_insert insert_mem_nhdsWithin_of_subset_insert

@[simp]
theorem ker_nhds [T1Space X] (x : X) : (𝓝 x).ker = {x} := by
  simp [ker_nhds_eq_specializes]

theorem biInter_basis_nhds [T1Space X] {ι : Sort*} {p : ι → Prop} {s : ι → Set X} {x : X}
    (h : (𝓝 x).HasBasis p s) : ⋂ (i) (_ : p i), s i = {x} := by
  rw [← h.ker, ker_nhds]
#align bInter_basis_nhds biInter_basis_nhds

@[simp]
theorem compl_singleton_mem_nhdsSet_iff [T1Space X] {x : X} {s : Set X} : {x}ᶜ ∈ 𝓝ˢ s ↔ x ∉ s := by
  rw [isOpen_compl_singleton.mem_nhdsSet, subset_compl_singleton_iff]
#align compl_singleton_mem_nhds_set_iff compl_singleton_mem_nhdsSet_iff

@[simp]
theorem nhdsSet_le_iff [T1Space X] {s t : Set X} : 𝓝ˢ s ≤ 𝓝ˢ t ↔ s ⊆ t := by
  refine' ⟨_, fun h => monotone_nhdsSet h⟩
  simp_rw [Filter.le_def]; intro h x hx
  specialize h {x}ᶜ
  simp_rw [compl_singleton_mem_nhdsSet_iff] at h
  by_contra hxt
  exact h hxt hx
#align nhds_set_le_iff nhdsSet_le_iff

@[simp]
theorem nhdsSet_inj_iff [T1Space X] {s t : Set X} : 𝓝ˢ s = 𝓝ˢ t ↔ s = t := by
  simp_rw [le_antisymm_iff]
  exact and_congr nhdsSet_le_iff nhdsSet_le_iff
#align nhds_set_inj_iff nhdsSet_inj_iff

theorem injective_nhdsSet [T1Space X] : Function.Injective (𝓝ˢ : Set X → Filter X) := fun _ _ hst =>
  nhdsSet_inj_iff.mp hst
#align injective_nhds_set injective_nhdsSet

theorem strictMono_nhdsSet [T1Space X] : StrictMono (𝓝ˢ : Set X → Filter X) :=
  monotone_nhdsSet.strictMono_of_injective injective_nhdsSet
#align strict_mono_nhds_set strictMono_nhdsSet

@[simp]
theorem nhds_le_nhdsSet_iff [T1Space X] {s : Set X} {x : X} : 𝓝 x ≤ 𝓝ˢ s ↔ x ∈ s := by
  rw [← nhdsSet_singleton, nhdsSet_le_iff, singleton_subset_iff]
#align nhds_le_nhds_set_iff nhds_le_nhdsSet_iff

/-- Removing a non-isolated point from a dense set, one still obtains a dense set. -/
theorem Dense.diff_singleton [T1Space X] {s : Set X} (hs : Dense s) (x : X) [NeBot (𝓝[≠] x)] :
    Dense (s \ {x}) :=
  hs.inter_of_isOpen_right (dense_compl_singleton x) isOpen_compl_singleton
#align dense.diff_singleton Dense.diff_singleton

/-- Removing a finset from a dense set in a space without isolated points, one still
obtains a dense set. -/
theorem Dense.diff_finset [T1Space X] [∀ x : X, NeBot (𝓝[≠] x)] {s : Set X} (hs : Dense s)
    (t : Finset X) : Dense (s \ t) := by
  induction t using Finset.induction_on with
  | empty => simpa using hs
  | insert _ ih =>
    rw [Finset.coe_insert, ← union_singleton, ← diff_diff]
    exact ih.diff_singleton _
#align dense.diff_finset Dense.diff_finset

/-- Removing a finite set from a dense set in a space without isolated points, one still
obtains a dense set. -/
theorem Dense.diff_finite [T1Space X] [∀ x : X, NeBot (𝓝[≠] x)] {s : Set X} (hs : Dense s)
    {t : Set X} (ht : t.Finite) : Dense (s \ t) := by
  convert hs.diff_finset ht.toFinset
  exact (Finite.coe_toFinset _).symm
#align dense.diff_finite Dense.diff_finite

/-- If a function to a `T1Space` tends to some limit `y` at some point `x`, then necessarily
`y = f x`. -/
theorem eq_of_tendsto_nhds [TopologicalSpace Y] [T1Space Y] {f : X → Y} {x : X} {y : Y}
    (h : Tendsto f (𝓝 x) (𝓝 y)) : f x = y :=
  by_contra fun hfa : f x ≠ y =>
    have fact₁ : {f x}ᶜ ∈ 𝓝 y := compl_singleton_mem_nhds hfa.symm
    have fact₂ : Tendsto f (pure x) (𝓝 y) := h.comp (tendsto_id'.2 <| pure_le_nhds x)
    fact₂ fact₁ (Eq.refl <| f x)
#align eq_of_tendsto_nhds eq_of_tendsto_nhds

theorem Filter.Tendsto.eventually_ne [TopologicalSpace Y] [T1Space Y] {g : X → Y}
    {l : Filter X} {b₁ b₂ : Y} (hg : Tendsto g l (𝓝 b₁)) (hb : b₁ ≠ b₂) : ∀ᶠ z in l, g z ≠ b₂ :=
  hg.eventually (isOpen_compl_singleton.eventually_mem hb)
#align filter.tendsto.eventually_ne Filter.Tendsto.eventually_ne

theorem ContinuousAt.eventually_ne [TopologicalSpace Y] [T1Space Y] {g : X → Y} {x : X} {y : Y}
    (hg1 : ContinuousAt g x) (hg2 : g x ≠ y) : ∀ᶠ z in 𝓝 x, g z ≠ y :=
  hg1.tendsto.eventually_ne hg2
#align continuous_at.eventually_ne ContinuousAt.eventually_ne

theorem eventually_ne_nhds [T1Space X] {a b : X} (h : a ≠ b) : ∀ᶠ x in 𝓝 a, x ≠ b :=
  IsOpen.eventually_mem isOpen_ne h

theorem eventually_ne_nhdsWithin [T1Space X] {a b : X} {s : Set X} (h : a ≠ b) :
    ∀ᶠ x in 𝓝[s] a, x ≠ b :=
  Filter.Eventually.filter_mono nhdsWithin_le_nhds <| eventually_ne_nhds h

/-- To prove a function to a `T1Space` is continuous at some point `x`, it suffices to prove that
`f` admits *some* limit at `x`. -/
theorem continuousAt_of_tendsto_nhds [TopologicalSpace Y] [T1Space Y] {f : X → Y} {x : X} {y : Y}
    (h : Tendsto f (𝓝 x) (𝓝 y)) : ContinuousAt f x := by
  rwa [ContinuousAt, eq_of_tendsto_nhds h]
#align continuous_at_of_tendsto_nhds continuousAt_of_tendsto_nhds

@[simp]
theorem tendsto_const_nhds_iff [T1Space X] {l : Filter Y} [NeBot l] {c d : X} :
    Tendsto (fun _ => c) l (𝓝 d) ↔ c = d := by simp_rw [Tendsto, Filter.map_const, pure_le_nhds_iff]
#align tendsto_const_nhds_iff tendsto_const_nhds_iff

/-- A point with a finite neighborhood has to be isolated. -/
theorem isOpen_singleton_of_finite_mem_nhds [T1Space X] (x : X)
    {s : Set X} (hs : s ∈ 𝓝 x) (hsf : s.Finite) : IsOpen ({x} : Set X) := by
  have A : {x} ⊆ s := by simp only [singleton_subset_iff, mem_of_mem_nhds hs]
  have B : IsClosed (s \ {x}) := (hsf.subset (diff_subset _ _)).isClosed
  have C : (s \ {x})ᶜ ∈ 𝓝 x := B.isOpen_compl.mem_nhds fun h => h.2 rfl
  have D : {x} ∈ 𝓝 x := by simpa only [← diff_eq, diff_diff_cancel_left A] using inter_mem hs C
  rwa [← mem_interior_iff_mem_nhds, ← singleton_subset_iff, subset_interior_iff_isOpen] at D
#align is_open_singleton_of_finite_mem_nhds isOpen_singleton_of_finite_mem_nhds

/-- If the punctured neighborhoods of a point form a nontrivial filter, then any neighborhood is
infinite. -/
theorem infinite_of_mem_nhds {X} [TopologicalSpace X] [T1Space X] (x : X) [hx : NeBot (𝓝[≠] x)]
    {s : Set X} (hs : s ∈ 𝓝 x) : Set.Infinite s := by
  refine' fun hsf => hx.1 _
  rw [← isOpen_singleton_iff_punctured_nhds]
  exact isOpen_singleton_of_finite_mem_nhds x hs hsf
#align infinite_of_mem_nhds infinite_of_mem_nhds

theorem discrete_of_t1_of_finite [T1Space X] [Finite X] :
    DiscreteTopology X := by
  apply singletons_open_iff_discrete.mp
  intro x
  rw [← isClosed_compl_iff]
  exact (Set.toFinite _).isClosed
#align discrete_of_t1_of_finite discrete_of_t1_of_finite

theorem PreconnectedSpace.trivial_of_discrete [PreconnectedSpace X] [DiscreteTopology X] :
    Subsingleton X := by
  rw [← not_nontrivial_iff_subsingleton]
  rintro ⟨x, y, hxy⟩
  rw [Ne.def, ← mem_singleton_iff, (isClopen_discrete _).eq_univ <| singleton_nonempty y] at hxy
  exact hxy (mem_univ x)
#align preconnected_space.trivial_of_discrete PreconnectedSpace.trivial_of_discrete

theorem IsPreconnected.infinite_of_nontrivial [T1Space X] {s : Set X} (h : IsPreconnected s)
    (hs : s.Nontrivial) : s.Infinite := by
  refine' mt (fun hf => (subsingleton_coe s).mp _) (not_subsingleton_iff.mpr hs)
  haveI := @discrete_of_t1_of_finite s _ _ hf.to_subtype
  exact @PreconnectedSpace.trivial_of_discrete _ _ (Subtype.preconnectedSpace h) _
#align is_preconnected.infinite_of_nontrivial IsPreconnected.infinite_of_nontrivial

theorem ConnectedSpace.infinite [ConnectedSpace X] [Nontrivial X] [T1Space X] : Infinite X :=
  infinite_univ_iff.mp <| isPreconnected_univ.infinite_of_nontrivial nontrivial_univ
#align connected_space.infinite ConnectedSpace.infinite

/-- A non-trivial connected T1 space has no isolated points. -/
instance (priority := 100) ConnectedSpace.neBot_nhdsWithin_compl_of_nontrivial_of_t1space
    [ConnectedSpace X] [Nontrivial X] [T1Space X] (x : X) :
    NeBot (𝓝[≠] x) := by
  by_contra contra
  rw [not_neBot, ← isOpen_singleton_iff_punctured_nhds] at contra
  replace contra := nonempty_inter isOpen_compl_singleton
    contra (compl_union_self _) (Set.nonempty_compl_of_nontrivial _) (singleton_nonempty _)
  simp [compl_inter_self {x}] at contra

theorem singleton_mem_nhdsWithin_of_mem_discrete {s : Set X} [DiscreteTopology s] {x : X}
    (hx : x ∈ s) : {x} ∈ 𝓝[s] x := by
  have : ({⟨x, hx⟩} : Set s) ∈ 𝓝 (⟨x, hx⟩ : s) := by simp [nhds_discrete]
  simpa only [nhdsWithin_eq_map_subtype_coe hx, image_singleton] using
    @image_mem_map _ _ _ ((↑) : s → X) _ this
#align singleton_mem_nhds_within_of_mem_discrete singleton_mem_nhdsWithin_of_mem_discrete

/-- The neighbourhoods filter of `x` within `s`, under the discrete topology, is equal to
the pure `x` filter (which is the principal filter at the singleton `{x}`.) -/
theorem nhdsWithin_of_mem_discrete {s : Set X} [DiscreteTopology s] {x : X} (hx : x ∈ s) :
    𝓝[s] x = pure x :=
  le_antisymm (le_pure_iff.2 <| singleton_mem_nhdsWithin_of_mem_discrete hx) (pure_le_nhdsWithin hx)
#align nhds_within_of_mem_discrete nhdsWithin_of_mem_discrete

theorem Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete {ι : Type*} {p : ι → Prop}
    {t : ι → Set X} {s : Set X} [DiscreteTopology s] {x : X} (hb : (𝓝 x).HasBasis p t)
    (hx : x ∈ s) : ∃ i, p i ∧ t i ∩ s = {x} := by
  rcases (nhdsWithin_hasBasis hb s).mem_iff.1 (singleton_mem_nhdsWithin_of_mem_discrete hx) with
    ⟨i, hi, hix⟩
  exact ⟨i, hi, hix.antisymm <| singleton_subset_iff.2 ⟨mem_of_mem_nhds <| hb.mem_of_mem hi, hx⟩⟩
#align filter.has_basis.exists_inter_eq_singleton_of_mem_discrete Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete

/-- A point `x` in a discrete subset `s` of a topological space admits a neighbourhood
that only meets `s` at `x`.  -/
theorem nhds_inter_eq_singleton_of_mem_discrete {s : Set X} [DiscreteTopology s] {x : X}
    (hx : x ∈ s) : ∃ U ∈ 𝓝 x, U ∩ s = {x} := by
  simpa using (𝓝 x).basis_sets.exists_inter_eq_singleton_of_mem_discrete hx
#align nhds_inter_eq_singleton_of_mem_discrete nhds_inter_eq_singleton_of_mem_discrete

/-- Let `x` be a point in a discrete subset `s` of a topological space, then there exists an open
set that only meets `s` at `x`.  -/
theorem isOpen_inter_eq_singleton_of_mem_discrete {s : Set X} [DiscreteTopology s] {x : X}
    (hx : x ∈ s) : ∃ U : Set X, IsOpen U ∧ U ∩ s = {x} := by
  obtain ⟨U, hU_nhds, hU_inter⟩ := nhds_inter_eq_singleton_of_mem_discrete hx
  obtain ⟨t, ht_sub, ht_open, ht_x⟩ := mem_nhds_iff.mp hU_nhds
  refine ⟨t, ht_open, Set.Subset.antisymm ?_ ?_⟩
  · exact hU_inter ▸ Set.inter_subset_inter_left s ht_sub
  · rw [Set.subset_inter_iff, Set.singleton_subset_iff, Set.singleton_subset_iff]
    exact ⟨ht_x, hx⟩

/-- For point `x` in a discrete subset `s` of a topological space, there is a set `U`
such that
1. `U` is a punctured neighborhood of `x` (ie. `U ∪ {x}` is a neighbourhood of `x`),
2. `U` is disjoint from `s`.
-/
theorem disjoint_nhdsWithin_of_mem_discrete {s : Set X} [DiscreteTopology s] {x : X} (hx : x ∈ s) :
    ∃ U ∈ 𝓝[≠] x, Disjoint U s :=
  let ⟨V, h, h'⟩ := nhds_inter_eq_singleton_of_mem_discrete hx
  ⟨{x}ᶜ ∩ V, inter_mem_nhdsWithin _ h,
    disjoint_iff_inter_eq_empty.mpr (by rw [inter_assoc, h', compl_inter_self])⟩
#align disjoint_nhds_within_of_mem_discrete disjoint_nhdsWithin_of_mem_discrete

/-- Let `X` be a topological space and let `s, t ⊆ X` be two subsets.  If there is an inclusion
`t ⊆ s`, then the topological space structure on `t` induced by `X` is the same as the one
obtained by the induced topological space structure on `s`. Use `embedding_inclusion` instead. -/
@[deprecated embedding_inclusion]
theorem TopologicalSpace.subset_trans {s t : Set X} (ts : t ⊆ s) :
    (instTopologicalSpaceSubtype : TopologicalSpace t) =
      (instTopologicalSpaceSubtype : TopologicalSpace s).induced (Set.inclusion ts) :=
  (embedding_inclusion ts).induced
#align topological_space.subset_trans TopologicalSpace.subset_trans

/-- A T₂ space, also known as a Hausdorff space, is one in which for every
  `x ≠ y` there exists disjoint open sets around `x` and `y`. This is
  the most widely used of the separation axioms. -/
@[mk_iff]
class T2Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Every two points in a Hausdorff space admit disjoint open neighbourhoods. -/
  t2 : Pairwise fun x y => ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v
#align t2_space T2Space

/-- Two different points can be separated by open sets. -/
theorem t2_separation [T2Space X] {x y : X} (h : x ≠ y) :
    ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v :=
  T2Space.t2 h
#align t2_separation t2_separation

-- todo: use this as a definition?
theorem t2Space_iff_disjoint_nhds : T2Space X ↔ Pairwise fun x y : X => Disjoint (𝓝 x) (𝓝 y) := by
  refine (t2Space_iff X).trans (forall₃_congr fun x y _ => ?_)
  simp only [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens y), exists_prop, ← exists_and_left,
    and_assoc, and_comm, and_left_comm]
#align t2_space_iff_disjoint_nhds t2Space_iff_disjoint_nhds

@[simp]
theorem disjoint_nhds_nhds [T2Space X] {x y : X} : Disjoint (𝓝 x) (𝓝 y) ↔ x ≠ y :=
  ⟨fun hd he => by simp [he, nhds_neBot.ne] at hd, (t2Space_iff_disjoint_nhds.mp ‹_› ·)⟩
#align disjoint_nhds_nhds disjoint_nhds_nhds

theorem pairwise_disjoint_nhds [T2Space X] : Pairwise (Disjoint on (𝓝 : X → Filter X)) := fun _ _ =>
  disjoint_nhds_nhds.2
#align pairwise_disjoint_nhds pairwise_disjoint_nhds

protected theorem Set.pairwiseDisjoint_nhds [T2Space X] (s : Set X) : s.PairwiseDisjoint 𝓝 :=
  pairwise_disjoint_nhds.set_pairwise s
#align set.pairwise_disjoint_nhds Set.pairwiseDisjoint_nhds

/-- Points of a finite set can be separated by open sets from each other. -/
theorem Set.Finite.t2_separation [T2Space X] {s : Set X} (hs : s.Finite) :
    ∃ U : X → Set X, (∀ x, x ∈ U x ∧ IsOpen (U x)) ∧ s.PairwiseDisjoint U :=
  s.pairwiseDisjoint_nhds.exists_mem_filter_basis hs nhds_basis_opens
#align set.finite.t2_separation Set.Finite.t2_separation

theorem isOpen_setOf_disjoint_nhds_nhds : IsOpen { p : X × X | Disjoint (𝓝 p.1) (𝓝 p.2) } := by
  simp only [isOpen_iff_mem_nhds, Prod.forall, mem_setOf_eq]
  intro x y h
  obtain ⟨U, hU, V, hV, hd⟩ := ((nhds_basis_opens x).disjoint_iff (nhds_basis_opens y)).mp h
  exact
    mem_nhds_prod_iff.mpr
      ⟨U, hU.2.mem_nhds hU.1, V, hV.2.mem_nhds hV.1, fun ⟨x', y'⟩ ⟨hx', hy'⟩ =>
        disjoint_of_disjoint_of_mem hd (hU.2.mem_nhds hx') (hV.2.mem_nhds hy')⟩
#align is_open_set_of_disjoint_nhds_nhds isOpen_setOf_disjoint_nhds_nhds

-- see Note [lower instance priority]
instance (priority := 100) T2Space.t1Space [T2Space X] : T1Space X :=
  t1Space_iff_disjoint_pure_nhds.mpr fun _ _ hne =>
    (disjoint_nhds_nhds.2 hne).mono_left <| pure_le_nhds _
#align t2_space.t1_space T2Space.t1Space

/-- A space is T₂ iff the neighbourhoods of distinct points generate the bottom filter. -/
theorem t2_iff_nhds : T2Space X ↔ ∀ {x y : X}, NeBot (𝓝 x ⊓ 𝓝 y) → x = y := by
  simp only [t2Space_iff_disjoint_nhds, disjoint_iff, neBot_iff, Ne.def, not_imp_comm, Pairwise]
#align t2_iff_nhds t2_iff_nhds

theorem eq_of_nhds_neBot [T2Space X] {x y : X} (h : NeBot (𝓝 x ⊓ 𝓝 y)) : x = y :=
  t2_iff_nhds.mp ‹_› h
#align eq_of_nhds_ne_bot eq_of_nhds_neBot

theorem t2Space_iff_nhds :
    T2Space X ↔ Pairwise fun x y : X => ∃ U ∈ 𝓝 x, ∃ V ∈ 𝓝 y, Disjoint U V := by
  simp only [t2Space_iff_disjoint_nhds, Filter.disjoint_iff, Pairwise]
#align t2_space_iff_nhds t2Space_iff_nhds

theorem t2_separation_nhds [T2Space X] {x y : X} (h : x ≠ y) :
    ∃ u v, u ∈ 𝓝 x ∧ v ∈ 𝓝 y ∧ Disjoint u v :=
  let ⟨u, v, open_u, open_v, x_in, y_in, huv⟩ := t2_separation h
  ⟨u, v, open_u.mem_nhds x_in, open_v.mem_nhds y_in, huv⟩
#align t2_separation_nhds t2_separation_nhds

theorem t2_separation_compact_nhds [LocallyCompactSpace X] [T2Space X] {x y : X} (h : x ≠ y) :
    ∃ u v, u ∈ 𝓝 x ∧ v ∈ 𝓝 y ∧ IsCompact u ∧ IsCompact v ∧ Disjoint u v := by
  simpa only [exists_prop, ← exists_and_left, and_comm, and_assoc, and_left_comm] using
    ((compact_basis_nhds x).disjoint_iff (compact_basis_nhds y)).1 (disjoint_nhds_nhds.2 h)
#align t2_separation_compact_nhds t2_separation_compact_nhds

theorem t2_iff_ultrafilter :
    T2Space X ↔ ∀ {x y : X} (f : Ultrafilter X), ↑f ≤ 𝓝 x → ↑f ≤ 𝓝 y → x = y :=
  t2_iff_nhds.trans <| by simp only [← exists_ultrafilter_iff, and_imp, le_inf_iff, exists_imp]
#align t2_iff_ultrafilter t2_iff_ultrafilter

theorem t2_iff_isClosed_diagonal : T2Space X ↔ IsClosed (diagonal X) := by
  simp only [t2Space_iff_disjoint_nhds, ← isOpen_compl_iff, isOpen_iff_mem_nhds, Prod.forall,
    nhds_prod_eq, compl_diagonal_mem_prod, mem_compl_iff, mem_diagonal_iff, Pairwise]
#align t2_iff_is_closed_diagonal t2_iff_isClosed_diagonal

theorem isClosed_diagonal [T2Space X] : IsClosed (diagonal X) :=
  t2_iff_isClosed_diagonal.mp ‹_›
#align is_closed_diagonal isClosed_diagonal

-- porting note: 2 lemmas moved below

theorem tendsto_nhds_unique [T2Space X] {f : Y → X} {l : Filter Y} {a b : X} [NeBot l]
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : a = b :=
  eq_of_nhds_neBot <| neBot_of_le <| le_inf ha hb
#align tendsto_nhds_unique tendsto_nhds_unique

theorem tendsto_nhds_unique' [T2Space X] {f : Y → X} {l : Filter Y} {a b : X} (_ : NeBot l)
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : a = b :=
  eq_of_nhds_neBot <| neBot_of_le <| le_inf ha hb
#align tendsto_nhds_unique' tendsto_nhds_unique'

theorem tendsto_nhds_unique_of_eventuallyEq [T2Space X] {f g : Y → X} {l : Filter Y} {a b : X}
    [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) (hfg : f =ᶠ[l] g) : a = b :=
  tendsto_nhds_unique (ha.congr' hfg) hb
#align tendsto_nhds_unique_of_eventually_eq tendsto_nhds_unique_of_eventuallyEq

theorem tendsto_nhds_unique_of_frequently_eq [T2Space X] {f g : Y → X} {l : Filter Y} {a b : X}
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) (hfg : ∃ᶠ x in l, f x = g x) : a = b :=
  have : ∃ᶠ z : X × X in 𝓝 (a, b), z.1 = z.2 := (ha.prod_mk_nhds hb).frequently hfg
  not_not.1 fun hne => this (isClosed_diagonal.isOpen_compl.mem_nhds hne)
#align tendsto_nhds_unique_of_frequently_eq tendsto_nhds_unique_of_frequently_eq

/-- If a function `f` is

- injective on a compact set `s`;
- continuous at every point of this set;
- injective on a neighborhood of each point of this set,

then it is injective on a neighborhood of this set. -/
theorem Set.InjOn.exists_mem_nhdsSet {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} {s : Set X} (inj : InjOn f s) (sc : IsCompact s)
    (fc : ∀ x ∈ s, ContinuousAt f x) (loc : ∀ x ∈ s, ∃ u ∈ 𝓝 x, InjOn f u) :
    ∃ t ∈ 𝓝ˢ s, InjOn f t := by
  have : ∀ x ∈ s ×ˢ s, ∀ᶠ y in 𝓝 x, f y.1 = f y.2 → y.1 = y.2 := fun (x, y) ⟨hx, hy⟩ ↦ by
    rcases eq_or_ne x y with rfl | hne
    · rcases loc x hx with ⟨u, hu, hf⟩
      exact Filter.mem_of_superset (prod_mem_nhds hu hu) <| forall_prod_set.2 hf
    · suffices ∀ᶠ z in 𝓝 (x, y), f z.1 ≠ f z.2 from this.mono fun _ hne h ↦ absurd h hne
      refine (fc x hx).prod_map' (fc y hy) <| isClosed_diagonal.isOpen_compl.mem_nhds ?_
      exact inj.ne hx hy hne
  rw [← eventually_nhdsSet_iff_forall, sc.nhdsSet_prod_eq sc] at this
  exact eventually_prod_self_iff.1 this

/-- If a function `f` is

- injective on a compact set `s`;
- continuous at every point of this set;
- injective on a neighborhood of each point of this set,

then it is injective on an open neighborhood of this set. -/
theorem Set.InjOn.exists_isOpen_superset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} {s : Set X} (inj : InjOn f s) (sc : IsCompact s)
    (fc : ∀ x ∈ s, ContinuousAt f x) (loc : ∀ x ∈ s, ∃ u ∈ 𝓝 x, InjOn f u) :
    ∃ t, IsOpen t ∧ s ⊆ t ∧ InjOn f t :=
  let ⟨_t, hst, ht⟩ := inj.exists_mem_nhdsSet sc fc loc
  let ⟨u, huo, hsu, hut⟩ := mem_nhdsSet_iff_exists.1 hst
  ⟨u, huo, hsu, ht.mono hut⟩

/-- A T₂.₅ space, also known as a Urysohn space, is a topological space
  where for every pair `x ≠ y`, there are two open sets, with the intersection of closures
  empty, one containing `x` and the other `y` . -/
class T25Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Given two distinct points in a T₂.₅ space, their filters of closed neighborhoods are
  disjoint. -/
  t2_5 : ∀ ⦃x y : X⦄, x ≠ y → Disjoint ((𝓝 x).lift' closure) ((𝓝 y).lift' closure)
#align t2_5_space T25Space

@[simp]
theorem disjoint_lift'_closure_nhds [T25Space X] {x y : X} :
    Disjoint ((𝓝 x).lift' closure) ((𝓝 y).lift' closure) ↔ x ≠ y :=
  ⟨fun h hxy => by simp [hxy, nhds_neBot.ne] at h, fun h => T25Space.t2_5 h⟩
#align disjoint_lift'_closure_nhds disjoint_lift'_closure_nhds

-- see Note [lower instance priority]
instance (priority := 100) T25Space.t2Space [T25Space X] : T2Space X :=
  t2Space_iff_disjoint_nhds.2 fun _ _ hne =>
    (disjoint_lift'_closure_nhds.2 hne).mono (le_lift'_closure _) (le_lift'_closure _)
#align t2_5_space.t2_space T25Space.t2Space

theorem exists_nhds_disjoint_closure [T25Space X] {x y : X} (h : x ≠ y) :
    ∃ s ∈ 𝓝 x, ∃ t ∈ 𝓝 y, Disjoint (closure s) (closure t) :=
  ((𝓝 x).basis_sets.lift'_closure.disjoint_iff (𝓝 y).basis_sets.lift'_closure).1 <|
    disjoint_lift'_closure_nhds.2 h
#align exists_nhds_disjoint_closure exists_nhds_disjoint_closure

theorem exists_open_nhds_disjoint_closure [T25Space X] {x y : X} (h : x ≠ y) :
    ∃ u : Set X,
      x ∈ u ∧ IsOpen u ∧ ∃ v : Set X, y ∈ v ∧ IsOpen v ∧ Disjoint (closure u) (closure v) := by
  simpa only [exists_prop, and_assoc] using
    ((nhds_basis_opens x).lift'_closure.disjoint_iff (nhds_basis_opens y).lift'_closure).1
      (disjoint_lift'_closure_nhds.2 h)
#align exists_open_nhds_disjoint_closure exists_open_nhds_disjoint_closure

section limUnder

variable [T2Space X] {f : Filter X}

/-!
### Properties of `lim` and `limUnder`

In this section we use explicit `Nonempty X` instances for `lim` and `limUnder`. This way the lemmas
are useful without a `Nonempty X` instance.
-/


theorem lim_eq {x : X} [NeBot f] (h : f ≤ 𝓝 x) : @lim _ _ ⟨x⟩ f = x :=
  tendsto_nhds_unique (le_nhds_lim ⟨x, h⟩) h
set_option linter.uppercaseLean3 false in
#align Lim_eq lim_eq

theorem lim_eq_iff [NeBot f] (h : ∃ x : X, f ≤ 𝓝 x) {x} : @lim _ _ ⟨x⟩ f = x ↔ f ≤ 𝓝 x :=
  ⟨fun c => c ▸ le_nhds_lim h, lim_eq⟩
set_option linter.uppercaseLean3 false in
#align Lim_eq_iff lim_eq_iff

theorem Ultrafilter.lim_eq_iff_le_nhds [CompactSpace X] {x : X} {F : Ultrafilter X} :
    F.lim = x ↔ ↑F ≤ 𝓝 x :=
  ⟨fun h => h ▸ F.le_nhds_lim, lim_eq⟩
set_option linter.uppercaseLean3 false in
#align ultrafilter.Lim_eq_iff_le_nhds Ultrafilter.lim_eq_iff_le_nhds

theorem isOpen_iff_ultrafilter' [CompactSpace X] (U : Set X) :
    IsOpen U ↔ ∀ F : Ultrafilter X, F.lim ∈ U → U ∈ F.1 := by
  rw [isOpen_iff_ultrafilter]
  refine' ⟨fun h F hF => h F.lim hF F F.le_nhds_lim, _⟩
  intro cond x hx f h
  rw [← Ultrafilter.lim_eq_iff_le_nhds.2 h] at hx
  exact cond _ hx
#align is_open_iff_ultrafilter' isOpen_iff_ultrafilter'

theorem Filter.Tendsto.limUnder_eq {x : X} {f : Filter Y} [NeBot f] {g : Y → X}
    (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g = x :=
  lim_eq h
#align filter.tendsto.lim_eq Filter.Tendsto.limUnder_eq

theorem Filter.limUnder_eq_iff {f : Filter Y} [NeBot f] {g : Y → X} (h : ∃ x, Tendsto g f (𝓝 x))
    {x} : @limUnder _ _ _ ⟨x⟩ f g = x ↔ Tendsto g f (𝓝 x) :=
  ⟨fun c => c ▸ tendsto_nhds_limUnder h, Filter.Tendsto.limUnder_eq⟩
#align filter.lim_eq_iff Filter.limUnder_eq_iff

theorem Continuous.limUnder_eq [TopologicalSpace Y] {f : Y → X} (h : Continuous f) (y : Y) :
    @limUnder _ _ _ ⟨f y⟩ (𝓝 y) f = f y :=
  (h.tendsto y).limUnder_eq
#align continuous.lim_eq Continuous.limUnder_eq

@[simp]
theorem lim_nhds (x : X) : @lim _ _ ⟨x⟩ (𝓝 x) = x :=
  lim_eq le_rfl
set_option linter.uppercaseLean3 false in
#align Lim_nhds lim_nhds

@[simp]
theorem limUnder_nhds_id (x : X) : @limUnder _ _ _ ⟨x⟩ (𝓝 x) id = x :=
  lim_nhds x
#align lim_nhds_id limUnder_nhds_id

@[simp]
theorem lim_nhdsWithin {x : X} {s : Set X} (h : x ∈ closure s) : @lim _ _ ⟨x⟩ (𝓝[s] x) = x :=
  haveI : NeBot (𝓝[s] x) := mem_closure_iff_clusterPt.1 h
  lim_eq inf_le_left
set_option linter.uppercaseLean3 false in
#align Lim_nhds_within lim_nhdsWithin

@[simp]
theorem limUnder_nhdsWithin_id {x : X} {s : Set X} (h : x ∈ closure s) :
    @limUnder _ _ _ ⟨x⟩ (𝓝[s] x) id = x :=
  lim_nhdsWithin h
#align lim_nhds_within_id limUnder_nhdsWithin_id

end limUnder

/-!
### `T2Space` constructions

We use two lemmas to prove that various standard constructions generate Hausdorff spaces from
Hausdorff spaces:

* `separated_by_continuous` says that two points `x y : X` can be separated by open neighborhoods
  provided that there exists a continuous map `f : X → Y` with a Hausdorff codomain such that
  `f x ≠ f y`. We use this lemma to prove that topological spaces defined using `induced` are
  Hausdorff spaces.

* `separated_by_openEmbedding` says that for an open embedding `f : X → Y` of a Hausdorff space
  `X`, the images of two distinct points `x y : X`, `x ≠ y` can be separated by open neighborhoods.
  We use this lemma to prove that topological spaces defined using `coinduced` are Hausdorff spaces.
-/


-- see Note [lower instance priority]
instance (priority := 100) DiscreteTopology.toT2Space
    [DiscreteTopology X] : T2Space X :=
  ⟨fun x y h => ⟨{x}, {y}, isOpen_discrete _, isOpen_discrete _, rfl, rfl, disjoint_singleton.2 h⟩⟩
#align discrete_topology.to_t2_space DiscreteTopology.toT2Space

theorem separated_by_continuous [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {x y : X} (h : f x ≠ f y) :
    ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v :=
  let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f ⁻¹' u, f ⁻¹' v, uo.preimage hf, vo.preimage hf, xu, yv, uv.preimage _⟩
#align separated_by_continuous separated_by_continuous

theorem separated_by_openEmbedding [TopologicalSpace Y] [T2Space X]
    {f : X → Y} (hf : OpenEmbedding f) {x y : X} (h : x ≠ y) :
    ∃ u v : Set Y, IsOpen u ∧ IsOpen v ∧ f x ∈ u ∧ f y ∈ v ∧ Disjoint u v :=
  let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f '' u, f '' v, hf.isOpenMap _ uo, hf.isOpenMap _ vo, mem_image_of_mem _ xu,
    mem_image_of_mem _ yv, disjoint_image_of_injective hf.inj uv⟩
#align separated_by_open_embedding separated_by_openEmbedding

instance {p : X → Prop} [T2Space X] : T2Space (Subtype p) :=
  ⟨fun _ _ h => separated_by_continuous continuous_subtype_val (mt Subtype.eq h)⟩

instance Prod.t2Space [T2Space X] [TopologicalSpace Y] [T2Space Y] : T2Space (X × Y) :=
  ⟨fun _ _ h => Or.elim (not_and_or.mp (mt Prod.ext_iff.mpr h))
    (fun h₁ => separated_by_continuous continuous_fst h₁) fun h₂ =>
    separated_by_continuous continuous_snd h₂⟩

/-- If the codomain of an injective continuous function is a Hausdorff space, then so is its
domain. -/
theorem T2Space.of_injective_continuous [TopologicalSpace Y] [T2Space Y] {f : X → Y}
    (hinj : Injective f) (hc : Continuous f) : T2Space X :=
  ⟨fun _ _ h => separated_by_continuous hc (hinj.ne h)⟩

/-- If the codomain of a topological embedding is a Hausdorff space, then so is its domain.
See also `T2Space.of_continuous_injective`. -/
theorem Embedding.t2Space [TopologicalSpace Y] [T2Space Y] {f : X → Y} (hf : Embedding f) :
    T2Space X :=
  .of_injective_continuous hf.inj hf.continuous
#align embedding.t2_space Embedding.t2Space

instance ULift.instT2Space [T2Space X] : T2Space (ULift X) :=
  embedding_uLift_down.t2Space

instance [T2Space X] [TopologicalSpace Y] [T2Space Y] :
    T2Space (X ⊕ Y) := by
  constructor
  rintro (x | x) (y | y) h
  · exact separated_by_openEmbedding openEmbedding_inl <| ne_of_apply_ne _ h
  · exact separated_by_continuous continuous_isLeft <| by simp
  · exact separated_by_continuous continuous_isLeft <| by simp
  · exact separated_by_openEmbedding openEmbedding_inr <| ne_of_apply_ne _ h

instance Pi.t2Space {Y : X → Type v} [∀ a, TopologicalSpace (Y a)]
    [∀ a, T2Space (Y a)] : T2Space (∀ a, Y a) :=
  ⟨fun _ _ h =>
    let ⟨i, hi⟩ := not_forall.mp (mt funext h)
    separated_by_continuous (continuous_apply i) hi⟩
#align Pi.t2_space Pi.t2Space

instance Sigma.t2Space {ι} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ a, T2Space (X a)] :
    T2Space (Σi, X i) := by
  constructor
  rintro ⟨i, x⟩ ⟨j, y⟩ neq
  rcases eq_or_ne i j with (rfl | h)
  · replace neq : x ≠ y := ne_of_apply_ne _ neq
    exact separated_by_openEmbedding openEmbedding_sigmaMk neq
  · let _ := (⊥ : TopologicalSpace ι); have : DiscreteTopology ι := ⟨rfl⟩
    exact separated_by_continuous (continuous_def.2 fun u _ => isOpen_sigma_fst_preimage u) h
#align sigma.t2_space Sigma.t2Space

variable {Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

theorem isClosed_eq [T2Space X] {f g : Y → X} (hf : Continuous f) (hg : Continuous g) :
    IsClosed { y : Y | f y = g y } :=
  continuous_iff_isClosed.mp (hf.prod_mk hg) _ isClosed_diagonal
#align is_closed_eq isClosed_eq

theorem isOpen_ne_fun [T2Space X] {f g : Y → X} (hf : Continuous f) (hg : Continuous g) :
    IsOpen { y : Y | f y ≠ g y } :=
  isOpen_compl_iff.mpr <| isClosed_eq hf hg
#align is_open_ne_fun isOpen_ne_fun

/-- If two continuous maps are equal on `s`, then they are equal on the closure of `s`. See also
`Set.EqOn.of_subset_closure` for a more general version. -/
protected theorem Set.EqOn.closure [T2Space X] {s : Set Y} {f g : Y → X} (h : EqOn f g s)
    (hf : Continuous f) (hg : Continuous g) : EqOn f g (closure s) :=
  closure_minimal h (isClosed_eq hf hg)
#align set.eq_on.closure Set.EqOn.closure

/-- If two continuous functions are equal on a dense set, then they are equal. -/
theorem Continuous.ext_on [T2Space X] {s : Set Y} (hs : Dense s) {f g : Y → X} (hf : Continuous f)
    (hg : Continuous g) (h : EqOn f g s) : f = g :=
  funext fun x => h.closure hf hg (hs x)
#align continuous.ext_on Continuous.ext_on

theorem eqOn_closure₂' [T2Space Z] {s : Set X} {t : Set Y} {f g : X → Y → Z}
    (h : ∀ x ∈ s, ∀ y ∈ t, f x y = g x y) (hf₁ : ∀ x, Continuous (f x))
    (hf₂ : ∀ y, Continuous fun x => f x y) (hg₁ : ∀ x, Continuous (g x))
    (hg₂ : ∀ y, Continuous fun x => g x y) : ∀ x ∈ closure s, ∀ y ∈ closure t, f x y = g x y :=
  suffices closure s ⊆ ⋂ y ∈ closure t, { x | f x y = g x y } by simpa only [subset_def, mem_iInter]
  (closure_minimal fun x hx => mem_iInter₂.2 <| Set.EqOn.closure (h x hx) (hf₁ _) (hg₁ _)) <|
    isClosed_biInter fun y _ => isClosed_eq (hf₂ _) (hg₂ _)
#align eq_on_closure₂' eqOn_closure₂'

theorem eqOn_closure₂ [T2Space Z] {s : Set X} {t : Set Y} {f g : X → Y → Z}
    (h : ∀ x ∈ s, ∀ y ∈ t, f x y = g x y) (hf : Continuous (uncurry f))
    (hg : Continuous (uncurry g)) : ∀ x ∈ closure s, ∀ y ∈ closure t, f x y = g x y :=
  eqOn_closure₂' h (fun x => continuous_uncurry_left x hf) (fun x => continuous_uncurry_right x hf)
    (fun y => continuous_uncurry_left y hg) fun y => continuous_uncurry_right y hg
#align eq_on_closure₂ eqOn_closure₂

/-- If `f x = g x` for all `x ∈ s` and `f`, `g` are continuous on `t`, `s ⊆ t ⊆ closure s`, then
`f x = g x` for all `x ∈ t`. See also `Set.EqOn.closure`. -/
theorem Set.EqOn.of_subset_closure [T2Space Y] {s t : Set X} {f g : X → Y} (h : EqOn f g s)
    (hf : ContinuousOn f t) (hg : ContinuousOn g t) (hst : s ⊆ t) (hts : t ⊆ closure s) :
    EqOn f g t := by
  intro x hx
  have : (𝓝[s] x).NeBot := mem_closure_iff_clusterPt.mp (hts hx)
  exact
    tendsto_nhds_unique_of_eventuallyEq ((hf x hx).mono_left <| nhdsWithin_mono _ hst)
      ((hg x hx).mono_left <| nhdsWithin_mono _ hst) (h.eventuallyEq_of_mem self_mem_nhdsWithin)
#align set.eq_on.of_subset_closure Set.EqOn.of_subset_closure

theorem Function.LeftInverse.closed_range [T2Space X] {f : X → Y} {g : Y → X}
    (h : Function.LeftInverse f g) (hf : Continuous f) (hg : Continuous g) : IsClosed (range g) :=
  have : EqOn (g ∘ f) id (closure <| range g) :=
    h.rightInvOn_range.eqOn.closure (hg.comp hf) continuous_id
  isClosed_of_closure_subset fun x hx => ⟨f x, this hx⟩
#align function.left_inverse.closed_range Function.LeftInverse.closed_range

theorem Function.LeftInverse.closedEmbedding [T2Space X] {f : X → Y} {g : Y → X}
    (h : Function.LeftInverse f g) (hf : Continuous f) (hg : Continuous g) : ClosedEmbedding g :=
  ⟨h.embedding hf hg, h.closed_range hf hg⟩
#align function.left_inverse.closed_embedding Function.LeftInverse.closedEmbedding

theorem separatedNhds_of_isCompact_isCompact [T2Space X] {s t : Set X} (hs : IsCompact s)
    (ht : IsCompact t) (hst : Disjoint s t) : SeparatedNhds s t := by
  simp only [SeparatedNhds, prod_subset_compl_diagonal_iff_disjoint.symm] at hst ⊢
  exact generalized_tube_lemma hs ht isClosed_diagonal.isOpen_compl hst
#align is_compact_is_compact_separated separatedNhds_of_isCompact_isCompact

section SeparatedFinset

theorem separatedNhds_of_finset_finset [T2Space X] (s t : Finset X) (h : Disjoint s t) :
    SeparatedNhds (s : Set X) t :=
  separatedNhds_of_isCompact_isCompact s.finite_toSet.isCompact t.finite_toSet.isCompact
    <| mod_cast h
#align finset_disjoint_finset_opens_of_t2 separatedNhds_of_finset_finset

theorem point_disjoint_finset_opens_of_t2 [T2Space X] {x : X} {s : Finset X} (h : x ∉ s) :
    SeparatedNhds ({x} : Set X) s :=
  mod_cast separatedNhds_of_finset_finset {x} s (Finset.disjoint_singleton_left.mpr h)
#align point_disjoint_finset_opens_of_t2 point_disjoint_finset_opens_of_t2

end SeparatedFinset

/-- In a `T2Space`, every compact set is closed. -/
theorem IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsCompact s) : IsClosed s :=
  isOpen_compl_iff.1 <| isOpen_iff_forall_mem_open.mpr fun x hx =>
    let ⟨u, v, _, vo, su, xv, uv⟩ :=
      separatedNhds_of_isCompact_isCompact hs isCompact_singleton (disjoint_singleton_right.2 hx)
    ⟨v, (uv.mono_left <| show s ≤ u from su).subset_compl_left, vo, by simpa using xv⟩
#align is_compact.is_closed IsCompact.isClosed

@[simp]
theorem Filter.coclosedCompact_eq_cocompact [T2Space X] : coclosedCompact X = cocompact X := by
  simp only [coclosedCompact, cocompact, iInf_and',
    and_iff_right_of_imp (@IsCompact.isClosed X _ _ _)]
#align filter.coclosed_compact_eq_cocompact Filter.coclosedCompact_eq_cocompact

@[simp]
theorem Bornology.relativelyCompact_eq_inCompact [T2Space X] :
    Bornology.relativelyCompact X = Bornology.inCompact X :=
  Bornology.ext _ _ Filter.coclosedCompact_eq_cocompact
#align bornology.relatively_compact_eq_in_compact Bornology.relativelyCompact_eq_inCompact

theorem IsCompact.preimage_continuous [CompactSpace X] [T2Space Y] {f : X → Y} {s : Set Y}
    (hs : IsCompact s) (hf : Continuous f) : IsCompact (f ⁻¹' s) :=
  (hs.isClosed.preimage hf).isCompact

/-- If `V : ι → Set X` is a decreasing family of compact sets then any neighborhood of
`⋂ i, V i` contains some `V i`. This is a version of `exists_subset_nhds_of_isCompact'` where we
don't need to assume each `V i` closed because it follows from compactness since `X` is
assumed to be Hausdorff. -/
theorem exists_subset_nhds_of_isCompact [T2Space X] {ι : Type*} [Nonempty ι] {V : ι → Set X}
    (hV : Directed (· ⊇ ·) V) (hV_cpct : ∀ i, IsCompact (V i)) {U : Set X}
    (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U :=
  exists_subset_nhds_of_isCompact' hV hV_cpct (fun i => (hV_cpct i).isClosed) hU
#align exists_subset_nhds_of_is_compact exists_subset_nhds_of_isCompact

theorem CompactExhaustion.isClosed [T2Space X] (K : CompactExhaustion X) (n : ℕ) : IsClosed (K n) :=
  (K.isCompact n).isClosed
#align compact_exhaustion.is_closed CompactExhaustion.isClosed

theorem IsCompact.inter [T2Space X] {s t : Set X} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ∩ t) :=
  hs.inter_right <| ht.isClosed
#align is_compact.inter IsCompact.inter

theorem image_closure_of_isCompact [T2Space Y] {s : Set X} (hs : IsCompact (closure s)) {f : X → Y}
    (hf : ContinuousOn f (closure s)) : f '' closure s = closure (f '' s) :=
  Subset.antisymm hf.image_closure <|
    closure_minimal (image_subset f subset_closure) (hs.image_of_continuousOn hf).isClosed
#align image_closure_of_is_compact image_closure_of_isCompact

/-- A continuous map from a compact space to a Hausdorff space is a closed map. -/
protected theorem Continuous.isClosedMap [CompactSpace X] [T2Space Y] {f : X → Y}
    (h : Continuous f) : IsClosedMap f := fun _s hs => (hs.isCompact.image h).isClosed
#align continuous.is_closed_map Continuous.isClosedMap

/-- A continuous injective map from a compact space to a Hausdorff space is a closed embedding. -/
theorem Continuous.closedEmbedding [CompactSpace X] [T2Space Y] {f : X → Y} (h : Continuous f)
    (hf : Function.Injective f) : ClosedEmbedding f :=
  closedEmbedding_of_continuous_injective_closed h hf h.isClosedMap
#align continuous.closed_embedding Continuous.closedEmbedding

/-- A continuous surjective map from a compact space to a Hausdorff space is a quotient map. -/
theorem QuotientMap.of_surjective_continuous [CompactSpace X] [T2Space Y] {f : X → Y}
    (hsurj : Surjective f) (hcont : Continuous f) : QuotientMap f :=
  hcont.isClosedMap.to_quotientMap hcont hsurj
#align quotient_map.of_surjective_continuous QuotientMap.of_surjective_continuous

instance (priority := 900) [WeaklyLocallyCompactSpace X] [T2Space Y] : LocallyCompactPair X Y where
  exists_mem_nhds_isCompact_mapsTo := by
    intro f x s hf hs
    rcases exists_compact_mem_nhds x with ⟨K, hKc, hKx⟩
    have hc : IsCompact (f '' K \ interior s) := (hKc.image hf).diff isOpen_interior
    have hd : Disjoint {f x} (f '' K \ interior s) := disjoint_singleton_left.2 fun h ↦
      h.2 <| mem_interior_iff_mem_nhds.2 hs
    rcases separatedNhds_of_isCompact_isCompact isCompact_singleton hc hd
      with ⟨U, V, Uo, Vo, hxU, hV, hd⟩
    refine ⟨K \ f ⁻¹' V, diff_mem hKx ?_, hKc.diff <| Vo.preimage hf, fun y hy ↦ ?_⟩
    · filter_upwards [hf.continuousAt <| Uo.mem_nhds (hxU rfl)] with x hx
        using Set.disjoint_left.1 hd hx
    · by_contra hys
      exact hy.2 (hV ⟨mem_image_of_mem _ hy.1, not_mem_subset interior_subset hys⟩)

theorem isPreirreducible_iff_subsingleton [T2Space X] {S : Set X} :
    IsPreirreducible S ↔ S.Subsingleton := by
  refine' ⟨fun h x hx y hy => _, Set.Subsingleton.isPreirreducible⟩
  by_contra e
  obtain ⟨U, V, hU, hV, hxU, hyV, h'⟩ := t2_separation e
  exact ((h U V hU hV ⟨x, hx, hxU⟩ ⟨y, hy, hyV⟩).mono <| inter_subset_right _ _).not_disjoint h'
#align is_preirreducible_iff_subsingleton isPreirreducible_iff_subsingleton

-- todo: use `alias` + `attribute [protected]` once we get `attribute [protected]`
protected lemma IsPreirreducible.subsingleton [T2Space X] {S : Set X} (h : IsPreirreducible S) :
    S.Subsingleton :=
  isPreirreducible_iff_subsingleton.1 h
#align is_preirreducible.subsingleton IsPreirreducible.subsingleton

theorem isIrreducible_iff_singleton [T2Space X] {S : Set X} : IsIrreducible S ↔ ∃ x, S = {x} := by
  rw [IsIrreducible, isPreirreducible_iff_subsingleton,
    exists_eq_singleton_iff_nonempty_subsingleton]
#align is_irreducible_iff_singleton isIrreducible_iff_singleton

/-- There does not exist a nontrivial preirreducible T₂ space. -/
theorem not_preirreducible_nontrivial_t2 (X) [TopologicalSpace X] [PreirreducibleSpace X]
    [Nontrivial X] [T2Space X] : False :=
  (PreirreducibleSpace.isPreirreducible_univ (X := X)).subsingleton.not_nontrivial nontrivial_univ
#align not_preirreducible_nontrivial_t2 not_preirreducible_nontrivial_t2

end Separation

section RegularSpace

/-- A topological space is called a *regular space* if for any closed set `s` and `a ∉ s`, there
exist disjoint open sets `U ⊇ s` and `V ∋ a`. We formulate this condition in terms of `Disjoint`ness
of filters `𝓝ˢ s` and `𝓝 a`. -/
@[mk_iff]
class RegularSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- If `a` is a point that does not belong to a closed set `s`, then `a` and `s` admit disjoint
  neighborhoods.  -/
  regular : ∀ {s : Set X} {a}, IsClosed s → a ∉ s → Disjoint (𝓝ˢ s) (𝓝 a)
#align regular_space RegularSpace

theorem regularSpace_TFAE (X : Type u) [TopologicalSpace X] :
    List.TFAE [RegularSpace X,
      ∀ (s : Set X) x, x ∉ closure s → Disjoint (𝓝ˢ s) (𝓝 x),
      ∀ (x : X) (s : Set X), Disjoint (𝓝ˢ s) (𝓝 x) ↔ x ∉ closure s,
      ∀ (x : X) (s : Set X), s ∈ 𝓝 x → ∃ t ∈ 𝓝 x, IsClosed t ∧ t ⊆ s,
      ∀ x : X, (𝓝 x).lift' closure ≤ 𝓝 x,
      ∀ x : X , (𝓝 x).lift' closure = 𝓝 x] := by
  tfae_have 1 ↔ 5
  · rw [regularSpace_iff, (@compl_surjective (Set X) _).forall, forall_swap]
    simp only [isClosed_compl_iff, mem_compl_iff, Classical.not_not, @and_comm (_ ∈ _),
      (nhds_basis_opens _).lift'_closure.le_basis_iff (nhds_basis_opens _), and_imp,
      (nhds_basis_opens _).disjoint_iff_right, exists_prop, ← subset_interior_iff_mem_nhdsSet,
      interior_compl, compl_subset_compl]
  tfae_have 5 → 6
  · exact fun h a => (h a).antisymm (𝓝 _).le_lift'_closure
  tfae_have 6 → 4
  · intro H a s hs
    rw [← H] at hs
    rcases (𝓝 a).basis_sets.lift'_closure.mem_iff.mp hs with ⟨U, hU, hUs⟩
    exact ⟨closure U, mem_of_superset hU subset_closure, isClosed_closure, hUs⟩
  tfae_have 4 → 2
  · intro H s a ha
    have ha' : sᶜ ∈ 𝓝 a := by rwa [← mem_interior_iff_mem_nhds, interior_compl]
    rcases H _ _ ha' with ⟨U, hU, hUc, hUs⟩
    refine' disjoint_of_disjoint_of_mem disjoint_compl_left _ hU
    rwa [← subset_interior_iff_mem_nhdsSet, hUc.isOpen_compl.interior_eq, subset_compl_comm]
  tfae_have 2 → 3
  · refine' fun H a s => ⟨fun hd has => mem_closure_iff_nhds_neBot.mp has _, H s a⟩
    exact (hd.symm.mono_right <| @principal_le_nhdsSet _ _ s).eq_bot
  tfae_have 3 → 1
  · exact fun H => ⟨fun hs ha => (H _ _).mpr <| hs.closure_eq.symm ▸ ha⟩
  tfae_finish
#align regular_space_tfae regularSpace_TFAE

theorem RegularSpace.ofLift'_closure (h : ∀ x : X, (𝓝 x).lift' closure = 𝓝 x) : RegularSpace X :=
  Iff.mpr ((regularSpace_TFAE X).out 0 5) h
#align regular_space.of_lift'_closure RegularSpace.ofLift'_closure

theorem RegularSpace.ofBasis {ι : X → Sort*} {p : ∀ a, ι a → Prop} {s : ∀ a, ι a → Set X}
    (h₁ : ∀ a, (𝓝 a).HasBasis (p a) (s a)) (h₂ : ∀ a i, p a i → IsClosed (s a i)) :
    RegularSpace X :=
  RegularSpace.ofLift'_closure fun a => (h₁ a).lift'_closure_eq_self (h₂ a)
#align regular_space.of_basis RegularSpace.ofBasis

theorem RegularSpace.ofExistsMemNhdsIsClosedSubset
    (h : ∀ (x : X), ∀ s ∈ 𝓝 x, ∃ t ∈ 𝓝 x, IsClosed t ∧ t ⊆ s) : RegularSpace X :=
  Iff.mpr ((regularSpace_TFAE X).out 0 3) h
#align regular_space.of_exists_mem_nhds_is_closed_subset RegularSpace.ofExistsMemNhdsIsClosedSubset

/-- A locally compact T2 space is regular. -/
instance (priority := 100) [LocallyCompactSpace X] [T2Space X] : RegularSpace X := by
  apply RegularSpace.ofExistsMemNhdsIsClosedSubset (fun x s hx ↦ ?_)
  rcases local_compact_nhds hx with ⟨k, kx, ks, hk⟩
  exact ⟨k, kx, hk.isClosed, ks⟩

variable [RegularSpace X] {x : X} {s : Set X}

theorem disjoint_nhdsSet_nhds : Disjoint (𝓝ˢ s) (𝓝 x) ↔ x ∉ closure s := by
  have h := (regularSpace_TFAE X).out 0 2
  exact h.mp ‹_› _ _
#align disjoint_nhds_set_nhds disjoint_nhdsSet_nhds

theorem disjoint_nhds_nhdsSet : Disjoint (𝓝 x) (𝓝ˢ s) ↔ x ∉ closure s :=
  disjoint_comm.trans disjoint_nhdsSet_nhds
#align disjoint_nhds_nhds_set disjoint_nhds_nhdsSet

theorem exists_mem_nhds_isClosed_subset {x : X} {s : Set X} (h : s ∈ 𝓝 x) :
    ∃ t ∈ 𝓝 x, IsClosed t ∧ t ⊆ s := by
  have h' := (regularSpace_TFAE X).out 0 3
  exact h'.mp ‹_› _ _ h
#align exists_mem_nhds_is_closed_subset exists_mem_nhds_isClosed_subset

theorem closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsClosed s) id :=
  hasBasis_self.2 fun _ => exists_mem_nhds_isClosed_subset
#align closed_nhds_basis closed_nhds_basis

theorem lift'_nhds_closure (x : X) : (𝓝 x).lift' closure = 𝓝 x :=
  (closed_nhds_basis x).lift'_closure_eq_self fun _ => And.right
#align lift'_nhds_closure lift'_nhds_closure

theorem Filter.HasBasis.nhds_closure {ι : Sort*} {x : X} {p : ι → Prop} {s : ι → Set X}
    (h : (𝓝 x).HasBasis p s) : (𝓝 x).HasBasis p fun i => closure (s i) :=
  lift'_nhds_closure x ▸ h.lift'_closure
#align filter.has_basis.nhds_closure Filter.HasBasis.nhds_closure

theorem hasBasis_nhds_closure (x : X) : (𝓝 x).HasBasis (fun s => s ∈ 𝓝 x) closure :=
  (𝓝 x).basis_sets.nhds_closure
#align has_basis_nhds_closure hasBasis_nhds_closure

theorem hasBasis_opens_closure (x : X) : (𝓝 x).HasBasis (fun s => x ∈ s ∧ IsOpen s) closure :=
  (nhds_basis_opens x).nhds_closure
#align has_basis_opens_closure hasBasis_opens_closure

theorem TopologicalSpace.IsTopologicalBasis.nhds_basis_closure {B : Set (Set X)}
    (hB : IsTopologicalBasis B) (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ s ∈ B) closure := by
  simpa only [and_comm] using hB.nhds_hasBasis.nhds_closure
#align topological_space.is_topological_basis.nhds_basis_closure TopologicalSpace.IsTopologicalBasis.nhds_basis_closure

theorem TopologicalSpace.IsTopologicalBasis.exists_closure_subset {B : Set (Set X)}
    (hB : IsTopologicalBasis B) {x : X} {s : Set X} (h : s ∈ 𝓝 x) :
    ∃ t ∈ B, x ∈ t ∧ closure t ⊆ s := by
  simpa only [exists_prop, and_assoc] using hB.nhds_hasBasis.nhds_closure.mem_iff.mp h
#align topological_space.is_topological_basis.exists_closure_subset TopologicalSpace.IsTopologicalBasis.exists_closure_subset

theorem disjoint_nhds_nhds_iff_not_specializes {a b : X} : Disjoint (𝓝 a) (𝓝 b) ↔ ¬a ⤳ b := by
  rw [← nhdsSet_singleton, disjoint_nhdsSet_nhds, specializes_iff_mem_closure]
#align disjoint_nhds_nhds_iff_not_specializes disjoint_nhds_nhds_iff_not_specializes

theorem specializes_comm {a b : X} : a ⤳ b ↔ b ⤳ a := by
  simp only [← (disjoint_nhds_nhds_iff_not_specializes (X := X)).not_left, disjoint_comm]
#align specializes_comm specializes_comm

alias ⟨Specializes.symm, _⟩ := specializes_comm
#align specializes.symm Specializes.symm

theorem specializes_iff_inseparable {a b : X} : a ⤳ b ↔ Inseparable a b :=
  ⟨fun h => h.antisymm h.symm, le_of_eq⟩
#align specializes_iff_inseparable specializes_iff_inseparable

theorem isClosed_setOf_specializes : IsClosed { p : X × X | p.1 ⤳ p.2 } := by
  simp only [← isOpen_compl_iff, compl_setOf, ← disjoint_nhds_nhds_iff_not_specializes,
    isOpen_setOf_disjoint_nhds_nhds]
#align is_closed_set_of_specializes isClosed_setOf_specializes

theorem isClosed_setOf_inseparable : IsClosed { p : X × X | Inseparable p.1 p.2 } := by
  simp only [← specializes_iff_inseparable, isClosed_setOf_specializes]
#align is_closed_set_of_inseparable isClosed_setOf_inseparable

protected theorem Inducing.regularSpace [TopologicalSpace Y] {f : Y → X} (hf : Inducing f) :
    RegularSpace Y :=
  RegularSpace.ofBasis
    (fun b => by rw [hf.nhds_eq_comap b]; exact (closed_nhds_basis _).comap _)
    fun b s hs => by exact hs.2.preimage hf.continuous
#align inducing.regular_space Inducing.regularSpace

theorem regularSpace_induced (f : Y → X) : @RegularSpace Y (induced f ‹_›) :=
  letI := induced f ‹_›
  Inducing.regularSpace ⟨rfl⟩
#align regular_space_induced regularSpace_induced

theorem regularSpace_sInf {X} {T : Set (TopologicalSpace X)} (h : ∀ t ∈ T, @RegularSpace X t) :
    @RegularSpace X (sInf T) := by
  let _ := sInf T
  have : ∀ a, (𝓝 a).HasBasis
      (fun If : ΣI : Set T, I → Set X =>
        If.1.Finite ∧ ∀ i : If.1, If.2 i ∈ @nhds X i a ∧ @IsClosed X i (If.2 i))
      fun If => ⋂ i : If.1, If.snd i := by
    intro a
    rw [nhds_sInf, ← iInf_subtype'']
    exact hasBasis_iInf fun t : T => @closed_nhds_basis X t (h t t.2) a
  refine' RegularSpace.ofBasis this fun a If hIf => isClosed_iInter fun i => _
  exact (hIf.2 i).2.mono (sInf_le (i : T).2)
#align regular_space_Inf regularSpace_sInf

theorem regularSpace_iInf {ι X} {t : ι → TopologicalSpace X} (h : ∀ i, @RegularSpace X (t i)) :
    @RegularSpace X (iInf t) :=
  regularSpace_sInf <| forall_range_iff.mpr h
#align regular_space_infi regularSpace_iInf

theorem RegularSpace.inf {X} {t₁ t₂ : TopologicalSpace X} (h₁ : @RegularSpace X t₁)
    (h₂ : @RegularSpace X t₂) : @RegularSpace X (t₁ ⊓ t₂) := by
  rw [inf_eq_iInf]
  exact regularSpace_iInf (Bool.forall_bool.2 ⟨h₂, h₁⟩)
#align regular_space.inf RegularSpace.inf

instance {p : X → Prop} : RegularSpace (Subtype p) :=
  embedding_subtype_val.toInducing.regularSpace

instance [TopologicalSpace Y] [RegularSpace Y] : RegularSpace (X × Y) :=
  (regularSpace_induced (@Prod.fst X Y)).inf (regularSpace_induced (@Prod.snd X Y))

instance {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, RegularSpace (X i)] :
    RegularSpace (∀ i, X i) :=
  regularSpace_iInf fun _ => regularSpace_induced _

/-- In a regular space, if a compact set and a closed set are disjoint, then they have disjoint
neighborhoods. -/
lemma separatedNhds_of_isCompact_isClosed [RegularSpace X] {s t : Set X}
    (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) : SeparatedNhds s t := by
  apply hs.induction_on (p := fun u ↦ SeparatedNhds u t)
  · simp
  · intro s u su hu
    exact hu.mono su Subset.rfl
  · intro u v hu hv
    exact hu.union_left hv
  · intro x hx
    have : tᶜ ∈ 𝓝 x := ht.isOpen_compl.mem_nhds (disjoint_left.1 hst hx)
    rcases exists_mem_nhds_isClosed_subset this with ⟨u, u_mem, u_closed, hu⟩
    refine ⟨interior u, mem_nhdsWithin_of_mem_nhds (interior_mem_nhds.2 u_mem), ?_⟩
    exact ⟨interior u, uᶜ, isOpen_interior, u_closed.isOpen_compl, Subset.rfl,
      subset_compl_comm.mp hu, disjoint_compl_right.mono_left (interior_subset)⟩

end RegularSpace

section T2OrLocallyCompactRegularSpace

/-- A topological space which is either T2 or locally compact regular. Equivalent to regularity
among locally compact spaces. These two classes share the properties that are needed to develop a
lot of measure theory, so it's worth defining a single class to avoid developing things twice. -/
class T2OrLocallyCompactRegularSpace (X : Type*) [TopologicalSpace X] : Prop :=
  out : T2Space X ∨ (LocallyCompactSpace X ∧ RegularSpace X)

instance (priority := 100) [h : T2Space X] : T2OrLocallyCompactRegularSpace X := ⟨Or.inl h⟩
instance (priority := 100) [h : LocallyCompactSpace X] [h' : RegularSpace X] :
  T2OrLocallyCompactRegularSpace X := ⟨Or.inr ⟨h, h'⟩⟩

/-- A locally compact space which is T2 or locally comapct regular is regular. Not an instance, as
one should instead assume `LocallyCompactSpace X` and `RegularSpace X`. -/
theorem RegularSpace.ofT2SpaceOrRegularSpace
    [LocallyCompactSpace X] [h : T2OrLocallyCompactRegularSpace X] : RegularSpace X := by
  rcases h.out with h'|⟨-, h'⟩ <;> infer_instance

/-- In a space which is T2 or locally compact regular, if a compact set `s` is contained in an
open set `u`, then its closure is also contained in `u`. -/
theorem IsCompact.closure_subset_of_isOpen [hX : T2OrLocallyCompactRegularSpace X]
    {s : Set X} (hs : IsCompact s) {u : Set X} (hu : IsOpen u) (h : s ⊆ u) :
    closure s ⊆ u := by
  rcases hX.out with h'|⟨-, h'⟩
  · rwa [hs.isClosed.closure_eq]
  obtain ⟨F, sF, F_closed, Fu⟩ : ∃ F, s ⊆ F ∧ IsClosed F ∧ F ⊆ u := by
    apply hs.induction_on (p := fun t ↦ ∃ F, t ⊆ F ∧ IsClosed F ∧ F ⊆ u)
    · exact ⟨∅, by simp⟩
    · intro t' t ht't ⟨F, tF, F_closed, Fu⟩
      exact ⟨F, ht't.trans tF, F_closed, Fu⟩
    · intro t t' ⟨F, tF, F_closed, Fu⟩ ⟨F', t'F', F'_closed, F'u⟩
      exact ⟨F ∪ F', union_subset_union tF t'F', F_closed.union F'_closed, union_subset Fu F'u⟩
    · intro x hx
      rcases exists_mem_nhds_isClosed_subset (hu.mem_nhds (h hx)) with ⟨F, F_mem, F_closed, Fu⟩
      exact ⟨F, nhdsWithin_le_nhds F_mem, F, Subset.rfl, F_closed, Fu⟩
  exact (closure_minimal sF F_closed).trans Fu

theorem separatedNhds_of_isCompact_isCompact_isClosed [hX : T2OrLocallyCompactRegularSpace X]
    {s t : Set X} (hs : IsCompact s) (ht : IsCompact t) (h't : IsClosed t)
    (hst : Disjoint s t) : SeparatedNhds s t := by
  rcases hX.out with h'|⟨-, h'⟩
  · exact separatedNhds_of_isCompact_isCompact hs ht hst
  · exact separatedNhds_of_isCompact_isClosed hs h't hst

protected theorem IsCompact.closure [hX : T2OrLocallyCompactRegularSpace X]
    {K : Set X} (hK : IsCompact K) : IsCompact (closure K) := by
  rcases hX.out with h'|⟨h', -⟩
  · rwa [hK.isClosed.closure_eq]
  rcases exists_compact_superset hK with ⟨L, L_comp, hL⟩
  exact L_comp.of_isClosed_subset isClosed_closure
    ((hK.closure_subset_of_isOpen isOpen_interior hL).trans interior_subset)

theorem isCompact_closure_of_subset_compact [T2OrLocallyCompactRegularSpace X]
    {s t : Set X} (ht : IsCompact t)
    (h : s ⊆ t) : IsCompact (closure s) :=
  ht.closure.of_isClosed_subset isClosed_closure (closure_mono h)
#align is_compact_closure_of_subset_compact isCompact_closure_of_subset_compact

/-- In a (possibly non-Hausdorff) locally compact regular space, for every containment `K ⊆ U` of
  a compact set `K` in an open set `U`, there is a compact closed neighborhood `L`
  such that `K ⊆ L ⊆ U`: equivalently, there is a compact closed set `L` such
  that `K ⊆ interior L` and `L ⊆ U`. -/
theorem exists_compact_closed_between [LocallyCompactSpace X] [RegularSpace X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (h_KU : K ⊆ U) :
    ∃ L, IsCompact L ∧ IsClosed L ∧ K ⊆ interior L ∧ L ⊆ U := by
  rcases exists_compact_between hK hU h_KU with ⟨L, L_comp, KL, LU⟩
  rcases exists_compact_between hK isOpen_interior KL with ⟨M, M_comp, KM, ML⟩
  refine ⟨closure M, ?_, isClosed_closure, ?_, ?_⟩
  · have : closure M ∩ L = closure M := by
      apply inter_eq_self_of_subset_left
      exact (M_comp.closure_subset_of_isOpen isOpen_interior ML).trans interior_subset
    rw [← this]
    apply L_comp.inter_left isClosed_closure
  · exact KM.trans (interior_mono subset_closure)
  · apply M_comp.closure_subset_of_isOpen hU
    exact ML.trans (interior_subset.trans LU)

/-- In a locally compact regular space, given a compact set `K` inside an open set `U`, we can find
an open set `V` between these sets with compact closure: `K ⊆ V` and the closure of `V` is
inside `U`. -/
theorem exists_open_between_and_isCompact_closure [LocallyCompactSpace X] [RegularSpace X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U ∧ IsCompact (closure V) := by
  rcases exists_compact_closed_between hK hU hKU with ⟨L, L_compact, L_closed, KL, LU⟩
  have A : closure (interior L) ⊆ L := by
    apply (closure_mono interior_subset).trans (le_of_eq L_closed.closure_eq)
  refine ⟨interior L, isOpen_interior, KL, A.trans LU, ?_⟩
  exact isCompact_closure_of_subset_compact L_compact interior_subset
#align exists_open_between_and_is_compact_closure exists_open_between_and_isCompact_closure

@[simp]
theorem exists_compact_superset_iff [T2OrLocallyCompactRegularSpace X] {s : Set X} :
    (∃ K, IsCompact K ∧ s ⊆ K) ↔ IsCompact (closure s) :=
  ⟨fun ⟨_K, hK, hsK⟩ => isCompact_closure_of_subset_compact hK hsK, fun h =>
    ⟨closure s, h, subset_closure⟩⟩
#align exists_compact_superset_iff exists_compact_superset_iff

/-- In a weakly locally compact space which is either T₂ or locally compact regular,
every compact set has an open neighborhood with compact closure. -/
theorem exists_open_superset_and_isCompact_closure
    [WeaklyLocallyCompactSpace X] [T2OrLocallyCompactRegularSpace X]
    {K : Set X} (hK : IsCompact K) : ∃ V, IsOpen V ∧ K ⊆ V ∧ IsCompact (closure V) := by
  rcases exists_compact_superset hK with ⟨K', hK', hKK'⟩
  exact ⟨interior K', isOpen_interior, hKK',
    isCompact_closure_of_subset_compact hK' interior_subset⟩
#align exists_open_superset_and_is_compact_closure exists_open_superset_and_isCompact_closure

/-- In a weakly locally compact which is either T₂ or locally compact regular,
every point has an open neighborhood with compact closure. -/
theorem exists_open_with_compact_closure
    [WeaklyLocallyCompactSpace X] [T2OrLocallyCompactRegularSpace X] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsCompact (closure U) := by
  simpa only [singleton_subset_iff]
    using exists_open_superset_and_isCompact_closure isCompact_singleton
#align exists_open_with_compact_closure exists_open_with_compact_closure

-- see Note [lower instance priority]
/-- A weakly locally compact Hausdorff space is locally compact. -/
instance (priority := 80) WeaklyLocallyCompactSpace.locallyCompactSpace
    [WeaklyLocallyCompactSpace X] [hX : T2OrLocallyCompactRegularSpace X] :
    LocallyCompactSpace X := by
  rcases hX.out with h'X|⟨h'X, -⟩
  · exact ⟨fun _ _ h =>
      let ⟨K, hKx, hKc, hKs⟩ := exists_mem_nhds_isCompact_mapsTo continuous_id h
      ⟨K, hKx, hKs, hKc⟩⟩
  · exact h'X
#align locally_compact_of_compact_nhds WeaklyLocallyCompactSpace.locallyCompactSpace

@[deprecated WeaklyLocallyCompactSpace.locallyCompactSpace]
theorem locally_compact_of_compact [T2Space X] [CompactSpace X] :
    LocallyCompactSpace X :=
  inferInstance
#align locally_compact_of_compact locally_compact_of_compact

/-- If a compact set is covered by two open sets, then we can cover it by two compact subsets. -/
theorem IsCompact.binary_compact_cover [T2OrLocallyCompactRegularSpace X] {K U V : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hV : IsOpen V) (h2K : K ⊆ U ∪ V) :
    ∃ K₁ K₂ : Set X, IsCompact K₁ ∧ IsCompact K₂ ∧ K₁ ⊆ U ∧ K₂ ⊆ V ∧ K = K₁ ∪ K₂ := by
  have hK' : IsCompact (closure K) := hK.closure
  have : SeparatedNhds (closure K \ U) (closure K \ V) := by
    apply separatedNhds_of_isCompact_isCompact_isClosed (hK'.diff hU) (hK'.diff hV)
      (isClosed_closure.sdiff hV)
    rw [disjoint_iff_inter_eq_empty, diff_inter_diff, diff_eq_empty]
    exact hK.closure_subset_of_isOpen (hU.union hV) h2K
  have : SeparatedNhds (K \ U) (K \ V) :=
    this.mono (diff_subset_diff_left (subset_closure)) (diff_subset_diff_left (subset_closure))
  rcases this with ⟨O₁, O₂, h1O₁, h1O₂, h2O₁, h2O₂, hO⟩
  exact ⟨K \ O₁, K \ O₂, hK.diff h1O₁, hK.diff h1O₂, diff_subset_comm.mp h2O₁,
    diff_subset_comm.mp h2O₂, by rw [← diff_inter, hO.inter_eq, diff_empty]⟩
#align is_compact.binary_compact_cover IsCompact.binary_compact_cover

open Finset Function

/-- For every finite open cover `Uᵢ` of a compact set, there exists a compact cover `Kᵢ ⊆ Uᵢ`. -/
theorem IsCompact.finite_compact_cover [T2OrLocallyCompactRegularSpace X]
    {s : Set X} (hs : IsCompact s) {ι}
    (t : Finset ι) (U : ι → Set X) (hU : ∀ i ∈ t, IsOpen (U i)) (hsC : s ⊆ ⋃ i ∈ t, U i) :
    ∃ K : ι → Set X, (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ U i) ∧ s = ⋃ i ∈ t, K i := by
  induction' t using Finset.induction with x t hx ih generalizing U s
  · refine' ⟨fun _ => ∅, fun _ => isCompact_empty, fun i => empty_subset _, _⟩
    simpa only [subset_empty_iff, Finset.not_mem_empty, iUnion_false, iUnion_empty] using hsC
  simp only [Finset.set_biUnion_insert] at hsC
  simp only [Finset.forall_mem_insert] at hU
  have hU' : ∀ i ∈ t, IsOpen (U i) := fun i hi => hU.2 i hi
  rcases hs.binary_compact_cover hU.1 (isOpen_biUnion hU') hsC with
    ⟨K₁, K₂, h1K₁, h1K₂, h2K₁, h2K₂, hK⟩
  rcases ih h1K₂ U hU' h2K₂ with ⟨K, h1K, h2K, h3K⟩
  refine' ⟨update K x K₁, _, _, _⟩
  · intro i
    rcases eq_or_ne i x with rfl | hi
    · simp only [update_same, h1K₁]
    · simp only [update_noteq hi, h1K]
  · intro i
    rcases eq_or_ne i x with rfl | hi
    · simp only [update_same, h2K₁]
    · simp only [update_noteq hi, h2K]
  · simp only [set_biUnion_insert_update _ hx, hK, h3K]
#align is_compact.finite_compact_cover IsCompact.finite_compact_cover

end T2OrLocallyCompactRegularSpace

section T3

/-- A T₃ space is a T₀ space which is a regular space. Any T₃ space is a T₁ space, a T₂ space, and
a T₂.₅ space.  -/
class T3Space (X : Type u) [TopologicalSpace X] extends T0Space X, RegularSpace X : Prop
#align t3_space T3Space

instance (priority := 90) [T0Space X] [RegularSpace X] : T3Space X := ⟨⟩

-- see Note [lower instance priority]
instance (priority := 100) T3Space.t25Space [T3Space X] : T25Space X := by
  refine' ⟨fun x y hne => _⟩
  rw [lift'_nhds_closure, lift'_nhds_closure]
  have : x ∉ closure {y} ∨ y ∉ closure {x} :=
    (t0Space_iff_or_not_mem_closure X).mp inferInstance hne
  simp only [← disjoint_nhds_nhdsSet, nhdsSet_singleton] at this
  exact this.elim id fun h => h.symm
#align t3_space.t2_5_space T3Space.t25Space

protected theorem Embedding.t3Space [TopologicalSpace Y] [T3Space Y] {f : X → Y}
    (hf : Embedding f) : T3Space X :=
  { toT0Space := hf.t0Space
    toRegularSpace := hf.toInducing.regularSpace }
#align embedding.t3_space Embedding.t3Space

instance Subtype.t3Space [T3Space X] {p : X → Prop} : T3Space (Subtype p) :=
  embedding_subtype_val.t3Space
#align subtype.t3_space Subtype.t3Space

instance ULift.instT3Space [T3Space X] : T3Space (ULift X) :=
  embedding_uLift_down.t3Space

instance [TopologicalSpace Y] [T3Space X] [T3Space Y] : T3Space (X × Y) := ⟨⟩

instance {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, T3Space (X i)] :
    T3Space (∀ i, X i) := ⟨⟩

/-- Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and `y ∈ V₂ ⊆ U₂`,
with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint. -/
theorem disjoint_nested_nhds [T3Space X] {x y : X} (h : x ≠ y) :
    ∃ U₁ ∈ 𝓝 x, ∃ V₁ ∈ 𝓝 x, ∃ U₂ ∈ 𝓝 y, ∃ V₂ ∈ 𝓝 y,
      IsClosed V₁ ∧ IsClosed V₂ ∧ IsOpen U₁ ∧ IsOpen U₂ ∧ V₁ ⊆ U₁ ∧ V₂ ⊆ U₂ ∧ Disjoint U₁ U₂ := by
  rcases t2_separation h with ⟨U₁, U₂, U₁_op, U₂_op, x_in, y_in, H⟩
  rcases exists_mem_nhds_isClosed_subset (U₁_op.mem_nhds x_in) with ⟨V₁, V₁_in, V₁_closed, h₁⟩
  rcases exists_mem_nhds_isClosed_subset (U₂_op.mem_nhds y_in) with ⟨V₂, V₂_in, V₂_closed, h₂⟩
  exact ⟨U₁, mem_of_superset V₁_in h₁, V₁, V₁_in, U₂, mem_of_superset V₂_in h₂, V₂, V₂_in,
    V₁_closed, V₂_closed, U₁_op, U₂_op, h₁, h₂, H⟩
#align disjoint_nested_nhds disjoint_nested_nhds

open SeparationQuotient

/-- The `SeparationQuotient` of a regular space is a T₃ space. -/
instance [RegularSpace X] : T3Space (SeparationQuotient X) where
  regular {s a} hs ha := by
    rcases surjective_mk a with ⟨a, rfl⟩
    rw [← disjoint_comap_iff surjective_mk, comap_mk_nhds_mk, comap_mk_nhdsSet]
    exact RegularSpace.regular (hs.preimage continuous_mk) ha

end T3

section NormalSpace

/-- A topological space is said to be a *normal space* if any two disjoint closed sets
have disjoint open neighborhoods. -/
class NormalSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- Two disjoint sets in a normal space admit disjoint neighbourhoods. -/
  normal : ∀ s t : Set X, IsClosed s → IsClosed t → Disjoint s t → SeparatedNhds s t

theorem normal_separation [NormalSpace X] {s t : Set X} (H1 : IsClosed s) (H2 : IsClosed t)
    (H3 : Disjoint s t) : SeparatedNhds s t :=
  NormalSpace.normal s t H1 H2 H3
#align normal_separation normal_separation

theorem disjoint_nhdsSet_nhdsSet [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hd : Disjoint s t) : Disjoint (𝓝ˢ s) (𝓝ˢ t) :=
  (normal_separation hs ht hd).disjoint_nhdsSet

theorem normal_exists_closure_subset [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsOpen t)
    (hst : s ⊆ t) : ∃ u, IsOpen u ∧ s ⊆ u ∧ closure u ⊆ t := by
  have : Disjoint s tᶜ := Set.disjoint_left.mpr fun x hxs hxt => hxt (hst hxs)
  rcases normal_separation hs (isClosed_compl_iff.2 ht) this with
    ⟨s', t', hs', ht', hss', htt', hs't'⟩
  refine ⟨s', hs', hss', Subset.trans (closure_minimal ?_ (isClosed_compl_iff.2 ht'))
    (compl_subset_comm.1 htt')⟩
  exact fun x hxs hxt => hs't'.le_bot ⟨hxs, hxt⟩
#align normal_exists_closure_subset normal_exists_closure_subset

/-- If the codomain of a closed embedding is a normal space, then so is the domain. -/
protected theorem ClosedEmbedding.normalSpace [TopologicalSpace Y] [NormalSpace Y] {f : X → Y}
    (hf : ClosedEmbedding f) : NormalSpace X where
  normal s t hs ht hst := by
    have H : SeparatedNhds (f '' s) (f '' t) :=
      NormalSpace.normal (f '' s) (f '' t) (hf.isClosedMap s hs) (hf.isClosedMap t ht)
        (disjoint_image_of_injective hf.inj hst)
    exact (H.preimage hf.continuous).mono (subset_preimage_image _ _) (subset_preimage_image _ _)

/-- A regular topological space with second countable topology is a normal space. -/
instance (priority := 100) NormalSpace.of_regularSpace_secondCountableTopology
    [RegularSpace X] [SecondCountableTopology X] : NormalSpace X := by
  have key : ∀ {s t : Set X}, IsClosed t → Disjoint s t →
    ∃ U : Set (countableBasis X), (s ⊆ ⋃ u ∈ U, ↑u) ∧ (∀ u ∈ U, Disjoint (closure ↑u) t) ∧
      ∀ n : ℕ, IsClosed (⋃ (u ∈ U) (_ : Encodable.encode u ≤ n), closure (u : Set X)) := by
    intro s t hc hd
    rw [disjoint_left] at hd
    have : ∀ x ∈ s, ∃ U ∈ countableBasis X, x ∈ U ∧ Disjoint (closure U) t := by
      intro x hx
      rcases (isBasis_countableBasis X).exists_closure_subset (hc.compl_mem_nhds (hd hx))
        with ⟨u, hu, hxu, hut⟩
      exact ⟨u, hu, hxu, disjoint_left.2 hut⟩
    choose! U hu hxu hd using this
    set V : s → countableBasis X := MapsTo.restrict _ _ _ hu
    refine' ⟨range V, _, forall_range_iff.2 <| Subtype.forall.2 hd, fun n => _⟩
    · rw [biUnion_range]
      exact fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxu x hx⟩
    · simp only [← iSup_eq_iUnion, iSup_and']
      exact (((finite_le_nat n).preimage_embedding (Encodable.encode' _)).subset <|
        inter_subset_right _ _).isClosed_biUnion fun u _ => isClosed_closure
  refine' { normal := fun s t hs ht hd => _ }
  rcases key ht hd with ⟨U, hsU, hUd, hUc⟩
  rcases key hs hd.symm with ⟨V, htV, hVd, hVc⟩
  refine ⟨⋃ u ∈ U, ↑u \ ⋃ (v ∈ V) (_ : Encodable.encode v ≤ Encodable.encode u), closure ↑v,
    ⋃ v ∈ V, ↑v \ ⋃ (u ∈ U) (_ : Encodable.encode u ≤ Encodable.encode v), closure ↑u,
    isOpen_biUnion fun u _ => (isOpen_of_mem_countableBasis u.2).sdiff (hVc _),
    isOpen_biUnion fun v _ => (isOpen_of_mem_countableBasis v.2).sdiff (hUc _),
    fun x hx => ?_, fun x hx => ?_, ?_⟩
  · rcases mem_iUnion₂.1 (hsU hx) with ⟨u, huU, hxu⟩
    refine' mem_biUnion huU ⟨hxu, _⟩
    simp only [mem_iUnion]
    rintro ⟨v, hvV, -, hxv⟩
    exact (hVd v hvV).le_bot ⟨hxv, hx⟩
  · rcases mem_iUnion₂.1 (htV hx) with ⟨v, hvV, hxv⟩
    refine' mem_biUnion hvV ⟨hxv, _⟩
    simp only [mem_iUnion]
    rintro ⟨u, huU, -, hxu⟩
    exact (hUd u huU).le_bot ⟨hxu, hx⟩
  · simp only [disjoint_left, mem_iUnion, mem_diff, not_exists, not_and, not_forall, not_not]
    rintro a ⟨u, huU, hau, haV⟩ v hvV hav
    rcases le_total (Encodable.encode u) (Encodable.encode v) with hle | hle
    exacts [⟨u, huU, hle, subset_closure hau⟩, (haV _ hvV hle <| subset_closure hav).elim]
#align normal_space_of_t3_second_countable NormalSpace.of_regularSpace_secondCountableTopology

end NormalSpace

section Normality

/-- A T₄ space is a normal T₁ space. -/
class T4Space (X : Type u) [TopologicalSpace X] extends T1Space X, NormalSpace X : Prop
#align normal_space NormalSpace

instance (priority := 100) [T1Space X] [NormalSpace X] : T4Space X := ⟨⟩

-- see Note [lower instance priority]
instance (priority := 100) T4Space.t3Space [T4Space X] : T3Space X where
  regular hs hxs := by simpa only [nhdsSet_singleton] using (normal_separation hs isClosed_singleton
    (disjoint_singleton_right.mpr hxs)).disjoint_nhdsSet
#align normal_space.t3_space T4Space.t3Space

instance (priority := 100) T4Space.of_compactSpace_t2Space [CompactSpace X] [T2Space X] :
    T4Space X where
  normal _s _t hs ht := separatedNhds_of_isCompact_isCompact hs.isCompact ht.isCompact
#align normal_of_compact_t2 T4Space.of_compactSpace_t2Space

/-- If the codomain of a closed embedding is a T₄ space, then so is the domain. -/
protected theorem ClosedEmbedding.t4Space [TopologicalSpace Y] [T4Space Y] {f : X → Y}
    (hf : ClosedEmbedding f) : T4Space X where
  toT1Space := hf.toEmbedding.t1Space
  toNormalSpace := hf.normalSpace
#align closed_embedding.normal_space ClosedEmbedding.t4Space

instance ULift.instT4Space [T4Space X] : T4Space (ULift X) :=
  ULift.closedEmbedding_down.t4Space

namespace SeparationQuotient

/-- The `SeparationQuotient` of a normal space is a normal space. -/
instance [NormalSpace X] : NormalSpace (SeparationQuotient X) where
  normal s t hs ht hd := separatedNhds_iff_disjoint.2 <| by
    rw [← disjoint_comap_iff surjective_mk, comap_mk_nhdsSet, comap_mk_nhdsSet]
    exact disjoint_nhdsSet_nhdsSet (hs.preimage continuous_mk) (ht.preimage continuous_mk)
      (hd.preimage mk)

end SeparationQuotient

variable (X)

end Normality

section CompletelyNormal

/-- A topological space `X` is a *completely normal Hausdorff space* if each subspace `s : Set X` is
a normal Hausdorff space. Equivalently, `X` is a `T₁` space and for any two sets `s`, `t` such that
`closure s` is disjoint with `t` and `s` is disjoint with `closure t`, there exist disjoint
neighbourhoods of `s` and `t`. -/
class T5Space (X : Type u) [TopologicalSpace X] extends T1Space X : Prop where
  /-- If `closure s` is disjoint with `t` and `s` is disjoint with `closure t`, then `s` and `t`
  admit disjoint neighbourhoods. -/
  completely_normal :
    ∀ ⦃s t : Set X⦄, Disjoint (closure s) t → Disjoint s (closure t) → Disjoint (𝓝ˢ s) (𝓝ˢ t)
#align t5_space T5Space

export T5Space (completely_normal)

theorem Embedding.t5Space [TopologicalSpace Y] [T5Space Y] {e : X → Y} (he : Embedding e) :
    T5Space X := by
  haveI := he.t1Space
  refine' ⟨fun s t hd₁ hd₂ => _⟩
  simp only [he.toInducing.nhdsSet_eq_comap]
  refine disjoint_comap (completely_normal ?_ ?_)
  · rwa [← subset_compl_iff_disjoint_left, image_subset_iff, preimage_compl,
      ← he.closure_eq_preimage_closure_image, subset_compl_iff_disjoint_left]
  · rwa [← subset_compl_iff_disjoint_right, image_subset_iff, preimage_compl,
      ← he.closure_eq_preimage_closure_image, subset_compl_iff_disjoint_right]
#align embedding.t5_space Embedding.t5Space

/-- A subspace of a `T₅` space is a `T₅` space. -/
instance [T5Space X] {p : X → Prop} : T5Space { x // p x } :=
  embedding_subtype_val.t5Space

instance ULift.instT5Space [T5Space X] : T5Space (ULift X) :=
  embedding_uLift_down.t5Space

-- see Note [lower instance priority]
/-- A `T₅` space is a `T₄` space. -/
instance (priority := 100) T5Space.toT4Space [T5Space X] : T4Space X where
  normal s t hs ht hd := separatedNhds_iff_disjoint.2 <|
    completely_normal (by rwa [hs.closure_eq]) (by rwa [ht.closure_eq])
#align t5_space.to_normal_space T5Space.toT4Space

open SeparationQuotient

/-- The `SeparationQuotient` of a completely normal R₀ space is a T₅ space.
We don't have typeclasses for completely normal spaces (without T₁ assumption) and R₀ spaces,
so we use `T5Space` for assumption and for conclusion.

One can prove this using a homeomorphism between `X` and `SeparationQuotient X`.
We give an alternative proof of the `completely_normal` axiom
that works without assuming that `X` is a T₁ space. -/
instance [T5Space X] : T5Space (SeparationQuotient X) where
  completely_normal s t hd₁ hd₂ := by
    rw [← disjoint_comap_iff surjective_mk, comap_mk_nhdsSet, comap_mk_nhdsSet]
    apply T5Space.completely_normal <;> rw [← preimage_mk_closure]
    exacts [hd₁.preimage mk, hd₂.preimage mk]

end CompletelyNormal

/-- In a compact T₂ space, the connected component of a point equals the intersection of all
its clopen neighbourhoods. -/
theorem connectedComponent_eq_iInter_isClopen [T2Space X] [CompactSpace X] (x : X) :
    connectedComponent x = ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, s := by
  apply Subset.antisymm connectedComponent_subset_iInter_isClopen
  -- Reduce to showing that the clopen intersection is connected.
  refine' IsPreconnected.subset_connectedComponent _ (mem_iInter.2 fun s => s.2.2)
  -- We do this by showing that any disjoint cover by two closed sets implies
  -- that one of these closed sets must contain our whole thing.
  -- To reduce to the case where the cover is disjoint on all of `X` we need that `s` is closed
  have hs : @IsClosed X _ (⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, s) :=
    isClosed_iInter fun s => s.2.1.1
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hs]
  intro a b ha hb hab ab_disj
  -- Since our space is normal, we get two larger disjoint open sets containing the disjoint
  -- closed sets. If we can show that our intersection is a subset of any of these we can then
  -- "descend" this to show that it is a subset of either a or b.
  rcases normal_separation ha hb ab_disj with ⟨u, v, hu, hv, hau, hbv, huv⟩
  obtain ⟨s, H⟩ : ∃ s : Set X, IsClopen s ∧ x ∈ s ∧ s ⊆ u ∪ v
  /- Now we find a clopen set `s` around `x`, contained in `u ∪ v`. We utilize the fact that
  `X \ u ∪ v` will be compact, so there must be some finite intersection of clopen neighbourhoods of
  `X` disjoint to it, but a finite intersection of clopen sets is clopen so we let this be our
  `s`. -/
  · have H1 := (hu.union hv).isClosed_compl.isCompact.inter_iInter_nonempty
      (fun s : { s : Set X // IsClopen s ∧ x ∈ s } => s) fun s => s.2.1.1
    rw [← not_disjoint_iff_nonempty_inter, imp_not_comm, not_forall] at H1
    cases' H1 (disjoint_compl_left_iff_subset.2 <| hab.trans <| union_subset_union hau hbv)
      with si H2
    refine' ⟨⋂ U ∈ si, Subtype.val U, _, _, _⟩
    · exact isClopen_biInter_finset fun s _ => s.2.1
    · exact mem_iInter₂.2 fun s _ => s.2.2
    · rwa [← disjoint_compl_left_iff_subset, disjoint_iff_inter_eq_empty,
        ← not_nonempty_iff_eq_empty]
  -- So, we get a disjoint decomposition `s = s ∩ u ∪ s ∩ v` of clopen sets. The intersection of all
  -- clopen neighbourhoods will then lie in whichever of u or v x lies in and hence will be a subset
  -- of either a or b.
  · have H1 := isClopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hu hv huv
    rw [union_comm] at H
    have H2 := isClopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hv hu huv.symm
    by_cases hxu : x ∈ u <;> [left; right]
    -- The x ∈ u case.
    · suffices ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, ↑s ⊆ u
        from Disjoint.left_le_of_le_sup_right hab (huv.mono this hbv)
      · apply Subset.trans _ (inter_subset_right s u)
        exact iInter_subset (fun s : { s : Set X // IsClopen s ∧ x ∈ s } => s.1)
          ⟨s ∩ u, H1, mem_inter H.2.1 hxu⟩
    -- If x ∉ u, we get x ∈ v since x ∈ u ∪ v. The rest is then like the x ∈ u case.
    · have h1 : x ∈ v :=
        (hab.trans (union_subset_union hau hbv) (mem_iInter.2 fun i => i.2.2)).resolve_left hxu
      suffices ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, ↑s ⊆ v
        from (huv.symm.mono this hau).left_le_of_le_sup_left hab
      · refine Subset.trans ?_ (inter_subset_right s v)
        exact iInter_subset (fun s : { s : Set X // IsClopen s ∧ x ∈ s } => s.1)
          ⟨s ∩ v, H2, mem_inter H.2.1 h1⟩
#align connected_component_eq_Inter_clopen connectedComponent_eq_iInter_isClopen

section Profinite

/-- A T1 space with a clopen basis is totally separated. -/
theorem totallySeparatedSpace_of_t1_of_basis_clopen [T1Space X]
    (h : IsTopologicalBasis { s : Set X | IsClopen s }) : TotallySeparatedSpace X := by
  constructor
  rintro x - y - hxy
  rcases h.mem_nhds_iff.mp (isOpen_ne.mem_nhds hxy) with ⟨U, hU, hxU, hyU⟩
  exact ⟨U, Uᶜ, hU.isOpen, hU.compl.isOpen, hxU, fun h => hyU h rfl, (union_compl_self U).superset,
    disjoint_compl_right⟩
#align totally_separated_space_of_t1_of_basis_clopen totallySeparatedSpace_of_t1_of_basis_clopen

variable [T2Space X] [CompactSpace X]

/-- A compact Hausdorff space is totally disconnected if and only if it is totally separated, this
  is also true for locally compact spaces. -/
theorem compact_t2_tot_disc_iff_tot_sep : TotallyDisconnectedSpace X ↔ TotallySeparatedSpace X := by
  refine ⟨fun h => ⟨fun x _ y _ => ?_⟩, @TotallySeparatedSpace.totallyDisconnectedSpace _ _⟩
  contrapose!
  intro hyp
  suffices x ∈ connectedComponent y by
    simpa [totallyDisconnectedSpace_iff_connectedComponent_singleton.1 h y, mem_singleton_iff]
  rw [connectedComponent_eq_iInter_isClopen, mem_iInter]
  rintro ⟨w : Set X, hw : IsClopen w, hy : y ∈ w⟩
  by_contra hx
  exact hyp wᶜ w hw.1.isOpen_compl hw.2 hx hy (@isCompl_compl _ w _).symm.codisjoint.top_le
    disjoint_compl_left
#align compact_t2_tot_disc_iff_tot_sep compact_t2_tot_disc_iff_tot_sep

variable [TotallyDisconnectedSpace X]

/-- A totally disconnected compact Hausdorff space is totally separated. -/
instance (priority := 100) : TotallySeparatedSpace X :=
  compact_t2_tot_disc_iff_tot_sep.mp inferInstance

theorem nhds_basis_clopen (x : X) : (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ IsClopen s) id :=
  ⟨fun U => by
    constructor
    · have hx : connectedComponent x = {x} :=
        totallyDisconnectedSpace_iff_connectedComponent_singleton.mp ‹_› x
      rw [connectedComponent_eq_iInter_isClopen] at hx
      intro hU
      let N := { s // IsClopen s ∧ x ∈ s }
      suffices : ∃ s : N, s.val ⊆ U
      · rcases this with ⟨⟨s, hs, hs'⟩, hs''⟩; exact ⟨s, ⟨hs', hs⟩, hs''⟩
      haveI : Nonempty N := ⟨⟨univ, isClopen_univ, mem_univ x⟩⟩
      have hNcl : ∀ s : N, IsClosed s.val := fun s => s.property.1.1
      have hdir : Directed Superset fun s : N => s.val := by
        rintro ⟨s, hs, hxs⟩ ⟨t, ht, hxt⟩
        exact ⟨⟨s ∩ t, hs.inter ht, ⟨hxs, hxt⟩⟩, inter_subset_left s t, inter_subset_right s t⟩
      have h_nhd : ∀ y ∈ ⋂ s : N, s.val, U ∈ 𝓝 y := fun y y_in => by
        erw [hx, mem_singleton_iff] at y_in
        rwa [y_in]
      exact exists_subset_nhds_of_compactSpace hdir hNcl h_nhd
    · rintro ⟨V, ⟨hxV, -, V_op⟩, hUV : V ⊆ U⟩
      rw [mem_nhds_iff]
      exact ⟨V, hUV, V_op, hxV⟩⟩
#align nhds_basis_clopen nhds_basis_clopen

theorem isTopologicalBasis_isClopen : IsTopologicalBasis { s : Set X | IsClopen s } := by
  apply isTopologicalBasis_of_isOpen_of_nhds fun U (hU : IsClopen U) => hU.2
  intro x U hxU U_op
  have : U ∈ 𝓝 x := IsOpen.mem_nhds U_op hxU
  rcases (nhds_basis_clopen x).mem_iff.mp this with ⟨V, ⟨hxV, hV⟩, hVU : V ⊆ U⟩
  use V
  tauto
#align is_topological_basis_clopen isTopologicalBasis_isClopen

/-- Every member of an open set in a compact Hausdorff totally disconnected space
  is contained in a clopen set contained in the open set.  -/
theorem compact_exists_isClopen_in_isOpen {x : X} {U : Set X} (is_open : IsOpen U) (memU : x ∈ U) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U :=
  isTopologicalBasis_isClopen.mem_nhds_iff.1 (is_open.mem_nhds memU)
#align compact_exists_clopen_in_open compact_exists_isClopen_in_isOpen

end Profinite

section LocallyCompact

variable {H : Type*} [TopologicalSpace H] [LocallyCompactSpace H] [T2Space H]

/-- A locally compact Hausdorff totally disconnected space has a basis with clopen elements. -/
theorem loc_compact_Haus_tot_disc_of_zero_dim [TotallyDisconnectedSpace H] :
    IsTopologicalBasis { s : Set H | IsClopen s } := by
  refine isTopologicalBasis_of_isOpen_of_nhds (fun u hu => hu.2) fun x U memU hU => ?_
  obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset hU memU
  let u : Set s := ((↑) : s → H) ⁻¹' interior s
  have u_open_in_s : IsOpen u := isOpen_interior.preimage continuous_subtype_val
  lift x to s using interior_subset xs
  haveI : CompactSpace s := isCompact_iff_compactSpace.1 comp
  obtain ⟨V : Set s, VisClopen, Vx, V_sub⟩ := compact_exists_isClopen_in_isOpen u_open_in_s xs
  have VisClopen' : IsClopen (((↑) : s → H) '' V) := by
    refine' ⟨comp.isClosed.closedEmbedding_subtype_val.closed_iff_image_closed.1 VisClopen.1, _⟩
    let v : Set u := ((↑) : u → s) ⁻¹' V
    have : ((↑) : u → H) = ((↑) : s → H) ∘ ((↑) : u → s) := rfl
    have f0 : Embedding ((↑) : u → H) := embedding_subtype_val.comp embedding_subtype_val
    have f1 : OpenEmbedding ((↑) : u → H) := by
      refine' ⟨f0, _⟩
      · have : Set.range ((↑) : u → H) = interior s := by
          rw [this, Set.range_comp, Subtype.range_coe, Subtype.image_preimage_coe]
          apply Set.inter_eq_self_of_subset_left interior_subset
        rw [this]
        apply isOpen_interior
    have f2 : IsOpen v := VisClopen.2.preimage continuous_subtype_val
    have f3 : ((↑) : s → H) '' V = ((↑) : u → H) '' v := by
      rw [this, image_comp, Subtype.image_preimage_coe, inter_eq_self_of_subset_left V_sub]
    rw [f3]
    apply f1.isOpenMap v f2
  refine' ⟨(↑) '' V, VisClopen', by simp [Vx], Subset.trans _ sU⟩
  simp
set_option linter.uppercaseLean3 false in
#align loc_compact_Haus_tot_disc_of_zero_dim loc_compact_Haus_tot_disc_of_zero_dim

/-- A locally compact Hausdorff space is totally disconnected
  if and only if it is totally separated. -/
theorem loc_compact_t2_tot_disc_iff_tot_sep :
    TotallyDisconnectedSpace H ↔ TotallySeparatedSpace H := by
  constructor
  · intro h
    exact totallySeparatedSpace_of_t1_of_basis_clopen loc_compact_Haus_tot_disc_of_zero_dim
  apply TotallySeparatedSpace.totallyDisconnectedSpace
#align loc_compact_t2_tot_disc_iff_tot_sep loc_compact_t2_tot_disc_iff_tot_sep

end LocallyCompact

/-- `ConnectedComponents X` is Hausdorff when `X` is Hausdorff and compact -/
instance ConnectedComponents.t2 [T2Space X] [CompactSpace X] : T2Space (ConnectedComponents X) := by
  -- Proof follows that of: https://stacks.math.columbia.edu/tag/0900
  -- Fix 2 distinct connected components, with points a and b
  refine ⟨ConnectedComponents.surjective_coe.forall₂.2 fun a b ne => ?_⟩
  rw [ConnectedComponents.coe_ne_coe] at ne
  have h := connectedComponent_disjoint ne
  -- write ↑b as the intersection of all clopen subsets containing it
  rw [connectedComponent_eq_iInter_isClopen b, disjoint_iff_inter_eq_empty] at h
  -- Now we show that this can be reduced to some clopen containing `↑b` being disjoint to `↑a`
  obtain ⟨U, V, hU, ha, hb, rfl⟩ : ∃ (U : Set X) (V : Set (ConnectedComponents X)),
      IsClopen U ∧ connectedComponent a ∩ U = ∅ ∧ connectedComponent b ⊆ U ∧ (↑) ⁻¹' V = U := by
    have h :=
      (isClosed_connectedComponent (α := X)).isCompact.elim_finite_subfamily_closed
        _ (fun s : { s : Set X // IsClopen s ∧ b ∈ s } => s.2.1.1) h
    cases' h with fin_a ha
    -- This clopen and its complement will separate the connected components of `a` and `b`
    set U : Set X := ⋂ (i : { s // IsClopen s ∧ b ∈ s }) (_ : i ∈ fin_a), i
    have hU : IsClopen U := isClopen_biInter_finset fun i _ => i.2.1
    exact ⟨U, (↑) '' U, hU, ha, subset_iInter₂ fun s _ => s.2.1.connectedComponent_subset s.2.2,
      (connectedComponents_preimage_image U).symm ▸ hU.biUnion_connectedComponent_eq⟩
  rw [ConnectedComponents.quotientMap_coe.isClopen_preimage] at hU
  refine' ⟨Vᶜ, V, hU.compl.isOpen, hU.isOpen, _, hb mem_connectedComponent, disjoint_compl_left⟩
  exact fun h => flip Set.Nonempty.ne_empty ha ⟨a, mem_connectedComponent, h⟩
#align connected_components.t2 ConnectedComponents.t2
