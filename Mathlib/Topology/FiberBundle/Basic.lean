/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Topology.FiberBundle.Trivialization
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Fiber bundles

Mathematically, a (topological) fiber bundle with fiber `F` over a base `B` is a space projecting on
`B` for which the fibers are all homeomorphic to `F`, such that the local situation around each
point is a direct product.

In our formalism, a fiber bundle is by definition the type `Bundle.TotalSpace F E` where
`E : B → Type*` is a function associating to `x : B` the fiber over `x`. This type
`Bundle.TotalSpace F E` is a type of pairs `⟨proj : B, snd : E proj⟩`.

To have a fiber bundle structure on `Bundle.TotalSpace F E`, one should
additionally have the following data:

* `F` should be a topological space;
* There should be a topology on `Bundle.TotalSpace F E`, for which the projection to `B` is
  a fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological space, and the injection
  from `E x` to `Bundle.TotalSpace F E` should be an embedding;
* There should be a distinguished set of bundle trivializations, the "trivialization atlas"
* There should be a choice of bundle trivialization at each point, which belongs to this atlas.

If all these conditions are satisfied, we register the typeclass `FiberBundle F E`.

It is in general nontrivial to construct a fiber bundle. A way is to start from the knowledge of
how changes of local trivializations act on the fiber. From this, one can construct the total space
of the bundle and its topology by a suitable gluing construction. The main content of this file is
an implementation of this construction: starting from an object of type
`FiberBundleCore` registering the trivialization changes, one gets the corresponding
fiber bundle and projection.

Similarly we implement the object `FiberPrebundle` which allows to define a topological
fiber bundle from trivializations given as partial equivalences with minimum additional properties.

## Main definitions

### Basic definitions

* `FiberBundle F E` : Structure saying that `E : B → Type*` is a fiber bundle with fiber `F`.

### Construction of a bundle from trivializations

* `Bundle.TotalSpace F E` is the type of pairs `(proj : B, snd : E proj)`. We can use the extra
  argument `F` to construct topology on the total space.
* `FiberBundleCore ι B F` : structure registering how changes of coordinates act
  on the fiber `F` above open subsets of `B`, where local trivializations are indexed by `ι`.

Let `Z : FiberBundleCore ι B F`. Then we define

* `Z.Fiber x`     : the fiber above `x`, homeomorphic to `F` (and defeq to `F` as a type).
* `Z.TotalSpace`  : the total space of `Z`, defined as `Bundle.TotalSpace F Z.Fiber` with a custom
                    topology.
* `Z.proj`        : projection from `Z.TotalSpace` to `B`. It is continuous.
* `Z.localTriv i` : for `i : ι`, bundle trivialization above the set `Z.baseSet i`, which is an
                    open set in `B`.

* `FiberPrebundle F E` : structure registering a cover of prebundle trivializations
  and requiring that the relative transition maps are open partial homeomorphisms.
* `FiberPrebundle.totalSpaceTopology a` : natural topology of the total space, making
  the prebundle into a bundle.

## Implementation notes

### Data vs mixins

For both fiber and vector bundles, one faces a choice: should the definition state the *existence*
of local trivializations (a propositional typeclass), or specify a fixed atlas of trivializations (a
typeclass containing data)?

In their initial mathlib implementations, both fiber and vector bundles were defined
propositionally. For vector bundles, this turns out to be mathematically wrong: in infinite
dimension, the transition function between two trivializations is not automatically continuous as a
map from the base `B` to the endomorphisms `F →L[R] F` of the fiber (considered with the
operator-norm topology), and so the definition needs to be modified by restricting consideration to
a family of trivializations (constituting the data) which are all mutually-compatible in this sense.
The PRs https://github.com/leanprover-community/mathlib/pull/13052 and
https://github.com/leanprover-community/mathlib/pull/13175 implemented this change.

There is still the choice about whether to hold this data at the level of fiber bundles or of vector
bundles. As of PR https://github.com/leanprover-community/mathlib/pull/17505, the data is all held
in `FiberBundle`, with `VectorBundle` a (propositional) mixin stating fiberwise-linearity.

This allows bundles to carry instances of typeclasses in which the scalar field, `R`, does not
appear as a parameter. Notably, we would like a vector bundle over `R` with fiber `F` over base `B`
to be a `ChartedSpace (B × F)`, with the trivializations providing the charts. This would be a
dangerous instance for typeclass inference, because `R` does not appear as a parameter in
`ChartedSpace (B × F)`. But if the data of the trivializations is held in `FiberBundle`, then a
fiber bundle with fiber `F` over base `B` can be a `ChartedSpace (B × F)`, and this is safe for
typeclass inference.

We expect that this choice of definition will also streamline constructions of fiber bundles with
similar underlying structure (e.g., the same bundle being both a real and complex vector bundle).

### Core construction

A fiber bundle with fiber `F` over a base `B` is a family of spaces isomorphic to `F`,
indexed by `B`, which is locally trivial in the following sense: there is a covering of `B` by open
sets such that, on each such open set `s`, the bundle is isomorphic to `s × F`.

To construct a fiber bundle formally, the main data is what happens when one changes trivializations
from `s × F` to `s' × F` on `s ∩ s'`: one should get a family of homeomorphisms of `F`, depending
continuously on the base point, satisfying basic compatibility conditions (cocycle property).
Useful classes of bundles can then be specified by requiring that these homeomorphisms of `F`
belong to some subgroup, preserving some structure (the "structure group of the bundle"): then
these structures are inherited by the fibers of the bundle.

Given such trivialization change data (encoded below in a structure called
`FiberBundleCore`), one can construct the fiber bundle. The intrinsic canonical
mathematical construction is the following.
The fiber above `x` is the disjoint union of `F` over all trivializations, modulo the gluing
identifications: one gets a fiber which is isomorphic to `F`, but non-canonically
(each choice of one of the trivializations around `x` gives such an isomorphism). Given a
trivialization over a set `s`, one gets an isomorphism between `s × F` and `proj^{-1} s`, by using
the identification corresponding to this trivialization. One chooses the topology on the bundle that
makes all of these into homeomorphisms.

For the practical implementation, it turns out to be more convenient to avoid completely the
gluing and quotienting construction above, and to declare above each `x` that the fiber is `F`,
but thinking that it corresponds to the `F` coming from the choice of one trivialization around `x`.
This has several practical advantages:
* without any work, one gets a topological space structure on the fiber. And if `F` has more
  structure it is inherited for free by the fiber.
* In the case of the tangent bundle of manifolds, this implies that on vector spaces the derivative
  (from `F` to `F`) and the manifold derivative (from `TangentSpace I x` to `TangentSpace I' (f x)`)
  are equal.

A drawback is that some silly constructions will typecheck: in the case of the tangent bundle, one
can add two vectors in different tangent spaces (as they both are elements of `F` from the point of
view of Lean). To solve this, one could mark the tangent space as irreducible, but then one would
lose the identification of the tangent space to `F` with `F`. There is however a big advantage of
this situation: even if Lean cannot check that two basepoints are defeq, it will accept the fact
that the tangent spaces are the same. For instance, if two maps `f` and `g` are locally inverse to
each other, one can express that the composition of their derivatives is the identity of
`TangentSpace I x`. One could fear issues as this composition goes from `TangentSpace I x` to
`TangentSpace I (g (f x))` (which should be the same, but should not be obvious to Lean
as it does not know that `g (f x) = x`). As these types are the same to Lean (equal to `F`), there
are in fact no dependent type difficulties here!

For this construction of a fiber bundle from a `FiberBundleCore`, we should thus
choose for each `x` one specific trivialization around it. We include this choice in the definition
of the `FiberBundleCore`, as it makes some constructions more
functorial and it is a nice way to say that the trivializations cover the whole space `B`.

With this definition, the type of the fiber bundle space constructed from the core data is
`Bundle.TotalSpace F (fun b : B ↦ F)`, but the topology is not the product one, in general.

We also take the indexing type (indexing all the trivializations) as a parameter to the fiber bundle
core: it could always be taken as a subtype of all the maps from open subsets of `B` to continuous
maps of `F`, but in practice it will sometimes be something else. For instance, on a manifold, one
will use the set of charts as a good parameterization for the trivializations of the tangent bundle.
Or for the pullback of a `FiberBundleCore`, the indexing type will be the same as
for the initial bundle.

## Tags
Fiber bundle, topological bundle, structure group
-/

@[expose] public section


variable {ι B F X : Type*} [TopologicalSpace X]

open TopologicalSpace Filter Set Bundle Topology

/-! ### General definition of fiber bundles -/

section FiberBundle

variable (F)
variable [TopologicalSpace B] [TopologicalSpace F] (E : B → Type*)
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]

/-- A (topological) fiber bundle with fiber `F` over a base `B` is a space projecting on `B`
for which the fibers are all homeomorphic to `F`, such that the local situation around each point
is a direct product. -/
@[informal "topological fiber bundle"]
@[informal "topological fiber bundle"]
class FiberBundle where
  totalSpaceMk_isInducing' : ∀ b : B, IsInducing (@TotalSpace.mk B F E b)
  trivializationAtlas' : Set (Trivialization F (π F E))
  trivializationAt' : B → Trivialization F (π F E)
  mem_baseSet_trivializationAt' : ∀ b : B, b ∈ (trivializationAt' b).baseSet
  trivialization_mem_atlas' : ∀ b : B, trivializationAt' b ∈ trivializationAtlas'

namespace FiberBundle

variable [FiberBundle F E] (b : B)

theorem totalSpaceMk_isInducing : IsInducing (@TotalSpace.mk B F E b) := totalSpaceMk_isInducing' b

/-- Atlas of a fiber bundle. -/
abbrev trivializationAtlas : Set (Trivialization F (π F E)) := trivializationAtlas'

/-- Trivialization of a fiber bundle at a point. -/
abbrev trivializationAt : Trivialization F (π F E) := trivializationAt' b

theorem mem_baseSet_trivializationAt : b ∈ (trivializationAt F E b).baseSet :=
  mem_baseSet_trivializationAt' b

theorem trivialization_mem_atlas : trivializationAt F E b ∈ trivializationAtlas F E :=
  trivialization_mem_atlas' b

end FiberBundle

export FiberBundle (totalSpaceMk_isInducing trivializationAtlas trivializationAt
  mem_baseSet_trivializationAt trivialization_mem_atlas)

variable {F}
variable {E}

/-- Given a type `E` equipped with a fiber bundle structure, this is a `Prop` typeclass
for trivializations of `E`, expressing that a trivialization is in the designated atlas for the
bundle.  This is needed because lemmas about the linearity of trivializations or the continuity (as
functions to `F →L[R] F`, where `F` is the model fiber) of the transition functions are only
expected to hold for trivializations in the designated atlas. -/
@[mk_iff]
class MemTrivializationAtlas [FiberBundle F E] (e : Trivialization F (π F E)) : Prop where
  out : e ∈ trivializationAtlas F E

instance [FiberBundle F E] (b : B) : MemTrivializationAtlas (trivializationAt F E b) where
  out := trivialization_mem_atlas F E b

namespace FiberBundle

variable (F)
variable [FiberBundle F E]

theorem map_proj_nhds (x : TotalSpace F E) : map (π F E) (𝓝 x) = 𝓝 x.proj :=
  (trivializationAt F E x.proj).map_proj_nhds <|
    (trivializationAt F E x.proj).mem_source.2 <| mem_baseSet_trivializationAt F E x.proj

variable (E)

/-- The projection from a fiber bundle to its base is continuous. -/
@[continuity]
theorem continuous_proj : Continuous (π F E) :=
  continuous_iff_continuousAt.2 fun x => (map_proj_nhds F x).le

/-- The projection from a fiber bundle to its base is an open map. -/
theorem isOpenMap_proj : IsOpenMap (π F E) :=
  IsOpenMap.of_nhds_le fun x => (map_proj_nhds F x).ge

/-- The projection from a fiber bundle with a nonempty fiber to its base is a surjective
map. -/
theorem surjective_proj [Nonempty F] : Function.Surjective (π F E) := fun b =>
  let ⟨p, _, hpb⟩ :=
    (trivializationAt F E b).proj_surjOn_baseSet (mem_baseSet_trivializationAt F E b)
  ⟨p, hpb⟩

/-- The projection from a fiber bundle with a nonempty fiber to its base is a quotient
map. -/
theorem isQuotientMap_proj [Nonempty F] : IsQuotientMap (π F E) :=
  (isOpenMap_proj F E).isQuotientMap (continuous_proj F E) (surjective_proj F E)

theorem continuous_totalSpaceMk (x : B) : Continuous (@TotalSpace.mk B F E x) :=
  (totalSpaceMk_isInducing F E x).continuous

theorem totalSpaceMk_isEmbedding (x : B) : IsEmbedding (@TotalSpace.mk B F E x) :=
  ⟨totalSpaceMk_isInducing F E x, TotalSpace.mk_injective x⟩

theorem totalSpaceMk_isClosedEmbedding [T1Space B] (x : B) :
    IsClosedEmbedding (@TotalSpace.mk B F E x) :=
  ⟨totalSpaceMk_isEmbedding F E x, by
    rw [TotalSpace.range_mk]
    exact isClosed_singleton.preimage <| continuous_proj F E⟩

/-- An arbitrary homeomorphism between any fiber and the model fiber.
This is useful to transfer topological properties of the model fiber. -/
noncomputable def homeomorphAt (b : B) : E b ≃ₜ F :=
  ((totalSpaceMk_isEmbedding F E b).toHomeomorph.trans <|
    Homeomorph.ofEqSubtypes <| TotalSpace.range_mk b).trans <|
    (trivializationAt F E b).preimageSingletonHomeomorph <| mem_baseSet_trivializationAt' b

lemma t0Space [T0Space F] (b : B) : T0Space (E b) :=
  FiberBundle.homeomorphAt F E b |>.symm.t0Space

lemma t1Space [T1Space F] (b : B) : T1Space (E b) :=
  FiberBundle.homeomorphAt F E b |>.symm.t1Space

lemma t2Space [T2Space F] (b : B) : T2Space (E b) :=
  FiberBundle.homeomorphAt F E b |>.symm.t2Space

lemma t3Space [T3Space F] (b : B) : T3Space (E b) :=
  FiberBundle.homeomorphAt F E b |>.symm.t3Space

variable {E F}

@[simp, mfld_simps]
theorem mem_trivializationAt_proj_source {x : TotalSpace F E} :
    x ∈ (trivializationAt F E x.proj).source :=
  (Trivialization.mem_source _).mpr <| mem_baseSet_trivializationAt F E x.proj

theorem trivializationAt_proj_fst {x : TotalSpace F E} :
    ((trivializationAt F E x.proj) x).1 = x.proj :=
  Trivialization.coe_fst' _ <| mem_baseSet_trivializationAt F E x.proj

variable (F)

open Trivialization

/-- Characterization of continuous functions (at a point, within a set) into a fiber bundle. -/
theorem continuousWithinAt_totalSpace (f : X → TotalSpace F E) {s : Set X} {x₀ : X} :
    ContinuousWithinAt f s x₀ ↔
      ContinuousWithinAt (fun x => (f x).proj) s x₀ ∧
        ContinuousWithinAt (fun x => ((trivializationAt F E (f x₀).proj) (f x)).2) s x₀ :=
  (trivializationAt F E (f x₀).proj).tendsto_nhds_iff mem_trivializationAt_proj_source

/-- Characterization of continuous functions (at a point) into a fiber bundle. -/
theorem continuousAt_totalSpace (f : X → TotalSpace F E) {x₀ : X} :
    ContinuousAt f x₀ ↔
      ContinuousAt (fun x => (f x).proj) x₀ ∧
        ContinuousAt (fun x => ((trivializationAt F E (f x₀).proj) (f x)).2) x₀ :=
  (trivializationAt F E (f x₀).proj).tendsto_nhds_iff mem_trivializationAt_proj_source

/-- Characterization of continuous sections within a set at a point of a vector bundle. -/
theorem continuousWithinAt_section {s : ∀ x, E x} {a : Set B} {x₀ : B} :
    ContinuousWithinAt (fun x ↦ TotalSpace.mk' F x (s x)) a x₀ ↔
      ContinuousWithinAt (fun x ↦ (trivializationAt F E x₀ ⟨x, s x⟩).2) a x₀ := by
  simp_rw [continuousWithinAt_totalSpace, and_iff_right_iff_imp]
  intro; exact continuousWithinAt_id

/-- Characterization of continuous sections of a vector bundle. -/
theorem continuousAt_section {s : ∀ x, E x} (x₀ : B) :
    ContinuousAt (fun x ↦ TotalSpace.mk' F x (s x)) x₀ ↔
      ContinuousAt (fun x ↦ (trivializationAt F E x₀ ⟨x, s x⟩).2) x₀ := by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_section F

end FiberBundle

variable (F)
variable (E)

/-- If `E` is a fiber bundle over a conditionally complete linear order,
then it is trivial over any closed interval. -/
theorem FiberBundle.exists_trivialization_Icc_subset [ConditionallyCompleteLinearOrder B]
    [OrderTopology B] [FiberBundle F E] (a b : B) :
    ∃ e : Trivialization F (π F E), Icc a b ⊆ e.baseSet := by
  obtain ⟨ea, hea⟩ : ∃ ea : Trivialization F (π F E), a ∈ ea.baseSet :=
    ⟨trivializationAt F E a, mem_baseSet_trivializationAt F E a⟩
  -- If `a < b`, then `[a, b] = ∅`, and the statement is trivial
  rcases lt_or_ge b a with _ | hab
  · exact ⟨ea, by simp [*]⟩
  /- Let `s` be the set of points `x ∈ [a, b]` such that `E` is trivializable over `[a, x]`.
    We need to show that `b ∈ s`. Let `c = Sup s`. We will show that `c ∈ s` and `c = b`. -/
  set s : Set B := { x ∈ Icc a b | ∃ e : Trivialization F (π F E), Icc a x ⊆ e.baseSet }
  have ha : a ∈ s := ⟨left_mem_Icc.2 hab, ea, by simp [hea]⟩
  have sne : s.Nonempty := ⟨a, ha⟩
  have hsb : b ∈ upperBounds s := fun x hx => hx.1.2
  have sbd : BddAbove s := ⟨b, hsb⟩
  set c := sSup s
  have hsc : IsLUB s c := isLUB_csSup sne sbd
  have hc : c ∈ Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  obtain ⟨-, ec : Trivialization F (π F E), hec : Icc a c ⊆ ec.baseSet⟩ : c ∈ s := by
    rcases hc.1.eq_or_lt with heq | hlt
    · rwa [← heq]
    refine ⟨hc, ?_⟩
    /- In order to show that `c ∈ s`, consider a trivialization `ec` of `proj` over a neighborhood
      of `c`. Its base set includes `(c', c]` for some `c' ∈ [a, c)`. -/
    obtain ⟨ec, hc⟩ : ∃ ec : Trivialization F (π F E), c ∈ ec.baseSet :=
      ⟨trivializationAt F E c, mem_baseSet_trivializationAt F E c⟩
    obtain ⟨c', hc', hc'e⟩ : ∃ c' ∈ Ico a c, Ioc c' c ⊆ ec.baseSet :=
      (mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset hlt).1
        (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds ec.open_baseSet hc)
    /- Since `c' < c = Sup s`, there exists `d ∈ s ∩ (c', c]`. Let `ead` be a trivialization of
      `proj` over `[a, d]`. Then we can glue `ead` and `ec` into a trivialization over `[a, c]`. -/
    obtain ⟨d, ⟨hdab, ead, had⟩, hd⟩ : ∃ d ∈ s, d ∈ Ioc c' c := hsc.exists_between hc'.2
    refine ⟨ead.piecewiseLe ec d (had ⟨hdab.1, le_rfl⟩) (hc'e hd), subset_ite.2 ?_⟩
    exact ⟨fun x hx => had ⟨hx.1.1, hx.2⟩, fun x hx => hc'e ⟨hd.1.trans (not_le.1 hx.2), hx.1.2⟩⟩
  /- So, `c ∈ s`. Let `ec` be a trivialization of `proj` over `[a, c]`.  If `c = b`, then we are
    done. Otherwise we show that `proj` can be trivialized over a larger interval `[a, d]`,
    `d ∈ (c, b]`, hence `c` is not an upper bound of `s`. -/
  rcases hc.2.eq_or_lt with heq | hlt
  · exact ⟨ec, heq ▸ hec⟩
  rsuffices ⟨d, hdcb, hd⟩ : ∃ d ∈ Ioc c b, ∃ e : Trivialization F (π F E), Icc a d ⊆ e.baseSet
  · exact ((hsc.1 ⟨⟨hc.1.trans hdcb.1.le, hdcb.2⟩, hd⟩).not_gt hdcb.1).elim
  /- Since the base set of `ec` is open, it includes `[c, d)` (hence, `[a, d)`) for some
    `d ∈ (c, b]`. -/
  obtain ⟨d, hdcb, hd⟩ : ∃ d ∈ Ioc c b, Ico c d ⊆ ec.baseSet :=
    (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hlt).1
      (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds ec.open_baseSet (hec ⟨hc.1, le_rfl⟩))
  have had : Ico a d ⊆ ec.baseSet := Ico_subset_Icc_union_Ico.trans (union_subset hec hd)
  by_cases he : Disjoint (Iio d) (Ioi c)
  · /- If `(c, d) = ∅`, then let `ed` be a trivialization of `proj` over a neighborhood of `d`.
      Then the disjoint union of `ec` restricted to `(-∞, d)` and `ed` restricted to `(c, ∞)` is
      a trivialization over `[a, d]`. -/
    obtain ⟨ed, hed⟩ : ∃ ed : Trivialization F (π F E), d ∈ ed.baseSet :=
      ⟨trivializationAt F E d, mem_baseSet_trivializationAt F E d⟩
    refine ⟨d, hdcb,
      (ec.restrOpen (Iio d) isOpen_Iio).disjointUnion (ed.restrOpen (Ioi c) isOpen_Ioi)
        (he.mono inter_subset_right inter_subset_right), fun x hx => ?_⟩
    rcases hx.2.eq_or_lt with (rfl | hxd)
    exacts [Or.inr ⟨hed, hdcb.1⟩, Or.inl ⟨had ⟨hx.1, hxd⟩, hxd⟩]
  · /- If `(c, d)` is nonempty, then take `d' ∈ (c, d)`. Since the base set of `ec` includes
          `[a, d)`, it includes `[a, d'] ⊆ [a, d)` as well. -/
    rw [disjoint_left] at he
    push Not at he
    rcases he with ⟨d', hdd' : d' < d, hd'c⟩
    exact ⟨d', ⟨hd'c, hdd'.le.trans hdcb.2⟩, ec, (Icc_subset_Ico_right hdd').trans had⟩

end FiberBundle

/-! ### Core construction for constructing fiber bundles -/

/-- Core data defining a locally trivial bundle with fiber `F` over a topological
space `B`. Note that "bundle" is used in its mathematical sense. This is the (computer science)
bundled version, i.e., all the relevant data is contained in the following structure. A family of
local trivializations is indexed by a type `ι`, on open subsets `baseSet i` for each `i : ι`.
Trivialization changes from `i` to `j` are given by continuous maps `coordChange i j` from
`baseSet i ∩ baseSet j` to the set of homeomorphisms of `F`, but we express them as maps
`B → F → F` and require continuity on `(baseSet i ∩ baseSet j) × F` to avoid the topology on the
space of continuous maps on `F`. -/
structure FiberBundleCore (ι : Type*) (B : Type*) [TopologicalSpace B] (F : Type*)
    [TopologicalSpace F] where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  coordChange : ι → ι → B → F → F
  coordChange_self : ∀ i, ∀ x ∈ baseSet i, ∀ v, coordChange i i x v = v
  continuousOn_coordChange : ∀ i j,
    ContinuousOn (fun p : B × F => coordChange i j p.1 p.2) ((baseSet i ∩ baseSet j) ×ˢ univ)
  coordChange_comp : ∀ i j k, ∀ x ∈ baseSet i ∩ baseSet j ∩ baseSet k, ∀ v,
    (coordChange j k x) (coordChange i j x v) = coordChange i k x v

namespace FiberBundleCore

variable [TopologicalSpace B] [TopologicalSpace F] (Z : FiberBundleCore ι B F)

/-- The index set of a fiber bundle core, as a convenience function for dot notation -/
@[nolint unusedArguments]
def Index (_Z : FiberBundleCore ι B F) := ι

/-- The base space of a fiber bundle core, as a convenience function for dot notation -/
@[nolint unusedArguments, reducible]
def Base (_Z : FiberBundleCore ι B F) := B

/-- The fiber of a fiber bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unusedArguments]
def Fiber (_ : FiberBundleCore ι B F) (_x : B) := F

instance topologicalSpaceFiber (x : B) : TopologicalSpace (Z.Fiber x) := ‹_›

/-- The total space of the fiber bundle, as a convenience function for dot notation.
It is by definition equal to `Bundle.TotalSpace F Z.Fiber`. -/
abbrev TotalSpace := Bundle.TotalSpace F Z.Fiber

/-- The projection from the total space of a fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps]
def proj : Z.TotalSpace → B :=
  Bundle.TotalSpace.proj

/-- Local homeomorphism version of the trivialization change. -/
def trivChange (i j : ι) : OpenPartialHomeomorph (B × F) (B × F) where
  source := (Z.baseSet i ∩ Z.baseSet j) ×ˢ univ
  target := (Z.baseSet i ∩ Z.baseSet j) ×ˢ univ
  toFun p := ⟨p.1, Z.coordChange i j p.1 p.2⟩
  invFun p := ⟨p.1, Z.coordChange j i p.1 p.2⟩
  map_source' p hp := by simpa using hp
  map_target' p hp := by simpa using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prodMk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx
    dsimp only
    rw [coordChange_comp, Z.coordChange_self]
    exacts [hx.1, ⟨⟨hx.1, hx.2⟩, hx.1⟩]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prodMk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx
    dsimp only
    rw [Z.coordChange_comp, Z.coordChange_self]
    · exact hx.2
    · simp [hx]
  open_source := ((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).prod isOpen_univ
  open_target := ((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).prod isOpen_univ
  continuousOn_toFun := continuous_fst.continuousOn.prodMk (Z.continuousOn_coordChange i j)
  continuousOn_invFun := by
    simpa [inter_comm] using continuous_fst.continuousOn.prodMk (Z.continuousOn_coordChange j i)

@[simp, mfld_simps]
theorem mem_trivChange_source (i j : ι) (p : B × F) :
    p ∈ (Z.trivChange i j).source ↔ p.1 ∈ Z.baseSet i ∩ Z.baseSet j := by
  rw [trivChange, mem_prod]
  simp

/-- Associate to a trivialization index `i : ι` the corresponding trivialization, i.e., a bijection
between `proj ⁻¹ (baseSet i)` and `baseSet i × F`. As the fiber above `x` is `F` but read in the
chart with index `index_at x`, the trivialization in the fiber above x is by definition the
coordinate change from i to `index_at x`, so it depends on `x`.
The local trivialization will ultimately be an open partial homeomorphism. For now, we only
introduce the partial equivalence version, denoted with a prime.
In further developments, avoid this auxiliary version, and use `Z.local_triv` instead. -/
def localTrivAsPartialEquiv (i : ι) : PartialEquiv Z.TotalSpace (B × F) where
  source := Z.proj ⁻¹' Z.baseSet i
  target := Z.baseSet i ×ˢ univ
  invFun p := ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩
  toFun p := ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩
  map_source' p hp := by
    simpa only [Set.mem_preimage, and_true, Set.mem_univ, Set.prodMk_mem_set_prod_eq] using hp
  map_target' p hp := by
    simpa only [Set.mem_preimage, and_true, Set.mem_univ, Set.mem_prod] using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    replace hx : x ∈ Z.baseSet i := hx
    dsimp only
    rw [Z.coordChange_comp, Z.coordChange_self] <;> apply_rules [mem_baseSet_at, mem_inter]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prodMk_mem_set_prod_eq, and_true, mem_univ] at hx
    dsimp only
    rw [Z.coordChange_comp, Z.coordChange_self]
    exacts [hx, ⟨⟨hx, Z.mem_baseSet_at _⟩, hx⟩]

variable (i : ι)

theorem mem_localTrivAsPartialEquiv_source (p : Z.TotalSpace) :
    p ∈ (Z.localTrivAsPartialEquiv i).source ↔ p.1 ∈ Z.baseSet i :=
  Iff.rfl

theorem mem_localTrivAsPartialEquiv_target (p : B × F) :
    p ∈ (Z.localTrivAsPartialEquiv i).target ↔ p.1 ∈ Z.baseSet i := by
  rw [localTrivAsPartialEquiv, mem_prod]
  simp only [and_true, mem_univ]

theorem localTrivAsPartialEquiv_apply (p : Z.TotalSpace) :
    (Z.localTrivAsPartialEquiv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl

/-- The composition of two local trivializations is the trivialization change `Z.trivChange i j`. -/
theorem localTrivAsPartialEquiv_trans (i j : ι) :
    (Z.localTrivAsPartialEquiv i).symm.trans (Z.localTrivAsPartialEquiv j) ≈
      (Z.trivChange i j).toPartialEquiv := by
  constructor
  · ext x
    simp only [mem_localTrivAsPartialEquiv_target, mfld_simps]
    rfl
  · rintro ⟨x, v⟩ hx
    simp only [trivChange, localTrivAsPartialEquiv, PartialEquiv.symm,
      Prod.mk_inj, prodMk_mem_set_prod_eq, PartialEquiv.trans_source, mem_inter_iff,
      mem_preimage, proj, mem_univ, (· ∘ ·),
      PartialEquiv.coe_trans] at hx ⊢
    simp only [Z.coordChange_comp, hx, mem_inter_iff, and_self_iff, mem_baseSet_at]

/-- Topological structure on the total space of a fiber bundle created from core, designed so
that all the local trivialization are continuous. -/
instance toTopologicalSpace : TopologicalSpace (Bundle.TotalSpace F Z.Fiber) :=
  TopologicalSpace.generateFrom <| ⋃ (i : ι) (s : Set (B × F)) (_ : IsOpen s),
    {(Z.localTrivAsPartialEquiv i).source ∩ Z.localTrivAsPartialEquiv i ⁻¹' s}

variable (b : B) (a : F)

theorem open_source' (i : ι) : IsOpen (Z.localTrivAsPartialEquiv i).source := by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [exists_prop, mem_iUnion, mem_singleton_iff]
  refine ⟨i, Z.baseSet i ×ˢ univ, (Z.isOpen_baseSet i).prod isOpen_univ, ?_⟩
  ext p
  simp only [localTrivAsPartialEquiv_apply, prodMk_mem_set_prod_eq, mem_inter_iff, and_self_iff,
    mem_localTrivAsPartialEquiv_source, and_true, mem_univ, mem_preimage]

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def localTriv (i : ι) : Trivialization F Z.proj where
  baseSet := Z.baseSet i
  open_baseSet := Z.isOpen_baseSet i
  source_eq := rfl
  target_eq := rfl
  proj_toFun p _ := by
    simp only [mfld_simps]
    rfl
  open_source := Z.open_source' i
  open_target := (Z.isOpen_baseSet i).prod isOpen_univ
  continuousOn_toFun := by
    rw [continuousOn_open_iff (Z.open_source' i)]
    intro s s_open
    apply TopologicalSpace.GenerateOpen.basic
    simp only [exists_prop, mem_iUnion, mem_singleton_iff]
    exact ⟨i, s, s_open, rfl⟩
  continuousOn_invFun := by
    refine continuousOn_isOpen_of_generateFrom fun t ht ↦ ?_
    simp only [exists_prop, mem_iUnion, mem_singleton_iff] at ht
    obtain ⟨j, s, s_open, ts⟩ : ∃ j s, IsOpen s ∧
      t = (localTrivAsPartialEquiv Z j).source ∩ localTrivAsPartialEquiv Z j ⁻¹' s := ht
    rw [ts]
    simp only [preimage_inter]
    let e := Z.localTrivAsPartialEquiv i
    let e' := Z.localTrivAsPartialEquiv j
    let f := e.symm.trans e'
    have : IsOpen (f.source ∩ f ⁻¹' s) := by
      rw [PartialEquiv.EqOnSource.source_inter_preimage_eq (Z.localTrivAsPartialEquiv_trans i j)]
      exact (continuousOn_open_iff (Z.trivChange i j).open_source).1
        (Z.trivChange i j).continuousOn _ s_open
    convert this using 1
    dsimp [f, PartialEquiv.trans_source]
    rw [← preimage_comp, inter_assoc]
  toPartialEquiv := Z.localTrivAsPartialEquiv i

/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a bundle trivialization -/
def localTrivAt (b : B) : Trivialization F (π F Z.Fiber) :=
  Z.localTriv (Z.indexAt b)

@[simp, mfld_simps]
theorem localTrivAt_def (b : B) : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=
  rfl

theorem localTrivAt_snd (b : B) (p) :
    (Z.localTrivAt b p).2 = Z.coordChange (Z.indexAt p.1) (Z.indexAt b) p.1 p.2 :=
  rfl

/-- If an element of `F` is invariant under all coordinate changes, then one can define a
corresponding section of the fiber bundle, which is continuous. This applies in particular to the
zero section of a vector bundle. Another example (not yet defined) would be the identity
section of the endomorphism bundle of a vector bundle. -/
theorem continuous_const_section (v : F)
    (h : ∀ i j, ∀ x ∈ Z.baseSet i ∩ Z.baseSet j, Z.coordChange i j x v = v) :
    Continuous (show B → Z.TotalSpace from fun x => ⟨x, v⟩) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have A : Z.baseSet (Z.indexAt x) ∈ 𝓝 x :=
    IsOpen.mem_nhds (Z.isOpen_baseSet (Z.indexAt x)) (Z.mem_baseSet_at x)
  refine ((Z.localTrivAt x).toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left ?_).2 ?_
  · exact A
  · apply continuousAt_id.prodMk
    simp only [mfld_simps]
    have : ContinuousOn (fun _ : B => v) (Z.baseSet (Z.indexAt x)) := continuousOn_const
    refine (this.congr fun y hy ↦ ?_).continuousAt A
    exact h _ _ _ ⟨mem_baseSet_at _ _, hy⟩

@[simp, mfld_simps]
theorem localTrivAsPartialEquiv_coe : ⇑(Z.localTrivAsPartialEquiv i) = Z.localTriv i :=
  rfl

@[simp, mfld_simps]
theorem localTrivAsPartialEquiv_source :
    (Z.localTrivAsPartialEquiv i).source = (Z.localTriv i).source :=
  rfl

@[simp, mfld_simps]
theorem localTrivAsPartialEquiv_target :
    (Z.localTrivAsPartialEquiv i).target = (Z.localTriv i).target :=
  rfl

@[simp, mfld_simps]
theorem localTrivAsPartialEquiv_symm :
    (Z.localTrivAsPartialEquiv i).symm = (Z.localTriv i).toPartialEquiv.symm :=
  rfl

@[simp, mfld_simps]
theorem baseSet_at : Z.baseSet i = (Z.localTriv i).baseSet :=
  rfl

@[simp, mfld_simps]
theorem localTriv_apply (p : Z.TotalSpace) :
    (Z.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl

@[simp, mfld_simps]
theorem localTrivAt_apply (p : Z.TotalSpace) : (Z.localTrivAt p.1) p = ⟨p.1, p.2⟩ := by
  rw [localTrivAt, localTriv_apply, coordChange_self]
  exact Z.mem_baseSet_at p.1

@[simp, mfld_simps]
theorem localTrivAt_apply_mk (b : B) (a : F) : (Z.localTrivAt b) ⟨b, a⟩ = ⟨b, a⟩ :=
  Z.localTrivAt_apply _

@[simp, mfld_simps]
theorem mem_localTriv_source (p : Z.TotalSpace) :
    p ∈ (Z.localTriv i).source ↔ p.1 ∈ (Z.localTriv i).baseSet :=
  Iff.rfl

@[simp, mfld_simps]
theorem mem_localTrivAt_source (p : Z.TotalSpace) (b : B) :
    p ∈ (Z.localTrivAt b).source ↔ p.1 ∈ (Z.localTrivAt b).baseSet :=
  Iff.rfl

@[simp, mfld_simps]
theorem mem_localTriv_target (p : B × F) :
    p ∈ (Z.localTriv i).target ↔ p.1 ∈ (Z.localTriv i).baseSet :=
  Trivialization.mem_target _

@[simp, mfld_simps]
theorem mem_localTrivAt_target (p : B × F) (b : B) :
    p ∈ (Z.localTrivAt b).target ↔ p.1 ∈ (Z.localTrivAt b).baseSet :=
  Trivialization.mem_target _

@[simp, mfld_simps]
theorem localTriv_symm_apply (p : B × F) :
    (Z.localTriv i).toOpenPartialHomeomorph.symm p =
      ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩ :=
  rfl

@[simp, mfld_simps]
theorem mem_localTrivAt_baseSet (b : B) : b ∈ (Z.localTrivAt b).baseSet := by
  rw [localTrivAt, ← baseSet_at]
  exact Z.mem_baseSet_at b

theorem mk_mem_localTrivAt_source : (⟨b, a⟩ : Z.TotalSpace) ∈ (Z.localTrivAt b).source := by
  simp only [mfld_simps]

set_option backward.isDefEq.respectTransparency false in
/-- A fiber bundle constructed from core is indeed a fiber bundle. -/
instance fiberBundle : FiberBundle F Z.Fiber where
  totalSpaceMk_isInducing' b := isInducing_iff_nhds.2 fun x ↦ by
    rw [(Z.localTrivAt b).nhds_eq_comap_inf_principal (mk_mem_localTrivAt_source _ _ _), comap_inf,
      comap_principal, comap_comap]
    simp only [Function.comp_def, localTrivAt_apply_mk, Trivialization.coe_coe,
      ← (isEmbedding_prodMkRight b).nhds_eq_comap]
    convert_to 𝓝 x = 𝓝 x ⊓ 𝓟 univ
    · congr
      exact eq_univ_of_forall (mk_mem_localTrivAt_source Z _)
    · rw [principal_univ, inf_top_eq]
  trivializationAtlas' := Set.range Z.localTriv
  trivializationAt' := Z.localTrivAt
  mem_baseSet_trivializationAt' := Z.mem_baseSet_at
  trivialization_mem_atlas' b := ⟨Z.indexAt b, rfl⟩

/-- The inclusion of a fiber into the total space is a continuous map. -/
@[continuity]
theorem continuous_totalSpaceMk (b : B) :
    Continuous (TotalSpace.mk b : Z.Fiber b → Bundle.TotalSpace F Z.Fiber) :=
  FiberBundle.continuous_totalSpaceMk F Z.Fiber b

/-- The projection on the base of a fiber bundle created from core is continuous -/
nonrec theorem continuous_proj : Continuous Z.proj :=
  FiberBundle.continuous_proj F Z.Fiber

/-- The projection on the base of a fiber bundle created from core is an open map -/
nonrec theorem isOpenMap_proj : IsOpenMap Z.proj :=
  FiberBundle.isOpenMap_proj F Z.Fiber

end FiberBundleCore

/-! ### Prebundle construction for constructing fiber bundles -/

variable (F)
variable (E : B → Type*) [TopologicalSpace B] [TopologicalSpace F]
  [∀ x, TopologicalSpace (E x)]

/-- This structure permits to define a fiber bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space. The total space is hence given a
topology in such a way that there is a fiber bundle structure for which the partial equivalences
are also open partial homeomorphisms and hence local trivializations. -/
structure FiberPrebundle where
  pretrivializationAtlas : Set (Pretrivialization F (π F E))
  pretrivializationAt : B → Pretrivialization F (π F E)
  mem_base_pretrivializationAt : ∀ x : B, x ∈ (pretrivializationAt x).baseSet
  pretrivialization_mem_atlas : ∀ x : B, pretrivializationAt x ∈ pretrivializationAtlas
  continuous_trivChange : ∀ e, e ∈ pretrivializationAtlas → ∀ e', e' ∈ pretrivializationAtlas →
    ContinuousOn (e ∘ e'.toPartialEquiv.symm) (e'.target ∩ e'.toPartialEquiv.symm ⁻¹' e.source)
  totalSpaceMk_isInducing : ∀ b : B, IsInducing (pretrivializationAt b ∘ TotalSpace.mk b)

namespace FiberPrebundle

variable {F E}
variable (a : FiberPrebundle F E) {e : Pretrivialization F (π F E)}

/-- Topology on the total space that will make the prebundle into a bundle. -/
@[implicit_reducible]
def totalSpaceTopology (a : FiberPrebundle F E) : TopologicalSpace (TotalSpace F E) :=
  ⨆ (e : Pretrivialization F (π F E)) (_ : e ∈ a.pretrivializationAtlas),
    coinduced e.setSymm instTopologicalSpaceSubtype

theorem continuous_symm_of_mem_pretrivializationAtlas (he : e ∈ a.pretrivializationAtlas) :
    @ContinuousOn _ _ _ a.totalSpaceTopology e.toPartialEquiv.symm e.target := by
  refine fun z H U h => preimage_nhdsWithin_coinduced' H (le_def.1 (nhds_mono ?_) U h)
  exact le_iSup₂ (α := TopologicalSpace (TotalSpace F E)) e he

theorem isOpen_source (e : Pretrivialization F (π F E)) :
    IsOpen[a.totalSpaceTopology] e.source := by
  refine isOpen_iSup_iff.mpr fun e' => isOpen_iSup_iff.mpr fun _ => ?_
  refine isOpen_coinduced.mpr (isOpen_induced_iff.mpr ⟨e.target, e.open_target, ?_⟩)
  ext ⟨x, hx⟩
  simp only [mem_preimage, Pretrivialization.setSymm, restrict, e.mem_target, e.mem_source,
    e'.proj_symm_apply hx]

theorem isOpen_target_of_mem_pretrivializationAtlas_inter (e e' : Pretrivialization F (π F E))
    (he' : e' ∈ a.pretrivializationAtlas) :
    IsOpen (e'.toPartialEquiv.target ∩ e'.toPartialEquiv.symm ⁻¹' e.source) := by
  letI := a.totalSpaceTopology
  obtain ⟨u, hu1, hu2⟩ := continuousOn_iff'.mp (a.continuous_symm_of_mem_pretrivializationAtlas he')
    e.source (a.isOpen_source e)
  rw [inter_comm, hu2]
  exact hu1.inter e'.open_target

/-- Promotion from a `Pretrivialization` to a `Trivialization`. -/
def trivializationOfMemPretrivializationAtlas (he : e ∈ a.pretrivializationAtlas) :
    @Trivialization B F _ _ _ a.totalSpaceTopology (π F E) :=
  let _ := a.totalSpaceTopology
  { e with
    open_source := a.isOpen_source e,
    continuousOn_toFun := by
      refine continuousOn_iff'.mpr fun s hs => ⟨e ⁻¹' s ∩ e.source,
        isOpen_iSup_iff.mpr fun e' => ?_, by rw [inter_assoc, inter_self]; rfl⟩
      refine isOpen_iSup_iff.mpr fun he' => ?_
      rw [isOpen_coinduced, isOpen_induced_iff]
      obtain ⟨u, hu1, hu2⟩ := continuousOn_iff'.mp (a.continuous_trivChange _ he _ he') s hs
      have hu3 := congr_arg (fun s => (fun x : e'.target => (x : B × F)) ⁻¹' s) hu2
      simp only [Subtype.coe_preimage_self, preimage_inter, univ_inter] at hu3
      refine ⟨u ∩ e'.toPartialEquiv.target ∩ e'.toPartialEquiv.symm ⁻¹' e.source, ?_, by
        simp only [preimage_inter, inter_univ, Subtype.coe_preimage_self, hu3.symm]; rfl⟩
      rw [inter_assoc]
      exact hu1.inter (a.isOpen_target_of_mem_pretrivializationAtlas_inter e e' he')
    continuousOn_invFun := a.continuous_symm_of_mem_pretrivializationAtlas he }

theorem mem_pretrivializationAt_source (b : B) (x : E b) :
    ⟨b, x⟩ ∈ (a.pretrivializationAt b).source := by
  simp only [(a.pretrivializationAt b).source_eq, mem_preimage]
  exact a.mem_base_pretrivializationAt b

@[simp]
theorem totalSpaceMk_preimage_source (b : B) :
    TotalSpace.mk b ⁻¹' (a.pretrivializationAt b).source = univ :=
  eq_univ_of_forall (a.mem_pretrivializationAt_source b)

@[continuity]
theorem continuous_totalSpaceMk (b : B) :
    Continuous[_, a.totalSpaceTopology] (TotalSpace.mk b) := by
  letI := a.totalSpaceTopology
  let e := a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas b)
  rw [e.toOpenPartialHomeomorph.continuous_iff_continuous_comp_left
      (a.totalSpaceMk_preimage_source b)]
  exact continuous_iff_le_induced.2 (a.totalSpaceMk_isInducing b).eq_induced.le

theorem inducing_totalSpaceMk_of_inducing_comp (b : B)
    (h : IsInducing (a.pretrivializationAt b ∘ TotalSpace.mk b)) :
    @IsInducing _ _ _ a.totalSpaceTopology (TotalSpace.mk b) := by
  letI := a.totalSpaceTopology
  rw [← restrict_comp_codRestrict (a.mem_pretrivializationAt_source b)] at h
  apply IsInducing.of_codRestrict (a.mem_pretrivializationAt_source b)
  refine h.of_comp ?_ (continuousOn_iff_continuous_restrict.mp
    (a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas b)).continuousOn)
  exact (a.continuous_totalSpaceMk b).codRestrict (a.mem_pretrivializationAt_source b)

/-- Make a `FiberBundle` from a `FiberPrebundle`.  Concretely this means
that, given a `FiberPrebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`FiberPrebundle.totalSpaceTopology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
@[implicit_reducible]
def toFiberBundle : @FiberBundle B F _ _ E a.totalSpaceTopology _ :=
  let _ := a.totalSpaceTopology
  { totalSpaceMk_isInducing' := fun b ↦ a.inducing_totalSpaceMk_of_inducing_comp b
      (a.totalSpaceMk_isInducing b)
    trivializationAtlas' :=
      { e | ∃ (e₀ : _) (he₀ : e₀ ∈ a.pretrivializationAtlas),
        e = a.trivializationOfMemPretrivializationAtlas he₀ },
    trivializationAt' := fun x ↦
      a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas x),
    mem_baseSet_trivializationAt' := a.mem_base_pretrivializationAt
    trivialization_mem_atlas' := fun x ↦ ⟨_, a.pretrivialization_mem_atlas x, rfl⟩ }

theorem continuous_proj : @Continuous _ _ a.totalSpaceTopology _ (π F E) := by
  letI := a.totalSpaceTopology
  letI := a.toFiberBundle
  exact FiberBundle.continuous_proj F E

instance {e₀} (he₀ : e₀ ∈ a.pretrivializationAtlas) :
    (letI := a.totalSpaceTopology; letI := a.toFiberBundle
      MemTrivializationAtlas (a.trivializationOfMemPretrivializationAtlas he₀)) :=
  letI := a.totalSpaceTopology; letI := a.toFiberBundle; ⟨e₀, he₀, rfl⟩

/-- For a fiber bundle `E` over `B` constructed using the `FiberPrebundle` mechanism,
continuity of a function `TotalSpace F E → X` on an open set `s` can be checked by precomposing at
each point with the pretrivialization used for the construction at that point. -/
theorem continuousOn_of_comp_right {X : Type*} [TopologicalSpace X] {f : TotalSpace F E → X}
    {s : Set B} (hs : IsOpen s) (hf : ∀ b ∈ s,
      ContinuousOn (f ∘ (a.pretrivializationAt b).toPartialEquiv.symm)
        ((s ∩ (a.pretrivializationAt b).baseSet) ×ˢ (Set.univ : Set F))) :
    @ContinuousOn _ _ a.totalSpaceTopology _ f (π F E ⁻¹' s) := by
  letI := a.totalSpaceTopology
  intro z hz
  let e : Trivialization F (π F E) :=
    a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas z.proj)
  refine (e.continuousAt_of_comp_right ?_
    ((hf z.proj hz).continuousAt (IsOpen.mem_nhds ?_ ?_))).continuousWithinAt
  · exact a.mem_base_pretrivializationAt z.proj
  · exact (hs.inter (a.pretrivializationAt z.proj).open_baseSet).prod isOpen_univ
  refine ⟨?_, mem_univ _⟩
  rw [e.coe_fst]
  · exact ⟨hz, a.mem_base_pretrivializationAt z.proj⟩
  · rw [e.mem_source]
    exact a.mem_base_pretrivializationAt z.proj

end FiberPrebundle

namespace FiberBundle
section extend

variable {E} [(x : B) → Zero (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]

/-- Extend a vector `v ∈ V x` to a section of the bundle `V`, whose value at `x` is `v`.
The details of the extension are mostly unspecified: for covariant derivatives, the value of
`s` at points other than `x` will not matter (except for shorter proofs).
-/
noncomputable def extend {x : B} (v₀ : E x) (x' : B) : E x' :=
  letI t := trivializationAt F E x
  letI w : F := (t ⟨x, v₀⟩).2
  -- TODO: use the `funToSec` helper from #36036 once available
  t.symm x' w

@[simp] lemma extend_apply_self {x : B} (v : E x) : extend F v x = v := by
  simp [extend, FiberBundle.mem_baseSet_trivializationAt' x]

end extend
end FiberBundle
