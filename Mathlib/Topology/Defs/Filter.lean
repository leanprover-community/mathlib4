/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
import Mathlib.Topology.Defs.Basic
import Mathlib.Order.Filter.Ultrafilter

/-!
# Definitions about filters in topological spaces

In this file we define filters in topological spaces,
as well as other definitions that rely on `Filter`s.
-/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open Filter
open scoped Topology

/-- A set is called a neighborhood of `x` if it contains an open set around `x`. The set of all
neighborhoods of `x` forms a filter, the neighborhood filter at `x`, is here defined as the
infimum over the principal filters of all open sets containing `x`. -/
irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s
#align nhds nhds
#align nhds_def nhds_def

@[inherit_doc]
scoped[Topology] notation "𝓝" => nhds

/-- The "neighborhood within" filter. Elements of `𝓝[s] x` are sets containing the
intersection of `s` and a neighborhood of `x`. -/
def nhdsWithin (x : X) (s : Set X) : Filter X :=
  𝓝 x ⊓ 𝓟 s
#align nhds_within nhdsWithin

@[inherit_doc]
scoped[Topology] notation "𝓝[" s "] " x:100 => nhdsWithin x s

/-- Notation for the filter of punctured neighborhoods of a point. -/
scoped[Topology] notation3 "𝓝[≠] " x:100 =>
  nhdsWithin x (@singleton _ (Set _) Set.instSingletonSet x)ᶜ

/-- Notation for the filter of right neighborhoods of a point. -/
scoped[Topology] notation3 "𝓝[≥] " x:100 => nhdsWithin x (Set.Ici x)

/-- Notation for the filter of left neighborhoods of a point. -/
scoped[Topology] notation3 "𝓝[≤] " x:100 => nhdsWithin x (Set.Iic x)

/-- Notation for the filter of punctured right neighborhoods of a point. -/
scoped[Topology] notation3 "𝓝[>] " x:100 => nhdsWithin x (Set.Ioi x)

/-- Notation for the filter of punctured left neighborhoods of a point. -/
scoped[Topology] notation3 "𝓝[<] " x:100 => nhdsWithin x (Set.Iio x)

/-- A point `x` is a cluster point of a filter `F` if `𝓝 x ⊓ F ≠ ⊥`.
Also known as an accumulation point or a limit point, but beware that terminology varies.
This is *not* the same as asking `𝓝[≠] x ⊓ F ≠ ⊥`, which is called `AccPt` in Mathlib.
See `mem_closure_iff_clusterPt` in particular. -/
def ClusterPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝 x ⊓ F)
#align cluster_pt ClusterPt

/-- A point `x` is a cluster point of a sequence `u` along a filter `F` if it is a cluster point
of `map u F`. -/
def MapClusterPt {ι : Type*} (x : X) (F : Filter ι) (u : ι → X) : Prop :=
  ClusterPt x (map u F)
#align map_cluster_pt MapClusterPt

/-- A point `x` is an accumulation point of a filter `F` if `𝓝[≠] x ⊓ F ≠ ⊥`.
See also `ClusterPt`. -/
def AccPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝[≠] x ⊓ F)
#align acc_pt AccPt

/-- A set `s` is compact if for every nontrivial filter `f` that contains `s`,
    there exists `a ∈ s` such that every set of `f` meets every neighborhood of `a`. -/
def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f
#align is_compact IsCompact

variable (X) in
/-- Type class for compact spaces. Separation is sometimes included in the definition, especially
in the French literature, but we do not include it here. -/
class CompactSpace : Prop where
  /-- In a compact space, `Set.univ` is a compact set. -/
  isCompact_univ : IsCompact (Set.univ : Set X)
#align compact_space CompactSpace

variable (X) in
/-- `X` is a noncompact topological space if it is not a compact space. -/
class NoncompactSpace : Prop where
  /-- In a noncompact space, `Set.univ` is not a compact set. -/
  noncompact_univ : ¬IsCompact (Set.univ : Set X)
#align noncompact_space NoncompactSpace

/-- We say that a topological space is a *weakly locally compact space*,
if each point of this space admits a compact neighborhood. -/
class WeaklyLocallyCompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Every point of a weakly locally compact space admits a compact neighborhood. -/
  exists_compact_mem_nhds (x : X) : ∃ s, IsCompact s ∧ s ∈ 𝓝 x

export WeaklyLocallyCompactSpace (exists_compact_mem_nhds)
#align exists_compact_mem_nhds WeaklyLocallyCompactSpace.exists_compact_mem_nhds

/-- There are various definitions of "locally compact space" in the literature,
which agree for Hausdorff spaces but not in general.
This one is the precise condition on X needed
for the evaluation map `C(X, Y) × X → Y` to be continuous for all `Y`
when `C(X, Y)` is given the compact-open topology.

See also `WeaklyLocallyCompactSpace`, a typeclass that only assumes
that each point has a compact neighborhood. -/
class LocallyCompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a locally compact space,
    every neighbourhood of every point contains a compact neighbourhood of that same point. -/
  local_compact_nhds : ∀ (x : X), ∀ n ∈ 𝓝 x, ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s
#align locally_compact_space LocallyCompactSpace

/-- We say that `X` and `Y` are a locally compact pair of topological spaces,
if for any continuous map `f : X → Y`, a point `x : X`, and a neighbourhood `s ∈ 𝓝 (f x)`,
there exists a compact neighbourhood `K ∈ 𝓝 x` such that `f` maps `K` to `s`.

This is a technical assumption that appears in several theorems,
most notably in `ContinuousMap.continuous_comp'` and `ContinuousMap.continuous_eval`.
It is satisfied in two cases:

- if `X` is a locally compact topological space, for obvious reasons;
- if `X` is a weakly locally compact topological space and `Y` is an R₁ space;
  this fact is a simple generalization of the theorem
  saying that a weakly locally compact R₁ topological space is locally compact.
-/
class LocallyCompactPair (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] : Prop where
  /-- If `f : X → Y` is a continuous map in a locally compact pair of topological spaces
  and `s : Set Y` is a neighbourhood of `f x`, `x : X`,
  then there exists a compact neighbourhood `K` of `x` such that `f` maps `K` to `s`. -/
  exists_mem_nhds_isCompact_mapsTo : ∀ {f : X → Y} {x : X} {s : Set Y},
    Continuous f → s ∈ 𝓝 (f x) → ∃ K ∈ 𝓝 x, IsCompact K ∧ Set.MapsTo f K s

export LocallyCompactPair (exists_mem_nhds_isCompact_mapsTo)

variable (X) in
/-- `Filter.cocompact` is the filter generated by complements to compact sets. -/
def Filter.cocompact : Filter X :=
  ⨅ (s : Set X) (_ : IsCompact s), 𝓟 sᶜ
#align filter.cocompact Filter.cocompact

variable (X) in
/-- `Filter.coclosedCompact` is the filter generated by complements to closed compact sets.
In a Hausdorff space, this is the same as `Filter.cocompact`. -/
def Filter.coclosedCompact : Filter X :=
  ⨅ (s : Set X) (_ : IsClosed s) (_ : IsCompact s), 𝓟 sᶜ
#align filter.coclosed_compact Filter.coclosedCompact

/-- A function between topological spaces is continuous at a point `x₀` within a subset `s`
if `f x` tends to `f x₀` when `x` tends to `x₀` while staying within `s`. -/
def ContinuousWithinAt (f : X → Y) (s : Set X) (x : X) : Prop :=
  Tendsto f (𝓝[s] x) (𝓝 (f x))
#align continuous_within_at ContinuousWithinAt

/-- A function between topological spaces is continuous on a subset `s`
when it's continuous at every point of `s` within `s`. -/
def ContinuousOn (f : X → Y) (s : Set X) : Prop :=
  ∀ x ∈ s, ContinuousWithinAt f s x
#align continuous_on ContinuousOn

set_option linter.uppercaseLean3 false

/-- If `f` is a filter, then `Filter.lim f` is a limit of the filter, if it exists. -/
noncomputable def lim [Nonempty X] (f : Filter X) : X :=
  Classical.epsilon fun x => f ≤ 𝓝 x
#align Lim lim

/--
If `F` is an ultrafilter, then `Filter.Ultrafilter.lim F` is a limit of the filter, if it exists.
Note that dot notation `F.lim` can be used for `F : Filter.Ultrafilter X`.
-/
noncomputable nonrec def Ultrafilter.lim (F : Ultrafilter X) : X :=
  @lim X _ (nonempty_of_neBot F) F
#align ultrafilter.Lim Ultrafilter.lim

/-- If `f` is a filter in `α` and `g : α → X` is a function, then `limUnder f g` is a limit of `g`
at `f`, if it exists. -/
noncomputable def limUnder {α : Type*} [Nonempty X] (f : Filter α) (g : α → X) : X :=
  lim (f.map g)
#align lim limUnder
