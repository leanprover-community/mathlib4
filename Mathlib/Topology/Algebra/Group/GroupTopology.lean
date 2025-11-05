/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Topology.Algebra.Group.Basic

/-!
### Lattice of group topologies

We define a type class `GroupTopology α` which endows a group `α` with a topology such that all
group operations are continuous.

Group topologies on a fixed group `α` are ordered, by reverse inclusion. They form a complete
lattice, with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : α → β` induces `coinduced f : TopologicalSpace α → GroupTopology β`.

The additive version `AddGroupTopology α` and corresponding results are provided as well.
-/

open Set Filter TopologicalSpace Function Topology Pointwise MulOpposite

universe u v w x

variable {G : Type w} {H : Type x} {α : Type u} {β : Type v}

/-- A group topology on a group `α` is a topology for which multiplication and inversion
are continuous. -/
structure GroupTopology (α : Type u) [Group α] : Type u
  extends TopologicalSpace α, IsTopologicalGroup α

/-- An additive group topology on an additive group `α` is a topology for which addition and
negation are continuous. -/
structure AddGroupTopology (α : Type u) [AddGroup α] : Type u
  extends TopologicalSpace α, IsTopologicalAddGroup α

attribute [to_additive] GroupTopology

namespace GroupTopology

variable [Group α]

/-- A version of the global `continuous_mul` suitable for dot notation. -/
@[to_additive /-- A version of the global `continuous_add` suitable for dot notation. -/]
theorem continuous_mul' (g : GroupTopology α) :
    haveI := g.toTopologicalSpace
    Continuous fun p : α × α => p.1 * p.2 := by
  letI := g.toTopologicalSpace
  haveI := g.toIsTopologicalGroup
  exact continuous_mul

/-- A version of the global `continuous_inv` suitable for dot notation. -/
@[to_additive /-- A version of the global `continuous_neg` suitable for dot notation. -/]
theorem continuous_inv' (g : GroupTopology α) :
    haveI := g.toTopologicalSpace
    Continuous (Inv.inv : α → α) := by
  letI := g.toTopologicalSpace
  haveI := g.toIsTopologicalGroup
  exact continuous_inv

@[to_additive]
theorem toTopologicalSpace_injective :
    Function.Injective (toTopologicalSpace : GroupTopology α → TopologicalSpace α) :=
  fun f g h => by
    cases f
    cases g
    congr

@[to_additive (attr := ext)]
theorem ext' {f g : GroupTopology α} (h : f.IsOpen = g.IsOpen) : f = g :=
  toTopologicalSpace_injective <| TopologicalSpace.ext h

/-- The ordering on group topologies on the group `γ`. `t ≤ s` if every set open in `s` is also open
in `t` (`t` is finer than `s`). -/
@[to_additive
  /-- The ordering on group topologies on the group `γ`. `t ≤ s` if every set open in `s`
  is also open in `t` (`t` is finer than `s`). -/]
instance : PartialOrder (GroupTopology α) :=
  PartialOrder.lift toTopologicalSpace toTopologicalSpace_injective

@[to_additive (attr := simp)]
theorem toTopologicalSpace_le {x y : GroupTopology α} :
    x.toTopologicalSpace ≤ y.toTopologicalSpace ↔ x ≤ y :=
  Iff.rfl

@[to_additive]
instance : Top (GroupTopology α) :=
  let _t : TopologicalSpace α := ⊤
  ⟨{  continuous_mul := continuous_top
      continuous_inv := continuous_top }⟩

@[to_additive (attr := simp)]
theorem toTopologicalSpace_top : (⊤ : GroupTopology α).toTopologicalSpace = ⊤ :=
  rfl

@[to_additive]
instance : Bot (GroupTopology α) :=
  let _t : TopologicalSpace α := ⊥
  ⟨{  continuous_mul := by
        haveI := discreteTopology_bot α
        fun_prop
      continuous_inv := continuous_bot }⟩

@[to_additive (attr := simp)]
theorem toTopologicalSpace_bot : (⊥ : GroupTopology α).toTopologicalSpace = ⊥ :=
  rfl

@[to_additive]
instance : BoundedOrder (GroupTopology α) where
  top := ⊤
  le_top x := show x.toTopologicalSpace ≤ ⊤ from le_top
  bot := ⊥
  bot_le x := show ⊥ ≤ x.toTopologicalSpace from bot_le

@[to_additive]
instance : Min (GroupTopology α) where min x y := ⟨x.1 ⊓ y.1, topologicalGroup_inf x.2 y.2⟩

@[to_additive (attr := simp)]
theorem toTopologicalSpace_inf (x y : GroupTopology α) :
    (x ⊓ y).toTopologicalSpace = x.toTopologicalSpace ⊓ y.toTopologicalSpace :=
  rfl

@[to_additive]
instance : SemilatticeInf (GroupTopology α) :=
  toTopologicalSpace_injective.semilatticeInf _ .rfl .rfl toTopologicalSpace_inf

@[to_additive]
instance : Inhabited (GroupTopology α) :=
  ⟨⊤⟩

/-- Infimum of a collection of group topologies. -/
@[to_additive /-- Infimum of a collection of additive group topologies -/]
instance : InfSet (GroupTopology α) where
  sInf S :=
    ⟨sInf (toTopologicalSpace '' S), topologicalGroup_sInf <| forall_mem_image.2 fun t _ => t.2⟩

@[to_additive (attr := simp)]
theorem toTopologicalSpace_sInf (s : Set (GroupTopology α)) :
    (sInf s).toTopologicalSpace = sInf (toTopologicalSpace '' s) := rfl

@[to_additive (attr := simp)]
theorem toTopologicalSpace_iInf {ι} (s : ι → GroupTopology α) :
    (⨅ i, s i).toTopologicalSpace = ⨅ i, (s i).toTopologicalSpace :=
  congr_arg sInf (range_comp _ _).symm

/-- Group topologies on `γ` form a complete lattice, with `⊥` the discrete topology and `⊤` the
indiscrete topology.

The infimum of a collection of group topologies is the topology generated by all their open sets
(which is a group topology).

The supremum of two group topologies `s` and `t` is the infimum of the family of all group
topologies contained in the intersection of `s` and `t`. -/
@[to_additive
  /-- Group topologies on `γ` form a complete lattice, with `⊥` the discrete topology and
  `⊤` the indiscrete topology.

  The infimum of a collection of group topologies is the topology generated by all their open sets
  (which is a group topology).

  The supremum of two group topologies `s` and `t` is the infimum of the family of all group
  topologies contained in the intersection of `s` and `t`. -/]
instance : CompleteSemilatticeInf (GroupTopology α) :=
  { inferInstanceAs (InfSet (GroupTopology α)),
    inferInstanceAs (PartialOrder (GroupTopology α)) with
    sInf_le := fun _ a haS => toTopologicalSpace_le.1 <| sInf_le ⟨a, haS, rfl⟩
    le_sInf := by
      intro S a hab
      apply (inferInstanceAs (CompleteLattice (TopologicalSpace α))).le_sInf
      rintro _ ⟨b, hbS, rfl⟩
      exact hab b hbS }

@[to_additive]
instance : CompleteLattice (GroupTopology α) :=
  { inferInstanceAs (BoundedOrder (GroupTopology α)),
    inferInstanceAs (SemilatticeInf (GroupTopology α)),
    completeLatticeOfCompleteSemilatticeInf _ with
    inf := (· ⊓ ·)
    top := ⊤
    bot := ⊥ }

/-- Given `f : α → β` and a topology on `α`, the coinduced group topology on `β` is the finest
topology such that `f` is continuous and `β` is a topological group. -/
@[to_additive
  /-- Given `f : α → β` and a topology on `α`, the coinduced additive group topology on `β`
  is the finest topology such that `f` is continuous and `β` is a topological additive group. -/]
def coinduced {α β : Type*} [t : TopologicalSpace α] [Group β] (f : α → β) : GroupTopology β :=
  sInf { b : GroupTopology β | TopologicalSpace.coinduced f t ≤ b.toTopologicalSpace }

@[to_additive]
theorem coinduced_continuous {α β : Type*} [t : TopologicalSpace α] [Group β] (f : α → β) :
    Continuous[t, (coinduced f).toTopologicalSpace] f := by
  rw [continuous_sInf_rng]
  rintro _ ⟨t', ht', rfl⟩
  exact continuous_iff_coinduced_le.2 ht'

end GroupTopology
