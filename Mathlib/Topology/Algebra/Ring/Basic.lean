/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Topology.Algebra.Group.Basic

#align_import topology.algebra.ring.basic from "leanprover-community/mathlib"@"9a59dcb7a2d06bf55da57b9030169219980660cd"

/-!

# Topological (semi)rings

A topological (semi)ring is a (semi)ring equipped with a topology such that all operations are
continuous. Besides this definition, this file proves that the topological closure of a subring
(resp. an ideal) is a subring (resp. an ideal) and defines products and quotients
of topological (semi)rings.

## Main Results

- `Subring.topologicalClosure`/`Subsemiring.topologicalClosure`: the topological closure of a
  `Subring`/`Subsemiring` is itself a `sub(semi)ring`.
- The product of two topological (semi)rings is a topological (semi)ring.
- The indexed product of topological (semi)rings is a topological (semi)ring.
-/


open Set Filter TopologicalSpace Function Topology Filter

section TopologicalSemiring

variable (α : Type*)

/-- a topological semiring is a semiring `R` where addition and multiplication are continuous.
We allow for non-unital and non-associative semirings as well.

The `TopologicalSemiring` class should *only* be instantiated in the presence of a
`NonUnitalNonAssocSemiring` instance; if there is an instance of `NonUnitalNonAssocRing`,
then `TopologicalRing` should be used. Note: in the presence of `NonAssocRing`, these classes are
mathematically equivalent (see `TopologicalSemiring.continuousNeg_of_mul` or
`TopologicalSemiring.toTopologicalRing`).  -/
class TopologicalSemiring [TopologicalSpace α] [NonUnitalNonAssocSemiring α] extends
  ContinuousAdd α, ContinuousMul α : Prop
#align topological_semiring TopologicalSemiring

/-- A topological ring is a ring `R` where addition, multiplication and negation are continuous.

If `R` is a (unital) ring, then continuity of negation can be derived from continuity of
multiplication as it is multiplication with `-1`. (See
`TopologicalSemiring.continuousNeg_of_mul` and
`topological_semiring.to_topological_add_group`) -/
class TopologicalRing [TopologicalSpace α] [NonUnitalNonAssocRing α] extends TopologicalSemiring α,
  ContinuousNeg α : Prop
#align topological_ring TopologicalRing

variable {α}

/-- If `R` is a ring with a continuous multiplication, then negation is continuous as well since it
is just multiplication with `-1`. -/
theorem TopologicalSemiring.continuousNeg_of_mul [TopologicalSpace α] [NonAssocRing α]
    [ContinuousMul α] : ContinuousNeg α where
  continuous_neg := by
    simpa using (continuous_const.mul continuous_id : Continuous fun x : α => -1 * x)
#align topological_semiring.has_continuous_neg_of_mul TopologicalSemiring.continuousNeg_of_mul

/-- If `R` is a ring which is a topological semiring, then it is automatically a topological
ring. This exists so that one can place a topological ring structure on `R` without explicitly
proving `continuous_neg`. -/
theorem TopologicalSemiring.toTopologicalRing [TopologicalSpace α] [NonAssocRing α]
    (_ : TopologicalSemiring α) : TopologicalRing α where
  toContinuousNeg := TopologicalSemiring.continuousNeg_of_mul
#align topological_semiring.to_topological_ring TopologicalSemiring.toTopologicalRing

-- See note [lower instance priority]
instance (priority := 100) TopologicalRing.to_topologicalAddGroup [NonUnitalNonAssocRing α]
    [TopologicalSpace α] [TopologicalRing α] : TopologicalAddGroup α := ⟨⟩
#align topological_ring.to_topological_add_group TopologicalRing.to_topologicalAddGroup

instance (priority := 50) DiscreteTopology.topologicalSemiring [TopologicalSpace α]
    [NonUnitalNonAssocSemiring α] [DiscreteTopology α] : TopologicalSemiring α := ⟨⟩
#align discrete_topology.topological_semiring DiscreteTopology.topologicalSemiring

instance (priority := 50) DiscreteTopology.topologicalRing [TopologicalSpace α]
    [NonUnitalNonAssocRing α] [DiscreteTopology α] : TopologicalRing α := ⟨⟩
#align discrete_topology.topological_ring DiscreteTopology.topologicalRing

section

variable [TopologicalSpace α] [Semiring α] [TopologicalSemiring α]

instance : TopologicalSemiring (ULift α) where

namespace Subsemiring

-- Porting note: named instance because generated name was huge
instance topologicalSemiring (S : Subsemiring α) : TopologicalSemiring S :=
  { S.toSubmonoid.continuousMul, S.toAddSubmonoid.continuousAdd with }

end Subsemiring

/-- The (topological-space) closure of a subsemiring of a topological semiring is
itself a subsemiring. -/
def Subsemiring.topologicalClosure (s : Subsemiring α) : Subsemiring α :=
  { s.toSubmonoid.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set α) }
#align subsemiring.topological_closure Subsemiring.topologicalClosure

@[simp]
theorem Subsemiring.topologicalClosure_coe (s : Subsemiring α) :
    (s.topologicalClosure : Set α) = _root_.closure (s : Set α) :=
  rfl
#align subsemiring.topological_closure_coe Subsemiring.topologicalClosure_coe

theorem Subsemiring.le_topologicalClosure (s : Subsemiring α) : s ≤ s.topologicalClosure :=
  _root_.subset_closure
#align subsemiring.le_topological_closure Subsemiring.le_topologicalClosure

theorem Subsemiring.isClosed_topologicalClosure (s : Subsemiring α) :
    IsClosed (s.topologicalClosure : Set α) := isClosed_closure
#align subsemiring.is_closed_topological_closure Subsemiring.isClosed_topologicalClosure

theorem Subsemiring.topologicalClosure_minimal (s : Subsemiring α) {t : Subsemiring α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align subsemiring.topological_closure_minimal Subsemiring.topologicalClosure_minimal

/-- If a subsemiring of a topological semiring is commutative, then so is its
topological closure. -/
def Subsemiring.commSemiringTopologicalClosure [T2Space α] (s : Subsemiring α)
    (hs : ∀ x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }
#align subsemiring.comm_semiring_topological_closure Subsemiring.commSemiringTopologicalClosure

end

section

variable {β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- The product topology on the cartesian product of two topological semirings
  makes the product into a topological semiring. -/
instance [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [TopologicalSemiring α]
    [TopologicalSemiring β] : TopologicalSemiring (α × β) where

/-- The product topology on the cartesian product of two topological rings
  makes the product into a topological ring. -/
instance [NonUnitalNonAssocRing α] [NonUnitalNonAssocRing β] [TopologicalRing α]
    [TopologicalRing β] : TopologicalRing (α × β) where

end

#adaptation_note /-- nightly-2024-04-08, needed to help `Pi.instTopologicalSemiring` -/
instance {β : Type*} {C : β → Type*} [∀ b, TopologicalSpace (C b)]
    [∀ b, NonUnitalNonAssocSemiring (C b)] [∀ b, TopologicalSemiring (C b)] :
    ContinuousAdd ((b : β) → C b) :=
  inferInstance

instance Pi.instTopologicalSemiring {β : Type*} {C : β → Type*} [∀ b, TopologicalSpace (C b)]
    [∀ b, NonUnitalNonAssocSemiring (C b)] [∀ b, TopologicalSemiring (C b)] :
    TopologicalSemiring (∀ b, C b) where
#align pi.topological_semiring Pi.instTopologicalSemiring

instance Pi.instTopologicalRing {β : Type*} {C : β → Type*} [∀ b, TopologicalSpace (C b)]
    [∀ b, NonUnitalNonAssocRing (C b)] [∀ b, TopologicalRing (C b)] :
    TopologicalRing (∀ b, C b) := ⟨⟩
#align pi.topological_ring Pi.instTopologicalRing

section MulOpposite

open MulOpposite

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [ContinuousAdd α] :
    ContinuousAdd αᵐᵒᵖ :=
  continuousAdd_induced opAddEquiv.symm

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [TopologicalSemiring α] :
    TopologicalSemiring αᵐᵒᵖ := ⟨⟩

instance [NonUnitalNonAssocRing α] [TopologicalSpace α] [ContinuousNeg α] : ContinuousNeg αᵐᵒᵖ :=
  opHomeomorph.symm.inducing.continuousNeg fun _ => rfl

instance [NonUnitalNonAssocRing α] [TopologicalSpace α] [TopologicalRing α] :
    TopologicalRing αᵐᵒᵖ := ⟨⟩

end MulOpposite

section AddOpposite

open AddOpposite

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [ContinuousMul α] :
    ContinuousMul αᵃᵒᵖ :=
  continuousMul_induced opMulEquiv.symm

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [TopologicalSemiring α] :
    TopologicalSemiring αᵃᵒᵖ := ⟨⟩

instance [NonUnitalNonAssocRing α] [TopologicalSpace α] [TopologicalRing α] :
    TopologicalRing αᵃᵒᵖ := ⟨⟩

end AddOpposite

section

variable {R : Type*} [NonUnitalNonAssocRing R] [TopologicalSpace R]

theorem TopologicalRing.of_addGroup_of_nhds_zero [TopologicalAddGroup R]
    (hmul : Tendsto (uncurry ((· * ·) : R → R → R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0)
    (hmul_left : ∀ x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0)
    (hmul_right : ∀ x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0) : TopologicalRing R where
  continuous_mul := by
    refine continuous_of_continuousAt_zero₂ (AddMonoidHom.mul (R := R)) ?_ ?_ ?_ <;>
      simpa only [ContinuousAt, mul_zero, zero_mul, nhds_prod_eq, AddMonoidHom.mul_apply]
#align topological_ring.of_add_group_of_nhds_zero TopologicalRing.of_addGroup_of_nhds_zero

theorem TopologicalRing.of_nhds_zero
    (hadd : Tendsto (uncurry ((· + ·) : R → R → R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0)
    (hneg : Tendsto (fun x => -x : R → R) (𝓝 0) (𝓝 0))
    (hmul : Tendsto (uncurry ((· * ·) : R → R → R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0)
    (hmul_left : ∀ x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0)
    (hmul_right : ∀ x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0)
    (hleft : ∀ x₀ : R, 𝓝 x₀ = map (fun x => x₀ + x) (𝓝 0)) : TopologicalRing R :=
  have := TopologicalAddGroup.of_comm_of_nhds_zero hadd hneg hleft
  TopologicalRing.of_addGroup_of_nhds_zero hmul hmul_left hmul_right
#align topological_ring.of_nhds_zero TopologicalRing.of_nhds_zero

end

variable [TopologicalSpace α]

section

variable [NonUnitalNonAssocRing α] [TopologicalRing α]

instance : TopologicalRing (ULift α) where

/-- In a topological semiring, the left-multiplication `AddMonoidHom` is continuous. -/
theorem mulLeft_continuous (x : α) : Continuous (AddMonoidHom.mulLeft x) :=
  continuous_const.mul continuous_id
#align mul_left_continuous mulLeft_continuous

/-- In a topological semiring, the right-multiplication `AddMonoidHom` is continuous. -/
theorem mulRight_continuous (x : α) : Continuous (AddMonoidHom.mulRight x) :=
  continuous_id.mul continuous_const
#align mul_right_continuous mulRight_continuous

end

variable [Ring α] [TopologicalRing α]

instance Subring.instTopologicalRing (S : Subring α) : TopologicalRing S :=
  { S.toSubmonoid.continuousMul, inferInstanceAs (TopologicalAddGroup S.toAddSubgroup) with }

/-- The (topological-space) closure of a subring of a topological ring is
itself a subring. -/
def Subring.topologicalClosure (S : Subring α) : Subring α :=
  { S.toSubmonoid.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := _root_.closure (S : Set α) }
#align subring.topological_closure Subring.topologicalClosure

theorem Subring.le_topologicalClosure (s : Subring α) : s ≤ s.topologicalClosure :=
  _root_.subset_closure
#align subring.le_topological_closure Subring.le_topologicalClosure

theorem Subring.isClosed_topologicalClosure (s : Subring α) :
    IsClosed (s.topologicalClosure : Set α) := isClosed_closure
#align subring.is_closed_topological_closure Subring.isClosed_topologicalClosure

theorem Subring.topologicalClosure_minimal (s : Subring α) {t : Subring α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align subring.topological_closure_minimal Subring.topologicalClosure_minimal

/-- If a subring of a topological ring is commutative, then so is its topological closure. -/
def Subring.commRingTopologicalClosure [T2Space α] (s : Subring α) (hs : ∀ x y : s, x * y = y * x) :
    CommRing s.topologicalClosure :=
  { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }
#align subring.comm_ring_topological_closure Subring.commRingTopologicalClosure

end TopologicalSemiring

/-!
### Lattice of ring topologies
We define a type class `RingTopology α` which endows a ring `α` with a topology such that all ring
operations are continuous.

Ring topologies on a fixed ring `α` are ordered, by reverse inclusion. They form a complete lattice,
with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : α → β` induces `coinduced f : TopologicalSpace α → RingTopology β`. -/


universe u v

/-- A ring topology on a ring `α` is a topology for which addition, negation and multiplication
are continuous. -/
structure RingTopology (α : Type u) [Ring α] extends TopologicalSpace α, TopologicalRing α : Type u
#align ring_topology RingTopology

namespace RingTopology

variable {α : Type*} [Ring α]

instance inhabited {α : Type u} [Ring α] : Inhabited (RingTopology α) :=
  ⟨let _ : TopologicalSpace α := ⊤;
    { continuous_add := continuous_top
      continuous_mul := continuous_top
      continuous_neg := continuous_top }⟩
#align ring_topology.inhabited RingTopology.inhabited

theorem toTopologicalSpace_injective :
    Injective (toTopologicalSpace : RingTopology α → TopologicalSpace α) := by
  intro f g _; cases f; cases g; congr

@[ext]
theorem ext {f g : RingTopology α} (h : f.IsOpen = g.IsOpen) : f = g :=
  toTopologicalSpace_injective <| TopologicalSpace.ext h
#align ring_topology.ext' RingTopology.ext

/-- The ordering on ring topologies on the ring `α`.
  `t ≤ s` if every set open in `s` is also open in `t` (`t` is finer than `s`). -/
instance : PartialOrder (RingTopology α) :=
  PartialOrder.lift RingTopology.toTopologicalSpace toTopologicalSpace_injective

private def def_sInf (S : Set (RingTopology α)) : RingTopology α :=
  let _ := sInf (toTopologicalSpace '' S)
  { toContinuousAdd := continuousAdd_sInf <| forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousAdd
    toContinuousMul := continuousMul_sInf <| forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousMul
    toContinuousNeg := continuousNeg_sInf <| forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousNeg }

/-- Ring topologies on `α` form a complete lattice, with `⊥` the discrete topology and `⊤` the
indiscrete topology.

The infimum of a collection of ring topologies is the topology generated by all their open sets
(which is a ring topology).

The supremum of two ring topologies `s` and `t` is the infimum of the family of all ring topologies
contained in the intersection of `s` and `t`. -/
instance : CompleteSemilatticeInf (RingTopology α) where
  sInf := def_sInf
  sInf_le := fun _ a haS => sInf_le (α := TopologicalSpace α) ⟨a, ⟨haS, rfl⟩⟩
  le_sInf := fun _ _ h => le_sInf (α := TopologicalSpace α) <| forall_mem_image.2 h

instance : CompleteLattice (RingTopology α) :=
  completeLatticeOfCompleteSemilatticeInf _

/-- Given `f : α → β` and a topology on `α`, the coinduced ring topology on `β` is the finest
topology such that `f` is continuous and `β` is a topological ring. -/
def coinduced {α β : Type*} [t : TopologicalSpace α] [Ring β] (f : α → β) : RingTopology β :=
  sInf { b : RingTopology β | t.coinduced f ≤ b.toTopologicalSpace }
#align ring_topology.coinduced RingTopology.coinduced

theorem coinduced_continuous {α β : Type*} [t : TopologicalSpace α] [Ring β] (f : α → β) :
    Continuous[t, (coinduced f).toTopologicalSpace] f :=
  continuous_sInf_rng.2 <| forall_mem_image.2 fun _ => continuous_iff_coinduced_le.2
#align ring_topology.coinduced_continuous RingTopology.coinduced_continuous

/-- The forgetful functor from ring topologies on `a` to additive group topologies on `a`. -/
def toAddGroupTopology (t : RingTopology α) : AddGroupTopology α where
  toTopologicalSpace := t.toTopologicalSpace
  toTopologicalAddGroup :=
    @TopologicalRing.to_topologicalAddGroup _ _ t.toTopologicalSpace t.toTopologicalRing
#align ring_topology.to_add_group_topology RingTopology.toAddGroupTopology

/-- The order embedding from ring topologies on `a` to additive group topologies on `a`. -/
def toAddGroupTopology.orderEmbedding : OrderEmbedding (RingTopology α) (AddGroupTopology α) :=
  OrderEmbedding.ofMapLEIff toAddGroupTopology fun _ _ => Iff.rfl
#align ring_topology.to_add_group_topology.order_embedding RingTopology.toAddGroupTopology.orderEmbedding

end RingTopology

section AbsoluteValue

/-- Construct an absolute value on a semiring `T` from an absolute value on a semiring `R`
and an injective ring homomorphism `f : T →+* R` -/
def AbsoluteValue.comp {R S T : Type*} [Semiring T] [Semiring R] [OrderedSemiring S]
    (v : AbsoluteValue R S) {f : T →+* R} (hf : Function.Injective f) : AbsoluteValue T S where
  toMulHom := v.1.comp f
  nonneg' _ := v.nonneg _
  eq_zero' _ := v.eq_zero.trans (map_eq_zero_iff f hf)
  add_le' _ _ := (congr_arg v (map_add f _ _)).trans_le (v.add_le _ _)
#align absolute_value.comp AbsoluteValue.comp

end AbsoluteValue
