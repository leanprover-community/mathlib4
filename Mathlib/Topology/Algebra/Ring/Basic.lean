/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Topology.Algebra.Group.Basic

/-!

# Topological (semi)rings

A topological (semi)ring is a (semi)ring equipped with a topology such that all operations are
continuous. Besides this definition, this file proves that the topological closure of a subring
(resp. an ideal) is a subring (resp. an ideal) and defines products and quotients
of topological (semi)rings.

## Main Results

- `Subring.topologicalClosure`/`Subsemiring.topologicalClosure`: the topological closure of a
  `Subring`/`Subsemiring` is itself a `Sub(semi)ring`.
- The product of two topological (semi)rings is a topological (semi)ring.
- The indexed product of topological (semi)rings is a topological (semi)ring.
-/

assert_not_exists Cardinal

open Set Filter TopologicalSpace Function Topology Filter

section IsTopologicalSemiring

variable (α : Type*)

/-- a topological semiring is a semiring `R` where addition and multiplication are continuous.
We allow for non-unital and non-associative semirings as well.

The `IsTopologicalSemiring` class should *only* be instantiated in the presence of a
`NonUnitalNonAssocSemiring` instance; if there is an instance of `NonUnitalNonAssocRing`,
then `IsTopologicalRing` should be used. Note: in the presence of `NonAssocRing`, these classes are
mathematically equivalent (see `IsTopologicalSemiring.continuousNeg_of_mul` or
`IsTopologicalSemiring.toIsTopologicalRing`). -/
class IsTopologicalSemiring [TopologicalSpace α] [NonUnitalNonAssocSemiring α] extends
  ContinuousAdd α, ContinuousMul α : Prop

/-- A topological ring is a ring `R` where addition, multiplication and negation are continuous.

If `R` is a (unital) ring, then continuity of negation can be derived from continuity of
multiplication as it is multiplication with `-1`. (See
`IsTopologicalSemiring.continuousNeg_of_mul` and
`topological_semiring.to_topological_add_group`) -/
class IsTopologicalRing [TopologicalSpace α] [NonUnitalNonAssocRing α]
    extends IsTopologicalSemiring α, ContinuousNeg α : Prop

variable {α}

/-- If `R` is a ring with a continuous multiplication, then negation is continuous as well since it
is just multiplication with `-1`. -/
theorem IsTopologicalSemiring.continuousNeg_of_mul [TopologicalSpace α] [NonAssocRing α]
    [ContinuousMul α] : ContinuousNeg α where
  continuous_neg := by
    simpa using (continuous_const.mul continuous_id : Continuous fun x : α => -1 * x)

/-- If `R` is a ring which is a topological semiring, then it is automatically a topological
ring. This exists so that one can place a topological ring structure on `R` without explicitly
proving `continuous_neg`. -/
theorem IsTopologicalSemiring.toIsTopologicalRing [TopologicalSpace α] [NonAssocRing α]
    (_ : IsTopologicalSemiring α) : IsTopologicalRing α where
  toContinuousNeg := IsTopologicalSemiring.continuousNeg_of_mul

-- See note [lower instance priority]
instance (priority := 100) IsTopologicalRing.to_topologicalAddGroup [NonUnitalNonAssocRing α]
    [TopologicalSpace α] [IsTopologicalRing α] : IsTopologicalAddGroup α := ⟨⟩

instance (priority := 50) DiscreteTopology.topologicalSemiring [TopologicalSpace α]
    [NonUnitalNonAssocSemiring α] [DiscreteTopology α] : IsTopologicalSemiring α := ⟨⟩

instance (priority := 50) DiscreteTopology.topologicalRing [TopologicalSpace α]
    [NonUnitalNonAssocRing α] [DiscreteTopology α] : IsTopologicalRing α := ⟨⟩

section

namespace NonUnitalSubsemiring

variable [TopologicalSpace α] [NonUnitalSemiring α] [IsTopologicalSemiring α]

instance instIsTopologicalSemiring (S : NonUnitalSubsemiring α) : IsTopologicalSemiring S :=
  { S.toSubsemigroup.continuousMul, S.toAddSubmonoid.continuousAdd with }

/-- The (topological) closure of a non-unital subsemiring of a non-unital topological semiring is
itself a non-unital subsemiring. -/
def topologicalClosure (s : NonUnitalSubsemiring α) : NonUnitalSubsemiring α :=
  { s.toSubsemigroup.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set α) }

@[simp]
theorem topologicalClosure_coe (s : NonUnitalSubsemiring α) :
    (s.topologicalClosure : Set α) = _root_.closure (s : Set α) :=
  rfl

theorem le_topologicalClosure (s : NonUnitalSubsemiring α) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem isClosed_topologicalClosure (s : NonUnitalSubsemiring α) :
    IsClosed (s.topologicalClosure : Set α) := isClosed_closure

theorem topologicalClosure_minimal (s : NonUnitalSubsemiring α) {t : NonUnitalSubsemiring α}
    (h : s ≤ t) (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

/-- If a non-unital subsemiring of a non-unital topological semiring is commutative, then so is its
topological closure.

See note [reducible non-instances] -/
abbrev nonUnitalCommSemiringTopologicalClosure [T2Space α] (s : NonUnitalSubsemiring α)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommSemiring s.topologicalClosure :=
  { NonUnitalSubsemiringClass.toNonUnitalSemiring s.topologicalClosure,
    s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end NonUnitalSubsemiring

variable [TopologicalSpace α] [Semiring α] [IsTopologicalSemiring α]

instance : IsTopologicalSemiring (ULift α) where

namespace Subsemiring

-- Porting note: named instance because generated name was huge
instance topologicalSemiring (S : Subsemiring α) : IsTopologicalSemiring S :=
  { S.toSubmonoid.continuousMul, S.toAddSubmonoid.continuousAdd with }

instance continuousSMul (s : Subsemiring α) (X) [TopologicalSpace X] [MulAction α X]
    [ContinuousSMul α X] : ContinuousSMul s X :=
  Submonoid.continuousSMul

end Subsemiring

/-- The (topological-space) closure of a subsemiring of a topological semiring is
itself a subsemiring. -/
def Subsemiring.topologicalClosure (s : Subsemiring α) : Subsemiring α :=
  { s.toSubmonoid.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set α) }

@[simp]
theorem Subsemiring.topologicalClosure_coe (s : Subsemiring α) :
    (s.topologicalClosure : Set α) = _root_.closure (s : Set α) :=
  rfl

theorem Subsemiring.le_topologicalClosure (s : Subsemiring α) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem Subsemiring.isClosed_topologicalClosure (s : Subsemiring α) :
    IsClosed (s.topologicalClosure : Set α) := isClosed_closure

theorem Subsemiring.topologicalClosure_minimal (s : Subsemiring α) {t : Subsemiring α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

/-- If a subsemiring of a topological semiring is commutative, then so is its
topological closure.

See note [reducible non-instances]. -/
abbrev Subsemiring.commSemiringTopologicalClosure [T2Space α] (s : Subsemiring α)
    (hs : ∀ x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }

end

section

variable {β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- The product topology on the cartesian product of two topological semirings
  makes the product into a topological semiring. -/
instance [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [IsTopologicalSemiring α]
    [IsTopologicalSemiring β] : IsTopologicalSemiring (α × β) where

/-- The product topology on the cartesian product of two topological rings
  makes the product into a topological ring. -/
instance [NonUnitalNonAssocRing α] [NonUnitalNonAssocRing β] [IsTopologicalRing α]
    [IsTopologicalRing β] : IsTopologicalRing (α × β) where

end

#adaptation_note /-- nightly-2024-04-08
needed to help `Pi.instIsTopologicalSemiring` -/
instance {β : Type*} {C : β → Type*} [∀ b, TopologicalSpace (C b)]
    [∀ b, NonUnitalNonAssocSemiring (C b)] [∀ b, IsTopologicalSemiring (C b)] :
    ContinuousAdd ((b : β) → C b) :=
  inferInstance

instance Pi.instIsTopologicalSemiring {β : Type*} {C : β → Type*} [∀ b, TopologicalSpace (C b)]
    [∀ b, NonUnitalNonAssocSemiring (C b)] [∀ b, IsTopologicalSemiring (C b)] :
    IsTopologicalSemiring (∀ b, C b) where

instance Pi.instIsTopologicalRing {β : Type*} {C : β → Type*} [∀ b, TopologicalSpace (C b)]
    [∀ b, NonUnitalNonAssocRing (C b)] [∀ b, IsTopologicalRing (C b)] :
    IsTopologicalRing (∀ b, C b) := ⟨⟩

section MulOpposite

open MulOpposite

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [ContinuousAdd α] :
    ContinuousAdd αᵐᵒᵖ :=
  continuousAdd_induced opAddEquiv.symm

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [IsTopologicalSemiring α] :
    IsTopologicalSemiring αᵐᵒᵖ := ⟨⟩

instance [NonUnitalNonAssocRing α] [TopologicalSpace α] [ContinuousNeg α] : ContinuousNeg αᵐᵒᵖ :=
  opHomeomorph.symm.isInducing.continuousNeg fun _ => rfl

instance [NonUnitalNonAssocRing α] [TopologicalSpace α] [IsTopologicalRing α] :
    IsTopologicalRing αᵐᵒᵖ := ⟨⟩

end MulOpposite

section AddOpposite

open AddOpposite

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [ContinuousMul α] :
    ContinuousMul αᵃᵒᵖ :=
  continuousMul_induced opMulEquiv.symm

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [IsTopologicalSemiring α] :
    IsTopologicalSemiring αᵃᵒᵖ := ⟨⟩

instance [NonUnitalNonAssocRing α] [TopologicalSpace α] [IsTopologicalRing α] :
    IsTopologicalRing αᵃᵒᵖ := ⟨⟩

end AddOpposite

section

variable {R : Type*} [NonUnitalNonAssocRing R] [TopologicalSpace R]

theorem IsTopologicalRing.of_addGroup_of_nhds_zero [IsTopologicalAddGroup R]
    (hmul : Tendsto (uncurry ((· * ·) : R → R → R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0)
    (hmul_left : ∀ x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0)
    (hmul_right : ∀ x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0) : IsTopologicalRing R where
  continuous_mul := by
    refine continuous_of_continuousAt_zero₂ (AddMonoidHom.mul (R := R)) ?_ ?_ ?_ <;>
      simpa only [ContinuousAt, mul_zero, zero_mul, nhds_prod_eq, AddMonoidHom.mul_apply]

theorem IsTopologicalRing.of_nhds_zero
    (hadd : Tendsto (uncurry ((· + ·) : R → R → R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0)
    (hneg : Tendsto (fun x => -x : R → R) (𝓝 0) (𝓝 0))
    (hmul : Tendsto (uncurry ((· * ·) : R → R → R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0)
    (hmul_left : ∀ x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0)
    (hmul_right : ∀ x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0)
    (hleft : ∀ x₀ : R, 𝓝 x₀ = map (fun x => x₀ + x) (𝓝 0)) : IsTopologicalRing R :=
  have := IsTopologicalAddGroup.of_comm_of_nhds_zero hadd hneg hleft
  IsTopologicalRing.of_addGroup_of_nhds_zero hmul hmul_left hmul_right

end

variable [TopologicalSpace α]

section

variable [NonUnitalNonAssocRing α] [IsTopologicalRing α]

instance : IsTopologicalRing (ULift α) where

/-- In a topological semiring, the left-multiplication `AddMonoidHom` is continuous. -/
theorem mulLeft_continuous (x : α) : Continuous (AddMonoidHom.mulLeft x) :=
  continuous_const.mul continuous_id

/-- In a topological semiring, the right-multiplication `AddMonoidHom` is continuous. -/
theorem mulRight_continuous (x : α) : Continuous (AddMonoidHom.mulRight x) :=
  continuous_id.mul continuous_const

end

namespace NonUnitalSubring

variable [NonUnitalRing α] [IsTopologicalRing α]

instance instIsTopologicalRing (S : NonUnitalSubring α) : IsTopologicalRing S :=
  { S.toSubsemigroup.continuousMul, inferInstanceAs (IsTopologicalAddGroup S.toAddSubgroup) with }

/-- The (topological) closure of a non-unital subring of a non-unital topological ring is
itself a non-unital subring. -/
def topologicalClosure (S : NonUnitalSubring α) : NonUnitalSubring α :=
  { S.toSubsemigroup.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := _root_.closure (S : Set α) }

theorem le_topologicalClosure (s : NonUnitalSubring α) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem isClosed_topologicalClosure (s : NonUnitalSubring α) :
    IsClosed (s.topologicalClosure : Set α) := isClosed_closure

theorem topologicalClosure_minimal (s : NonUnitalSubring α) {t : NonUnitalSubring α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

/-- If a non-unital subring of a non-unital topological ring is commutative, then so is its
topological closure.

See note [reducible non-instances] -/
abbrev nonUnitalCommRingTopologicalClosure [T2Space α] (s : NonUnitalSubring α)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommRing s.topologicalClosure :=
  { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end NonUnitalSubring

variable [Ring α] [IsTopologicalRing α]

instance Subring.instIsTopologicalRing (S : Subring α) : IsTopologicalRing S :=
  { S.toSubmonoid.continuousMul, inferInstanceAs (IsTopologicalAddGroup S.toAddSubgroup) with }

instance Subring.continuousSMul (s : Subring α) (X) [TopologicalSpace X] [MulAction α X]
    [ContinuousSMul α X] : ContinuousSMul s X :=
  Subsemiring.continuousSMul s.toSubsemiring X

/-- The (topological-space) closure of a subring of a topological ring is
itself a subring. -/
def Subring.topologicalClosure (S : Subring α) : Subring α :=
  { S.toSubmonoid.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := _root_.closure (S : Set α) }

theorem Subring.le_topologicalClosure (s : Subring α) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem Subring.isClosed_topologicalClosure (s : Subring α) :
    IsClosed (s.topologicalClosure : Set α) := isClosed_closure

theorem Subring.topologicalClosure_minimal (s : Subring α) {t : Subring α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

/-- If a subring of a topological ring is commutative, then so is its topological closure.

See note [reducible non-instances]. -/
abbrev Subring.commRingTopologicalClosure [T2Space α] (s : Subring α)
    (hs : ∀ x y : s, x * y = y * x) : CommRing s.topologicalClosure :=
  { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }

end IsTopologicalSemiring

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
structure RingTopology (α : Type u) [Ring α]
    extends TopologicalSpace α, IsTopologicalRing α : Type u

namespace RingTopology

variable {α : Type*} [Ring α]

instance inhabited {α : Type u} [Ring α] : Inhabited (RingTopology α) :=
  ⟨let _ : TopologicalSpace α := ⊤;
    { continuous_add := continuous_top
      continuous_mul := continuous_top
      continuous_neg := continuous_top }⟩

theorem toTopologicalSpace_injective :
    Injective (toTopologicalSpace : RingTopology α → TopologicalSpace α) := by
  intro f g _; cases f; cases g; congr

@[ext]
theorem ext {f g : RingTopology α} (h : f.IsOpen = g.IsOpen) : f = g :=
  toTopologicalSpace_injective <| TopologicalSpace.ext h

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

theorem coinduced_continuous {α β : Type*} [t : TopologicalSpace α] [Ring β] (f : α → β) :
    Continuous[t, (coinduced f).toTopologicalSpace] f :=
  continuous_sInf_rng.2 <| forall_mem_image.2 fun _ => continuous_iff_coinduced_le.2

/-- The forgetful functor from ring topologies on `a` to additive group topologies on `a`. -/
def toAddGroupTopology (t : RingTopology α) : AddGroupTopology α where
  toTopologicalSpace := t.toTopologicalSpace
  toIsTopologicalAddGroup :=
    @IsTopologicalRing.to_topologicalAddGroup _ _ t.toTopologicalSpace t.toIsTopologicalRing

/-- The order embedding from ring topologies on `a` to additive group topologies on `a`. -/
def toAddGroupTopology.orderEmbedding : OrderEmbedding (RingTopology α) (AddGroupTopology α) :=
  OrderEmbedding.ofMapLEIff toAddGroupTopology fun _ _ => Iff.rfl

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

end AbsoluteValue
