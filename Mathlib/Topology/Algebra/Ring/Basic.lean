/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Topology.Algebra.Group.GroupTopology

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

variable (R : Type*)

/-- a topological semiring is a semiring `R` where addition and multiplication are continuous.
We allow for non-unital and non-associative semirings as well.

The `IsTopologicalSemiring` class should *only* be instantiated in the presence of a
`NonUnitalNonAssocSemiring` instance; if there is an instance of `NonUnitalNonAssocRing`,
then `IsTopologicalRing` should be used. Note: in the presence of `NonAssocRing`, these classes are
mathematically equivalent (see `IsTopologicalSemiring.continuousNeg_of_mul` or
`IsTopologicalSemiring.toIsTopologicalRing`). -/
class IsTopologicalSemiring [TopologicalSpace R] [NonUnitalNonAssocSemiring R] : Prop
    extends ContinuousAdd R, ContinuousMul R

/-- A topological ring is a ring `R` where addition, multiplication and negation are continuous.

If `R` is a (unital) ring, then continuity of negation can be derived from continuity of
multiplication as it is multiplication with `-1`. (See
`IsTopologicalSemiring.continuousNeg_of_mul` and
`topological_semiring.to_topological_add_group`) -/
class IsTopologicalRing [TopologicalSpace R] [NonUnitalNonAssocRing R] : Prop
    extends IsTopologicalSemiring R, ContinuousNeg R

variable {R}

/-- If `R` is a ring with a continuous multiplication, then negation is continuous as well since it
is just multiplication with `-1`. -/
theorem IsTopologicalSemiring.continuousNeg_of_mul [TopologicalSpace R] [NonAssocRing R]
    [ContinuousMul R] : ContinuousNeg R where
  continuous_neg := by
    simpa using (continuous_const.mul continuous_id : Continuous fun x : R => -1 * x)

/-- If `R` is a ring which is a topological semiring, then it is automatically a topological
ring. This exists so that one can place a topological ring structure on `R` without explicitly
proving `continuous_neg`. -/
theorem IsTopologicalSemiring.toIsTopologicalRing [TopologicalSpace R] [NonAssocRing R]
    (_ : IsTopologicalSemiring R) : IsTopologicalRing R where
  toContinuousNeg := IsTopologicalSemiring.continuousNeg_of_mul

-- See note [lower instance priority]
instance (priority := 100) IsTopologicalRing.to_topologicalAddGroup [NonUnitalNonAssocRing R]
    [TopologicalSpace R] [IsTopologicalRing R] : IsTopologicalAddGroup R := ⟨⟩

instance (priority := 50) DiscreteTopology.topologicalSemiring [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [DiscreteTopology R] : IsTopologicalSemiring R := ⟨⟩

instance (priority := 50) DiscreteTopology.topologicalRing [TopologicalSpace R]
    [NonUnitalNonAssocRing R] [DiscreteTopology R] : IsTopologicalRing R := ⟨⟩

section

namespace NonUnitalSubsemiring

variable [TopologicalSpace R] [NonUnitalSemiring R] [IsTopologicalSemiring R]

instance instIsTopologicalSemiring (S : NonUnitalSubsemiring R) : IsTopologicalSemiring S :=
  { S.toSubsemigroup.continuousMul, S.toAddSubmonoid.continuousAdd with }

/-- The (topological) closure of a non-unital subsemiring of a non-unital topological semiring is
itself a non-unital subsemiring. -/
def topologicalClosure (s : NonUnitalSubsemiring R) : NonUnitalSubsemiring R :=
  { s.toSubsemigroup.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set R) }

@[simp]
theorem topologicalClosure_coe (s : NonUnitalSubsemiring R) :
    (s.topologicalClosure : Set R) = _root_.closure (s : Set R) :=
  rfl

theorem le_topologicalClosure (s : NonUnitalSubsemiring R) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem isClosed_topologicalClosure (s : NonUnitalSubsemiring R) :
    IsClosed (s.topologicalClosure : Set R) := isClosed_closure

theorem topologicalClosure_minimal (s : NonUnitalSubsemiring R) {t : NonUnitalSubsemiring R}
    (h : s ≤ t) (ht : IsClosed (t : Set R)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

/-- If a non-unital subsemiring of a non-unital topological semiring is commutative, then so is its
topological closure.

See note [reducible non-instances] -/
abbrev nonUnitalCommSemiringTopologicalClosure [T2Space R] (s : NonUnitalSubsemiring R)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommSemiring s.topologicalClosure :=
  { NonUnitalSubsemiringClass.toNonUnitalSemiring s.topologicalClosure,
    s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end NonUnitalSubsemiring

variable [TopologicalSpace R] [Semiring R] [IsTopologicalSemiring R]

instance : IsTopologicalSemiring (ULift R) where

namespace Subsemiring

instance topologicalSemiring (S : Subsemiring R) : IsTopologicalSemiring S :=
  { S.toSubmonoid.continuousMul, S.toAddSubmonoid.continuousAdd with }

instance continuousSMul (s : Subsemiring R) (X) [TopologicalSpace X] [MulAction R X]
    [ContinuousSMul R X] : ContinuousSMul s X :=
  Submonoid.continuousSMul

end Subsemiring

/-- The (topological-space) closure of a subsemiring of a topological semiring is
itself a subsemiring. -/
def Subsemiring.topologicalClosure (s : Subsemiring R) : Subsemiring R :=
  { s.toSubmonoid.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set R) }

@[simp]
theorem Subsemiring.topologicalClosure_coe (s : Subsemiring R) :
    (s.topologicalClosure : Set R) = _root_.closure (s : Set R) :=
  rfl

theorem Subsemiring.le_topologicalClosure (s : Subsemiring R) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem Subsemiring.isClosed_topologicalClosure (s : Subsemiring R) :
    IsClosed (s.topologicalClosure : Set R) := isClosed_closure

theorem Subsemiring.topologicalClosure_minimal (s : Subsemiring R) {t : Subsemiring R} (h : s ≤ t)
    (ht : IsClosed (t : Set R)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

/-- If a subsemiring of a topological semiring is commutative, then so is its
topological closure.

See note [reducible non-instances]. -/
abbrev Subsemiring.commSemiringTopologicalClosure [T2Space R] (s : Subsemiring R)
    (hs : ∀ x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }

end

section

variable {S : Type*} [TopologicalSpace R] [TopologicalSpace S]

/-- The product topology on the Cartesian product of two topological semirings
  makes the product into a topological semiring. -/
instance [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [IsTopologicalSemiring R]
    [IsTopologicalSemiring S] : IsTopologicalSemiring (R × S) where

/-- The product topology on the Cartesian product of two topological rings
  makes the product into a topological ring. -/
instance [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [IsTopologicalRing R]
    [IsTopologicalRing S] : IsTopologicalRing (R × S) where

end

#adaptation_note /-- nightly-2024-04-08
needed to help `Pi.instIsTopologicalSemiring` -/
instance {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
    [∀ i, NonUnitalNonAssocSemiring (R i)] [∀ i, IsTopologicalSemiring (R i)] :
    ContinuousAdd ((i : ι) → R i) :=
  inferInstance

instance Pi.instIsTopologicalSemiring {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
    [∀ i, NonUnitalNonAssocSemiring (R i)] [∀ i, IsTopologicalSemiring (R i)] :
    IsTopologicalSemiring (∀ i, R i) where

instance Pi.instIsTopologicalRing {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
    [∀ i, NonUnitalNonAssocRing (R i)] [∀ i, IsTopologicalRing (R i)] :
    IsTopologicalRing (∀ i, R i) := ⟨⟩

section MulOpposite

open MulOpposite

instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [ContinuousAdd R] :
    ContinuousAdd Rᵐᵒᵖ :=
  continuousAdd_induced opAddEquiv.symm

instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring Rᵐᵒᵖ := ⟨⟩

instance [NonUnitalNonAssocRing R] [TopologicalSpace R] [ContinuousNeg R] : ContinuousNeg Rᵐᵒᵖ :=
  opHomeomorph.symm.isInducing.continuousNeg fun _ => rfl

instance [NonUnitalNonAssocRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsTopologicalRing Rᵐᵒᵖ := ⟨⟩

end MulOpposite

section AddOpposite

open AddOpposite

instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [ContinuousMul R] :
    ContinuousMul Rᵃᵒᵖ :=
  continuousMul_induced opMulEquiv.symm

instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring Rᵃᵒᵖ := ⟨⟩

instance [NonUnitalNonAssocRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsTopologicalRing Rᵃᵒᵖ := ⟨⟩

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

variable [TopologicalSpace R]

section

variable [NonUnitalNonAssocRing R] [IsTopologicalRing R]

instance : IsTopologicalRing (ULift R) where

/-- In a topological semiring, the left-multiplication `AddMonoidHom` is continuous. -/
theorem mulLeft_continuous (x : R) : Continuous (AddMonoidHom.mulLeft x) :=
  continuous_const.mul continuous_id

/-- In a topological semiring, the right-multiplication `AddMonoidHom` is continuous. -/
theorem mulRight_continuous (x : R) : Continuous (AddMonoidHom.mulRight x) :=
  continuous_id.mul continuous_const

end

namespace NonUnitalSubring

variable [NonUnitalRing R] [IsTopologicalRing R]

instance instIsTopologicalRing (S : NonUnitalSubring R) : IsTopologicalRing S :=
  { S.toSubsemigroup.continuousMul, inferInstanceAs (IsTopologicalAddGroup S.toAddSubgroup) with }

/-- The (topological) closure of a non-unital subring of a non-unital topological ring is
itself a non-unital subring. -/
def topologicalClosure (S : NonUnitalSubring R) : NonUnitalSubring R :=
  { S.toSubsemigroup.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := _root_.closure (S : Set R) }

theorem le_topologicalClosure (s : NonUnitalSubring R) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem isClosed_topologicalClosure (s : NonUnitalSubring R) :
    IsClosed (s.topologicalClosure : Set R) := isClosed_closure

theorem topologicalClosure_minimal (s : NonUnitalSubring R) {t : NonUnitalSubring R} (h : s ≤ t)
    (ht : IsClosed (t : Set R)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

/-- If a non-unital subring of a non-unital topological ring is commutative, then so is its
topological closure.

See note [reducible non-instances] -/
abbrev nonUnitalCommRingTopologicalClosure [T2Space R] (s : NonUnitalSubring R)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommRing s.topologicalClosure :=
  { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end NonUnitalSubring

variable [Ring R] [IsTopologicalRing R]

instance Subring.instIsTopologicalRing (S : Subring R) : IsTopologicalRing S :=
  { S.toSubmonoid.continuousMul, inferInstanceAs (IsTopologicalAddGroup S.toAddSubgroup) with }

instance Subring.continuousSMul (s : Subring R) (X) [TopologicalSpace X] [MulAction R X]
    [ContinuousSMul R X] : ContinuousSMul s X :=
  Subsemiring.continuousSMul s.toSubsemiring X

/-- The (topological-space) closure of a subring of a topological ring is
itself a subring. -/
def Subring.topologicalClosure (S : Subring R) : Subring R :=
  { S.toSubmonoid.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := _root_.closure (S : Set R) }

theorem Subring.le_topologicalClosure (s : Subring R) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem Subring.isClosed_topologicalClosure (s : Subring R) :
    IsClosed (s.topologicalClosure : Set R) := isClosed_closure

theorem Subring.topologicalClosure_minimal (s : Subring R) {t : Subring R} (h : s ≤ t)
    (ht : IsClosed (t : Set R)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

/-- If a subring of a topological ring is commutative, then so is its topological closure.

See note [reducible non-instances]. -/
abbrev Subring.commRingTopologicalClosure [T2Space R] (s : Subring R)
    (hs : ∀ x y : s, x * y = y * x) : CommRing s.topologicalClosure :=
  { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }

end IsTopologicalSemiring

/-!
### Lattice of ring topologies
We define a type class `RingTopology R` which endows a ring `R` with a topology such that all ring
operations are continuous.

Ring topologies on a fixed ring `R` are ordered, by reverse inclusion. They form a complete lattice,
with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : R → S` induces `coinduced f : TopologicalSpace R → RingTopology S`. -/


universe u v

/-- A ring topology on a ring `R` is a topology for which addition, negation and multiplication
are continuous. -/
structure RingTopology (R : Type u) [Ring R] : Type u
  extends TopologicalSpace R, IsTopologicalRing R

namespace RingTopology

variable {R : Type*} [Ring R]

instance inhabited {R : Type u} [Ring R] : Inhabited (RingTopology R) :=
  ⟨let _ : TopologicalSpace R := ⊤;
    { continuous_add := continuous_top
      continuous_mul := continuous_top
      continuous_neg := continuous_top }⟩

theorem toTopologicalSpace_injective :
    Injective (toTopologicalSpace : RingTopology R → TopologicalSpace R) := by
  intro f g _; cases f; cases g; congr

@[ext]
theorem ext {f g : RingTopology R} (h : f.IsOpen = g.IsOpen) : f = g :=
  toTopologicalSpace_injective <| TopologicalSpace.ext h

/-- The ordering on ring topologies on the ring `R`.
  `t ≤ s` if every set open in `s` is also open in `t` (`t` is finer than `s`). -/
instance : PartialOrder (RingTopology R) :=
  PartialOrder.lift RingTopology.toTopologicalSpace toTopologicalSpace_injective

private def def_sInf (S : Set (RingTopology R)) : RingTopology R :=
  let _ := sInf (toTopologicalSpace '' S)
  { toContinuousAdd := continuousAdd_sInf <| forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousAdd
    toContinuousMul := continuousMul_sInf <| forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousMul
    toContinuousNeg := continuousNeg_sInf <| forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousNeg }

/-- Ring topologies on `R` form a complete lattice, with `⊥` the discrete topology and `⊤` the
indiscrete topology.

The infimum of a collection of ring topologies is the topology generated by all their open sets
(which is a ring topology).

The supremum of two ring topologies `s` and `t` is the infimum of the family of all ring topologies
contained in the intersection of `s` and `t`. -/
instance : CompleteSemilatticeInf (RingTopology R) where
  sInf := def_sInf
  sInf_le := fun _ a haS => sInf_le (α := TopologicalSpace R) ⟨a, ⟨haS, rfl⟩⟩
  le_sInf := fun _ _ h => le_sInf (α := TopologicalSpace R) <| forall_mem_image.2 h

instance : CompleteLattice (RingTopology R) :=
  completeLatticeOfCompleteSemilatticeInf _

/-- Given `f : R → S` and a topology on `R`, the coinduced ring topology on `S` is the finest
topology such that `f` is continuous and `S` is a topological ring. -/
def coinduced {R S : Type*} [t : TopologicalSpace R] [Ring S] (f : R → S) : RingTopology S :=
  sInf { b : RingTopology S | t.coinduced f ≤ b.toTopologicalSpace }

theorem coinduced_continuous {R S : Type*} [t : TopologicalSpace R] [Ring S] (f : R → S) :
    Continuous[t, (coinduced f).toTopologicalSpace] f :=
  continuous_sInf_rng.2 <| forall_mem_image.2 fun _ => continuous_iff_coinduced_le.2

/-- The forgetful functor from ring topologies on `a` to additive group topologies on `a`. -/
def toAddGroupTopology (t : RingTopology R) : AddGroupTopology R where
  toTopologicalSpace := t.toTopologicalSpace
  toIsTopologicalAddGroup :=
    @IsTopologicalRing.to_topologicalAddGroup _ _ t.toTopologicalSpace t.toIsTopologicalRing

/-- The order embedding from ring topologies on `a` to additive group topologies on `a`. -/
def toAddGroupTopology.orderEmbedding : OrderEmbedding (RingTopology R) (AddGroupTopology R) :=
  OrderEmbedding.ofMapLEIff toAddGroupTopology fun _ _ => Iff.rfl

end RingTopology

section AbsoluteValue

/-- Construct an absolute value on a semiring `T` from an absolute value on a semiring `R`
and an injective ring homomorphism `f : T →+* R` -/
def AbsoluteValue.comp {R S T : Type*} [Semiring T] [Semiring R] [Semiring S] [PartialOrder S]
    (v : AbsoluteValue R S) {f : T →+* R} (hf : Function.Injective f) : AbsoluteValue T S where
  toMulHom := v.1.comp f
  nonneg' _ := v.nonneg _
  eq_zero' _ := v.eq_zero.trans (map_eq_zero_iff f hf)
  add_le' _ _ := (congr_arg v (map_add f _ _)).trans_le (v.add_le _ _)

end AbsoluteValue
