import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.NonUnitalSubalgebra
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.FieldTheory.Subfield
import Mathlib.Tactic.SetLike.Macro
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.StarSubalgebra

set_option autoImplicit true

/-
This file is not intended for inclusion in the final form of the PR. Rather, these
lemmas would be added and/or marked with the appropriate attribute where they appear
in the library. They are only included here in order to determine whether this is a
good approach and to make testing easier.
-/

lemma ofNat_mem [AddMonoidWithOne R] [SetLike S R] [AddSubmonoidWithOneClass S R]
    (s : S) (n : ℕ) [n.AtLeastTwo] :
    no_index (OfNat.ofNat n) ∈ s := by
  rw [←Nat.cast_eq_ofNat]; exact natCast_mem s n

lemma ofScientific_mem [Field F] [SetLike S F] [SubfieldClass S F] (s : S) (b : Bool) (n m : ℕ) :
    (OfScientific.ofScientific n b m : F) ∈ s :=
  SubfieldClass.coe_rat_mem ..

-- general lemmas for `SetLike` classes
attribute [set_like]
  -- Mathlib.GroupTheory.Submonoid.Basic
  one_mem
  zero_mem
  pow_mem
  nsmul_mem
  -- Mathlib.GroupTheory.Subsemigroup.Basic
  mul_mem
  add_mem
  -- Mathlib.GroupTheory.Subgroup.Basic
  neg_mem
  sub_mem
  zpow_mem
  div_mem
  inv_mem
  zsmul_mem
  -- Mathlib.Algebra.Star.Basic
  star_mem
  -- Mathlib.Algebra.Algebra.Subalgebra.Basic
  algebraMap_mem
  -- Mathlib.RingTheory.Subsemiring.Basic
  natCast_mem
  ofNat_mem
  -- Mathlib.RingTheory.Subring.Basic
  coe_int_mem
  -- Mathlib.FieldTheory.Subfield
  ofScientific_mem
  SubfieldClass.coe_rat_mem
  SubfieldClass.rat_smul_mem

-- specific lemmas for `SetLike` classes
attribute [set_like]
  ConvexCone.smul_mem
  -- Mathlib.Analysis.Convex.Cone.Basic
  skewAdjoint.smul_mem
  -- Mathlib.Algebra.Star.SelfAdjoint


-- we want `nsmul_mem` and `zsmul_mem` to trigger before this
attribute [set_like 10] SMulMemClass.smul_mem

example [Ring R] (S : Subring R) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (n m : ℕ) :
    n • x ^ 3 - 2 • y + z ^ m ∈ S := by
  set_like

-- These lemmas need to exist so that the `set_like` tactic can apply them
-- Mathlib.GroupTheory.Subsemigroup.Basic
@[to_additive]
lemma Subsemigroup.mem_closure_of_mem {M : Type*} [Mul M] {s : Set M} {x : M} (hx : x ∈ s) :
    x ∈ Subsemigroup.closure s :=
  Subsemigroup.subset_closure hx
-- Mathlib.GroupTheory.Submonoid.Basic
@[to_additive]
lemma Submonoid.mem_closure_of_mem {M : Type*} [MulOneClass M] {s : Set M} {x : M} (hx : x ∈ s) :
    x ∈ Submonoid.closure s :=
  Submonoid.subset_closure hx
-- Mathlib.GroupTheory.Subgroup.Basic
@[to_additive]
lemma Subgroup.mem_closure_of_mem {G : Type*} [Group G] {k : Set G} {x : G} (hx : x ∈ k) :
    x ∈ Subgroup.closure k :=
  Subgroup.subset_closure hx
-- Mathlib.LinearAlgebra.Span
lemma Submodule.mem_span_of_mem {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {s : Set M} {x : M} (hx : x ∈ s) : x ∈ Submodule.span R s :=
  Submodule.subset_span hx
-- Mathlib.RingTheory.Subring.Basic
lemma Subring.mem_closure_of_mem {R : Type*} [Ring R] {s : Set R} {x : R} (hx : x ∈ s) :
    x ∈ Subring.closure s :=
  Subring.subset_closure hx
-- Mathlib.RingTheory.Subsemiring.Basic
lemma Subsemiring.mem_closure_of_mem {R : Type*} [NonAssocSemiring R] {s : Set R} {x : R}
    (hx : x ∈ s) : x ∈ Subsemiring.closure s :=
  Subsemiring.subset_closure hx
-- Mathlib.RingTheory.Adjoin.Basic
lemma Algebra.mem_adjoin_of_mem {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {s : Set A} {x : A} (hx : x ∈ s) : x ∈ Algebra.adjoin R s :=
  Algebra.subset_adjoin hx
-- Mathlib.Algebra.Star.Subalgebra
lemma StarSubalgebra.mem_adjoin_of_mem (R : Type*) {A : Type*} [CommSemiring R] [StarRing R]
    [Semiring A] [Algebra R A] [StarRing A] [StarModule R A] (s : Set A) {x : A} (hx : x ∈ s) :
    x ∈ StarSubalgebra.adjoin R s :=
  StarSubalgebra.subset_adjoin R s hx
-- Mathlib.RingTheory.NonUnitalSubsemiring.Basic
lemma NonUnitalSubsemiring.mem_closure_of_mem {R : Type*} [NonUnitalNonAssocSemiring R] {s : Set R}
    {x : R} (hx : x ∈ s) : x ∈ NonUnitalSubsemiring.closure s :=
  NonUnitalSubsemiring.subset_closure hx
-- Mathlib.RingTheory.NonUnitalSubring.Basic
lemma NonUnitalSubring.mem_closure_of_mem {R : Type*} [NonUnitalNonAssocRing R] {s : Set R}
    {x : R} (hx : x ∈ s) : x ∈ NonUnitalSubring.closure s :=
  NonUnitalSubring.subset_closure hx
-- Mathlib.Algebra.Algebra.Subalgebra
lemma NonUnitalAlgebra.mem_adjoin_of_mem (R : Type*) {A : Type*} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    {s : Set A} {x : A} (hx : x ∈ s) : x ∈ NonUnitalAlgebra.adjoin R s :=
  NonUnitalAlgebra.subset_adjoin R hx
-- Mathlib.Algebra.Star.NonUnitalSubalgebra
lemma NonUnitalStarAlgebra.mem_adjoin_of_mem (R : Type*) {A : Type*} [CommSemiring R] [StarRing R]
    [NonUnitalSemiring A] [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [StarModule R A] (s : Set A) {x : A} (hx : x ∈ s) : x ∈ NonUnitalStarAlgebra.adjoin R s :=
  NonUnitalStarAlgebra.subset_adjoin R s hx
-- Mathlib.FieldTheory.Subfield
theorem Subfield.mem_closure_of_mem {K : Type*} [Field K] {s : Set K} {x : K} (hx : x ∈ s) :
    x ∈ Subfield.closure s :=
  Subfield.subset_closure hx

attribute [set_like 20]
  Subsemigroup.mem_closure_of_mem
  Submonoid.mem_closure_of_mem
  Subgroup.mem_closure_of_mem
  AddSubsemigroup.mem_closure_of_mem
  AddSubmonoid.mem_closure_of_mem
  AddSubgroup.mem_closure_of_mem
  Submodule.mem_span_of_mem
  Subring.mem_closure_of_mem
  Subsemiring.mem_closure_of_mem
  Algebra.mem_adjoin_of_mem
  StarSubalgebra.mem_adjoin_of_mem
  NonUnitalSubsemiring.mem_closure_of_mem
  NonUnitalSubring.mem_closure_of_mem
  NonUnitalAlgebra.mem_adjoin_of_mem
  NonUnitalStarAlgebra.mem_adjoin_of_mem
  Subfield.mem_closure_of_mem
  -- specific lemmas
  -- Mathlib.Topology.Algebra.Algebra
  Algebra.self_mem_elementalAlgebra
  -- Mathlib.Topology.Algebra.StarSubalgebra
  elementalStarAlgebra.self_mem

example [Ring R] (S : Set R) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (n m : ℕ) :
    n • x ^ 3 - y + z ^ m ∈ Subring.closure S := by
  set_like

-- this instance is currently missing
instance StarSubalgebra.smulMemClass [CommSemiring R] [Semiring A] [Algebra R A] [StarRing R]
  [StarRing A] [StarModule R A] : SMulMemClass (StarSubalgebra R A) R A where
  smul_mem {s} r a (ha : a ∈ s.toSubalgebra) :=
    (SMulMemClass.smul_mem r ha : r • a ∈ s.toSubalgebra)

example [CommRing R] [Ring A] [Algebra R A] [StarRing R] [StarRing A] [StarModule R A]
    (r : R) (a b c : A) (n : ℕ) :
    -b + star (algebraMap R A r) + a ^ n * c ∈ StarSubalgebra.adjoin R {a, b, c} := by
  set_like?

example [Monoid M] (x : M) (n : ℕ) : x ^ n ∈ Submonoid.closure {x} := by
  set_like

example [Monoid M] (x y z w : M) (n : ℕ) : (x * y) ^ n * w ∈ Submonoid.closure {x, y, z, w} := by
  set_like

example [Group M] (x : M) (n : ℤ) : x ^ n ∈ Subgroup.closure {x} := by
  set_like

example [Monoid M] (x y z : M) (S₁ S₂ : Submonoid M) (h : S₁ ≤ S₂) (hx : x ∈ S₁)
    (hy : y ∈ S₁) (hz : z ∈ S₂) :
    x * y * z ∈ S₂ := by
  set_like

example [Monoid M] (x y z : M) (S₁ S₂ : Submonoid M) (h : S₁ ≤ S₂) (hx : x ∈ S₁)
    (hy : y ∈ S₁) (hz : z ∈ S₂) :
    x * y * z ∈ S₁ ⊔ S₂ := by
  set_like

example [Monoid M] (x y z : M) (S : Submonoid M) (hxy : x * y ∈ S)  (hz : z ∈ S) :
    z * (x * y) ∈ S := by
  set_like

example [Field F] (S : Subfield F) (q : ℚ) : (q : F) ∈ S := by
  set_like

example [Field F] (S : Subfield F) : (1.2 : F) ∈ S := by
  set_like

example [Field F] (S : Subfield F) (x : F) (hx : x ∈ S) : ((12e-100 : F) • x⁻¹) ∈ S := by
  set_like
