import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.NonUnitalSubalgebra
import Mathlib.Tactic.SetLike.Macro

set_option autoImplicit true

/-
This file is not intended for inclusion in the final form of the PR. Rather, these
lemmas would be added and/or marked with the appropriate attribute where they appear
in the library. They are only included here in order to determine whether this is a
good approach and to make testing easier.
-/

-- currently `aesop` fails to apply this lemma for explicit numerals
-- so it can't prove things like `37 ∈ S` which come up sometimes.
lemma ofNat_mem [Ring R] (S : Subring R) (n : ℕ) [n.AtLeastTwo] :
    OfNat.ofNat (α := R) n ∈ S := by
  rw [←Nat.cast_eq_ofNat]; exact natCast_mem S n

attribute [set_like]
  zero_mem
  one_mem
  add_mem
  neg_mem
  sub_mem
  star_mem
  algebraMap_mem
  nsmul_mem
  zsmul_mem
  pow_mem
  natCast_mem
  coe_int_mem
  ofNat_mem

-- we wan `nsmul_mem` and `zsmul_mem` to trigger before these
attribute [aesop safe 2 apply (rule_sets [SetLike])] SMulMemClass.smul_mem mul_mem

example [Ring R] (S : Subring R) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (n m : ℕ) :
    n • x ^ 3 - y + z ^ m ∈ S := by
  set_like

-- These lemmas need to exist so that the `set_like` tactic can apply them
lemma Subsemigroup.mem_closure_of_mem {M : Type*} [Mul M] {s : Set M} {x : M} (hx : x ∈ s) :
    x ∈ Subsemigroup.closure s :=
  Subsemigroup.subset_closure hx
lemma Submonoid.mem_closure_of_mem {M : Type*} [MulOneClass M] {s : Set M} {x : M} (hx : x ∈ s) :
    x ∈ Submonoid.closure s :=
  Submonoid.subset_closure hx
lemma Subgroup.mem_closure_of_mem {G : Type*} [Group G] {k : Set G} {x : G} (hx : x ∈ k) :
    x ∈ Subgroup.closure k :=
  Subgroup.subset_closure hx
lemma AddSubsemigroup.mem_closure_of_mem {M : Type*} [Add M] {s : Set M} {x : M} (hx : x ∈ s) :
    x ∈ AddSubsemigroup.closure s :=
  AddSubsemigroup.subset_closure hx
lemma AddSubmonoid.mem_closure_of_mem {M : Type*} [AddZeroClass M] {s : Set M}
    {x : M} (hx : x ∈ s) : x ∈ AddSubmonoid.closure s :=
  AddSubmonoid.subset_closure hx
lemma AddSubgroup.mem_closure_of_mem {G : Type*} [AddGroup G] {k : Set G} {x : G} (hx : x ∈ k) :
    x ∈ AddSubgroup.closure k :=
  AddSubgroup.subset_closure hx
lemma Submodule.mem_span_of_mem {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {s : Set M} {x : M} (hx : x ∈ s) : x ∈ Submodule.span R s :=
  Submodule.subset_span hx
lemma Subring.mem_closure_of_mem {R : Type*} [Ring R] {s : Set R} {x : R} (hx : x ∈ s) :
    x ∈ Subring.closure s :=
  Subring.subset_closure hx
lemma Subsemiring.mem_closure_of_mem {R : Type*} [NonAssocSemiring R] {s : Set R} {x : R}
    (hx : x ∈ s) : x ∈ Subsemiring.closure s :=
  Subsemiring.subset_closure hx
lemma Algebra.mem_adjoin_of_mem {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {s : Set A} {x : A} (hx : x ∈ s) : x ∈ Algebra.adjoin R s :=
  Algebra.subset_adjoin hx
lemma StarSubalgebra.mem_adjoin_of_mem (R : Type*) {A : Type*} [CommSemiring R] [StarRing R]
    [Semiring A] [Algebra R A] [StarRing A] [StarModule R A] (s : Set A) {x : A} (hx : x ∈ s) :
    x ∈ StarSubalgebra.adjoin R s :=
  StarSubalgebra.subset_adjoin R s hx
lemma NonUnitalSubsemiring.mem_closure_of_mem {R : Type*} [NonUnitalNonAssocSemiring R] {s : Set R}
    {x : R} (hx : x ∈ s) : x ∈ NonUnitalSubsemiring.closure s :=
  NonUnitalSubsemiring.subset_closure hx
lemma NonUnitalSubring.mem_closure_of_mem {R : Type*} [NonUnitalNonAssocRing R] {s : Set R}
    {x : R} (hx : x ∈ s) : x ∈ NonUnitalSubring.closure s :=
  NonUnitalSubring.subset_closure hx
lemma NonUnitalAlgebra.mem_adjoin_of_mem (R : Type*) {A : Type*} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    {s : Set A} {x : A} (hx : x ∈ s) : x ∈ NonUnitalAlgebra.adjoin R s :=
  NonUnitalAlgebra.subset_adjoin R hx
lemma NonUnitalStarAlgebra.mem_adjoin_of_mem (R : Type*) {A : Type*} [CommSemiring R] [StarRing R]
    [NonUnitalSemiring A] [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [StarModule R A] (s : Set A) {x : A} (hx : x ∈ s) : x ∈ NonUnitalStarAlgebra.adjoin R s :=
  NonUnitalStarAlgebra.subset_adjoin R s hx

attribute [aesop 10% apply (rule_sets [SetLike])]
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

example [Ring R] (S : Set R) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (n m : ℕ) :
    n • x ^ 3 - y + z ^ m ∈ Subring.closure S := by
  set_like

-- this instance is currently missing
instance StarSubalgebra.smulMemClass [CommSemiring R] [Semiring A] [Algebra R A] [StarRing R]
  [StarRing A] [StarModule R A] : SMulMemClass (StarSubalgebra R A) R A where
  smul_mem {s} r a (ha : a ∈ s.toSubalgebra) :=
    (SMulMemClass.smul_mem r ha : r • a ∈ s.toSubalgebra)

example [CommRing R] [Ring A] [Algebra R A] [StarRing R] [StarRing A] [StarModule R A]
    (r : R) (a b c : A) (s : Set A) (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (n : ℕ) :
    -b + star (algebraMap R A r) + a ^ n * c ∈ StarSubalgebra.adjoin R s := by
  set_like

example [Monoid M] (x : M) (n : ℕ) : x ^ n ∈ Submonoid.closure {x} := by
  set_like

example [Monoid M] (x y z w : M) (n : ℕ) : (x * y) ^ n * w ∈ Submonoid.closure {x, y, z, w} := by
  set_like
