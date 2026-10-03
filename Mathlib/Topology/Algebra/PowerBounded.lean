/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Topology.Algebra.Bounded

/-! ### Power-bounded elements

Let `M` be a monoid with zero, endowed with a topology.

* `IsPowerBounded a` says that `a : M` is *power bounded*, i.e., its powers `a ^ n` are bounded.

Let `R` be a semiring, endowed with a topology.

* `isPowerBounded_zero`: `0` is power bounded.

* `isPowerBounded_one`: `1` is power bounded.

Let `R` be a commutative topological ring and `S` a ring such that `R` is an `S`-module and has
the `S`-linear topology.

* `PowerBounded.subring`: the set of power bounded elements form a ring.

The key examples will be:
    · `S = R`: i.e., we have `[IsLinearTopology R R]`
    · `S = ℤ`: which can be infered from `[Ring R] [TopologicalSpace R] [NonarchimedeanRing R]`
-/

@[expose] public section

open Filter Topology Pointwise

namespace PowerBounded

open TopologicalRing

variable {M : Type*} [MonoidWithZero M] [TopologicalSpace M]

/-- An element is power-bounded if `{aⁿ | n}` is bounded. -/
def IsPowerBounded (a : M) : Prop :=
  IsBounded (Set.range (a ^ · : ℕ → M))

/-- `0` is power-bounded. -/
theorem isPowerBounded_zero : IsPowerBounded (0 : M) := by
  apply isBounded_pair_zero_one.subset
  rintro _ ⟨n, rfl⟩
  rcases n with _ | n <;> simp [zero_pow]

/-- `1` is power-bounded. -/
theorem isPowerBounded_one : IsPowerBounded (1 : M) := by
  apply isBounded_pair_zero_one.subset
  rintro _ ⟨n, rfl⟩
  simp

section Semiring

variable {R : Type*} [Semiring R] [TopologicalSpace R]

/-- If `a` and `b` commute then `a * b` is power-bounded if `a` and `b` are. -/
theorem isPowerBounded_mul_of_commute {a b : R} (h : Commute a b) (ha : IsPowerBounded a)
    (hb : IsPowerBounded b) : IsPowerBounded (a * b) := by
  apply (ha.mul hb).subset
  rintro _ ⟨n, rfl⟩
  simp only [Commute.mul_pow h]
  exact Set.mul_mem_mul ⟨n, rfl⟩ ⟨n, rfl⟩

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R] [TopologicalSpace R]

theorem isPowerBounded_mul {a b : R}
    (ha : IsPowerBounded a) (hb : IsPowerBounded b) : IsPowerBounded (a * b) :=
  isPowerBounded_mul_of_commute (Commute.all ..) ha hb

end CommSemiring

section Ring

variable {R : Type*} [Ring R] [TopologicalSpace R]

/-- `-a` is power-bounded if `a` is. -/
theorem IsPowerBounded.neg [ContinuousMul R] [ContinuousNeg R] {a : R} (ha : IsPowerBounded a) :
    IsPowerBounded (-a) := by
  apply (((isBounded_singleton (-1)).union (isBounded_singleton 1)).mul ha).subset
  rintro _ ⟨n, rfl⟩; change (-a) ^ n ∈ _
  rw [neg_pow]
  refine Set.mul_mem_mul ?_ ⟨n, rfl⟩
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  <;> simp [hk, pow_succ]

/-- If `a` and `b` commute then `a + b` is power bounded if `a` and `b` are. -/
theorem isPowerBounded_add_of_commute (S : Type*) [Ring S] [Module S R] [ContinuousAdd R]
    [IsLinearTopology S R] {a b : R} (hab : Commute a b)
    (ha : IsPowerBounded a) (hb : IsPowerBounded b) : IsPowerBounded (a + b) := by
  intro U hU
  obtain ⟨J, hJ, hJU⟩ := (IsLinearTopology.hasBasis_open_submodule S).mem_iff.mp hU
  obtain ⟨V, hV, hSV⟩ := (ha.mul hb) (J : Set R) (hJ.mem_nhds J.zero_mem)
  refine ⟨V, hV, ?_⟩
  rintro _ ⟨v, hv, _, ⟨n, rfl⟩, rfl⟩
  apply hJU
  change v * (a + b) ^ n ∈ _
  rw [hab.add_pow, Finset.mul_sum]
  refine Submodule.sum_mem J fun m _ ↦ ?_
  rw [show v * (a ^ m * b ^ (n - m) * ↑(n.choose m)) =
      (n.choose m) • (v * (a ^ m * b ^ (n - m))) by
    rw [nsmul_eq_mul, Nat.cast_commute, ← mul_assoc]]
  exact J.toAddSubmonoid.nsmul_mem
    (hSV (Set.mul_mem_mul hv (Set.mul_mem_mul ⟨m, rfl⟩ ⟨n - m, rfl⟩))) _

end Ring

section CommRing

variable {R : Type*} [CommRing R] [TopologicalSpace R]

theorem IsPowerBounded.add (S : Type*) [Ring S] [Module S R] [ContinuousAdd R]
    [IsLinearTopology S R] {a b : R} (ha : IsPowerBounded a) (hb : IsPowerBounded b) :
    IsPowerBounded (a + b) :=
  isPowerBounded_add_of_commute S (Commute.all ..) ha hb

variable (R) in
/-- The set of power bounded elements is a subring. -/
def subring {S : Type*} [Ring S] [Module S R] [IsTopologicalRing R] [IsLinearTopology S R] :
    Subring R where
  carrier := {a : R | IsPowerBounded a}
  mul_mem' := isPowerBounded_mul
  one_mem' := isPowerBounded_one
  add_mem' := IsPowerBounded.add S
  zero_mem' := isPowerBounded_zero
  neg_mem' := IsPowerBounded.neg

end CommRing

end PowerBounded
