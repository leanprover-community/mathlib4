/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import Mathlib.NumberTheory.FrobeniusNumber

import Mathlib.Data.ZMod.Basic

/-!
# Quiver periodicity and aperiodicity

The *period* of a vertex `i` of a quiver is the greatest common divisor of the lengths of the
cycles at `i`. In a strongly connected quiver the period does not depend on the vertex, and is
called the *index of imprimitivity*; a quiver is *aperiodic* when it equals `1`.

## Main definitions

* `Quiver.cycleLengths i`: the lengths of the cycles at `i`, including the trivial one.
* `Quiver.period i`: the period of `i`, i.e. the gcd of `Quiver.cycleLengths i`.
* `Quiver.imprimitivityIndex V`: the common period of the vertices of a strongly connected
  quiver.
* `Quiver.IsAperiodic V`: predicate for the index of imprimitivity to be `1`.
* `Quiver.IsCyclicPartition f`: predicate for `f` to send each edge from one class to the next,
  cyclically.

## Main statements

* `Quiver.period_dvd_of_mem_cycleLengths` and `Quiver.dvd_period`: `period i` is the greatest
  common divisor of the cycle lengths at `i`.
* `Quiver.exists_forall_ge_mem_cycleLengths`: aperiodicity is cofinite, i.e. if `period i = 1`
  then every sufficiently large natural number is a cycle length at `i`.
* `Quiver.period_eq_of_isSStronglyConnected`: in a strongly connected quiver all vertices have
  the same period.
* `Quiver.exists_isCyclicPartition`: a strongly connected quiver admits a cyclic partition into
  `imprimitivityIndex V` classes.

## Tags

quiver, aperiodic, primitive matrix, Perron–Frobenius theorem

## References

* [E. Seneta, *Non-negative Matrices and Markov Chains*][seneta2006]
-/

@[expose] public section

namespace Quiver

variable {V : Type*} [Quiver V] {i j : V} {a b k m n : ℕ}

/-! ### Cycle lengths -/

/-- The lengths of the cycles at a vertex `i`, including the trivial cycle of length `0`. -/
def cycleLengths (i : V) : Set ℕ := {k | ∃ p : Path i i, p.length = k}

lemma mem_cycleLengths_iff : k ∈ cycleLengths i ↔ ∃ p : Path i i, p.length = k := Iff.rfl

@[simp] lemma zero_mem_cycleLengths : 0 ∈ cycleLengths i := ⟨.nil, rfl⟩

/-- Cycle lengths at a vertex are closed under addition: concatenate the two cycles. -/
lemma add_mem_cycleLengths (ha : a ∈ cycleLengths i) (hb : b ∈ cycleLengths i) :
    a + b ∈ cycleLengths i := by
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨q, rfl⟩ := hb
  exact ⟨p.comp q, by simp [Path.length_comp]⟩

lemma const_mul_mem_cycleLengths (ha : a ∈ cycleLengths i) (m : ℕ) : m * a ∈ cycleLengths i := by
  induction m with
  | zero => simp
  | succ k ih => simpa [Nat.succ_mul] using add_mem_cycleLengths ih ha

lemma mul_const_mem_cycleLengths (ha : a ∈ cycleLengths i) (m : ℕ) : a * m ∈ cycleLengths i :=
  Nat.mul_comm m a ▸ const_mul_mem_cycleLengths ha m

/-- The cycle lengths at `i` are closed under taking the additive closure. -/
lemma mem_cycleLengths_of_mem_closure (hn : n ∈ AddSubmonoid.closure (cycleLengths i)) :
    n ∈ cycleLengths i := by
  induction hn using AddSubmonoid.closure_induction with
  | mem x hx => exact hx
  | zero => exact zero_mem_cycleLengths
  | add a b _ _ ha hb => exact add_mem_cycleLengths ha hb

/-- A cycle obtained by composing `p` with a path `s` back to the base point. -/
lemma length_comp_mem_cycleLengths {v : V} (p : Path i v) (s : Path v i) :
    (p.comp s).length ∈ cycleLengths i :=
  ⟨p.comp s, rfl⟩

/-! ### The period of a vertex -/

/-- The period of a vertex `i`: the greatest common divisor of the lengths of the cycles at `i`.

If the only cycle at `i` is the trivial one, this is `0`. -/
noncomputable def period (i : V) : ℕ := Nat.setGcd (cycleLengths i)

/-- The period divides every cycle length. -/
lemma period_dvd_of_mem_cycleLengths (hk : k ∈ cycleLengths i) : period i ∣ k :=
  Nat.setGcd_dvd_of_mem hk

/-- The characterizing property of `period`: it is the greatest common divisor of the cycle
lengths. -/
lemma dvd_period_iff : m ∣ period i ↔ ∀ k ∈ cycleLengths i, m ∣ k := Nat.dvd_setGcd_iff

/-- Universal property: every common divisor of the cycle lengths divides the period. This is what
makes `period` the *greatest* common divisor. -/
lemma dvd_period (hm : ∀ k ∈ cycleLengths i, m ∣ k) : m ∣ period i := dvd_period_iff.2 hm

@[simp] lemma period_eq_zero : period i = 0 ↔ cycleLengths i = {0} := by
  rw [period, Nat.setGcd_eq_zero_iff]
  exact ⟨fun h ↦ h.antisymm (Set.singleton_subset_iff.2 zero_mem_cycleLengths), Eq.subset⟩

@[simp] lemma period_pos : 0 < period i ↔ ∃ k ∈ cycleLengths i, k ≠ 0 := by
  simp [Nat.pos_iff_ne_zero, Set.eq_singleton_iff_unique_mem]

/-- Every common divisor of the cycle lengths is at most the period, provided a nontrivial cycle
exists. -/
lemma le_period (hm : ∀ k ∈ cycleLengths i, m ∣ k) (h : ∃ k ∈ cycleLengths i, k ≠ 0) :
    m ≤ period i :=
  Nat.le_of_dvd (period_pos.2 h) (dvd_period hm)

/-! ### Aperiodicity is cofinite -/

/-- **Aperiodicity is cofinite**: if the period at `i` is `1`, then every sufficiently large
natural number is the length of a cycle at `i`. -/
theorem exists_forall_ge_mem_cycleLengths (h : period i = 1) :
    ∃ N, ∀ n, N ≤ n → n ∈ cycleLengths i := by
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge (cycleLengths i)
  exact ⟨N, fun n hn ↦ mem_cycleLengths_of_mem_closure (hN n hn (h ▸ one_dvd n : period i ∣ n))⟩

/-! ### Strongly connected quivers -/

/-- Half of `period_eq_of_isSStronglyConnected`: a round trip `i ⟶ j ⟶ i` transports every cycle
at `j` to a cycle at `i`, so `period i` divides every cycle length at `j`. -/
private lemma period_dvd_of_round_trip (p : Path i j) (q : Path j i) (hk : k ∈ cycleLengths j) :
    period i ∣ k := by
  obtain ⟨c, rfl⟩ := hk
  have h1 : period i ∣ (p.comp q).length := period_dvd_of_mem_cycleLengths ⟨p.comp q, rfl⟩
  have h2 : period i ∣ (p.comp q).length + c.length :=
    period_dvd_of_mem_cycleLengths ⟨(p.comp c).comp q, by simp only [Path.length_comp]; lia⟩
  exact (Nat.dvd_add_right h1).1 h2

/-- In a strongly connected quiver the period is the same at every vertex. -/
theorem period_eq_of_isSStronglyConnected (hsc : IsSStronglyConnected V) (i j : V) :
    period i = period j := by
  obtain ⟨p, -⟩ := hsc i j
  obtain ⟨q, -⟩ := hsc j i
  exact Nat.dvd_antisymm
    (dvd_period fun _ hk ↦ period_dvd_of_round_trip p q hk)
    (dvd_period fun _ hk ↦ period_dvd_of_round_trip q p hk)

variable (V) in
/-- The index of imprimitivity of a quiver: the common period of its vertices.

This is only meaningful for strongly connected quivers (see
`period_eq_of_isSStronglyConnected`). Otherwise different vertices may have different periods,
and this is the junk value `period (Classical.arbitrary V)`. -/
noncomputable def imprimitivityIndex [Nonempty V] : ℕ := period (Classical.arbitrary V)

variable (V) in
/-- A quiver is aperiodic if its index of imprimitivity is `1`. -/
def IsAperiodic [Nonempty V] : Prop := imprimitivityIndex V = 1

lemma imprimitivityIndex_pos [Nonempty V] (hsc : IsSStronglyConnected V) :
    0 < imprimitivityIndex V := by
  obtain ⟨p, hp⟩ := hsc (Classical.arbitrary V) (Classical.arbitrary V)
  exact period_pos.2 ⟨p.length, ⟨p, rfl⟩, hp.ne'⟩

lemma imprimitivityIndex_dvd [Nonempty V] (hsc : IsSStronglyConnected V)
    (hk : k ∈ cycleLengths i) : imprimitivityIndex V ∣ k := by
  rw [imprimitivityIndex, period_eq_of_isSStronglyConnected hsc _ i]
  exact period_dvd_of_mem_cycleLengths hk

/-! ### Cyclic partitions -/

/-- A cyclic partition of the vertices into `h` classes: every edge goes from one class to the
next one cyclically. -/
def IsCyclicPartition {h : ℕ} (f : V → ZMod h) : Prop :=
  ∀ ⦃i j : V⦄, (i ⟶ j) → f j = f i + 1

/-- A strongly connected quiver admits a cyclic partition into `imprimitivityIndex V` classes. -/
theorem exists_isCyclicPartition [Nonempty V] (hsc : IsSStronglyConnected V) :
    ∃ f : V → ZMod (imprimitivityIndex V), IsCyclicPartition f := by
  choose P _hP using fun v ↦ hsc (Classical.arbitrary V) v
  refine ⟨fun v ↦ (P v).length, fun i j e ↦ ?_⟩
  obtain ⟨s, -⟩ := hsc j (Classical.arbitrary V)
  have h1 := imprimitivityIndex_dvd hsc (length_comp_mem_cycleLengths (P j) s)
  have h2 := imprimitivityIndex_dvd hsc (length_comp_mem_cycleLengths ((P i).cons e) s)
  rw [← ZMod.natCast_eq_zero_iff] at h1 h2
  push_cast [Path.length_comp, Path.length_cons] at h1 h2
  exact add_right_cancel (h1.trans h2.symm)

end Quiver
