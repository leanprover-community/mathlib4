/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import Mathlib.Data.Nat.ModEq
public import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Quiver periodicity and aperiodicity

The *period* of a vertex `i` of a quiver is the greatest common divisor of the lengths of the
cycles at `i`. In a strongly connected quiver the period does not depend on the vertex, and is
called the *index of imprimitivity*; a quiver is *aperiodic* when it equals `1`.

## Main definitions

* `Quiver.cycleLengths i`: the lengths of the positive-length cycles at `i`.
* `Quiver.period i`: the period of `i`, i.e. the gcd of `Quiver.cycleLengths i`.
* `Quiver.imprimitivityIndex V`: the common period of the vertices of a strongly connected
  quiver.
* `Quiver.IsAperiodic V`: the index of imprimitivity is `1`.
* `Quiver.IsCyclicPartition f`: `f` sends each edge from one class to the next, cyclically.

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

/-- The lengths of the positive-length cycles at a vertex `i`. -/
def cycleLengths (i : V) : Set ℕ := {k | 0 < k ∧ ∃ p : Path i i, p.length = k}

lemma mem_cycleLengths_iff : k ∈ cycleLengths i ↔ 0 < k ∧ ∃ p : Path i i, p.length = k := Iff.rfl

lemma zero_notMem_cycleLengths : 0 ∉ cycleLengths i := fun h ↦ h.1.false

/-- Cycle lengths at a vertex are closed under addition: concatenate the two cycles. -/
lemma add_mem_cycleLengths (ha : a ∈ cycleLengths i) (hb : b ∈ cycleLengths i) :
    a + b ∈ cycleLengths i := by
  obtain ⟨ha, p, rfl⟩ := ha
  obtain ⟨hb, q, rfl⟩ := hb
  exact ⟨by omega, p.comp q, by simp [Path.length_comp]⟩

lemma const_mul_mem_cycleLengths (ha : a ∈ cycleLengths i) (hm : 0 < m) :
    m * a ∈ cycleLengths i := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using ha
    · simpa [Nat.succ_mul] using add_mem_cycleLengths (ih hk) ha

lemma mul_const_mem_cycleLengths (ha : a ∈ cycleLengths i) (hm : 0 < m) :
    a * m ∈ cycleLengths i :=
  Nat.mul_comm m a ▸ const_mul_mem_cycleLengths ha hm

/-- Every element of the additive closure of the cycle lengths at `i` is either `0` or itself a
cycle length at `i`. -/
lemma eq_zero_or_mem_cycleLengths_of_mem_closure (hn : n ∈ AddSubmonoid.closure (cycleLengths i)) :
    n = 0 ∨ n ∈ cycleLengths i := by
  induction hn using AddSubmonoid.closure_induction with
  | mem x hx => exact .inr hx
  | zero => exact .inl rfl
  | add a b _ _ ha hb =>
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · simp
    · simpa using .inr hb
    · simpa using .inr ha
    · exact .inr (add_mem_cycleLengths ha hb)

/-- A cycle obtained by composing `p` with a positive-length path `s` back to the base point. -/
lemma length_comp_mem_cycleLengths {v : V} (p : Path i v) (s : Path v i) (hs : 0 < s.length) :
    (p.comp s).length ∈ cycleLengths i :=
  ⟨lt_of_lt_of_le hs (by simp [Path.length_comp]), p.comp s, rfl⟩

/-! ### The period of a vertex -/

/-- The period of a vertex `i`: the greatest common divisor of the lengths of the cycles at `i`.

If there are no cycles at `i` this is `0`. -/
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

@[simp] lemma period_eq_zero : period i = 0 ↔ cycleLengths i = ∅ := by
  rw [period, Nat.setGcd_eq_zero_iff, Set.eq_empty_iff_forall_notMem]
  exact ⟨fun h k hk ↦ zero_notMem_cycleLengths (Set.mem_singleton_iff.1 (h hk) ▸ hk),
    fun h k hk ↦ (h k hk).elim⟩

@[simp] lemma period_pos : 0 < period i ↔ (cycleLengths i).Nonempty := by
  rw [Nat.pos_iff_ne_zero, Ne, period_eq_zero, Set.nonempty_iff_ne_empty]

/-- Every common divisor of the cycle lengths is at most the period, provided a cycle exists. -/
lemma le_period (hm : ∀ k ∈ cycleLengths i, m ∣ k) (h : (cycleLengths i).Nonempty) :
    m ≤ period i :=
  Nat.le_of_dvd (period_pos.2 h) (dvd_period hm)

/-! ### Aperiodicity is cofinite -/

/-- **Aperiodicity is cofinite**: if the period at `i` is `1`, then every sufficiently large
natural number is the length of a cycle at `i`. -/
theorem exists_forall_ge_mem_cycleLengths (h : period i = 1) :
    ∃ N, ∀ n, N ≤ n → n ∈ cycleLengths i := by
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge (cycleLengths i)
  refine ⟨N + 1, fun n hn ↦ ?_⟩
  exact (eq_zero_or_mem_cycleLengths_of_mem_closure
    (hN n (by omega) (h ▸ one_dvd n : period i ∣ n))).resolve_left (by omega)

/-! ### Strongly connected quivers -/

/-- Half of `period_eq_of_isSStronglyConnected`: a round trip `i ⟶ j ⟶ i` transports every cycle
at `j` to a cycle at `i`, so `period i` divides every cycle length at `j`. -/
private lemma period_dvd_of_round_trip (p : Path i j) (q : Path j i) (hpq : 0 < (p.comp q).length)
    (hk : k ∈ cycleLengths j) : period i ∣ k := by
  obtain ⟨hk0, c, rfl⟩ := hk
  have h1 : period i ∣ (p.comp q).length :=
    period_dvd_of_mem_cycleLengths ⟨hpq, p.comp q, rfl⟩
  have h2 : period i ∣ (p.comp q).length + c.length := by
    refine period_dvd_of_mem_cycleLengths ⟨?_, (p.comp c).comp q, ?_⟩ <;>
      simp only [Path.length_comp] at hpq ⊢ <;> omega
  exact (Nat.dvd_add_right h1).1 h2

/-- In a strongly connected quiver the period is the same at every vertex. -/
theorem period_eq_of_isSStronglyConnected (hsc : IsSStronglyConnected V) (i j : V) :
    period i = period j := by
  obtain ⟨p, hp⟩ := hsc i j
  obtain ⟨q, hq⟩ := hsc j i
  have hpq : 0 < (p.comp q).length := lt_of_lt_of_le hp (by simp [Path.length_comp])
  have hqp : 0 < (q.comp p).length := lt_of_lt_of_le hq (by simp [Path.length_comp])
  exact Nat.dvd_antisymm
    (dvd_period fun _ hk ↦ period_dvd_of_round_trip p q hpq hk)
    (dvd_period fun _ hk ↦ period_dvd_of_round_trip q p hqp hk)

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
  exact period_pos.2 ⟨p.length, hp, p, rfl⟩

lemma imprimitivityIndex_dvd [Nonempty V] (hsc : IsSStronglyConnected V)
    (hk : k ∈ cycleLengths i) : imprimitivityIndex V ∣ k := by
  rw [imprimitivityIndex, period_eq_of_isSStronglyConnected hsc _ i]
  exact period_dvd_of_mem_cycleLengths hk

/-! ### Cyclic partitions -/

/-- A cyclic partition of the vertices into `h` classes: every edge goes from one class to the
next one cyclically. -/
def IsCyclicPartition {h : ℕ} (f : V → Fin h) : Prop :=
  ∀ ⦃i j : V⦄, (i ⟶ j) → (f j : ℕ) = ((f i : ℕ) + 1) % h

/-- A strongly connected quiver admits a cyclic partition into `imprimitivityIndex V` classes. -/
theorem exists_isCyclicPartition [Nonempty V] (hsc : IsSStronglyConnected V) :
    ∃ f : V → Fin (imprimitivityIndex V), IsCyclicPartition f := by
  set h := imprimitivityIndex V
  have hpos : 0 < h := imprimitivityIndex_pos hsc
  choose P _hP using fun v ↦ hsc (Classical.arbitrary V) v
  refine ⟨fun v ↦ ⟨(P v).length % h, Nat.mod_lt _ hpos⟩, fun i j e ↦ ?_⟩
  obtain ⟨s, hs⟩ := hsc j (Classical.arbitrary V)
  have h1 : h ∣ (P j).length + s.length := by
    simpa [Path.length_comp] using
      imprimitivityIndex_dvd hsc (length_comp_mem_cycleLengths (P j) s hs)
  have h2 : h ∣ (P i).length + 1 + s.length := by
    simpa [Path.length_comp, Nat.add_assoc] using
      imprimitivityIndex_dvd hsc (length_comp_mem_cycleLengths ((P i).cons e) s hs)
  have := ((Nat.modEq_zero_iff_dvd).2 h1).trans ((Nat.modEq_zero_iff_dvd).2 h2).symm
  simpa [Nat.ModEq, Nat.add_mod_right, Nat.mod_mod_of_dvd] using
    this.add_right_cancel' s.length

end Quiver
