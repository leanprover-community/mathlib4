/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.ModEq

/-!
# Quiver periodicity and aperiodicity

Period, index of imprimitivity, and cyclic partitions for strongly connected quivers.

## Main definitions

* `CycleLengths`: lengths of positive cycles at a vertex.
* `indexOfImprimitivity`: gcd of cycle lengths.

## Tags

quiver, aperiodic, primitive matrix, Perron–Frobenius theorem
-/

@[expose] public section

namespace Quiver
variable {V : Type*} [Quiver V]

/-- Lengths of positive cycles at a vertex `i`. -/
def CycleLengths (i : V) : Set ℕ := {k | k > 0 ∧ ∃ p : Path i i, p.length = k}

/-- The set of common divisors of all cycle lengths at `i`. (If there are no cycles this is all
  of `ℕ`, so the least element is `0`.) -/
def commonDivisorsSet (i : V) : Set ℕ := {d | ∀ k ∈ CycleLengths i, d ∣ k}

lemma one_mem_commonDivisorsSet (i : V) : 1 ∈ commonDivisorsSet i := fun _ _ ↦ one_dvd _

lemma commonDivisorsSet_nonempty (i : V) : (commonDivisorsSet i).Nonempty :=
  ⟨1, one_mem_commonDivisorsSet i⟩

/-- The period of a vertex `i`: the least common divisor of all cycle lengths at `i`.

If there are no cycles, this is `0` (since then `commonDivisorsSet i = Set.univ`). -/
noncomputable def period (i : V) : ℕ := by
  letI : DecidablePred fun d : ℕ => d ∈ commonDivisorsSet i := Classical.decPred _
  exact Nat.find (commonDivisorsSet_nonempty (i := i))

/-- `period i` is the least element of the set of common divisors of all cycle lengths at `i`. -/
lemma period_min (i : V) :
    period i ∈ commonDivisorsSet i ∧
      ∀ m ∈ commonDivisorsSet i, period i ≤ m := by
  classical
  refine ⟨?_, fun m hm ↦ ?_⟩
  · simpa [period] using (Nat.find_spec (commonDivisorsSet_nonempty (i := i)))
  · simpa [period] using (Nat.find_min' (commonDivisorsSet_nonempty (i := i)) hm)

/-- Basic characterization of `period`: divisibility plus minimality. -/
lemma period_spec (i : V) : (∀ k ∈ CycleLengths i, period i ∣ k) ∧
    (∀ m, (∀ k ∈ CycleLengths i, m ∣ k) → period i ≤ m) :=
  ⟨fun k hk ↦ (period_min i).1 k hk, fun m hm ↦ (period_min i).2 m hm⟩

lemma period_mem_commonDivisorsSet (i : V) : period i ∈ commonDivisorsSet i :=
  (period_min i).1

lemma period_le_of_commonDivisor (i : V) {m : ℕ} (hm : ∀ k ∈ CycleLengths i, m ∣ k) :
    period i ≤ m :=
  (period_spec i).2 _ hm

lemma divides_cycle_length {i : V} {k : ℕ} (hk : k ∈ CycleLengths i) : period i ∣ k :=
  (period_spec i).1 _ hk

lemma period_divides_cycle_lengths (i : V) : ∀ {k}, k ∈ CycleLengths i → period i ∣ k :=
  divides_cycle_length

lemma period_pos_of_nonempty_cycles (i : V) (h_nonempty : (CycleLengths i).Nonempty) :
    period i > 0 := by
  obtain ⟨k, hk⟩ := h_nonempty
  obtain ⟨t, ht⟩ := (period_spec i).1 k hk
  exact Nat.pos_of_ne_zero (fun hzero ↦ (Nat.pos_iff_ne_zero.mp hk.1) (by simpa [hzero] using ht))

/--
**Theorem: In a strongly connected quiver, the period is the same for all vertices**.
-/
theorem period_constant_of_strongly_connected (h_sc : Quiver.IsSStronglyConnected V) :
    ∀ i j : V, period i = period j := by
  intro i j
  obtain ⟨p, hp_pos⟩ := h_sc i j
  obtain ⟨q, hq_pos⟩ := h_sc j i
  have h_div_j : ∀ k ∈ CycleLengths j, period i ∣ k := by
    intro k hk
    obtain ⟨hk_pos, ⟨c, hc_len⟩⟩ := hk
    have ht_pos : 0 < (p.comp q).length := lt_of_lt_of_le hp_pos (by simp [Path.length_comp])
    have ht_mem : (p.comp q).length ∈ CycleLengths i := ⟨ht_pos, ⟨p.comp q, rfl⟩⟩
    refine (Nat.dvd_add_right ((period_spec i).1 _ ht_mem)).1 ?_
    let t' : ℕ := ((p.comp c).comp q).length
    have : p.length + k + q.length = t' := by aesop
    have h_dvd_t' : period i ∣ t' :=
      (period_spec i).1 _ ⟨lt_of_lt_of_le hk_pos (by grind), ⟨(p.comp c).comp q, rfl⟩⟩
    have h_eq : t' = (p.comp q).length + k := by
      simp [t', Path.length_comp, hc_len, Nat.add_assoc, Nat.add_comm]
    grind
  have h_div_i : ∀ k ∈ CycleLengths i, period j ∣ k := by
    intro k hk
    obtain ⟨hk_pos, ⟨c, hc_len⟩⟩ := hk
    have h_dvd_t : period j ∣ (q.comp p).length := (period_spec j).1 _
      ⟨lt_of_lt_of_le hq_pos (by simp [Path.length_comp]), ⟨q.comp p, rfl⟩⟩
    refine (Nat.dvd_add_right h_dvd_t).1 ?_
    · let t' : ℕ := ((q.comp c).comp p).length
      have : q.length + k + p.length = t' := by
        simp [t', Path.length_comp, hc_len, Nat.add_comm, Nat.add_left_comm]
      have h_dvd_t' : period j ∣ t' :=
        (period_spec j).1 _ ⟨lt_of_lt_of_le hk_pos (by lia), ⟨(q.comp c).comp p, rfl⟩⟩
      have h_eq : t' = (q.comp p).length + k := by
        simp [t', Path.length_comp, hc_len, Nat.add_comm, Nat.add_left_comm]
      grind
  exact le_antisymm (period_le_of_commonDivisor i h_div_i) (period_le_of_commonDivisor j h_div_j)

/-- The index of imprimitivity of a strongly connected quiver: the common period of its
vertices. Requires `Nonempty` to select an arbitrary vertex. -/
noncomputable def indexOfImprimitivity [Nonempty V] (_G : Quiver V) : ℕ :=
  period (Classical.arbitrary V)

/-- A strongly connected quiver is aperiodic if its index of imprimitivity is 1. -/
def IsAperiodic [Nonempty V] (G : Quiver V) : Prop :=
  indexOfImprimitivity G = 1

/-! # Cyclic Structure and Frobenius Normal Form -/

/-- A cyclic partition of the vertices with period h.
    The partition is represented by a map from `V` to `Fin h`.
    Edges only go from one class to the next one cyclically.
    We define the successor within `Fin h` by modular addition of 1 (staying in `Fin h`). -/
def IsCyclicPartition {h : ℕ} (h_pos : 0 < h) (partition : V → Fin h) : Prop :=
  let succMod : Fin h → Fin h := fun x => ⟨(x.val + 1) % h, Nat.mod_lt _ h_pos⟩
  ∀ i j : V, Nonempty (i ⟶ j) → partition j = succMod (partition i)

/-- If the right factor of a composed path has positive length, the composed cycle at `i`
belongs to `CycleLengths i`. -/
lemma mem_CycleLengths_of_comp_right {i v : V} (p : Path i v) (s : Path v i)
    (hs_pos : 0 < s.length) :
    (p.comp s).length ∈ CycleLengths i :=
  ⟨lt_of_lt_of_le hs_pos (by simp [Path.length_comp]), ⟨p.comp s, rfl⟩⟩

/-- Variant: if we first extend a path by a single edge using `cons` and then compose on the right
with a positive-length path back to the base, we still get a cycle length in `CycleLengths`. -/
lemma mem_CycleLengths_of_cons_comp_right {i v w : V} (p : Path i v) (e : v ⟶ w) (s : Path w i)
    (hs_pos : 0 < s.length) :
    (((p.cons e).comp s).length) ∈ CycleLengths i :=
  mem_CycleLengths_of_comp_right (p := p.cons e) (s := s) hs_pos

/--
Theorem: A strongly connected quiver with index of imprimitivity h admits a cyclic partition.
-/
theorem exists_cyclic_partition_of_strongly_connected [Nonempty V]
    (h_sc : Quiver.IsSStronglyConnected V) :
    ∀ (h_pos : 0 < indexOfImprimitivity (inferInstance : Quiver V)),
      ∃ partition : V → Fin (indexOfImprimitivity (inferInstance : Quiver V)),
        IsCyclicPartition h_pos partition := by
  intro h_pos
  let h := indexOfImprimitivity (inferInstance : Quiver V)
  change ∃ partition : V → Fin h, IsCyclicPartition h_pos partition
  let i0 : V := Classical.arbitrary V
  have hpaths : ∀ v : V, ∃ p : Path i0 v, 0 < p.length := fun v => h_sc i0 v
  let chosen : ∀ v : V, { p : Path i0 v // 0 < p.length } :=
    fun v => ⟨Classical.choose (hpaths v), Classical.choose_spec (hpaths v)⟩
  let P : ∀ v : V, Path i0 v := fun v => (chosen v).1
  let partition : V → Fin h := fun v => ⟨(P v).length % h, Nat.mod_lt _ h_pos⟩
  refine ⟨partition, fun i j hij ↦ ?_⟩
  obtain ⟨e⟩ := hij
  obtain ⟨s, hs_pos⟩ := h_sc j i0
  apply Fin.ext
  calc (P j).length % h = ((P i).length + 1) % h := ?_
       _   = ((P i).length % h + 1) % h := ?_
  · have hdvd1 : h ∣ ((P j).comp s).length :=
      divides_cycle_length (mem_CycleLengths_of_comp_right (p := P j) (s := s) hs_pos)
    have h1 : Nat.ModEq h ((P j).length + s.length) 0 := by
      simpa [Nat.ModEq, Path.length_comp] using Nat.mod_eq_zero_of_dvd hdvd1
    have hdvd2 : h ∣ (((P i).cons e).comp s).length :=
      divides_cycle_length
        (mem_CycleLengths_of_cons_comp_right (p := P i) (e := e) (s := s) hs_pos)
    have h2 : Nat.ModEq h ((P i).length + 1 + s.length) 0 := by
      simpa [Nat.ModEq, Path.length_comp, Path.length_cons, Nat.add_assoc] using
        Nat.mod_eq_zero_of_dvd hdvd2
    simpa [Nat.ModEq] using Nat.ModEq.add_right_cancel' s.length (h1.trans h2.symm)
  · rw [Nat.add_mod]; by_cases h1 : h = 1 <;> aesop

end Quiver
