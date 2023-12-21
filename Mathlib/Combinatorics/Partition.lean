/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Combinatorics.Composition
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic.ApplyFun

#align_import combinatorics.partition from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Partitions

A partition of a natural number `n` is a way of writing `n` as a sum of positive integers, where the
order does not matter: two sums that differ only in the order of their summands are considered the
same partition. This notion is closely related to that of a composition of `n`, but in a composition
of `n` the order does matter.
A summand of the partition is called a part.

## Main functions

* `p : Partition n` is a structure, made of a multiset of integers which are all positive and
  add up to `n`.

## Implementation details

The main motivation for this structure and its API is to show Euler's partition theorem, and
related results.

The representation of a partition as a multiset is very handy as multisets are very flexible and
already have a well-developed API.

## Tags

Partition

## References

<https://en.wikipedia.org/wiki/Partition_(number_theory)>
-/


variable {α : Type*}

open Multiset

open BigOperators

namespace Nat

/-- A partition of `n` is a multiset of positive integers summing to `n`. -/
@[ext]
structure Partition (n : ℕ) where
  /-- positive integers summing to `n`-/
  parts : Multiset ℕ
  /-- proof that the `parts` are positive-/
  parts_pos : ∀ {i}, i ∈ parts → 0 < i
  /-- proof that the `parts` sum to `n`-/
  parts_sum : parts.sum = n
  -- porting notes: chokes on `parts_pos`
  --deriving DecidableEq
#align nat.partition Nat.Partition

namespace Partition

instance decidableEqParition: DecidableEq (Partition n)
  | p, q => by simp [Partition.ext_iff]; exact decidableEq p.parts q.parts

/-- A composition induces a partition (just convert the list to a multiset). -/
def ofComposition (n : ℕ) (c : Composition n) : Partition n
    where
  parts := c.blocks
  parts_pos {i} hi := c.blocks_pos hi
  parts_sum := by rw [Multiset.coe_sum, c.blocks_sum]
#align nat.partition.of_composition Nat.Partition.ofComposition

theorem ofComposition_surj {n : ℕ} : Function.Surjective (ofComposition n) := by
  rintro ⟨b, hb₁, hb₂⟩
  rcases Quotient.exists_rep b with ⟨b, rfl⟩
  refine' ⟨⟨b, fun {i} hi => hb₁ hi, _⟩, Partition.ext _ _ rfl⟩
  simpa using hb₂
#align nat.partition.of_composition_surj Nat.Partition.ofComposition_surj

-- The argument `n` is kept explicit here since it is useful in tactic mode proofs to generate the
-- proof obligation `l.sum = n`.
/-- Given a multiset which sums to `n`, construct a partition of `n` with the same multiset, but
without the zeros.
-/
def ofSums (n : ℕ) (l : Multiset ℕ) (hl : l.sum = n) : Partition n
    where
  parts := l.filter (· ≠ 0)
  parts_pos {i} hi := Nat.pos_of_ne_zero <| by apply of_mem_filter hi
  parts_sum := by
    have lt : l.filter (· = 0) + l.filter (· ≠ 0) = l := filter_add_not _ l
    apply_fun Multiset.sum at lt
    have lz : (l.filter (· = 0)).sum = 0 := by
      rw [Multiset.sum_eq_zero_iff]
      simp
    rwa [sum_add (filter (fun x => x = 0) l) (filter (fun x => ¬x = 0) l),lz,hl, zero_add] at lt
#align nat.partition.of_sums Nat.Partition.ofSums

/-- A `Multiset ℕ` induces a partition on its sum. -/
def ofMultiset (l : Multiset ℕ) : Partition l.sum :=
  ofSums _ l rfl
#align nat.partition.of_multiset Nat.Partition.ofMultiset

/-- The partition of exactly one part. -/
def indiscretePartition (n : ℕ) : Partition n :=
  ofSums n {n} rfl
#align nat.partition.indiscrete_partition Nat.Partition.indiscretePartition

instance {n : ℕ} : Inhabited (Partition n) :=
  ⟨indiscretePartition n⟩

/-- The number of times a positive integer `i` appears in the partition `ofSums n l hl` is the same
as the number of times it appears in the multiset `l`.
(For `i = 0`, `Partition.non_zero` combined with `Multiset.count_eq_zero_of_not_mem` gives that
this is `0` instead.)
-/
theorem count_ofSums_of_ne_zero {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n) {i : ℕ} (hi : i ≠ 0) :
    (ofSums n l hl).parts.count i = l.count i :=
  count_filter_of_pos hi
#align nat.partition.count_of_sums_of_ne_zero Nat.Partition.count_ofSums_of_ne_zero

theorem count_ofSums_zero {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n) :
    (ofSums n l hl).parts.count 0 = 0 :=
  count_filter_of_neg fun h => h rfl
#align nat.partition.count_of_sums_zero Nat.Partition.count_ofSums_zero

/-- Show there are finitely many partitions by considering the surjection from compositions to
partitions.
-/
instance (n : ℕ) : Fintype (Partition n) :=
  Fintype.ofSurjective (ofComposition n) ofComposition_surj

/-- The finset of those partitions in which every part is odd. -/
def odds (n : ℕ) : Finset (Partition n) :=
  Finset.univ.filter fun c => ∀ i ∈ c.parts, ¬Even i
#align nat.partition.odds Nat.Partition.odds

/-- The finset of those partitions in which each part is used at most once. -/
def distincts (n : ℕ) : Finset (Partition n) :=
  Finset.univ.filter fun c => c.parts.Nodup
#align nat.partition.distincts Nat.Partition.distincts

/-- The finset of those partitions in which every part is odd and used at most once. -/
def oddDistincts (n : ℕ) : Finset (Partition n) :=
  odds n ∩ distincts n
#align nat.partition.odd_distincts Nat.Partition.oddDistincts

end Partition

end Nat
