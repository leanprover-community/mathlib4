/-
Copyright (c) 2025 Runtian Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Runtian Zhou
-/
module

public import Mathlib.Combinatorics.Quiver.Schreier
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.ZMod.Basic

/-!
# Cayley Graph Examples

This file provides concrete examples of Cayley graphs for common groups,
demonstrating the Cayley graph infrastructure defined in `Schreier.lean`.

## Main definitions

* `Quiver.cyclicGenerator` - Standard generator `{1}` for `ℤ/nℤ`
* `Quiver.CayleyCyclic` - Cayley graph of cyclic groups (directed cycle)
* `Quiver.adjacentTranspositions` - Adjacent transpositions for symmetric groups
* `Quiver.CayleySym` - Cayley graph of symmetric groups
* `Quiver.intGenerator` - Standard generator `{1}` for `ℤ`
* `Quiver.CayleyInt` - Cayley graph of the integers (bi-infinite path)

## Main results

* `Quiver.cyclicGenerator_closure_eq_top` - `{1}` generates `ℤ/nℤ`
* `Quiver.cayleyCyclic_connected` - The cyclic Cayley graph is connected
* `Quiver.adjacentTranspositions_closure_eq_top` - Adjacent transpositions generate `S_n`
* `Quiver.cayleySym_connected` - The symmetric group Cayley graph is connected
* `Quiver.intGenerator_closure_eq_top` - `{1}` generates `ℤ`
* `Quiver.cayleyInt_connected` - The integer Cayley graph is connected
-/

@[expose] public section

namespace Quiver

/-!
## Cayley Graph of Cyclic Groups

The Cayley graph of `ℤ/nℤ` with generator `1` is a directed cycle of length `n`.
We use `Multiplicative (ZMod n)` to view the additive group as multiplicative,
since the Cayley graph infrastructure uses multiplicative group notation.
-/

/-- The standard generator for the cyclic group `Multiplicative (ZMod n)`.
This is just `1` viewed as an element of the multiplicative version of `ℤ/nℤ`. -/
@[nolint unusedArguments]
def cyclicGenerator (n : ℕ) : Fin 1 → Multiplicative (ZMod n) :=
  fun _ ↦ Multiplicative.ofAdd 1

/-- The Cayley graph of the cyclic group ℤ/nℤ with the standard generator {1}.
This is a directed cycle of length n: each vertex k has an edge to k+1 (mod n). -/
abbrev CayleyCyclic (n : ℕ) : Type := CayleyGraph (cyclicGenerator n)

/-- The generator 1 generates the entire cyclic group ℤ/nℤ. -/
theorem cyclicGenerator_closure_eq_top (n : ℕ) [NeZero n] :
    Subgroup.closure (Set.range (cyclicGenerator n)) = ⊤ := by
  rw [Set.range_unique, ← Subgroup.zpowers_eq_closure]
  ext x
  simp only [Subgroup.mem_zpowers_iff, Subgroup.mem_top, iff_true]
  -- Every element of Multiplicative (ZMod n) is a power of 1
  use x.toAdd.val
  simp only [cyclicGenerator, zpow_natCast]
  -- Goal: (Multiplicative.ofAdd 1) ^ x.toAdd.val = x
  -- Use that ofAdd is injective
  rw [← ofAdd_toAdd x, ← ofAdd_nsmul]
  congr 1
  rw [nsmul_eq_mul, mul_one]
  exact ZMod.natCast_zmod_val x.toAdd

/-- The cyclic Cayley graph is preconnected (any two vertices are reachable). -/
theorem cayleyCyclic_preconnected (n : ℕ) [NeZero n] (x y : CayleyCyclic n) :
    Nonempty (Path (Symmetrify.of.obj x) (Symmetrify.of.obj y)) := by
  apply cayley_preconnected
  exact cyclicGenerator_closure_eq_top n

/-- The cyclic Cayley graph is connected. -/
theorem cayleyCyclic_connected (n : ℕ) [NeZero n] :
    Subsingleton (WeaklyConnectedComponent (CayleyCyclic n)) := by
  apply cayley_connected
  exact cyclicGenerator_closure_eq_top n

/-- The cyclic Cayley graph is locally finite (each vertex has exactly one outgoing edge). -/
noncomputable instance cayleyCyclic_locallyFinite (n : ℕ) (g : CayleyCyclic n) :
    Fintype (Σ h, g ⟶ h) :=
  cayley_locally_finite (cyclicGenerator n) g

/-!
## Cayley Graph of Symmetric Groups

The Cayley graph of `Equiv.Perm (Fin n)` with adjacent transpositions generates `S_n`.
-/

open Equiv in
/-- Adjacent transpositions for the symmetric group on `Fin (n+1)`.
Maps `i : Fin n` to the transposition `swap i (i+1)`. -/
def adjacentTranspositions (n : ℕ) : Fin n → Perm (Fin (n + 1)) :=
  fun i ↦ swap (Fin.castSucc i) (Fin.succ i)

open Equiv in
/-- The Cayley graph of the symmetric group S_{n+1} with adjacent transpositions.
This is the standard Cayley graph used in combinatorics. -/
abbrev CayleySym (n : ℕ) : Type := CayleyGraph (adjacentTranspositions n)

/-- Adjacent transpositions generate the symmetric group.

This is a classical result: any permutation can be written as a product of adjacent
transpositions (equivalently, bubble sort can sort any list). -/
theorem adjacentTranspositions_closure_eq_top (n : ℕ) :
    Subgroup.closure (Set.range (adjacentTranspositions n)) = ⊤ := by
  -- We use the fact that adjacent transpositions generate the symmetric group as a monoid,
  -- then lift to subgroup.
  apply Subgroup.closure_eq_top_of_mclosure_eq_top
  exact Equiv.Perm.mclosure_swap_castSucc_succ n

/-- The symmetric group Cayley graph is preconnected. -/
theorem cayleySym_preconnected (n : ℕ) (x y : CayleySym n) :
    Nonempty (Path (Symmetrify.of.obj x) (Symmetrify.of.obj y)) := by
  apply cayley_preconnected
  exact adjacentTranspositions_closure_eq_top n

/-- The symmetric group Cayley graph is connected. -/
theorem cayleySym_connected (n : ℕ) :
    Subsingleton (WeaklyConnectedComponent (CayleySym n)) := by
  apply cayley_connected
  exact adjacentTranspositions_closure_eq_top n

/-- The symmetric group Cayley graph is locally finite. -/
noncomputable instance cayleySym_locallyFinite (n : ℕ) (g : CayleySym n) :
    Fintype (Σ h, g ⟶ h) :=
  cayley_locally_finite (adjacentTranspositions n) g

/-!
## Cayley Graph of the Integers

The Cayley graph of `ℤ` with generator `{1}` is the bi-infinite path graph:
each integer `n` has a single outgoing edge to `n + 1`. This demonstrates that
the formalization handles infinite groups correctly.
-/

/-- The standard generator for the infinite cyclic group `ℤ` (viewed multiplicatively).
This maps the unique element of `Fin 1` to `Multiplicative.ofAdd 1`. -/
@[nolint unusedArguments]
def intGenerator : Fin 1 → Multiplicative ℤ :=
  fun _ ↦ Multiplicative.ofAdd 1

/-- The Cayley graph of `ℤ` with the standard generator `{1}`.
This is the bi-infinite path graph: each vertex `n` has an edge to `n + 1`. -/
abbrev CayleyInt : Type := CayleyGraph intGenerator

/-- The generator `1` generates the entire group `ℤ`. -/
theorem intGenerator_closure_eq_top :
    Subgroup.closure (Set.range intGenerator) = ⊤ := by
  rw [Set.range_unique, ← Subgroup.zpowers_eq_closure]
  ext x
  simp only [Subgroup.mem_zpowers_iff, Subgroup.mem_top, iff_true]
  use x.toAdd
  simp only [intGenerator]
  rw [← ofAdd_toAdd x, ← ofAdd_zsmul]
  congr 1
  simp

/-- The integer Cayley graph is preconnected (any two vertices are reachable). -/
theorem cayleyInt_preconnected (x y : CayleyInt) :
    Nonempty (Path (Symmetrify.of.obj x) (Symmetrify.of.obj y)) := by
  apply cayley_preconnected
  exact intGenerator_closure_eq_top

/-- The integer Cayley graph is connected. -/
theorem cayleyInt_connected :
    Subsingleton (WeaklyConnectedComponent CayleyInt) := by
  apply cayley_connected
  exact intGenerator_closure_eq_top

/-- The integer Cayley graph is locally finite (each vertex has exactly one outgoing edge). -/
noncomputable instance cayleyInt_locallyFinite (g : CayleyInt) :
    Fintype (Σ h, g ⟶ h) :=
  cayley_locally_finite intGenerator g

end Quiver
