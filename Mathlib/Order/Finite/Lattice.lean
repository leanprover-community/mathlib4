/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.EquivFin

/-!
# Lattice structure on a finite semilattice with an extremal element

In a finite meet-semilattice with a greatest element, any two elements have a least upper
bound, namely the infimum of their common upper bounds, of which there is at least one.
We record this as `Finite.toLattice`, and the dual statement as `Finite.toLatticeOfSup`.

It is used to build the join of the refinement order on set partitions, which Coq-Combi
provides as part of the lattice structure of `setpart` in `theories/Combi/setpartition.v`.

## Main definitions

* `Finite.toLattice` : a finite meet-semilattice with a top element is a lattice.
* `Finite.toLatticeOfSup` : a finite join-semilattice with a bottom element is a lattice.
-/

@[expose] public section

open scoped Classical in
/-- A finite meet-semilattice with a greatest element is a lattice: the join of `a` and `b`
is the infimum of their common upper bounds, of which there is at least one, namely `⊤`.

This is a `def`, not an instance, to avoid a diamond with the lattice structures that most
finite orders carry already; use `letI := Finite.toLattice α` to put it in scope. -/
@[instance_reducible]
noncomputable def Finite.toLattice (α : Type*) [SemilatticeInf α] [OrderTop α] [Finite α] :
    Lattice α :=
  letI := Fintype.ofFinite α
  { ‹SemilatticeInf α› with
    sup := fun a b => (Finset.univ.filter fun c => a ≤ c ∧ b ≤ c).inf id
    le_sup_left := fun a b => Finset.le_inf fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact hc.1
    le_sup_right := fun a b => Finset.le_inf fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact hc.2
    sup_le := fun a b c hac hbc => Finset.inf_le (f := id) (by simp [hac, hbc]) }

open scoped Classical in
/-- A finite join-semilattice with a least element is a lattice: the meet of `a` and `b`
is the supremum of their common lower bounds, of which there is at least one, namely `⊥`.

This is a `def`, not an instance, to avoid a diamond with the lattice structures that most
finite orders carry already; use `letI := Finite.toLatticeOfSup α` to put it in scope. -/
@[instance_reducible]
noncomputable def Finite.toLatticeOfSup (α : Type*) [SemilatticeSup α] [OrderBot α]
    [Finite α] : Lattice α :=
  letI := Fintype.ofFinite α
  { ‹SemilatticeSup α› with
    inf := fun a b => (Finset.univ.filter fun c => c ≤ a ∧ c ≤ b).sup id
    inf_le_left := fun a b => Finset.sup_le fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact hc.1
    inf_le_right := fun a b =>  Finset.sup_le fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact hc.2
    le_inf := fun a b c hab hac => Finset.le_sup (f := id) (by simp [hab, hac]) }
