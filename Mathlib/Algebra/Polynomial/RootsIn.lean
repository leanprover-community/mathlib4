/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Paul Cadman
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Interval.Set.Defs

/-!
# Roots of a polynomial in a set

## Main definitions

* `Polynomial.rootsIn p s`: the distinct roots of `p` in the set `s`.
* `Polynomial.rootsIoo p S a b`: the distinct roots of `p` in `S` that are in the open interval from
  `a` to `b`.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] (p : R[X])

section rootsIoo

variable (S : Type*) [CommRing S] [IsDomain S] [Algebra R S] [Preorder S]

open scoped Classical in
/-- The distinct roots of `p` in `S` that are in the open interval from `a` to `b`. -/
noncomputable def rootsIoo (a b : S) : Finset S :=
  (p.aroots S).toFinset.filter (fun x ↦ a < x ∧ x < b)

open scoped Classical in
theorem rootsIoo_def (a b : S) :
    p.rootsIoo S a b = (p.aroots S).toFinset.filter (fun x ↦ a < x ∧ x < b) := by
  rw [rootsIoo]

end rootsIoo

variable [IsDomain R]

open scoped Classical in
/-- The distinct roots of `p` in `s`. -/
noncomputable def rootsIn (s : Set R) : Finset R :=
  p.roots.toFinset.filter (fun x ↦ x ∈ s)

@[simp]
theorem mem_rootsIn {p : R[X]} {s : Set R} {x : R} :
    x ∈ p.rootsIn s ↔ x ∈ p.roots ∧ x ∈ s := by
  simp [rootsIn]

@[simp]
theorem rootsIn_empty : p.rootsIn ∅ = ∅ := by
  simp [rootsIn]

theorem rootsIn_Ioo [Preorder R] (a b : R) : p.rootsIn (Set.Ioo a b) = p.rootsIoo R a b := by
  ext x
  simp [rootsIoo, aroots_def]

end Polynomial
