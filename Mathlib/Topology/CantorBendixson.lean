/-
Copyright (c) 2026 Zikang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zikang Yu
-/
module

public import Mathlib.SetTheory.Ordinal.FixedPointApproximants
public import Mathlib.Topology.DerivedSet

/-!
# Cantor-Bendixson derivatives and perfect kernel

This file defines the transfinite iteration of the relative derived-set operator
and the associated perfect kernel.

For closed sets, the relative derived set agrees with `derivedSet`, so this recovers the usual
Cantor-Bendixson derivative sequence of a closed set.

## Main definitions

* `CantorBendixson.iteratedDerivedSet s a`: the `a`-th transfinite iterate of `relDerivedSet`
  starting from `s`.
* `CantorBendixson.perfectKernel s`: the largest perfect subset of `s`, defined as the
  intersection of all iterated derived sets of `s`.

## Main statements

* `CantorBendixson.iteratedDerivedSet_constant_iff_preperfect`: a set is preperfect if and only
  if every iterated derived set is equal to the original set.
* `CantorBendixson.iteratedDerivedSet_stay`: the iterated derived-set sequence eventually
  stabilizes.
* `CantorBendixson.perfect_perfectKernel`: the perfect kernel of a closed set is perfect.
* `CantorBendixson.subset_perfectKernel_of_perfect`: the perfect kernel is the largest perfect
  subset.

## Notation

* `sᵈ[a]`: the `a`-th iterated relative derived set of `s`.

## Implementation notes

* We define `iteratedDerivedSet` using `OrdinalApprox.gfpApprox` applied to `relDerivedSet`.
  This keeps the transfinite sequence antitone for arbitrary sets.
* If `s` is closed, then `relDerivedSet s = derivedSet s`, so successor stages agree with the
  ambient derived-set operator.

## TODO

* Pointwise and setwise Cantor-Bendixson ranks.
* A generalized Cantor-Bendixson decomposition theorem for arbitrary topological spaces and
  arbitrary cardinalities of topological bases.
-/

@[expose] public section

open Set Cardinal Order OrdinalApprox Function

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The transfinite iteration of the relative derived-set operator on a set. -/
def iteratedDerivedSet (s : Set X) : Ordinal → Set X :=
  gfpApprox relDerivedSet s

@[deprecated (since := "2026-11-11")]
protected alias CantorBendixson.iteratedDerivedSet :=
  iteratedDerivedSet

@[inherit_doc iteratedDerivedSet]
scoped[CantorBendixson] notation:max s "ᵈ[" a "]" => iteratedDerivedSet s a

open scoped CantorBendixson

variable {s t : Set X} {a b : Ordinal}

theorem iteratedDerivedSet_def (s : Set X) (a : Ordinal) :
    sᵈ[a] = s ∩ ⋂ b < a, relDerivedSet sᵈ[b] := by
  rw [iteratedDerivedSet, gfpApprox_def]
  rfl

@[simp]
theorem iteratedDerivedSet_zero (s : Set X) : sᵈ[0] = s := by
  simp [iteratedDerivedSet, gfpApprox_zero]

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.iteratedDerivedSet_zero :=
  iteratedDerivedSet_zero

@[simp]
theorem iteratedDerivedSet_add_one (s : Set X) (a : Ordinal) : sᵈ[a + 1] = relDerivedSet sᵈ[a] :=
  gfpApprox_add_one _ relDerivedSet_subset a

@[deprecated (since := "2026-11-12")]
alias iteratedDerivedSet_succ := iteratedDerivedSet_add_one

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.iteratedDerivedSet_succ :=
  iteratedDerivedSet_add_one

theorem iteratedDerivedSet_limit (s : Set X) (ha : IsSuccLimit a) : sᵈ[a] = ⋂ b < a, sᵈ[b] := by
  simpa [iteratedDerivedSet] using gfpApprox_of_isSuccLimit relDerivedSet ha

theorem iteratedDerivSet_of_ne_zero (s : Set X) (ha : a ≠ 0) :
    sᵈ[a] = ⋂ b < a, relDerivedSet sᵈ[b] := by
  rw [iteratedDerivedSet_def, inter_eq_right]
  apply (iInter₂_subset 0 ha.pos).trans
  simp

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.iteratedDerivedSet_limit :=
  iteratedDerivedSet_limit

/-- A set is preperfect if and only if every stage of its iterated relative derived-set sequence
is equal to the original set. -/
theorem preperfect_iff_iteratedDerivedSet_eq_const :
    Preperfect s ↔ iteratedDerivedSet s = const _ s := by
  rw [preperfect_iff_eq_relDerivedSet, eq_comm,
    ← gfpApprox_eq_all_of_fixedPoint _ relDerivedSet_subset]
  simp [iteratedDerivedSet, eq_const_iff]

theorem _root_.Preperfect.iteratedDerivedSet_eq (hs : Preperfect s) (i : Ordinal) : sᵈ[i] = s := by
  rw [preperfect_iff_iteratedDerivedSet_eq_const.1 hs, const_apply]

@[deprecated (since := "2026-11-12")]
alias iteratedDerivedSet_constant_iff_preperfect := preperfect_iff_iteratedDerivedSet_eq_const

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.iteratedDerivedSet_constant_iff_preperfect :=
  preperfect_iff_iteratedDerivedSet_eq_const

theorem isClosed_iteratedDerivedSet (hs : IsClosed s) (a : Ordinal) : IsClosed sᵈ[a] := by
  induction a using Ordinal.limitRecOn with
  | zero => simpa
  | add_one a ha =>
    simp_all [ha.relDerivedSet_eq, isClosed_iff_derivedSet_subset, derivedSet_mono]
  | limit a ha ih =>
    simpa [iteratedDerivedSet_limit s ha] using
      isClosed_iInter fun i => isClosed_iInter fun hi => ih i hi

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.isClosed_iteratedDerivedSet := isClosed_iteratedDerivedSet

theorem iteratedDerivedSet_antitone (s : Set X) : Antitone (iteratedDerivedSet s) :=
  gfpApprox_anti_right _

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.iteratedDerivedSet_antitone := iteratedDerivedSet_antitone

theorem iteratedDerivedSet_monotone : Monotone (fun s : Set X => iteratedDerivedSet s) :=
  gfpApprox_mono_mid _

@[deprecated (since := "2026-11-12")] alias iteratedDerivedSet_mono :=
  iteratedDerivedSet_monotone

@[deprecated (since := "2026-11-11")] alias CantorBendixson.iteratedDerivedSet_mono :=
  iteratedDerivedSet_monotone

/-- If the iterated derived set stops changing at a successor stage, then `sᵈ[a]` is a fixed
point of `relDerivSet`. -/
theorem mem_fixedPoints_of_iteratedDerivedSet_succ_eq (ha : sᵈ[a + 1] = sᵈ[a]) :
    sᵈ[a] ∈ fixedPoints relDerivedSet := by
  rwa [Function.mem_fixedPoints_iff, ← iteratedDerivedSet_add_one]

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.mem_fixedPoints_of_iteratedDerivedSet_succ_eq :=
  mem_fixedPoints_of_iteratedDerivedSet_succ_eq

theorem iteratedDerivedSet_mem_fixedPoints (s : Set X) : ∃ a, sᵈ[a] ∈ fixedPoints relDerivedSet :=
  ⟨_, gfpApprox_ord_mem_fixedPoint relDerivedSet relDerivedSet_subset⟩

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.iteratedDerivedSet_mem_fixedPoints :=
  iteratedDerivedSet_mem_fixedPoints

/-- The perfect kernel of a set, defined as the intersection of all iterated derived sets. It is
the largest perfect subset of the original set. -/
def perfectKernel (s : Set X) : Set X :=
  ⋂ a, sᵈ[a]

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.perfectKernel := perfectKernel

theorem perfectKernel_subset_iteratedDerivedSet (s : Set X) (a : Ordinal) :
    perfectKernel s ⊆ sᵈ[a] :=
  iInter_subset _ a

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.perfectKernel_subset_iteratedDerivedSet :=
  perfectKernel_subset_iteratedDerivedSet

theorem perfectKernel_subset (s : Set X) : perfectKernel s ⊆ s := by
  simpa [iteratedDerivedSet_zero] using perfectKernel_subset_iteratedDerivedSet s 0

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.perfectKernel_subset :=
  perfectKernel_subset

theorem perfectKernel_monotone : Monotone (perfectKernel (X := X)) := by
  intro s t hst
  simpa [perfectKernel] using Set.iInter_mono'' (iteratedDerivedSet_monotone hst)

@[deprecated (since := "2026-11-12")]
alias perfectKernel_mono := perfectKernel_monotone

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.perfectKernel_mono :=
  perfectKernel_monotone

theorem isClosed_perfectKernel (hs : IsClosed s) : IsClosed (perfectKernel s) :=
  isClosed_iInter (isClosed_iteratedDerivedSet hs)

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.isClosed_perfectKernel := isClosed_perfectKernel

@[simp]
theorem perfectKernel_empty : perfectKernel (∅ : Set X) = ∅ := by
  simpa using perfectKernel_subset ∅

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.perfectKernel_empty := perfectKernel_empty

/-- Once `sᵈ[a]` is a fixed point of `relDerivSet`, the perfect kernel equals `sᵈ[a]`. -/
theorem perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints
    (ha : sᵈ[a] ∈ fixedPoints relDerivedSet) : perfectKernel s = sᵈ[a] := by
  refine le_antisymm (perfectKernel_subset_iteratedDerivedSet s a) ?_
  refine subset_iInter fun i => ?_
  rcases lt_or_ge i a with hi | hi
  · exact iteratedDerivedSet_antitone s hi.le
  · exact (gfpApprox_eq_of_mem_fixedPoints relDerivedSet hi ha).ge

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints :=
  perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints

/-- Every perfect subset of a set is contained in its perfect kernel. -/
theorem _root_.Perfect.subset_perfectKernel {P : Set X} (hP : Perfect P) (hPs : P ⊆ s) :
    P ⊆ perfectKernel s := by
  refine subset_iInter fun i => ?_
  rw [← hP.acc.iteratedDerivedSet_eq i]
  exact iteratedDerivedSet_monotone hPs i

/-- The perfect kernel of a closed set is perfect. -/
theorem perfect_perfectKernel (hs : IsClosed s) : Perfect (perfectKernel s) := by
  obtain ⟨a, ha⟩ := iteratedDerivedSet_mem_fixedPoints s
  rw [perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints ha]
  refine perfect_iff_eq_derivedSet.mpr ?_
  simpa [(isClosed_iteratedDerivedSet hs a).relDerivedSet_eq] using
    (Function.mem_fixedPoints_iff.mp ha).symm

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.perfect_perfectKernel :=
  perfect_perfectKernel

/-- Taking the perfect kernel of a closed set is idempotent. -/
theorem perfectKernel_idem (hs : IsClosed s) : perfectKernel (perfectKernel s) = perfectKernel s :=
  subset_antisymm (perfectKernel_subset _) <|
    (perfect_perfectKernel hs).subset_perfectKernel Subset.rfl

@[deprecated (since := "2026-11-11")]
alias CantorBendixson.perfectKernel_idem :=
  perfectKernel_idem
