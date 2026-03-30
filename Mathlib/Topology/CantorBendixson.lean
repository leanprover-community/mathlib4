/-
Copyright (c) 2026 Zikang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zikang Yu
-/
module

public import Mathlib.SetTheory.Cardinal.Ordinal
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

* `CantorBendixson.iteratedDerivedSet_zero`
* `CantorBendixson.iteratedDerivedSet_succ`
* `CantorBendixson.iteratedDerivedSet_limit`
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
* The current implementation is not universe polymorphic because it uses `gfpApprox`. A universe
  polymorphic implementation depends on upstream support in that module.

## TODO

* Pointwise and setwise Cantor-Bendixson ranks.
* A generalized Cantor-Bendixson decomposition theorem for arbitrary topological spaces and
  arbitrary cardinalities of topological bases.

-/

@[expose] public section

open Filter Set Cardinal OrdinalApprox

universe u

namespace CantorBendixson

section

variable {X : Type u} [TopologicalSpace X]

/-- The transfinite iteration of the relative derived-set operator on a set. -/
def iteratedDerivedSet (s : Set X) : Ordinal → Set X :=
  gfpApprox relDerivedSet s

@[inherit_doc CantorBendixson.iteratedDerivedSet]
scoped[CantorBendixson] notation:max s "ᵈ[" a "]" => iteratedDerivedSet s a

variable {s t : Set X} {a b : Ordinal}

@[simp]
theorem iteratedDerivedSet_zero :
    sᵈ[0] = s := by
  simp [iteratedDerivedSet, gfpApprox_zero]

@[simp]
theorem iteratedDerivedSet_succ :
    sᵈ[a + 1] = relDerivedSet (sᵈ[a]) := by
  simpa [iteratedDerivedSet] using
    gfpApprox_add_one relDerivedSet s relDerivedSet_subset a

theorem iteratedDerivedSet_limit (ha : Order.IsSuccLimit a) :
    sᵈ[a] = ⋂ b : Set.Iio a, sᵈ[b] := by
  simpa [iteratedDerivedSet] using gfpApprox_limit _ s ha

/-- A set is preperfect if and only if every stage of its iterated relative derived-set sequence
is equal to the original set. -/
theorem iteratedDerivedSet_constant_iff_preperfect :
    Preperfect s ↔ ∀ a : Ordinal, sᵈ[a] = s := by
  simp only [preperfect_iff_subset_derivedSet]
  constructor <;> intro h
  · intro a
    rw [iteratedDerivedSet,
      gfpApprox_eq_of_mem_fixedPoints _ s relDerivedSet_subset (zero_le a)]
    · simp [gfpApprox_zero]
    simpa [Function.IsFixedPt, gfpApprox_zero, relDerivedSet] using h
  · specialize h 1
    rw [← zero_add 1, iteratedDerivedSet_succ] at h
    simpa [relDerivedSet] using h

theorem isClosed_iteratedDerivedSet (hs : IsClosed s) :
    ∀ a : Ordinal, IsClosed (sᵈ[a]) := by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero => simpa only [iteratedDerivedSet_zero]
  | succ a ha =>
    simp_all [ha.relDerivedSet_eq, isClosed_iff_derivedSet_subset, derivedSet_mono]
  | limit a ha ih =>
    simpa [iteratedDerivedSet_limit ha] using
      isClosed_iInter fun i => isClosed_iInter fun hi => ih i hi

theorem iteratedDerivedSet_antitone (s : Set X) :
    Antitone (iteratedDerivedSet s) := gfpApprox_antitone _ s

theorem iteratedDerivedSet_mono :
    Monotone (fun s : Set X => iteratedDerivedSet s) :=
  gfpApprox_mono_mid _

/-- `stayOn s a` means that the iterated derived-set sequence of `s` is constant from stage `a`
onward. -/
abbrev stayOn (s : Set X) (a : Ordinal) : Prop :=
  ∀ b : Ordinal, a ≤ b → sᵈ[b] = sᵈ[a]

theorem stayOn.mono (h : stayOn s a) (hle : a ≤ b) :
    stayOn s b := by
  simp only [stayOn] at *
  exact fun c hle' => by simpa [h b hle] using h c (le_trans hle hle')

/-- If the iterated derived set stops changing at a successor stage, then it stays constant. -/
theorem stayOn_of_iteratedDerivedSet_succ_eq (ha : sᵈ[a + 1] = sᵈ[a]) :
    stayOn s a := by
  exact fun b hab =>
    gfpApprox_eq_of_mem_fixedPoints _ s relDerivedSet_subset hab <|
      Function.mem_fixedPoints_iff.mpr <| by simpa using ha

variable (s)

theorem iteratedDerivedSet_stay :
    ∃ a : Ordinal, stayOn s a := by
  exact ⟨(Order.succ #(Set X)).ord, fun b hb =>
    gfpApprox_eq_of_mem_fixedPoints _ s relDerivedSet_subset hb <|
      gfpApprox_ord_mem_fixedPoint _ s relDerivedSet_subset⟩

/-- The perfect kernel of a set, defined as the intersection of all iterated derived sets. It is
the largest perfect subset of the original set. -/
def perfectKernel : Set X :=
  ⋂ a : Ordinal, sᵈ[a]

theorem perfectKernel_subset_iteratedDerivedSet (a : Ordinal) :
    perfectKernel s ⊆ sᵈ[a] :=
  Set.iInter_subset _ a

theorem perfectKernel_subset :
    perfectKernel s ⊆ s := by
  simpa [iteratedDerivedSet_zero] using perfectKernel_subset_iteratedDerivedSet s 0

variable {s}

theorem perfectKernel_mono (hst : s ⊆ t) :
    perfectKernel s ⊆ perfectKernel t := by
  simpa [perfectKernel] using Set.iInter_mono'' (iteratedDerivedSet_mono hst)

theorem isClosed_perfectKernel (hs : IsClosed s) :
    IsClosed (perfectKernel s) :=
  isClosed_iInter (isClosed_iteratedDerivedSet hs)

@[simp]
theorem perfectKernel_empty :
    perfectKernel (∅ : Set X) = ∅ := by
  simpa using perfectKernel_subset ∅

/-- Once the iterated derived-set sequence stabilizes, the perfect kernel is equal to its eventual
value. -/
theorem perfectKernel_eq_iteratedDerivedSet_of_stayOn (ha : stayOn s a) :
    perfectKernel s = sᵈ[a] := by
  refine le_antisymm (perfectKernel_subset_iteratedDerivedSet s a) ?_
  refine Set.subset_iInter fun i => ?_
  rcases lt_or_ge i a with hi | hi
  · exact iteratedDerivedSet_antitone s hi.le
  · simp [ha i hi]

/-- Every perfect subset of a set is contained in its perfect kernel. -/
theorem subset_perfectKernel_of_perfect
    {P : Set X} (hP : Perfect P) (hPs : P ⊆ s) :
    P ⊆ perfectKernel s := by
  refine Set.subset_iInter fun i => ?_
  simpa [iteratedDerivedSet_constant_iff_preperfect.mp hP.acc i] using
    iteratedDerivedSet_mono hPs i

/-- The perfect kernel of a closed set is perfect. -/
theorem perfect_perfectKernel (hs : IsClosed s) :
    Perfect (perfectKernel s) := by
  obtain ⟨a, ha⟩ := iteratedDerivedSet_stay s
  rw [perfectKernel_eq_iteratedDerivedSet_of_stayOn ha]
  refine perfect_iff_eq_derivedSet.mpr ?_
  simpa [iteratedDerivedSet_succ, (isClosed_iteratedDerivedSet hs a).relDerivedSet_eq] using
    (ha (a + 1) le_self_add).symm

/-- Taking the perfect kernel of a closed set is idempotent. -/
theorem perfectKernel_idem (hs : IsClosed s) :
    perfectKernel (perfectKernel s) = perfectKernel s := by
  exact subset_antisymm (perfectKernel_subset _) <|
    subset_perfectKernel_of_perfect (perfect_perfectKernel hs) Subset.rfl

end

end CantorBendixson
