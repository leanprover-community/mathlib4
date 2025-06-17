/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Mathlib.Computability.LTS.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Trace Equivalence

Definitions and results on trace equivalence for `LTS`s.

## Main definitions

- `LTS.traces`: the set of traces of a state.
- `TraceEq s1 s2`: `s1` and `s2` are trace equivalent, i.e., they have the same sets of traces.

## Notations

- `s1 ~tr[lts] s2`: the states `s1` and `s2` are trace equivalent in `lts`.

## Main statements

- `TraceEq.eqv`: trace equivalence is an equivalence relation (see `Equivalence`).
- `TraceEq.deterministic_sim`: for a deterministic `LTS`, trace equivalence is a simulation.

-/

universe u v

variable {State : Type u} {Label : Type v} (lts : LTS State Label)

/-- The traces of a state `s` is the set of all lists of labels `μs` such that there is a multi-step
transition labelled by `μs` originating from `s`. -/
def LTS.traces (s : State) := { μs : List Label | ∃ s', lts.mtr s μs s' }

/-- If there is a multi-step transition from `s` labelled by `μs`, then `μs` is in the traces of
`s`. -/
theorem LTS.traces_in (s : State) (μs : List Label) (s' : State) (h : lts.mtr s μs s') :
  μs ∈ lts.traces s := by
  simp [LTS.traces]
  exists s'

/-- Two states are trace equivalent if they have the same set of traces. -/
def TraceEq (s1 s2 : State) := lts.traces s1 = lts.traces s2

/--
Notation for trace equivalence.

Differently from standard pen-and-paper presentations, we require the lts to be mentioned
explicitly.
-/
notation s " ~tr[" lts "] " s' => TraceEq lts s s'

/-- Trace equivalence is reflexive. -/
theorem TraceEq.refl (s : State) : s ~tr[lts] s := by
  simp only [TraceEq]

/-- Trace equivalence is symmetric. -/
theorem TraceEq.symm (lts : LTS State Label) {s1 s2 : State} (h : s1 ~tr[lts] s2) :
  s2 ~tr[lts] s1 := by
  simp only [TraceEq] at h
  simp only [TraceEq]
  rw [h]

/-- Trace equivalence is transitive. -/
theorem TraceEq.trans {s1 s2 s3 : State} (h1 : s1 ~tr[lts] s2) (h2 : s2 ~tr[lts] s3) :
  s1 ~tr[lts] s3 := by
  simp only [TraceEq]
  simp only [TraceEq] at h1
  simp only [TraceEq] at h2
  rw [h1, h2]

/-- Bisimilarity is an equivalence relation. -/
theorem TraceEq.eqv (lts : LTS State Label) : Equivalence (TraceEq lts) := {
    refl := TraceEq.refl lts
    symm := TraceEq.symm lts
    trans := TraceEq.trans lts
  }

/-- In a deterministic LTS, trace equivalence is a simulation. -/
theorem TraceEq.deterministic_sim
  (lts : LTS State Label) (hdet : lts.Deterministic) (s1 s2 : State) (h : s1 ~tr[lts] s2) :
  ∀ μ s1', lts.tr s1 μ s1' → ∃ s2', lts.tr s2 μ s2' ∧ s1' ~tr[lts] s2' := by
  intro μ s1' htr1
  have hmtr1 := LTS.mtr.single lts htr1
  simp [TraceEq] at h
  have hin := LTS.traces_in lts s1 [μ] s1' hmtr1
  rw [h] at hin
  obtain ⟨s2', hmtr2⟩ := hin
  exists s2'
  constructor
  · apply LTS.mtr.single_invert lts _ _ _ hmtr2
  · simp only [TraceEq, LTS.traces]
    funext μs'
    simp only [eq_iff_iff]
    simp only [setOf]
    constructor
    case mp =>
      intro hmtr1'
      obtain ⟨s1'', hmtr1'⟩ := hmtr1'
      have hmtr1comp := LTS.mtr.comp lts hmtr1 hmtr1'
      have hin := LTS.traces_in lts s1 ([μ] ++ μs') s1'' hmtr1comp
      rw [h] at hin
      simp [LTS.traces] at hin
      obtain ⟨s', hmtr2'⟩ := hin
      cases hmtr2'
      case stepL s2'' htr2 hmtr2' =>
        exists s'
        have htr2' := LTS.mtr.single_invert lts _ _ _ hmtr2
        have hdets2 := hdet s2 μ s2' s2'' htr2' htr2
        rw [hdets2]
        exact hmtr2'
    case mpr =>
      intro hmtr2'
      obtain ⟨s2'', hmtr2'⟩ := hmtr2'
      have hmtr2comp := LTS.mtr.comp lts hmtr2 hmtr2'
      have hin := LTS.traces_in lts s2 ([μ] ++ μs') s2'' hmtr2comp
      rw [← h] at hin
      simp [LTS.traces] at hin
      obtain ⟨s', hmtr1'⟩ := hin
      cases hmtr1'
      case stepL s1'' htr1 hmtr1' =>
        exists s'
        have htr1' := LTS.mtr.single_invert lts _ _ _ hmtr1
        have hdets1 := hdet s1 μ s1' s1'' htr1' htr1
        rw [hdets1]
        exact hmtr1'
