/-
Copyright (c) 2026 Evgeny Zaprudnov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evgeny Zaprudnov
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Incidence columns over ZMod 2

An indexed undirected multigraph is specified by its two endpoint maps. The edge type
retains parallel edges as distinct indices, and both endpoints are counted, so a loop
has zero incidence column over ZMod 2.

The forest criterion below is the absence of a nonempty finite edge set with even
degree at every vertex. The reduced incidence result shows that deleting the row of
a distinguished root does not change column independence.
-/

@[expose] public section

namespace Incidence

variable {V E : Type*}
variable [DecidableEq V]
variable [Fintype E] [DecidableEq E]

/-- The contribution of one indexed edge to the degree parity at a vertex. -/
def entry (source target : E → V) (e : E) (v : V) : ZMod 2 :=
  (if source e = v then 1 else 0) + (if target e = v then 1 else 0)

/-- The ZMod 2 incidence column of an indexed edge. -/
def column (source target : E → V) (e : E) : V → ZMod 2 :=
  fun v => entry source target e v

/-- The indicator of a finite set of indexed edges, viewed over ZMod 2. -/
def edgeIndicator (F : Finset E) (e : E) : ZMod 2 :=
  if e ∈ F then 1 else 0

/-- The degree parity of a vertex in a finite set of indexed edges. -/
def degreeParity (source target : E → V) (F : Finset E) (v : V) : ZMod 2 :=
  ∑ e : E, edgeIndicator F e * entry source target e v

/-- Every nonempty finite edge set has a vertex of odd degree. -/
def IsForest (source target : E → V) : Prop :=
  ∀ F : Finset E, F.Nonempty → ∃ v : V, degreeParity source target F v ≠ 0

/-- Every element of ZMod 2 is either zero or one. -/
private theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A ZMod 2 coefficient function is the indicator of its nonzero support. -/
private theorem coefficient_eq_edgeIndicator (c : E → ZMod 2) :
    c = edgeIndicator (Finset.univ.filter fun e => c e ≠ 0) := by
  classical
  funext e
  by_cases he : c e = 0
  · simp [edgeIndicator, he]
  · have hc : c e = 1 := by
      rcases zmod_two_eq_zero_or_one (c e) with hzero | hone
      · exact (he hzero).elim
      · exact hone
    have hmem : e ∈ Finset.univ.filter (fun e => c e ≠ 0) := by
      simp [hc]
    simp [edgeIndicator, hmem, hc]

/-- The linear combination with coefficients 1_F is the degree-parity function. -/
private theorem combination_edgeIndicator
    (source target : E → V) (F : Finset E) :
    (∑ e : E, edgeIndicator F e • column source target e) =
      fun v => degreeParity source target F v := by
  classical
  ext v
  simp only [Finset.sum_apply, Pi.smul_apply, column, degreeParity, smul_eq_mul]

/-- The indexed incidence columns over ZMod 2 are linearly independent if and only if
every nonempty finite edge set has a vertex of odd degree.

The edge type keeps parallel edges distinct. A loop contributes twice at its endpoint
and therefore gives a zero column.
-/
theorem columns_linearIndependent_iff_isForest
    (source target : E → V) :
    LinearIndependent (ZMod 2) (column source target) ↔ IsForest source target := by
  classical
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h F hF
    by_contra hNoOdd
    have hEven : ∀ v : V, degreeParity source target F v = 0 := by
      intro v
      by_contra hv
      exact hNoOdd ⟨v, hv⟩
    let c : E → ZMod 2 := edgeIndicator F
    have hzero :
        (∑ e : E, c e • column source target e) = 0 := by
      rw [combination_edgeIndicator]
      funext v
      exact hEven v
    have hcoeff := h c hzero
    obtain ⟨e, he⟩ := hF
    have hnonzero : c e ≠ 0 := by
      simp [c, edgeIndicator, he]
    exact hnonzero (hcoeff e)
  · intro hForest c hzero
    by_contra hNotAllZero
    push Not at hNotAllZero
    obtain ⟨e, he⟩ := hNotAllZero
    let F : Finset E := Finset.univ.filter fun e => c e ≠ 0
    have hF : F.Nonempty := by
      refine ⟨e, ?_⟩
      simp [F, he]
    obtain ⟨v, hv⟩ := hForest F hF
    have hrep : c = edgeIndicator F := by
      simpa [F] using coefficient_eq_edgeIndicator c
    rw [hrep] at hzero
    have hpoint := congrFun hzero v
    rw [combination_edgeIndicator] at hpoint
    exact hv hpoint

/-- Reversing all edge orientations does not change the incidence-forest property. -/
theorem isForest_comm (source target : E → V) :
    IsForest source target ↔ IsForest target source := by
  constructor <;> intro h F hF
  · obtain ⟨v, hv⟩ := h F hF
    refine ⟨v, ?_⟩
    simpa [degreeParity, entry, add_comm] using hv
  · obtain ⟨v, hv⟩ := h F hF
    refine ⟨v, ?_⟩
    simpa [degreeParity, entry, add_comm] using hv

/-- The sum of the incidence entries of one edge is zero in ZMod 2. -/
private theorem entry_sum_vertices_eq_zero
    {V E : Type*} [Fintype V] [DecidableEq V]
    (source target : E → V) (e : E) :
    (∑ v : V, entry source target e v) = 0 := by
  classical
  norm_num [entry, Finset.sum_add_distrib]
  exact ZMod.natCast_self 2

/-- The sum of all vertex-degree parities is zero: every edge contributes two incidences. -/
theorem degreeParity_sum_vertices_eq_zero
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (source target : E → V) (F : Finset E) :
    (∑ v : V, degreeParity source target F v) = 0 := by
  classical
  simp only [degreeParity]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp [entry_sum_vertices_eq_zero]

/-- The reduced incidence column of an edge in a graph with an exterior root.
The endpoint none denotes the root, whose row is omitted. -/
def reducedColumn (source target : E → Option V) (e : E) : V → ZMod 2 :=
  fun v => entry source target e (some v)

/-- A finite edge-set combination of reduced incidence columns is the degree-parity
function restricted to the non-root vertices. -/
private theorem reducedCombination_edgeIndicator
    (source target : E → Option V) (F : Finset E) :
    (∑ e : E, edgeIndicator F e • reducedColumn source target e) =
      fun v => degreeParity source target F (some v) := by
  classical
  ext v
  simp only [Finset.sum_apply, Pi.smul_apply, reducedColumn, degreeParity, smul_eq_mul]

/-- Removing the exterior-root row preserves column independence over ZMod 2.
The omitted root coordinate is forced by the handshake-parity identity. -/
theorem reducedColumns_linearIndependent_iff_isForest
    {V E : Type*} [Finite V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (source target : E → Option V) :
    LinearIndependent (ZMod 2) (reducedColumn source target) ↔ IsForest source target := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h F hF
    by_contra hNoOdd
    have hEven : ∀ v : Option V, degreeParity source target F v = 0 := by
      intro v
      by_contra hv
      exact hNoOdd ⟨v, hv⟩
    have hzero :
        (∑ e : E, edgeIndicator F e • reducedColumn source target e) = 0 := by
      rw [reducedCombination_edgeIndicator]
      funext v
      exact hEven (some v)
    have hcoeff := h (edgeIndicator F) hzero
    obtain ⟨e, he⟩ := hF
    have hnonzero : edgeIndicator F e ≠ 0 := by
      simp [edgeIndicator, he]
    exact hnonzero (hcoeff e)
  · intro hForest c hzero
    by_contra hNotAllZero
    push Not at hNotAllZero
    obtain ⟨e, he⟩ := hNotAllZero
    let F : Finset E := Finset.univ.filter fun e => c e ≠ 0
    have hF : F.Nonempty := by
      refine ⟨e, ?_⟩
      simp [F, he]
    have hrep : c = edgeIndicator F := by
      simpa [F] using coefficient_eq_edgeIndicator c
    have hSome : ∀ v : V, degreeParity source target F (some v) = 0 := by
      intro v
      have hpoint := congrFun hzero v
      rw [hrep] at hpoint
      simpa only [Finset.sum_apply, Pi.smul_apply, reducedColumn, degreeParity,
        smul_eq_mul, Pi.zero_apply] using hpoint
    have htotal :
        (∑ v : Option V, degreeParity source target F v) = 0 :=
      degreeParity_sum_vertices_eq_zero source target F
    rw [Fintype.sum_option] at htotal
    have hsumSome :
        (∑ v : V, degreeParity source target F (some v)) = 0 := by
      simp [hSome]
    rw [hsumSome, add_zero] at htotal
    have hEven : ∀ v : Option V, degreeParity source target F v = 0 := by
      intro v
      cases v with
      | none => exact htotal
      | some v => exact hSome v
    obtain ⟨v, hv⟩ := hForest F hF
    exact hv (hEven v)

/-- An incidence forest cannot contain a loop. -/
theorem isForest_no_loop (source target : E → V)
    (hForest : IsForest source target) :
    ∀ e : E, source e ≠ target e := by
  classical
  intro e he
  let F : Finset E := {e}
  have hF : F.Nonempty := by simp [F]
  obtain ⟨v, hv⟩ := hForest F hF
  have hTwo : (1 : ZMod 2) + 1 = 0 := by
    calc
      (1 : ZMod 2) + 1 = (2 : ZMod 2) := by norm_num
      _ = 0 := ZMod.natCast_self 2
  have hEven : degreeParity source target F v = 0 := by
    by_cases htv : target e = v
    · simp [F, degreeParity, edgeIndicator, entry, he, htv, hTwo]
    · simp [F, degreeParity, edgeIndicator, entry, he, htv]
  exact hv hEven

/-- An incidence forest cannot contain distinct parallel edges. -/
theorem isForest_no_parallel_edges (source target : E → V)
    (hForest : IsForest source target) :
    ∀ e f : E, e ≠ f →
      (source e = source f ∧ target e = target f) ∨
      (source e = target f ∧ target e = source f) → False := by
  classical
  have hLI : LinearIndependent (ZMod 2) (column source target) :=
    (columns_linearIndependent_iff_isForest source target).2 hForest
  have hinj : Function.Injective (column source target) := hLI.injective
  intro e f hef hEndpoints
  apply hef
  apply hinj
  funext v
  rcases hEndpoints with hSame | hReverse
  · simp [column, entry, hSame.1, hSame.2]
  · simp [column, entry, hReverse.1, hReverse.2, add_comm]

/-- Coefficients on a reduced incidence forest are uniquely determined by their
incidence sum. -/
theorem reducedForest_coefficients_unique
    {V E : Type*} [Finite V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (source target : E → Option V)
    (hForest : IsForest source target)
    (c d : E → ZMod 2)
    (hEq :
      (∑ e : E, c e • reducedColumn source target e) =
      (∑ e : E, d e • reducedColumn source target e)) :
    c = d := by
  classical
  have hLI : LinearIndependent (ZMod 2) (reducedColumn source target) :=
    (reducedColumns_linearIndependent_iff_isForest source target).2 hForest
  rw [Fintype.linearIndependent_iff] at hLI
  have hzero :
      (∑ e : E, (c e - d e) • reducedColumn source target e) = 0 := by
    calc
      (∑ e : E, (c e - d e) • reducedColumn source target e)
          = ∑ e : E,
              (c e • reducedColumn source target e -
                d e • reducedColumn source target e) := by
              simp only [sub_smul]
      _ = (∑ e : E, c e • reducedColumn source target e) -
          (∑ e : E, d e • reducedColumn source target e) := by
            rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hEq, sub_self]
  have hcoeff := hLI (fun e => c e - d e) hzero
  funext e
  exact sub_eq_zero.mp (hcoeff e)

end Incidence
