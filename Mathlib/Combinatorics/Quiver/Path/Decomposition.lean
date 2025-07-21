/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Tactic.Cases

/-!
# Path Decomposition and Boundary Crossing

This file provides lemmas for decomposing non-empty paths and for reasoning about paths that cross
the boundary of a given set of vertices `S`.

## Main results

* `Quiver.Path.eq_cons_of_ne_nil`: Any non-`nil` path can be written as `p'.cons e`.
* `Quiver.Path.eq_toPath_comp_of_ne_nil`: Any non-`nil` path can be written as `e.toPath.comp p'`.
* `Quiver.Path.exists_boundary_edge`: A path from a vertex outside a set `S` to a vertex inside `S`
  must contain a "boundary edge" `u ⟶ v` where `u ∉ S` and `v ∈ S`.
* `Quiver.Path.exists_crossing_edge`: A corollary of the above, guaranteeing the existence of such
  an edge without providing the full path decomposition.
-/


namespace Quiver.Path

open List

section PathDecomposition

variable {V : Type*} [Quiver V] {R : Type*}

/-- Every non-empty path can be decomposed as an initial path plus a final edge. -/
lemma eq_cons_of_ne_nil {a b : V} (p : Path a b) (h : p.length > 0) :
    ∃ (c : V) (p' : Path a c) (e : c ⟶ b), p = p'.cons e := by
  cases p with | nil => simp at h | cons p' e => exact ⟨_, p', e, rfl⟩

/-- Every non-empty path can be decomposed as a first edge plus a remaining path. -/
lemma eq_toPath_comp_of_ne_nil {a b : V} (p : Path a b) (h : p.length > 0) :
    ∃ (c : V) (e : a ⟶ c) (p' : Path c b), p = e.toPath.comp p' ∧ p.length = p'.length + 1 := by
  have h_len : p.length = (p.length - 1) + 1 := by omega
  obtain ⟨c, e, p', hp', rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p h_len
  use c, e, p'; exact ⟨rfl, by omega⟩

end PathDecomposition

section BoundaryEdges

variable {V : Type*} [Quiver V]

@[simp]
lemma cons_eq_comp_toPath {a b c : V} (p : Path a b) (e : b ⟶ c) :
    p.cons e = p.comp e.toPath := by
  rfl

/-- A path from a vertex not in `S` to a vertex in `S` must cross the boundary. -/
theorem exists_boundary_edge {a b : V} (p : Path a b) (S : Set V)
    (ha_not_in_S : a ∉ S) (hb_in_S : b ∈ S) :
    ∃ (u v : V) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      u ∉ S ∧ v ∈ S ∧ p = p₁.comp (e.toPath.comp p₂) := by
  induction' h_len : p.length with n ih generalizing a b S ha_not_in_S hb_in_S
  · have hab : a = b := eq_of_length_zero p h_len
    subst hab
    exact (ha_not_in_S hb_in_S).elim
  · have h_pos : 0 < p.length := by rw[h_len]; simp only [lt_add_iff_pos_left, add_pos_iff,
      Nat.lt_one_iff, pos_of_gt, or_true]
    obtain ⟨c, p', e, rfl⟩ := eq_cons_of_ne_nil p h_pos
    by_cases hc_in_S : c ∈ S
    · have p'_len : p'.length = n := by exact Nat.succ_inj.mp h_len
      obtain ⟨u, v, e_uv, p₁, p₂, hu_not_S, hv_S, hp'⟩ :=
        ih p' S ha_not_in_S hc_in_S p'_len
      refine ⟨u, v, e_uv, p₁, p₂.comp e.toPath, hu_not_S, hv_S, ?_⟩
      rw [cons_eq_comp_toPath, hp', Path.comp_assoc, Path.comp_assoc]
    · refine ⟨c, b, e, p', Path.nil, hc_in_S, hb_in_S, ?_⟩
      simp only [comp_nil]
      simp_all only [exists_and_left, cons_eq_comp_toPath, length_comp,
        lt_add_iff_pos_left, add_pos_iff, Nat.lt_add_one, or_true]

/-- A path from a vertex in `S` to a vertex not in `S` must cross the boundary. -/
theorem exists_boundary_edge_from_set {a b : V} (p : Path a b) (S : Set V)
    (ha_in_S : a ∈ S) (hb_not_in_S : b ∉ S) :
    ∃ (u v : V) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      u ∈ S ∧ v ∉ S ∧ p = p₁.comp (e.toPath.comp p₂) := by
  classical
  have ha_not_in_compl : a ∉ Sᶜ := by simpa
  have hb_in_compl : b ∈ Sᶜ := by simpa
  obtain ⟨u, v, e, p₁, p₂, hu_not_in_compl, hv_in_compl, hp⟩ :=
    exists_boundary_edge p Sᶜ ha_not_in_compl hb_in_compl
  refine ⟨u, v, e, p₁, p₂, ?_, ?_, hp⟩
  · simpa using hu_not_in_compl
  · simpa using hv_in_compl

/-- Corollary: there exists an edge crossing the boundary. -/
theorem exists_crossing_edge {a b : V} (p : Path a b) (S : Set V)
    (ha_not_in_S : a ∉ S) (hb_in_S : b ∈ S) :
    ∃ (u v : V) (_ : u ⟶ v), u ∉ S ∧ v ∈ S := by
  obtain ⟨u, v, e, _, _, hu_not_S, hv_S, _⟩ := exists_boundary_edge p S ha_not_in_S hb_in_S
  exact ⟨u, v, e, hu_not_S, hv_S⟩

end BoundaryEdges

end Quiver.Path
