/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Tactic.Cases

/-!
# Path Decomposition and Boundary Crossing

This section provides lemmas for decomposing non-empty paths and for reasoning about paths that
cross the boundary of a given set of vertices `S`.
-/
namespace Quiver.Path

open List

section Decomposition

lemma length_ne_zero_iff_eq_comp (p : Path a b) :
    p.length ≠ 0 ↔ ∃ (c : V) (e : a ⟶ c) (p' : Path c b),
      p = e.toPath.comp p' ∧ p.length = p'.length + 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h_len : p.length = (p.length - 1) + 1 := by omega
    obtain ⟨c, e, p', hp', rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p h_len
    exact ⟨c, e, p', rfl, by omega⟩
  · rintro ⟨c, p', e, rfl, h⟩
    simp [h]

end Decomposition

section BoundaryEdges

variable {V : Type*} [Quiver V]

/-- A path from a vertex not in `S` to a vertex in `S` must cross the boundary. -/
theorem exists_notMem_mem_hom_path_path_of_notMem_mem {a b : V} (p : Path a b) (S : Set V)
    (ha_not_in_S : a ∉ S) (hb_in_S : b ∈ S) :
    ∃ᵉ (u ∉ S) (v ∈ S) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      p = p₁.comp (e.toPath.comp p₂) := by
  induction' h_len : p.length with n ih generalizing a b S ha_not_in_S hb_in_S
  · obtain rfl := eq_of_length_zero p h_len
    exact (ha_not_in_S hb_in_S).elim
  · have h_pos : 0 < p.length := by rw[h_len]; simp only [lt_add_iff_pos_left, add_pos_iff,
      Nat.lt_one_iff, pos_of_gt, or_true]
    have h_ne : p.length ≠ 0 := ne_of_gt h_pos
    obtain ⟨c, p', e, rfl⟩ := (length_ne_zero_iff_eq_cons p).mp h_ne
    by_cases hc_in_S : c ∈ S
    · have p'_len : p'.length = n := by simp_all
      obtain ⟨u, hu_not_S, v, hv_S, e_uv, p₁, p₂, hp'⟩ :=
        ih p' S ha_not_in_S hc_in_S p'_len
      refine ⟨u, hu_not_S, v, hv_S, e_uv, p₁, p₂.comp e.toPath, ?_⟩
      simp [hp', comp_toPath_eq_cons]
    · refine ⟨c, hc_in_S, b, hb_in_S, e, p', Path.nil, ?_⟩
      simp [comp_toPath_eq_cons]

theorem exists_mem_notMem_hom_path_path_of_notMem_mem {a b : V} (p : Path a b) (S : Set V)
    (ha_in_S : a ∈ S) (hb_not_in_S : b ∉ S) :
    ∃ᵉ (u ∈ S) (v ∉ S) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      p = p₁.comp (e.toPath.comp p₂) := by
  classical
  have ha_not_in_compl : a ∉ Sᶜ := by simpa
  have hb_in_compl : b ∈ Sᶜ := by simpa
  obtain ⟨u, hu_not_in_compl, v, hv_in_compl, e, p₁, p₂, hp⟩ :=
    exists_notMem_mem_hom_path_path_of_notMem_mem p Sᶜ ha_not_in_compl hb_in_compl
  simp at hu_not_in_compl hv_in_compl
  refine ⟨u, hu_not_in_compl, v, hv_in_compl, e, p₁, p₂, hp⟩

/-- Corollary: there exists an edge crossing the boundary. -/
theorem exists_notMem_mem_hom_of_notMem_mem {a b : V} (p : Path a b) (S : Set V)
    (ha_not_in_S : a ∉ S) (hb_in_S : b ∈ S) :
    ∃ (u v : V) (_ : u ⟶ v), u ∉ S ∧ v ∈ S := by
  obtain ⟨u, hu_not_S, v, hv_S, e, _, _⟩ :=
    exists_notMem_mem_hom_path_path_of_notMem_mem p S ha_not_in_S hb_in_S
  exact ⟨u, v, e, hu_not_S, hv_S⟩

end BoundaryEdges

end Quiver.Path
