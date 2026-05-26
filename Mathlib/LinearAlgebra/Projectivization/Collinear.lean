/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Bhavik Mehta
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import Mathlib.LinearAlgebra.Projectivization.Independence
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!

# Collinearity in Projective Space

This file defines collinearity of points in projective space and proves
the uniqueness of the line through two distinct points.

## Main Results

* `Projectivization.IsCollinear`: A family of points in projective space is collinear if there exists
  a submodule of dimension at most 2 containing all points in the family.
* `Projectivization.line_unique`: Given two distinct points in projective space, there is a unique
  line (submodule of dimension 2) containing both points.

## Tags
Projective space, collinearity, projective geometry

-/

@[expose] public section

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  (M : Submodule K V) (S : Set (Projectivization K V))

namespace Projectivization

/-- If there exists a submodule of dimension at most 2 containing all points in
  `S`, then `S` is collinear. The finite-dimensionality is required so that this notion is
  meaningful even when `V` is infinite-dimensional. -/
def IsCollinear : Prop := ∃ (M : Subspace K V), Module.Finite K M.submodule ∧
  Module.finrank K M.submodule ≤ 2 ∧ S ⊆ M

lemma IsCollinear_iff : IsCollinear S ↔ ∃ (M : Subspace K V), Module.Finite K M.submodule ∧
  Module.finrank K M.submodule ≤ 2 ∧ S ⊆ M := Iff.rfl

-- attribute [local instance] Fintype.ofFinite in
@[simp]
lemma isCollinear_empty : IsCollinear (∅ : Set (Projectivization K V)) := by
  obtain ⟨⟨ι, b⟩⟩ : Module.Free K V := Module.Free.of_divisionRing K V
  obtain hV | ⟨x, y, hxy⟩ : (Module.Finite K V ∧ Module.finrank K V < 2) ∨ (∃ a b : ι, a ≠ b) := by
    rcases subsingleton_or_nontrivial ι with hι | hι
    · let : Fintype ι := Fintype.ofFinite ι
      refine Or.inl ⟨Module.Finite.of_basis b, ?_⟩
      rw [Module.finrank_eq_card_basis b]
      have : Fintype.card ι ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hι
      omega
    · exact Or.inr hι.exists_pair_ne
  · have : Module.Finite K V := hV.1
    refine ⟨(⊤ : Submodule K V).projectivization, ?_, ?_, Set.empty_subset _⟩
    · rw [Subspace.submodule.apply_symm_apply]; infer_instance
    · rw [Subspace.submodule.apply_symm_apply, finrank_top]
      omega
  · refine ⟨(Submodule.span K {b x, b y}).projectivization, ?_, ?_, Set.empty_subset _⟩
    · rw [Subspace.submodule.apply_symm_apply]
      exact Module.Finite.span_of_finite _ (Set.toFinite _)
    · rw [Subspace.submodule.apply_symm_apply]
      classical
      grw [finrank_span_le_card]
      simp [Finset.card_le_two]

open scoped LinearAlgebra.Projectivization

lemma isCollinear_subset (s t : Set (ℙ K V)) (hst : s ⊆ t) (h : IsCollinear t) : IsCollinear s := by
  obtain ⟨M, hMfin, hM1, hM2⟩ := h
  exact ⟨M, hMfin, hM1, hst.trans hM2⟩

@[simp]
lemma isCollinear_singleton' (a : ℙ K V) : IsCollinear {a} := by
  induction a using ind with | h v hv =>
  refine ⟨(Submodule.span K {v}).projectivization, ?_, ?_, ?_⟩
  · rw [Subspace.submodule.apply_symm_apply]
    exact Module.Finite.span_of_finite _ (Set.toFinite _)
  · rw [Subspace.submodule.apply_symm_apply, finrank_span_singleton hv]
    omega
  · simp [Submodule.mem_span_of_mem]

lemma isCollinear_subsingleton (hS : S.Subsingleton) :
    IsCollinear S := by
  obtain hS' | ⟨x, hx⟩ := hS.eq_empty_or_singleton <;> simp_all

lemma isCollinear_pair (a b : ℙ K V) : IsCollinear {a, b} := by
  if h : a = b then simp [h] else
  induction a using Projectivization.ind with | h v hv =>
  induction b using Projectivization.ind with | h w hw =>
  change _ ≠ _ at h
  rw [← independent_pair_iff_ne, independent_mk_iff_LinearIndependent] at h
  refine ⟨(Submodule.span K {v, w}).projectivization, ?_, ?_, fun s hs ↦ hs.casesOn ?_ ?_⟩
  · rw [Subspace.submodule.apply_symm_apply]
    exact Module.Finite.span_of_finite _ (Set.toFinite _)
  · rw [Subspace.submodule.apply_symm_apply, ← Matrix.range_cons_cons_empty v w ![]]
    simp [finrank_span_eq_card h]
  all_goals rintro rfl; simp [Submodule.mem_span_of_mem]

lemma isCollinear_of_card_eq_two (hS : S.ncard = 2) : IsCollinear S := by
  obtain ⟨x, y, _, rfl⟩ := Set.ncard_eq_two.1 hS
  exact isCollinear_pair x y

lemma line_unique' {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) (huv : LinearIndependent K ![u, v])
    (p : Submodule K V) (hp1 : Module.finrank K p = 2)
    (hp2 : mk K u hu ∈ p.projectivization) (hp3 : mk K v hv ∈ p.projectivization) :
    p = Submodule.span K {u, v} := by
  have h1 : Submodule.span K {u, v} ≤ p := by
    refine Submodule.span_le.2 fun x hx ↦ ?_
    simp only [Submodule.mk_mem_projectivization_iff] at hp2 hp3
    refine hx.casesOn ?_ ?_ <;> simp_all
  have : Module.Finite K p := Module.finite_of_finrank_eq_succ hp1
  refine Submodule.eq_of_le_of_finrank_eq h1 ?_ |>.symm
  rw [hp1, ← Matrix.range_cons_cons_empty _ _ ![]]
  simp [finrank_span_eq_card huv]

lemma line_unique {x y : ℙ K V} (hxy : x ≠ y) (p q : Submodule K V) (hp1 : Module.finrank K p = 2)
    (hq1 : Module.finrank K q = 2) (hp2 : x ∈ p.projectivization) (hp3 : y ∈ p.projectivization)
    (hq2 : x ∈ q.projectivization) (hq3 : y ∈ q.projectivization) : p = q := by
  induction x using ind with | h v hv =>
  induction y using ind with | h w hw =>
  rw [← independent_pair_iff_ne, independent_mk_iff_LinearIndependent] at hxy
  rw [line_unique' hv hw hxy p hp1 hp2 hp3, line_unique' hv hw hxy q hq1 hq2 hq3]

end Projectivization
