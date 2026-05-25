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

# Colinearity in Projective Space

This file defines colinearity of points in projective space and proves
the uniqueness of the line through two distinct points.

## Main Results

* `Projectivization.IsColinear`: A family of points in projective space is colinear if there exists
  a submodule of dimension at most 2 containing all points in the family.
* `Projectivization.line_unique`: Given two distinct points in projective space, there is a unique
  line (submodule of dimension 2) containing both points.

## Tags
Projective space, colinearity, projective geometry

-/

@[expose] public section

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  (M : Submodule K V) (S : Set (Projectivization K V))

namespace Projectivization

/-- If there exists a submodule of dimension at most 2 containing all points in
  `S`, then `S` is colinear. The finite-dimensionality is required so that this notion is
  meaningful even when `V` is infinite-dimensional. -/
def IsColinear : Prop := ∃ (M : Subspace K V), Module.Finite K M.submodule ∧
  Module.finrank K M.submodule ≤ 2 ∧ S ⊆ M

lemma IsColinear_iff : IsColinear S ↔ ∃ (M : Subspace K V), Module.Finite K M.submodule ∧
  Module.finrank K M.submodule ≤ 2 ∧ S ⊆ M := Iff.rfl

@[simp]
lemma isColin_empty : IsColinear (∅ : Set (Projectivization K V)) := by
  obtain ⟨⟨ι, b⟩⟩ : Module.Free K V := Module.Free.of_divisionRing K V
  obtain hV | ⟨x, y, hxy⟩ : (Module.Finite K V ∧ Module.finrank K V < 2) ∨ (∃ a b : ι, a ≠ b) := by
    rcases subsingleton_or_nontrivial ι with hι | hι
    · have : Fintype ι := Fintype.ofFinite ι
      refine Or.inl ⟨Module.Finite.of_basis b, ?_⟩
      rw [Module.finrank_eq_card_basis b]
      have : Fintype.card ι ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hι
      omega
    · exact Or.inr hι.exists_pair_ne
  · haveI : Module.Finite K V := hV.1
    refine ⟨(⊤ : Submodule K V).projectivization, ?_, ?_, Set.empty_subset _⟩
    · rw [Subspace.submodule.apply_symm_apply]; infer_instance
    · rw [Subspace.submodule.apply_symm_apply, finrank_top]
      omega
  · refine ⟨(Submodule.span K {b x, b y}).projectivization, ?_, ?_, Set.empty_subset _⟩
    · rw [Subspace.submodule.apply_symm_apply]
      exact Module.Finite.span_of_finite _ (Set.toFinite _)
    · rw [Subspace.submodule.apply_symm_apply]
      convert le_of_eq <| @finrank_span_eq_card K V _ _ _ _ _ ({x, y} : Set ι)
        (Set.Finite.fintype <| Set.toFinite {x, y}) (b ∘ Subtype.val)
        (linearIndependent_comp_subtype_iff.2 <| b.linearIndepOn _)
      all_goals try simp
      exact (Set.card_insert {y} hxy).symm

open scoped LinearAlgebra.Projectivization

lemma isColin_subset (s t : Set (ℙ K V)) (hst : s ⊆ t) (h : IsColinear t) : IsColinear s := by
  obtain ⟨M, hMfin, hM1, hM2⟩ := h
  exact ⟨M, hMfin, hM1, hst.trans hM2⟩

@[simp]
lemma isColin_singleton' (a : ℙ K V) : IsColinear {a} := by
  induction a using ind with | h v hv =>
  refine ⟨(Submodule.span K {v}).projectivization, ?_, ?_, ?_⟩
  · rw [Subspace.submodule.apply_symm_apply]
    exact Module.Finite.span_of_finite _ (Set.toFinite _)
  · rw [Subspace.submodule.apply_symm_apply, finrank_span_singleton hv]
    omega
  · simp [Submodule.mem_span_of_mem]

lemma isColin_subsingleton (hS : S.Subsingleton) :
    IsColinear S := by
  obtain hS' | ⟨x, hx⟩ := hS.eq_empty_or_singleton <;> simp_all

lemma isColin_pair (a b : ℙ K V) : IsColinear {a, b} := by
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

lemma isColin_of_card_eq_two (hS : S.ncard = 2) : IsColinear S := by
  obtain ⟨x, y, _, rfl⟩ := Set.ncard_eq_two.1 hS
  exact isColin_pair x y

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
