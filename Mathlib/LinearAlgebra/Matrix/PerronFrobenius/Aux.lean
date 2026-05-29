/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.LinearAlgebra.Matrix.Spectrum.PerronFrobenius
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Analysis.Convex.StdSimplex

/-!
# Auxiliary results for Perron–Frobenius theory

Matrix–vector identities, simplex lemmas, and filter facts used in the Perron–Frobenius
development.

## Implementation notes

This file collects lemmas that are not yet in mathlib but are shared by several files in the
Perron–Frobenius chain.

## Tags

Perron–Frobenius theorem, standard simplex, matrix–vector product
-/

@[expose] public section

open Filter Set Finset Matrix Topology Convex

theorem eventually_to_open {α : Type*} [TopologicalSpace α] {p : α → Prop} {a : α}
    (h : ∀ᶠ x in 𝓝 a, p x) :
    ∃ U : Set α, IsOpen U ∧ a ∈ U ∧ ∀ x ∈ U, p x := by
  rcases mem_nhds_iff.mp h with ⟨U, hU_sub, hU_open, haU⟩
  exact ⟨U, hU_open, haU, hU_sub⟩

theorem continuousOn_finset_inf' {α β : Type*} [TopologicalSpace α] [LinearOrder β]
    [TopologicalSpace β] [OrderTopology β] {ι : Type*} {s : Finset ι} {U : Set α}
    (hs : s.Nonempty) {f : ι → α → β} (hf : ∀ i ∈ s, ContinuousOn (f i) U) :
    ContinuousOn (fun x => s.inf' hs (fun i => f i x)) U :=
  ContinuousOn.finset_inf'_apply hs hf

theorem finset_inf'_mono_subset {α β : Type*} [LinearOrder β] {s t : Finset α} (h : s ⊆ t)
    {f : α → β} {hs : s.Nonempty} {ht : t.Nonempty} :
    t.inf' ht f ≤ s.inf' hs f :=
  inf'_mono f h hs

theorem mulVec_nonneg {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {x : n → ℝ} (hx : ∀ i, 0 ≤ x i) : ∀ i, 0 ≤ (A *ᵥ x) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hx j)

theorem exists_pos_of_sum_one_of_nonneg {n : Type*} [Fintype n] [Nonempty n] {x : n → ℝ}
    (hsum : ∑ i, x i = 1) (hnonneg : ∀ i, 0 ≤ x i) : ∃ j, 0 < x j := by
  by_contra h
  push_neg at h
  have : ∑ i, x i = 0 := by simp [fun i => le_antisymm (h i) (hnonneg i)]
  linarith

theorem pow_mulVec_succ {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
    {A : Matrix n n ℝ} (k : ℕ) (x : n → ℝ) :
    (A ^ (k + 1)).mulVec x = A.mulVec ((A ^ k).mulVec x) := by
  simp only [mulVec_mulVec, pow_succ']

theorem iInf_apply_eq_finset_inf'_apply_fun {α β γ : Type*} [Fintype α] [Nonempty α]
    [ConditionallyCompleteLinearOrder γ] (f : α → β → γ) :
    (fun x => ⨅ i, f i x) =
      fun x =>
        (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i => f i x) := by
  ext x
  have h1 : ⨅ i, f i x = ⨅ i ∈ Set.univ, f i x := by simp only [mem_univ, ciInf_unique]
  have h2 : ⨅ i ∈ Set.univ, f i x = ⨅ i ∈ (Finset.univ : Finset α), f i x := by
    congr; ext i; simp only [mem_univ, ciInf_unique, Finset.mem_univ]
  have h3 :
      ⨅ i ∈ (Finset.univ : Finset α), f i x =
        (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i => f i x) := by
    rw [Finset.inf'_eq_csInf_image]
    simp only [ciInf_unique, Finset.mem_univ, Finset.coe_univ, image_univ]
    rfl
  rw [h1, h2, h3]

theorem mul_div_cancel_pos_right {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c : K} (h : a * b = c) (hb : 0 < b) : c / b = a := by
  rw [← h]
  exact mul_div_cancel_right₀ a hb.ne'

theorem continuousOn_iInf {α β : Type*} [Fintype α] [Nonempty α] [TopologicalSpace β]
    {s : Set β} {f : α → β → ℝ} (hf : ∀ i, ContinuousOn (f i) s) :
    ContinuousOn (fun x => ⨅ i, f i x) s := by
  classical
  let g : β → ℝ := fun x =>
    (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i => f i x)
  have hg : ContinuousOn g s := ContinuousOn.finset_inf'_apply Finset.univ_nonempty fun i _ => hf i
  rwa [iInf_apply_eq_finset_inf'_apply_fun f]

theorem sum_pos_of_mem {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℝ}
    (h_nonneg : ∀ a ∈ s, 0 ≤ f a) (a : α) (ha_mem : a ∈ s) (ha_pos : 0 < f a) :
    0 < ∑ x ∈ s, f x := by
  rw [← add_sum_erase s f ha_mem]
  exact add_pos_of_pos_of_nonneg ha_pos (Finset.sum_nonneg fun x hx =>
    h_nonneg x (Finset.mem_of_mem_erase hx))

lemma Finset.inf'_eq_ciInf {α β} [ConditionallyCompleteLinearOrder β] {s : Finset α}
    (h : s.Nonempty) (f : α → β) :
    s.inf' h f = ⨅ i : s, f i := by
  rw [Finset.inf'_eq_csInf_image]
  congr; ext x; simp [Set.mem_image, Set.mem_range]

variable {n : Type*}

lemma exists_pos_of_ne_zero [Fintype n] {v : n → ℝ} (h_nonneg : ∀ i, 0 ≤ v i)
    (h_ne_zero : v ≠ 0) : ∃ i, 0 < v i := by
  contrapose! h_ne_zero
  ext i
  exact le_antisymm (by simp_all) (h_nonneg i)

lemma Set.toFinset_nonempty_iff {α : Type*} [Fintype α] [DecidableEq α] (s : Set α)
    [Finite s] [Fintype s] :
    s.toFinset.Nonempty ↔ s.Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, Set.mem_toFinset.mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Set.mem_toFinset.mpr hx⟩

lemma div_le_iff {a b c : ℝ} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b := by
  rw [@le_iff_le_iff_lt_iff_lt]
  exact lt_div_iff₀ hb

lemma Finset.inf'_pos {α : Type*} {s : Finset α} (hs : s.Nonempty) {f : α → ℝ}
    (h_pos : ∀ a ∈ s, 0 < f a) :
    0 < s.inf' hs f := by
  obtain ⟨b, hb_mem, h_fb_is_inf⟩ := s.exists_mem_eq_inf' hs f
  rw [h_fb_is_inf]
  exact h_pos b hb_mem

lemma mulVec_apply {n : Type*} [Fintype n] {A : Matrix n n ℝ} {v : n → ℝ} (i : n) :
    (A *ᵥ v) i = ∑ j, A i j * v j :=
  rfl

lemma sum_pos_of_nonneg_of_ne_zero {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_nonneg : ∀ a ∈ s, 0 ≤ f a) (h_ne_zero : ∑ x ∈ s, f x ≠ 0) :
    0 < ∑ x ∈ s, f x :=
  lt_of_le_of_ne (Finset.sum_nonneg h_nonneg) h_ne_zero.symm

lemma Function.exists_ne_zero_of_ne_zero {α β} [Zero β] {f : α → β} (h : f ≠ fun _ => 0) :
    ∃ i, f i ≠ 0 := by
  contrapose! h
  ext x
  exact h x

lemma Nat.eq_one_or_one_lt (n : ℕ) (hn : n ≠ 0) : n = 1 ∨ 1 < n := by
  rcases n with _ | n
  · contradiction
  rcases n with _ | n
  · exact Or.inl rfl
  · exact Or.inr (Nat.succ_lt_succ (Nat.succ_pos _))

lemma Finset.inf'_eq_of_forall_le_of_exists_le {α β} [LinearOrder β] {s : Finset α}
    (hs : s.Nonempty) (f : α → β) (y : β) (h_le : ∀ i ∈ s, y ≤ f i)
    (h_exists : ∃ i ∈ s, f i = y) :
    s.inf' hs f = y := by
  apply le_antisymm
  · obtain ⟨i, hi_mem, hi_eq⟩ := h_exists
    rw [← hi_eq]
    exact inf'_le f hi_mem
  · exact (le_inf'_iff hs f).mpr h_le

lemma ne_zero_of_mem_stdSimplex {n : Type*} [Fintype n] [Nonempty n] {x : n → ℝ}
    (hx : x ∈ stdSimplex ℝ n) : x ≠ 0 := by
  intro h
  linarith [hx.2, show (∑ i, x i) = 0 from by subst h; simp]

namespace Matrix

lemma dotProduct_pos_of_pos_of_nonneg_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    {u v : n → ℝ} (hu_pos : ∀ i, 0 < u i) (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    0 < u ⬝ᵥ v := by
  obtain ⟨i, hi⟩ := exists_pos_of_ne_zero hv_nonneg hv_ne_zero
  exact sum_pos_of_mem (fun j _ => mul_nonneg (hu_pos j).le (hv_nonneg j)) i (Finset.mem_univ i)
    (mul_pos (hu_pos i) hi)

lemma dotProduct_smul_left {n : Type*} [Fintype n] (c : ℝ) (v w : n → ℝ) :
    (c • v) ⬝ᵥ w = c * (v ⬝ᵥ w) := by
  unfold dotProduct
  simp [smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm]

/-- `u ⬝ᵥ (A *ᵥ v) = (Aᵀ *ᵥ u) ⬝ᵥ v`. -/
lemma dotProduct_mulVec_comm {n : Type*} [Fintype n] [DecidableEq n] (u v : n → ℝ) (A : Matrix n n ℝ) :
    u ⬝ᵥ (A *ᵥ v) = (Aᵀ *ᵥ u) ⬝ᵥ v := by
  rw [dotProduct_mulVec, vecMul_eq_mulVec_transpose]

lemma diagonal_mulVec_ones {n : Type*} [DecidableEq n] [Fintype n] (d : n → ℝ) :
    diagonal d *ᵥ (fun _ => 1) = d := by
  ext i; simp [mulVec_diagonal]

lemma diagonal_inv_mulVec_self {n : Type*} [DecidableEq n] [Fintype n] {d : n → ℝ}
    (hd : ∀ i, d i ≠ 0) :
    diagonal (d⁻¹) *ᵥ d = fun _ => (1 : ℝ) := by
  ext i
  simp [mulVec_diagonal, IsUnit.inv_mul_cancel (isUnit_iff_ne_zero.mpr (hd i))]

end Matrix
