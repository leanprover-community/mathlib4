/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.Combinatorics.Quiver.Path.PerronFrobenius
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith

/-!
# Lemmas for Perron–Frobenius theory

Supporting lemmas on irreducible matrices, positive matrix–vector products, and quiver paths
used in the Collatz–Wielandt and Perron–Frobenius chain.

## Main results

* `path_exists_in_support_of_irreducible`: irreducibility yields connecting paths inside supports.
* `positive_mul_vec_of_nonneg_vec`: strictly positive matrices map non-negative vectors to
  positive vectors.
* `irreducible_mulVec_ne_zero`: irreducible matrices preserve non-zero non-negative vectors.

## Tags

irreducible matrix, quiver path, Perron–Frobenius theorem
-/

@[expose] public section

namespace Matrix
section PerronFrobenius

open Matrix Finset Quiver Quiver.Path

variable {n : Type*} {A : Matrix n n ℝ}

--open Quiver.Path

/-- A path in the submatrix `A.submatrix Subtype.val Subtype.val` lifts to a path in the
original quiver `toQuiver A`, and all vertices along that lifted path lie in `S`. -/
theorem path_in_submatrix_to_original (S : Set n) [DecidablePred S] {i j : S}
    (p : @Quiver.Path S (letI := Matrix.toQuiver A; inducedQuiver S) i j) :
  letI : Quiver n := Matrix.toQuiver A
  letI : Quiver S := inducedQuiver S
  ∃ p' : @Path n (Matrix.toQuiver A) i.val j.val,
    ∀ k, k ∈ p'.activeVertices → k ∈ S := by
  letI : Quiver n := Matrix.toQuiver A
  letI : Quiver S := inducedQuiver S
  let p' := (Subquiver.embedding S).mapPath p
  exact ⟨p', Subquiver.mapPath_embedding_vertices_in_set S p⟩


/-- A path exists between vertices in `S` when the submatrix on `S` is irreducible. -/
theorem path_exists_in_support_of_irreducible (S : Set n) [DecidablePred S]
    (hS : IsIrreducible (A.submatrix (Subtype.val : S → n) (Subtype.val : S → n)))
    (i j : n) (hi : i ∈ S) (hj : j ∈ S) :
  letI : Quiver n := Matrix.toQuiver A
  letI : Quiver S := inducedQuiver S
    ∃ p : Quiver.Path i j, ∀ k, k ∈ p.activeVertices → k ∈ S := by
  letI : Quiver n := Matrix.toQuiver A
  letI : Quiver S := inducedQuiver S
  let i' : S := ⟨i, hi⟩
  let j' : S := ⟨j, hj⟩
  have h_submatrix := hS.connected
  obtain ⟨p_sub, _hp_sub_pos⟩ := h_submatrix i' j'
  -- Convert the path in `toQuiver (A.submatrix ...)` to a path in the induced quiver on `S`.
  have p_sub' : @Quiver.Path S (letI := Matrix.toQuiver A; inducedQuiver S) i' j' := by
    -- Both quivers have the same arrows: `0 < A i.val j.val`.
    have conv : ∀ {a : S},
        @Quiver.Path S
            (Matrix.toQuiver (A.submatrix (Subtype.val : S → n) (Subtype.val : S → n))) i' a →
          @Quiver.Path S (letI := Matrix.toQuiver A; inducedQuiver S) i' a := by
      intro a p
      induction p with
      | nil =>
          exact Quiver.Path.nil
      | @cons b c p e ih =>
          refine Quiver.Path.cons ih ?_
          -- `e : 0 < (A.submatrix Subtype.val Subtype.val) _ _`, rewrite as `0 < A _ _`.
          simpa [Matrix.toQuiver, Matrix.submatrix_apply] using e
    exact conv p_sub
  obtain ⟨p, hp⟩ := path_in_submatrix_to_original S p_sub'
  exact ⟨p, hp⟩

lemma positive_mul_vec_pos [Fintype n] (hA_pos : ∀ i j, 0 < A i j) {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_ne_zero : x ≠ 0) : ∀ i, 0 < (A.mulVec x) i := by
  intro i
  --  `A.mulVec x i = ∑ j, A i j * x j`
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (le_of_lt (hA_pos i j)) (hx_nonneg j)
  · have : ∃ k, 0 < x k := by
      by_contra h_all_nonpos
      push Not at h_all_nonpos
      have h_zero : x = 0 := funext (fun j => le_antisymm (h_all_nonpos j) (hx_nonneg j))
      exact hx_ne_zero h_zero
    rcases this with ⟨k, hk_pos⟩
    refine ⟨k, ?_, ?_⟩
    · simp only [Finset.mem_univ]  --  `k ∈ Finset.univ`
    · exact mul_pos (hA_pos i k) hk_pos

variable {A : Matrix n n ℝ}

theorem positive_mul_vec_of_nonneg_vec [Fintype n] (hA_pos : ∀ i j, 0 < A i j) {v : n → ℝ}
    (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) : ∀ i, 0 < (A *ᵥ v) i := by
  intro i
  simp only [mulVec, dotProduct]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (le_of_lt (hA_pos i j)) (hv_nonneg j)
  · have : ∃ k, 0 < v k := by
      by_contra h_all_nonpos
      push Not at h_all_nonpos
      have h_zero : v = 0 := funext (fun j => le_antisymm (h_all_nonpos j) (hv_nonneg j))
      exact hv_ne_zero h_zero
    rcases this with ⟨k, hk_pos⟩
    refine ⟨k, Finset.mem_univ k, ?_⟩
    exact mul_pos (hA_pos i k) hk_pos

lemma path_exists_of_pos_entry {A : Matrix n n ℝ} {i j : n} (h_pos : 0 < A i j) :
  letI : Quiver n := toQuiver A
  ∃ p : Quiver.Path i j, 0 < p.length := by
  letI : Quiver n := toQuiver A
  refine ⟨(show i ⟶ j from ⟨h_pos⟩).toPath, ?_⟩
  simp [Quiver.Path.length_toPath]

lemma irreducible_of_all_entries_positive {A : Matrix n n ℝ} (hA : ∀ i j, 0 < A i j) :
  IsIrreducible A := by
  letI : Quiver n := toQuiver A
  refine ⟨fun i j => (hA i j).le, ?_⟩
  intro i j
  simpa using (path_exists_of_pos_entry (A := A) (i := i) (j := j) (h_pos := hA i j))

lemma exists_boundary_crossing_in_support [DecidableEq n] [Fintype n] (hA_irred : IsIrreducible A) (_ : ∀ i j, 0 ≤ A i j)
    {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) (_ : v ≠ 0) (S T : Set n) (hS_nonempty : S.Nonempty) (hT_nonempty : T.Nonempty)
    (h_partition : ∀ i, i ∈ S ↔ v i > 0) (h_complement : ∀ i, i ∈ T ↔ v i = 0) :
    ∃ (i j : n), i ∈ T ∧ j ∈ S ∧ 0 < A i j := by
  obtain ⟨i₀, hi₀_in_T⟩ := hT_nonempty
  obtain ⟨j₀, hj₀_in_S⟩ := hS_nonempty
  letI : Quiver n := toQuiver A
  obtain ⟨p, _hp_pos⟩ := hA_irred.connected i₀ j₀
  obtain ⟨y, z, e, _, _, hy_not_S, hz_in_S, _⟩ :=
    @Quiver.Path.exists_boundary_edge n (toQuiver A) _ _ p S
    (fun h_i0_in_S => by
      have hi₀_zero : v i₀ = 0 := (h_complement i₀).mp hi₀_in_T
      have hi₀_pos : v i₀ > 0 := (h_partition i₀).mp h_i0_in_S
      exact ne_of_gt hi₀_pos hi₀_zero)
    hj₀_in_S
  have hy_in_T : y ∈ T := by
    by_contra hy_not_T
    rcases lt_or_eq_of_le (hv_nonneg y) with h_pos | h_zero
    · exact hy_not_S ((h_partition y).mpr h_pos)
    · exact (hy_not_T ((h_complement y).mpr h_zero.symm)).elim
  exact ⟨y, z, hy_in_T, hz_in_S, by simpa using e.down⟩

theorem exists_connecting_edge_of_irreducible [DecidableEq n] [Fintype n] {A : Matrix n n ℝ}
    (hA_irred : A.IsIrreducible) {v : n → ℝ}
    (hv_nonneg : ∀ i, 0 ≤ v i) (S T : Set n) (hS_nonempty : S.Nonempty) (hT_nonempty : T.Nonempty)
    (h_partition : ∀ i, i ∈ S ↔ v i > 0) (h_complement : ∀ i, i ∈ T ↔ v i = 0) :
    ∃ (i j : n), i ∈ T ∧ j ∈ S ∧ 0 < A i j :=
  exists_boundary_crossing_in_support hA_irred hA_irred.1 hv_nonneg
    (by
      obtain ⟨i, hi⟩ := hS_nonempty
      intro h
      exact ((h_partition i).mp hi).ne' (congrFun h i))
    S T hS_nonempty hT_nonempty h_partition h_complement

theorem irreducible_mulVec_ne_zero [DecidableEq n] [Fintype n] (hA_irred : IsIrreducible A)
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA_ne_zero : A ≠ 0) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    A *ᵥ v ≠ 0 := by
  by_contra h_Av_zero
  let S : Set n := {i | v i > 0}
  let T : Set n := {i | v i = 0}
  have hS_nonempty : S.Nonempty := by
    by_contra hS_empty
    rw [Set.not_nonempty_iff_eq_empty] at hS_empty
    apply hv_ne_zero
    ext k
    have : v k ≤ 0 := by
      by_contra hv_pos
      have : k ∈ S := not_le.mp hv_pos
      rw [hS_empty] at this
      exact Set.notMem_empty k this
    exact le_antisymm this (hv_nonneg k)
  by_cases hT_is_empty : T = ∅
  · have v_all_pos : ∀ i, v i > 0 := by
      intro i
      have hi_not_in_T : i ∉ T := by simp [hT_is_empty]
      have hi_ne_zero : v i ≠ 0 := by simpa [T] using hi_not_in_T
      exact lt_of_le_of_ne (hv_nonneg i) (id (Ne.symm hi_ne_zero))
    have A_is_zero : A = 0 := by
      ext k j
      have : (A *ᵥ v) k = 0 := congrFun h_Av_zero k
      rw [mulVec, dotProduct] at this
      have terms_nonneg : ∀ idx, 0 ≤ A k idx * v idx :=
        fun idx => mul_nonneg (hA_nonneg k idx) (le_of_lt (v_all_pos idx))
      have term_kj_is_zero := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => terms_nonneg i)).mp this j (Finset.mem_univ _)
      exact (mul_eq_zero.mp term_kj_is_zero).resolve_right (v_all_pos j).ne'
    exact hA_ne_zero A_is_zero
  · have hT_nonempty : T.Nonempty := Set.nonempty_iff_ne_empty.mpr hT_is_empty
    obtain ⟨i, j, hi_T, hj_S, hA_ij_pos⟩ := exists_boundary_crossing_in_support
      hA_irred hA_nonneg hv_nonneg hv_ne_zero S T hS_nonempty hT_nonempty
      (fun i => by simp [S]) (fun i => by simp [T])
    have hA_ij_zero : A i j = 0 := by
      have : (A *ᵥ v) i = 0 := congrFun h_Av_zero i
      rw [mulVec, dotProduct] at this
      have terms_nonneg : ∀ k ∈ Finset.univ, 0 ≤ A i k * v k :=
        fun k _ => mul_nonneg (hA_nonneg i k) (hv_nonneg k)
      have term_j_is_zero := (Finset.sum_eq_zero_iff_of_nonneg terms_nonneg).mp this j (Finset.mem_univ _)
      have hv_j_pos : v j > 0 := by simp [S] at hj_S; exact hj_S
      exact (mul_eq_zero.mp term_j_is_zero).resolve_right (ne_of_gt hv_j_pos)
    exact (ne_of_gt hA_ij_pos) hA_ij_zero

variable --{n : Type*} [Fintype n] [DecidableEq n]
          {A : Matrix n n ℝ} {r : ℝ}

/-- A zero matrix is not irreducible if the dimension is greater than 1. -/
lemma not_irreducible_of_zero_matrix {n : Type*} [Fintype n] [Nonempty n]
    (h_card_gt_one : 1 < Fintype.card n) : ¬ IsIrreducible (0 : Matrix n n ℝ) := by
  intro h
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card h_card_gt_one
  -- Irreducibility gives a positive-length path in `toQuiver 0`.
  obtain ⟨p, hp_pos⟩ := h.connected i j
  -- But `toQuiver 0` has no arrows: `i ⟶ j` means `0 < 0`.
  cases p with
  | nil =>
      simp at hp_pos
  | cons p' e =>
      exact (lt_irrefl (0 : ℝ)) e.down

/-- If an irreducible matrix `A` has a row `i` where `A*v` is zero, then all entries `A i k` must be zero
    for `k` in the support of `v`. -/
lemma zero_block_of_mulVec_eq_zero_row [Fintype n] (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
   (S : Set n) (hS_def: S = {i | 0 < v i}) (i : n) (h_Av_i_zero : (A *ᵥ v) i = 0) : ∀ k ∈ S, A i k = 0 := by
  intro k hk_S_mem
  rw [mulVec, dotProduct] at h_Av_i_zero
  have h_sum_terms_nonneg : ∀ l, 0 ≤ A i l * v l :=
    fun l ↦ mul_nonneg (hA_nonneg i l) (hv_nonneg l)
  have h_Aik_vk_zero : A i k * v k = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun l _ ↦ h_sum_terms_nonneg l)).mp h_Av_i_zero k (mem_univ k)
  have vk_pos : 0 < v k := by rwa [hS_def] at hk_S_mem
  exact (mul_eq_zero.mp h_Aik_vk_zero).resolve_right (ne_of_gt vk_pos)

/-- For an irreducible matrix on a one-element type, the (unique) diagonal entry is positive. -/
lemma irreducible_one_element_implies_diagonal_pos [Fintype n]
    {A : Matrix n n ℝ} (hA_irred : IsIrreducible A)
    (h_card_one : Fintype.card n = 1) (i : n) :
    0 < A i i := by
  letI G := toQuiver A
  obtain ⟨p, hp_pos⟩ := hA_irred.connected i i
  obtain ⟨j, p', e, rfl⟩ := Quiver.Path.path_decomposition_last_edge p hp_pos
  have h_sub : Subsingleton n := by
    rcases (Fintype.card_eq_one_iff).1 h_card_one with ⟨a, ha⟩
    exact ⟨fun x y => by simp [ha x, ha y]⟩
  haveI : Subsingleton n := h_sub
  have hji : j = i := Subsingleton.elim _ _
  have e_pos : 0 < A j i := by simpa using e.down
  simpa [hji] using e_pos

/-- An irreducible matrix with a positive diagonal is primitive. -/
theorem IsPrimitive.of_irreducible_pos_diagonal [Fintype n] [Nonempty n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA_irred : IsIrreducible A)
    (hA_diag_pos : ∀ i, 0 < A i i) :
    IsPrimitive A := by
  let N := Fintype.card n
  have h_card_pos : 0 < N := Fintype.card_pos
  let k := (N - 1) * N + 1
  have hk_pos : 0 < k := by
    rcases Nat.eq_or_lt_of_le (Nat.one_le_of_lt h_card_pos) with hN | hN_lt
    · have h1 : N = 1 := by omega
      simp [k, h1]
    · omega
  constructor
  · exact hA_nonneg
  · use k, hk_pos
    intro i j
    letI : Quiver n := toQuiver A
    -- Convert the goal to existence of a length-`k` path in `toQuiver A`.
    rw [Matrix.pow_apply_pos_iff_nonempty_path (A := A) hA_nonneg k i j]
    obtain ⟨p_ij, hp_len_le⟩ : ∃ p : Path i j, p.length ≤ N - 1 := by
      obtain ⟨p_any, _hp_any_pos⟩ := hA_irred.connected i j
      let S := { len | ∃ (p : Path i j), p.length = len }
      have hS_nonempty : S.Nonempty := ⟨p_any.length, ⟨p_any, rfl⟩⟩
      classical
      let min_len := Nat.find hS_nonempty
      obtain ⟨p_shortest, h_shortest_len⟩ := Nat.find_spec hS_nonempty
      have h_shortest : ∀ (q : Path i j), p_shortest.length ≤ q.length := by
        intro q
        rw [h_shortest_len]
        exact Nat.find_min' hS_nonempty ⟨q, rfl⟩
      have h_simple : p_shortest.IsStrictlySimple := isStrictlySimple_of_shortest p_shortest h_shortest
      use p_shortest
      have h_len : p_shortest.length ≤ N - 1 := by
        have h := @Quiver.Path.length_le_card_minus_one_of_isSimple n _ _ _ i j p_shortest h_simple
        simpa [N] using h
      exact h_len
    let e_loop : i ⟶ i := ⟨hA_diag_pos i⟩
    let p_loop : Path i i := e_loop.toPath
    have p_loop_len : p_loop.length = 1 := by simp [p_loop, e_loop, Quiver.Path.length_toPath]
    let num_loops := k - p_ij.length
    have h_num_loops_nonneg : p_ij.length ≤ k := by
      dsimp [k]
      have h_card_ge_one : 1 ≤ N := Nat.one_le_of_lt h_card_pos
      have h_len_le : ↑p_ij.length ≤ ↑(N - 1) := Nat.cast_le.mpr hp_len_le
      have h_k_ge : ↑((N - 1) * N + 1) ≥ ↑(N - 1) * 1 + 1 := by
        gcongr
      linarith
    let p_final := (Path.replicate num_loops p_loop).comp p_ij
    refine ⟨⟨p_final, ?_⟩⟩
    rw [Path.length_comp, Path.length_replicate, p_loop_len, mul_one,
      Nat.sub_add_cancel h_num_loops_nonneg]

/-- If a path between two points in a set `S` must leave `S`, irreducibility guarantees
a path from the exit point back to an entry point. -/
private lemma exists_path_back_to_set
    (hA_irred : A.IsIrreducible) (S : Set n)
    {u v : n} (hu : u ∈ S) (hv : v ∉ S) :
    letI : Quiver n := A.toQuiver
    ∃ (i j : n) (p : Path i j),
      i ∈ S ∧ j ∉ S ∧ (∀ k, k ∈ p.vertices.tail → k ∉ S) := by
  letI : Quiver n := A.toQuiver
  letI : DecidablePred (· ∈ S) := Classical.decPred _
  obtain ⟨p, _hp_pos⟩ := hA_irred.connected u v
  obtain ⟨i, j, e, _p₁, _p₂, hi, hj, _hp⟩ :=
    Quiver.Path.exists_boundary_edge_from_set p S hu hv
  refine ⟨i, j, e.toPath, hi, hj, ?_⟩
  intro k hk
  -- `e.toPath.vertices.tail = [j]`.
  have hk_mem : k ∈ ([j] : List n) := by
    simpa [Quiver.Path.vertices_toPath_tail] using hk
  have hk_eq : k = j := by
    simpa [List.mem_singleton] using hk_mem
  subst hk_eq
  exact hj

/-- If `A` is irreducible, any two vertices of the same strongly–connected
component `S` can be joined by a path **staying inside** `S`. -/
lemma path_exists_in_component {A : Matrix n n ℝ}
    (S : Set n) [DecidablePred (· ∈ S)]
    (hS_strong_conn :
      letI : Quiver n := A.toQuiver;
      letI : Quiver S := inducedQuiver S;
      Quiver.IsSStronglyConnected S)
    (i j : n) (hi : i ∈ S) (hj : j ∈ S) :
    letI : Quiver n := A.toQuiver
    ∃ p : Path i j, ∀ k, k ∈ p.vertices → k ∈ S := by
  letI : Quiver n := A.toQuiver
  letI G_S : Quiver S := inducedQuiver S
  let i' : S := ⟨i, hi⟩
  let j' : S := ⟨j, hj⟩
  obtain ⟨p_sub, _hp_pos⟩ := by
    letI : Quiver n := A.toQuiver
    letI : Quiver S := inducedQuiver S
    exact hS_strong_conn i' j'
  let p := Prefunctor.mapPath (Quiver.Subquiver.embedding S) p_sub
  refine ⟨p, ?_⟩
  intro k hk
  have hka : k ∈ p.activeVertices :=
    mem_vertices_to_active hk
  exact (Quiver.Subquiver.mapPath_embedding_vertices_in_set S p_sub _ hka)

lemma Irreducible.exists_edge_out {A : Matrix n n ℝ}
    (hA_irred : A.IsIrreducible)
    (S : Set n) (hS_ne_empty : S.Nonempty) (hS_ne_univ : S ≠ Set.univ) :
    ∃ (i : n) (_ : i ∈ S) (j : n) (_ : j ∉ S), 0 < A i j := by
  letI G := toQuiver A
  obtain ⟨i, hi⟩ := hS_ne_empty
  obtain ⟨j, hj_compl⟩ := Set.nonempty_compl.mpr hS_ne_univ
  obtain ⟨p, _hp_pos⟩ := hA_irred.connected i j
  have hj : j ∉ S := by simpa using hj_compl
  obtain ⟨u, v, e, _p₁, _p₂, hu_in_S, hv_not_in_S, _hp⟩ :=
    Quiver.Path.exists_boundary_edge_from_set p S hi hj
  exact ⟨u, hu_in_S, v, hv_not_in_S, by simpa using e.down⟩

-- Lemma: Simple paths have bounded length by vertex count
lemma length_bounded_by_support_size [Quiver n] [DecidableEq n] [Fintype n] {_ : Matrix n n ℝ}
    {support : Set n} [DecidablePred (· ∈ support)] (_ : Set.Finite support)
    {i j : n} (p : Path i j)
    (hp_support : ∀ k, k ∈ p.vertices → k ∈ support) (hp_simple : IsStrictlySimple p) :
    p.length < support.toFinite.toFinset.card := by
  have h_subset : p.vertexFinset ⊆ support.toFinite.toFinset := by
    intro v hv
    simp only [Set.Finite.mem_toFinset]
    exact hp_support v (List.mem_toFinset.mp hv)
  have h_card := card_vertexFinset_of_isStrictlySimple hp_simple
  have h_card_le := Finset.card_le_card h_subset
  rw [h_card] at h_card_le
  exact h_card_le


lemma reachable_in_support_closed [DecidableEq n]
    {A : Matrix n n ℝ}
    (support : Set n) [DecidablePred (· ∈ support)] :
    letI : Quiver n := Matrix.toQuiver A
    let R := { k | ∃ (i : n) (_ : i ∈ support) (p : Path i k),
                    ∀ v, v ∈ p.vertices → v ∈ support }
    R = support := by
  letI : Quiver n := Matrix.toQuiver A
  let R := { k | ∃ (i : n) (hi : i ∈ support) (p : Path i k),
                  ∀ v, v ∈ p.vertices → v ∈ support }
  apply Set.Subset.antisymm
  · intro k hkR
    rcases hkR with ⟨i, hi, p, hp⟩
    have : k ∈ p.vertices := end_mem_vertices p
    exact hp k this
  · intro k hk_supp
    refine ⟨k, hk_supp, (Path.nil : Path k k), ?_⟩
    intro v hv
    simp [Quiver.Path.vertices_nil] at hv
    subst hv; exact hk_supp

/-!
If the principal sub-matrix supported on `support` is irreducible,
then any two vertices in `support` can be joined by a path that
stays *inside* `support`.
-/
lemma path_exists_in_support
    (support : Set n) [DecidablePred (· ∈ support)]
    (h_sub_irred :
      (A.submatrix (Subtype.val : support → n) (Subtype.val : support → n)).IsIrreducible)
    {i j : n} (hi : i ∈ support) (hj : j ∈ support) :
    letI : Quiver n := Matrix.toQuiver A
    ∃ p : Quiver.Path i j, ∀ k, k ∈ p.activeVertices → k ∈ support := by
  classical
  simpa using
    Matrix.path_exists_in_support_of_irreducible
      (A := A) (S := support) h_sub_irred i j hi hj

end PerronFrobenius

end Matrix
