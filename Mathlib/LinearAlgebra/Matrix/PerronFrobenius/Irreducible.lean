/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Lemmas
public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Uniqueness

/-!
# Perron–Frobenius for irreducible matrices

Existence, positivity, and uniqueness of the Perron eigenpair for irreducible non-negative
matrices.

## Main results

* `exists_positive_eigenvector_of_irreducible`: existence of a strictly positive Perron eigenvector.
* `pft_irreducible`: the full Perron–Frobenius theorem for irreducible matrices.
* `uniqueness_of_positive_eigenvector_gen`: uniqueness of the positive eigenvector up to scaling.

## References

* [E. Seneta, *Non-negative Matrices and Markov Chains*][seneta2006]

## Tags

Perron–Frobenius theorem, irreducible matrix, positive eigenvector
-/

@[expose] public section

namespace Matrix
open Quiver

open CollatzWielandt
variable {n : Type*} [DecidableEq n] {A : Matrix n n ℝ}

/-- If `A` is irreducible then so is `1 + A`. -/
theorem Irreducible.add_one (h_irred : A.IsIrreducible) : (1 + A).IsIrreducible := by
  let B := (1 : Matrix n n ℝ) + A
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_⟩
  · by_cases h : i = j
    · subst h
      simpa [B] using by
        have : (0 : ℝ) ≤ A i i := h_irred.1 i i
        linarith
    · simpa [B, h] using h_irred.1 i j
  · -- Work in the quiver of `A` to extract a positive-length path.
    letI : Quiver n := toQuiver A
    obtain ⟨pA, hpA_pos⟩ := h_irred.connected i j
    -- Any arrow in `A.toQuiver` is also an arrow in `(1 + A).toQuiver`.
    have map_edge : ∀ {u v : n}, (0 < A u v) → (0 < B u v) := by
      intro u v huv
      by_cases h_eq : u = v
      · subst h_eq
        have : (0 : ℝ) < 1 + A u u := by linarith
        simpa [B] using this
      · simpa [B, h_eq] using huv
    -- Lift paths from `toQuiver A` to `toQuiver B`, preserving length.
    let pA' : @Quiver.Path n (toQuiver A) i j := pA
    let rec liftPath_len :
      ∀ {u v : n} (p : @Quiver.Path n (toQuiver A) u v),
        Σ p' : @Quiver.Path n (toQuiver B) u v,
          PLift
            ((@Quiver.Path.length n (toQuiver B) u v p') =
              (@Quiver.Path.length n (toQuiver A) u v p))
      | u, _, @Quiver.Path.nil n (toQuiver A) u =>
          ⟨@Quiver.Path.nil n (toQuiver B) u, ⟨by simp⟩⟩
      | u, _, @Quiver.Path.cons n (toQuiver A) u b c p e =>
          let ⟨p', hp'⟩ := liftPath_len p
          have eA : 0 < A b c := e.down
          ⟨@Quiver.Path.cons n (toQuiver B) u b c p' ⟨map_edge eA⟩,
            ⟨by simp [hp'.down]⟩⟩
    obtain ⟨pB, hp_len⟩ := liftPath_len pA'
    have hpA_pos' : 0 < (@Quiver.Path.length n (toQuiver A) i j pA') := by
      simpa using hpA_pos
    have hpB_pos : 0 < (@Quiver.Path.length n (toQuiver B) i j pB) := by
      simpa [hp_len.down] using hpA_pos'
    -- Return a `B.toQuiver`-path witness.
    letI : Quiver n := toQuiver B
    have hpB_pos' : 0 < pB.length := by
      simpa using hpB_pos
    exact ⟨pB, hpB_pos'⟩

/-
A non-zero, non-negative eigenvector of an irreducible matrix is
in fact strictly positive.
-/
lemma eigenvector_no_zero_entries_of_irreducible [Fintype n] {r : ℝ} (hA_irred : A.IsIrreducible)
    (_ : 0 < r) {v : n → ℝ} (h_eig : A *ᵥ v = r • v) (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ∀ i, 0 < v i := by
  by_contra h_has_zero
  push Not at h_has_zero
  obtain ⟨i₀, hi₀_zero⟩ := h_has_zero
  let S : Set n := { i | 0 < v i }
  let T : Set n := { i | v i = 0 }
  have hS_nonempty : S.Nonempty := exists_pos_of_ne_zero hv_nonneg hv_ne_zero
  have hT_nonempty : T.Nonempty := ⟨i₀, by simp [T, le_antisymm hi₀_zero (hv_nonneg i₀)]⟩
  have hT_ne_univ : (T : Set n) ≠ Set.univ := by
    intro hT
    apply hv_ne_zero
    funext i
    have : i ∈ T := by simpa [hT] using (Set.mem_univ i)
    simpa [T] using this
  rcases Irreducible.exists_edge_out (A := A) hA_irred T hT_nonempty hT_ne_univ with
    ⟨j, hj_T, i, hi_not_T, hAji_pos⟩
  have vi_pos : 0 < v i :=
    lt_of_le_of_ne (hv_nonneg i) <| by
      have : v i ≠ 0 := by simpa [T] using hi_not_T
      simpa [eq_comm] using this
  have vj_zero : v j = 0 := by simpa [T] using hj_T
  have hji : A j i * v i = 0 := (Finset.sum_eq_zero_iff_of_nonneg (by
    intro k _
    exact mul_nonneg (hA_irred.1 j k) (hv_nonneg k))).1
      (by simpa [mulVec_apply, Pi.smul_apply, smul_eq_mul, vj_zero] using
            congr_fun h_eig j) i (Finset.mem_univ i)
  have hAji_zero : A j i = 0 := by
    exact (mul_eq_zero.mp hji).resolve_right vi_pos.ne'
  have : (0 : ℝ) < 0 := by
    simpa [hAji_zero] using hAji_pos
  exact this.false

variable [Fintype n]

/-- **Perron–Frobenius, irreducible case (Existence part)**
If `A` is a non-negative irreducible matrix, then there exists a
strictly positive eigenvalue `r > 0` and a strictly positive
eigenvector `v` (`∀ i, 0 < v i`) such that `A *ᵥ v = r • v`.

The proof uses the auxiliary matrix `B = 1 + A`, which is primitive,
to apply the Perron-Frobenius theorem for primitive matrices and translate
the result back to `A`. -/
theorem exists_positive_eigenvector_of_irreducible [Nonempty n] (hA_irred : A.IsIrreducible) :
    ∃ (r : ℝ) (v : n → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ A *ᵥ v = r • v := by
  -- 1.  We add the identity: `B := 1 + A`.
  let B : Matrix n n ℝ := 1 + A
  -- 1a.  Non-negativity of `B`.
  have hB_nonneg : ∀ i j, 0 ≤ B i j := by
    intro i j
    by_cases h : i = j
    · subst h
      simpa [B] using add_nonneg (show (0 : ℝ) ≤ 1 from zero_le_one) (hA_irred.1 i i)
    · simpa [B, h] using hA_irred.1 i j
  -- 1b.  Positive diagonal entries of `B`.
  have hB_diag_pos : ∀ i, 0 < B i i := by
    intro i
    simpa [B] using
      add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 1) (hA_irred.1 i i)
  -- 1c.  `B` is irreducible.
  have hB_irred : (1 + A).IsIrreducible := Irreducible.add_one (A := A) hA_irred
  -- 1d.  `B` is primitive.
  have hB_prim : B.IsPrimitive :=
    IsPrimitive.of_irreducible_pos_diagonal B hB_nonneg hB_irred hB_diag_pos
  -- 2.  Primitive Perron–Frobenius applied to `B`.
  obtain ⟨rB, v, hrB_pos, hv_pos, h_eig_B⟩ :=
    exists_positive_eigenvector_of_primitive (A := B) hB_prim hB_nonneg
  -- 3.  We translate the eigen-relation for `B` to one for `A`.
  have h_eig_A : A *ᵥ v = (rB - 1) • v := by
    have h_exp : v + A *ᵥ v = rB • v := by
      simpa [B, add_mulVec, one_mulVec] using h_eig_B
    have : A *ᵥ v = rB • v - v := eq_sub_of_add_eq' h_exp
    simpa [one_smul, sub_smul] using this
  -- 4.  We show that `rB - 1 > 0`.
  classical
  letI GA : Quiver n := toQuiver A
  -- 4a.  We find a positive entry of `A`.
  have h_pos_entry : ∃ i j, 0 < A i j := by
    let i₀ : n := Classical.arbitrary n
    obtain ⟨p₀, hp₀_len⟩ := hA_irred.connected i₀ i₀
    obtain ⟨j, e, -, -, -⟩ := Quiver.Path.path_decomposition_first_edge p₀ hp₀_len
    exact ⟨i₀, j, e.down⟩
  rcases h_pos_entry with ⟨i₀, j₀, hA_pos⟩
  -- 4b.  The `i₀`-component of `A * v` is positive.
  have hAv_i₀_pos : 0 < (A *ᵥ v) i₀ := by
    simpa [mulVec_apply] using
      (sum_pos_of_mem (s := (Finset.univ : Finset n))
        (fun k _ ↦ mul_nonneg (hA_irred.1 _ _) (le_of_lt (hv_pos k))) j₀ (by simp)
        (by simpa using mul_pos hA_pos (hv_pos j₀)))
  -- 4c.  We use the `i₀`-component of the eigen-equation for `B`.
  have : 0 < (rB - 1) * v i₀ := by
      simpa [h_eig_A, Pi.smul_apply, smul_eq_mul] using hAv_i₀_pos
  have hrA_pos : 0 < rB - 1 := by
    exact (mul_pos_iff_of_pos_right (hv_pos i₀)).1 this
  exact ⟨rB - 1, v, hrA_pos, hv_pos, h_eig_A⟩

/-! A non-zero, non-negative eigenvector of an irreducible matrix
  is in fact strictly positive. -/
lemma eigenvector_is_positive_of_irreducible {r : ℝ} (hA_irred : A.IsIrreducible)
    {v : n → ℝ} (h_eig : A *ᵥ v = r • v) (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ∀ i, 0 < v i := by
  by_contra h_has_nonpos
  push Not at h_has_nonpos
  rcases h_has_nonpos with ⟨i₀, hvi₀_le⟩
  let S : Set n := {i | 0 < v i}
  let T : Set n := {i | v i = 0}
  have h_partition : ∀ i, i ∈ S ↔ v i > 0 := by simp [S]
  have h_complement : ∀ i, i ∈ T ↔ v i = 0 := by simp [T]
  have hS_nonempty : S.Nonempty := exists_pos_of_ne_zero hv_nonneg hv_ne_zero
  have hT_nonempty : T.Nonempty := ⟨i₀, by simp [T, le_antisymm hvi₀_le (hv_nonneg i₀)]⟩
  have hvi₀0 : v i₀ = 0 := le_antisymm hvi₀_le (hv_nonneg i₀)
  have hS_ne_univ : (S : Set n) ≠ Set.univ := by
    intro hS
    have hi₀ : i₀ ∈ S := by simpa [hS] using (Set.mem_univ i₀)
    have : ¬ i₀ ∈ S := by simp [S, hvi₀0]
    exact this hi₀
  obtain ⟨j, i, hjT, hiS, hAji_pos⟩ := exists_connecting_edge_of_irreducible
      (A := A) hA_irred hv_nonneg S T hS_nonempty hT_nonempty h_partition h_complement
  have vj_zero : v j = 0 := by simpa [T] using hjT
  have h_sum_zero : (∑ k, A j k * v k) = 0 := by
    simpa [mulVec_apply, Pi.smul_apply, smul_eq_mul, vj_zero] using
      (congrArg (fun f : n → ℝ ↦ f j) h_eig)
  have h_all_zero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ ↦ mul_nonneg (hA_irred.1 j k) (hv_nonneg k))).1 h_sum_zero
  have h_Aji_vi_zero : A j i * v i = 0 := by
    simpa using h_all_zero i (by simp)
  have vi_pos : 0 < v i := by simpa [S] using hiS
  have h_Aji_zero : A j i = 0 := (mul_eq_zero.mp h_Aji_vi_zero).resolve_right vi_pos.ne'
  exact (lt_irrefl (0 : ℝ)) (by simp [h_Aji_zero] at hAji_pos)

variable [Nonempty n]

omit [DecidableEq n] [Fintype n] in
lemma Irreducible.exists_pos_entry (hA_irred : A.IsIrreducible) : ∃ i j : n, 0 < A i j := by
  letI : Quiver n := toQuiver A
  let i₀ : n := Classical.choice ‹Nonempty n›
  obtain ⟨p, hp⟩ := hA_irred.connected i₀ i₀
  obtain ⟨j, e, -, -, -⟩ := Quiver.Path.path_decomposition_first_edge p hp
  refine ⟨i₀, j, e.down⟩

/--
Given an irreducible non-negative matrix `A` and two strictly positive
eigenvectors for the same positive eigenvalue, they differ by a positive
scalar.
-/
theorem uniqueness_of_positive_eigenvector_gen {r : ℝ} (hA_irred : A.IsIrreducible)
    (hr_pos : 0 < r) {v w : n → ℝ} (hv_pos : ∀ i, 0 < v i) (hw_pos : ∀ i, 0 < w i)
    (hv_eig : A *ᵥ v = r • v) (hw_eig : A *ᵥ w = r • w) :
  ∃ c : ℝ, 0 < c ∧ v = c • w := by
  -- 1.  c := infᵢ (vᵢ / wᵢ)
  let c : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i : n ↦ v i / w i)
  have hc_pos : 0 < c :=
    Finset.inf'_pos Finset.univ_nonempty (fun i _ ↦ div_pos (hv_pos i) (hw_pos i))
  -- 2.  z := v − c•w  (still an eigenvector)
  let z : n → ℝ := v - c • w
  have hz_eig : A *ᵥ z = r • z := by
    calc
      A *ᵥ z
          = A *ᵥ v - A *ᵥ (c • w) := by
              simp only [mulVec_sub, z]
      _   = r • v - c • (r • w) := by
              simp only [hv_eig, mulVec_smul, hw_eig]
      _   = r • (v - c • w) := by
              rw [smul_sub, smul_comm, ← smul_assoc]
      _   = r • z := by
              simp only [z]
  -- 3.  z ≥ 0
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    have hmul : c * w i ≤ v i :=
      (le_div_iff₀ (hw_pos i)).1 <| by
        simpa [c] using
          (Finset.inf'_le (s := Finset.univ) (f := fun i : n ↦ v i / w i) (by simp))
    simpa [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using (sub_nonneg.mpr hmul)
  -- 4.  analyse `z`
  rcases eq_or_ne z 0 with hz_zero | hz_nonzero
  · -- 4a. (`z = 0`)  ⇒  `v = c • w`
    refine ⟨c, hc_pos, sub_eq_zero.mp (by simpa [z] using hz_zero)⟩
  · -- 4b. (`z ≠ 0`)  ⇒  contradiction
    have hz_pos : ∀ i, 0 < z i :=
      eigenvector_no_zero_entries_of_irreducible
        hA_irred hr_pos hz_eig hz_nonneg hz_nonzero
    -- the infimum is attained
    obtain ⟨i₀, _, h_inf_eq⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (fun i : n ↦ v i / w i)
    -- at the attaining index we must have `z i₀ = 0`, contradiction
    have hzi₀_zero : z i₀ = 0 := by
      have hw : w i₀ ≠ 0 := (hw_pos i₀).ne'
      have : v i₀ = c * w i₀ := (div_eq_iff hw).1 (by grind)
      simp [z, this, smul_eq_mul]
    have : 0 < z i₀ := hz_pos i₀
    have : (0 : ℝ) < 0 := by
      simp only [hzi₀_zero, lt_self_iff_false, z] at this
    simp_all only [div_pos_iff_of_pos_left, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, sub_nonneg, sub_pos, Finset.mem_univ, lt_self_iff_false, z, c]


/-- **Perron–Frobenius, primitive case (existence, positvity and uniqueness)** -/
theorem pft_primitive (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    ∃! (v : stdSimplex ℝ n), ∃ (r : ℝ) (_ : r > 0), A *ᵥ v.val = r • v.val := by
  obtain ⟨r, v_raw, hr_pos, hv_raw_pos, hv_raw_eig⟩ :=
    exists_positive_eigenvector_of_primitive hA_prim hA_nonneg
  let s : ℝ := ∑ i, v_raw i
  have hs_pos : 0 < s :=
    Finset.sum_pos (fun i _ ↦ hv_raw_pos i) Finset.univ_nonempty
  have hs_ne  : s ≠ 0 := ne_of_gt hs_pos
  let v0 : n → ℝ := s⁻¹ • v_raw
  have hv0_nonneg : ∀ i, 0 ≤ v0 i := fun i ↦ mul_nonneg (inv_nonneg.mpr (le_of_lt hs_pos)) (hv_raw_pos i).le
  have h_sum_v0 : ∑ i, v0 i = 1 := by
    calc
        ∑ i, v0 i
            = ∑ i, s⁻¹ * v_raw i := by simp [v0, smul_eq_mul]
        _ = s⁻¹ * ∑ i, v_raw i   := by
              rw [Finset.mul_sum]
        _ = s⁻¹ * s               := by simp [s]
        _ = 1                     := by field_simp [hs_ne]
  have hv0_simplex : v0 ∈ stdSimplex ℝ n := ⟨hv0_nonneg, h_sum_v0⟩
  have hv0_pos : ∀ i, 0 < v0 i := fun i ↦ mul_pos (inv_pos.mpr hs_pos) (hv_raw_pos i)
  have hv0_eig : A *ᵥ v0 = r • v0 := by
    calc
      A *ᵥ v0 = A *ᵥ (s⁻¹ • v_raw) := rfl
      _       = s⁻¹ • (A *ᵥ v_raw) := by rw [mulVec_smul]
      _       = s⁻¹ • (r • v_raw)  := by rw [hv_raw_eig]
      _       = r • (s⁻¹ • v_raw)  := by rw [smul_comm]
      _       = r • v0             := rfl
  refine ⟨⟨v0, hv0_simplex⟩, ⟨r, hr_pos, hv0_eig⟩, ?_⟩
  · intro w ⟨r', hr'_pos, hw_eig⟩
    have hw_pos : ∀ i, 0 < w.1 i :=
      eigenvector_of_primitive_is_positive hA_prim hr'_pos
        hw_eig w.property.1 (ne_zero_of_mem_stdSimplex w.property)
    let c : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i : n ↦ v0 i / w.1 i)
    obtain ⟨i₀, _, hc_eq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i : n ↦ v0 i / w.1 i)
    have v0_ge_cw : ∀ j, c * w.1 j ≤ v0 j :=
      fun j ↦ (le_div_iff₀ (hw_pos j)).mp (Finset.inf'_le _ (Finset.mem_univ j))
    have h_sum : c * (A *ᵥ w.1) i₀ ≤ (A *ᵥ v0) i₀ := by
      dsimp [Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have h := mul_le_mul_of_nonneg_left (v0_ge_cw j) (hA_nonneg i₀ j)
      rwa [mul_left_comm]
    have hw_i₀  : (A *ᵥ w.1) i₀ = r' * w.1 i₀ := by
      rw [hw_eig]
      simp only [Pi.smul_apply, smul_eq_mul]
    have v0_i₀_eq : v0 i₀ = c * w.1 i₀ := by
      have : c = v0 i₀ / w.1 i₀ := hc_eq
      have w_ne : w.1 i₀ ≠ 0 := ne_of_gt (hw_pos i₀)
      field_simp [this, w_ne]
      simp [*]
    have h_r_ge_r' : r ≥ r' := by
      have h_pos : 0 < c * w.1 i₀ := mul_pos
        (Finset.inf'_pos Finset.univ_nonempty (fun i _ ↦ div_pos (hv0_pos i) (hw_pos i))) (hw_pos i₀)
      have h1 : c * r' * w.1 i₀ ≤ r * v0 i₀ := by
        calc
          c * r' * w.1 i₀ = c * (r' * w.1 i₀)   := by ring
          _ = c * (A *ᵥ w.1) i₀                 := by rw [hw_i₀]
          _ ≤ (A *ᵥ v0) i₀                      := h_sum
          _ = r * v0 i₀                         := by rw [hv0_eig]; simp only [Pi.smul_apply, smul_eq_mul]
      have h2 : c * r' * w.1 i₀ ≤ r * (c * w.1 i₀) := by
        rwa [v0_i₀_eq] at h1
      have h2' : r' * (c * w.1 i₀) ≤ r * (c * w.1 i₀) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h2
      exact le_of_mul_le_mul_right h2' h_pos
    let d : ℝ := Finset.univ.inf' Finset.univ_nonempty
                   (fun i : n ↦ w.1 i / v0 i)
    obtain ⟨j₀, _, hd_eq⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (fun i : n ↦ w.1 i / v0 i)
    have w_ge_dv0 : ∀ j, d * v0 j ≤ w.1 j :=
      fun j ↦ (le_div_iff₀ (hv0_pos j)).mp (Finset.inf'_le _ (Finset.mem_univ j))
    have h_sum2 : d * (A *ᵥ v0) j₀ ≤ (A *ᵥ w.1) j₀ := by
      dsimp only [mulVec, dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have h := mul_le_mul_of_nonneg_left (w_ge_dv0 j) (hA_nonneg j₀ j)
      rwa [mul_left_comm]
    have w_j₀_eq : w.1 j₀ = d * v0 j₀ := by
      have v0_ne : v0 j₀ ≠ 0 := ne_of_gt (hv0_pos j₀)
      aesop
    have h_r'_ge_r : r' ≥ r := by
      have h1 : d * r * v0 j₀ ≤ r' * w.1 j₀ := by
        calc
          d * r * v0 j₀ = d * (r * v0 j₀) := by ring
          _ = d * (A *ᵥ v0) j₀ := by simp only [hv0_eig, Pi.smul_apply,
            smul_eq_mul]
          _ ≤ (A *ᵥ w.1) j₀ := h_sum2
          _ = r' * w.1 j₀ := by simp only [hw_eig, Pi.smul_apply,
            smul_eq_mul]
      have h2 : d * r * v0 j₀ ≤ r' * (d * v0 j₀) := by
        rwa [w_j₀_eq] at h1
      have h2' : r * (d * v0 j₀) ≤ r' * (d * v0 j₀) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h2
      exact (le_of_mul_le_mul_right h2' (mul_pos (Finset.inf'_pos Finset.univ_nonempty
         (fun i _ ↦ div_pos (hw_pos i) (hv0_pos i))) (hv0_pos j₀)))
    have hr_eq : r = r' := le_antisymm h_r'_ge_r h_r_ge_r'
    have hw_eig' : A *ᵥ w.1 = r • w.1 := by
      simp only [hw_eig, hr_eq]
    rcases uniqueness_of_positive_eigenvector hA_prim hr_pos v0 w.1 hv0_eig hw_eig' hv0_pos hw_pos
        with ⟨c', hc'_pos, hc'_eq⟩
    have hc'_one : c' = 1 := by
      have h_sum_w : ∑ i, w.1 i = 1 := w.property.2
      calc
        c' = c' * 1                 := by ring
        _  = c' * (∑ i, w.1 i)      := by rw [h_sum_w]
        _  = (∑ i, c' * w.1 i)      := by rw [Finset.mul_sum]
        _  = (∑ i, v0 i)            := by
               simp only [hc'_eq, Pi.smul_apply, smul_eq_mul]
        _  = 1                      := h_sum_v0
    ext i
    simp [hc'_eq, hc'_one]


open Quiver

/-- Perron–Frobenius theorem for irreducible real matrices (Existence, positivity, uniqueness).
Let A : Matrix n n ℝ be an irreducible nonnegative matrix
indexed by a finite nonempty type n.
Then there exists a unique eigenpair (v, r) where
  • v : stdSimplex ℝ n is a probability vector
    (i.e. v.val has nonnegative entries summing to 1),
  • r : ℝ is a positive scalar,
such that
  A *ᵥ v.val = r • v.val   and   r > 0.
Moreover, this eigenvector v in the standard simplex is unique,
and the corresponding eigenvalue r is the Perron root of A.
-/
theorem pft_irreducible {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA_irred : A.IsIrreducible) :
    ∃! (v : stdSimplex ℝ n), ∃ (r : ℝ), r > 0 ∧ A *ᵥ v.val = r • v.val := by
  let B : Matrix n n ℝ := 1 + A
  have hB_nonneg : ∀ i j, 0 ≤ B i j := by
    intro i j; by_cases h : i = j
    · subst h; simpa [B] using add_nonneg zero_le_one (hA_irred.1 i i)
    · simpa [B, h] using hA_irred.1 i j
  have hB_diag_pos : ∀ i, 0 < B i i := by
    intro i; simpa [B] using add_pos_of_pos_of_nonneg zero_lt_one (hA_irred.1 i i)
  have hB_irred : B.IsIrreducible := by
    simpa [B] using (Irreducible.add_one (A := A) hA_irred)
  have hB_prim : B.IsPrimitive :=
    IsPrimitive.of_irreducible_pos_diagonal B hB_nonneg hB_irred hB_diag_pos
  obtain ⟨v, hv_unique⟩ := pft_primitive hB_prim hB_nonneg
  obtain ⟨rB, hrB_pos, h_eig_B⟩ := hv_unique.1
  let r : ℝ := rB - 1
  have h_eig_A : A *ᵥ v.val = r • v.val := by
    have h_B_eig_expanded : (1 + A) *ᵥ v.val = rB • v.val := by simpa [B] using h_eig_B
    have h_A_eig_expanded : v.val + A *ᵥ v.val = rB • v.val :=
      by simpa [add_mulVec, one_mulVec] using h_B_eig_expanded
    simpa [r, sub_smul, one_smul] using (eq_sub_of_add_eq' h_A_eig_expanded)
  let v_pos := eigenvector_of_primitive_is_positive
      hB_prim hrB_pos h_eig_B v.2.1 (ne_zero_of_mem_stdSimplex v.2)
  obtain ⟨i₀, j₀, hA_pos⟩ := Irreducible.exists_pos_entry (A := A) hA_irred
  have h_nonneg : ∀ k ∈ Finset.univ, 0 ≤ A i₀ k * v.val k :=
    fun k _ ↦ mul_nonneg (hA_irred.1 _ _) (le_of_lt (v_pos k))
  have hAv_pos : 0 < (A *ᵥ v.val) i₀ := by
    simpa [mulVec_apply] using (sum_pos_of_mem (h_nonneg) j₀ (Finset.mem_univ _) (mul_pos hA_pos (v_pos _)))
  have : 0 < r * v.val i₀ := by
    simpa [Pi.smul_apply, smul_eq_mul, h_eig_A] using hAv_pos
  have hr_pos : 0 < r := (mul_pos_iff_of_pos_right (v_pos _)).1 this
  refine ⟨v, ⟨r, hr_pos, h_eig_A⟩, ?_⟩
  · intro v' ⟨r', hr'_pos, h_eig_A'⟩
    have h_eig_B' : B *ᵥ v'.val = (r' + 1) • v'.val := by
      simp [B, add_mulVec, one_mulVec, add_smul, one_smul, h_eig_A', add_comm]
    have h_rB_eq : rB = r' + 1 := by
      obtain ⟨i, hi_ne_zero⟩ := Function.exists_ne_zero_of_ne_zero (ne_zero_of_mem_stdSimplex v.property)
      have : (rB • v.val) i = ((r' + 1) • v.val) i := by
        rw [← h_eig_B, ← (hv_unique.2 v' ⟨r' + 1, by linarith, h_eig_B'⟩), h_eig_B']
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at this
      exact (mul_left_inj' hi_ne_zero).mp (this)
    have hr_eq : r = r' := by
      calc
        r = rB - 1 := by rfl
        _ = (r' + 1) - 1 := by rw [h_rB_eq]
        _ = r' := by ring
    obtain ⟨c, hc_pos, hcv⟩ := uniqueness_of_positive_eigenvector_gen
      hA_irred hr_pos (eigenvector_is_positive_of_irreducible
      hA_irred h_eig_A v.2.1 (ne_zero_of_mem_stdSimplex v.2)) (eigenvector_is_positive_of_irreducible
      hA_irred h_eig_A' v'.2.1 (ne_zero_of_mem_stdSimplex v'.2)) h_eig_A (by grind)
    have hc_one : c = 1 := by
      calc c
        _ = c * 1 := (mul_one c).symm
        _ = c * (∑ i, v'.val i) := by rw [v'.property.2]
        _ = ∑ i, c * v'.val i := by rw [Finset.mul_sum]
        _ = ∑ i, v.val i := by simp [hcv, smul_eq_mul]
        _ = 1 := v.property.2
    exact Subtype.val_injective (by simp [hcv, hc_one, one_smul])

end Matrix
