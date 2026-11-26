/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Gareth Ma, Seewoo Lee
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Algebra.Module.ZLattice.RootLattice.D
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Basic properties of the E₈ lattice

We define the E₈ lattice as the set of vectors in `ℝ⁸` whose coordinates are either all integers
or all half-integers, and whose coordinates sum to an even integer (`Submodule.E8`). We show that it
is the `ℤ`-span of the rows of an explicit matrix (`E8Matrix`), and prove various properties of the
E₈ lattice.

This code is based on results from the Sphere Packing project, see https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/03cb63c9bf51a7c879f5ace0d88fc784c6e84121/SpherePacking/Basic/E8.lean, which was itself inspired by prioir work by Gareth Ma, see https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/42c839d1002f5bcc1f8d2eb73190d97cd9c52852/SpherePacking/Basic/E8.lean

## Main declarations

* `Submodule.E8`: The `E₈` lattice as a submodule of `Fin 8 → R` for a field `R` in which `2` is
  nonzero. We define it to be the set of vectors in `Fin 8 → R` such that the sum of coordinates is
  even, and either all coordinates are integers, or all coordinates are half of an odd integer.
* `Submodule.E8_eq_sup`: The `E₈` lattice can be seen as "two copies of `D₈`". It is equal to the
  lattice spanned by the checkerboard lattice `D₈` and the vector `(2⁻¹,...,2⁻¹)`.
* `E8Matrix`: An explicit matrix whose rows form a basis for the E₈ lattice over ℤ.
* `E8Matrix_unimodular`: A proof that `E8Matrix` has determinant 1.
* `span_E8Matrix_eq_top`: The `ℝ`-span of `E8Matrix` is the whole of `ℝ⁸`.
* `span_E8Matrix`: The `ℤ`-span of `E8Matrix` is the E₈ lattice. This is the third characterisation
  of the E₈ lattice given in this file.
* `covolume_E8`: The E₈ lattice in `Fin 8 → ℝ` has covolume `1`.
* `E8Lattice`: The E₈ lattice as a submodule of eight-dimensional Euclidean space. This additional
  definition is valuable, since it now puts the correct metric space structure on the lattice.
* `isEven_E8Lattice`: The E₈ lattice is even, i.e., the norm-squared of any vector in E₈ is an even
  integer.
* `isIntegral_E8Lattice`: The E₈ lattice is integral, i.e., the inner product of any two vectors in
  E₈ is an integer.
* `covolume_E8Lattice`: `E8Lattice` has covolume `1`.

## TODO

* Add `E₆` and `E₇` lattices.
* Relate with Cartan matrices of type E.
-/

@[expose] public section

variable {R : Type*}

open Module

/-- The `E₈` lattice as a `ℤ`-submodule of `Fin 8 → R`: the vectors whose coordinates are either
all integers or all halves of odd integers, and whose coordinates sum to an even integer. -/
def Submodule.E8 (R : Type*) [Field R] [NeZero (2 : R)] :
    Submodule ℤ (Fin 8 → R) where
  carrier :=
    {v | ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i)) ∧ ∑ i, v i ≡ 0 [PMOD 2]}
  add_mem' := by
    simp only [Set.mem_ofPred_eq, and_imp, nsmul_eq_mul, Nat.cast_ofNat, Pi.add_apply]
    rintro a b ha has hb hbs
    refine ⟨?_, by simpa [Finset.sum_add_distrib] using has.add hbs⟩
    obtain ha | ha := ha <;> obtain hb | hb := hb
    · refine .inl fun i ↦ ?_
      obtain ⟨a', ha⟩ := ha i
      obtain ⟨b', hb⟩ := hb i
      exact ⟨a' + b', by simp [ha, hb]⟩
    · refine .inr fun i ↦ ?_
      obtain ⟨a', ha⟩ := ha i
      obtain ⟨b', hb', hb⟩ := hb i
      exact ⟨2 * a' + b', Even.add_odd (by simp) hb', by simp [← ha, ← hb, mul_add]⟩
    · refine .inr fun i ↦ ?_
      obtain ⟨a', ha', ha⟩ := ha i
      obtain ⟨b', hb⟩ := hb i
      exact ⟨a' + 2 * b', ha'.add_even (by simp), by simp [ha, hb, mul_add]⟩
    · refine .inl fun i ↦ ?_
      obtain ⟨a', ha', ha⟩ := ha i
      obtain ⟨b', hb', hb⟩ := hb i
      obtain ⟨k, hk⟩ := ha'.add_odd hb'
      have := congrArg (Int.cast : ℤ → R) hk
      push_cast [ha, hb] at this
      exact ⟨k, mul_left_cancel₀ (NeZero.ne (2 : R)) (by linear_combination -this)⟩
  zero_mem' := ⟨.inl fun _ ↦ ⟨0, by simp⟩, by simp⟩
  smul_mem' := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Set.mem_ofPred_eq, zsmul_eq_mul, Pi.mul_apply,
      Pi.intCast_apply, and_imp]
    intro c a ha has
    refine ⟨?_, by simpa [← Finset.mul_sum] using has.zsmul' (z := c)⟩
    obtain ha | ha := ha
    · refine .inl fun i ↦ ?_
      obtain ⟨a, ha⟩ := ha i
      exact ⟨c * a, by simp [ha]⟩
    obtain ⟨c, rfl⟩ | hc := c.even_or_odd
    · refine .inl fun i ↦ ?_
      obtain ⟨j, -, hj⟩ := ha i
      exact ⟨c * j, by push_cast [hj]; ring⟩
    · refine .inr fun i ↦ ?_
      obtain ⟨j, hj, hj'⟩ := ha i
      exact ⟨c * j, hc.mul hj, by push_cast [hj']; ring⟩

lemma Submodule.mem_E8 {R : Type*} [Field R] [NeZero (2 : R)] {v : Fin 8 → R} :
    v ∈ E8 R ↔
      ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i))
        ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  simp [E8]

lemma Submodule.mem_E8' {R : Type*} [Field R] [NeZero (2 : R)] {v : Fin 8 → R} :
    v ∈ E8 R ↔
      ((∀ i, ∃ n : ℤ, Even n ∧ n = 2 • v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i))
        ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  have (k : R) : (∃ n : ℤ, Even n ∧ n = 2 • k) ↔ (∃ n : ℤ, n = k) :=
    ⟨fun ⟨n, ⟨⟨l, hl⟩, hn⟩⟩ ↦ ⟨l, by simpa [← two_mul, hl, NeZero.ne (2 : R)] using hn⟩,
     fun ⟨n, hn⟩ ↦ ⟨2 * n, ⟨even_two_mul n, by simp [hn]⟩⟩⟩
  simp_rw [this, mem_E8]

lemma Submodule.mem_E8'' {R : Type*} [Field R] [NeZero (2 : R)] {v : Fin 8 → R} :
    v ∈ E8 R ↔
      ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, n + 2⁻¹ = v i))
        ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  have key (x : R) : (∃ n : ℤ, Odd n ∧ n = 2 • x) ↔ ∃ n : ℤ, n + 2⁻¹ = x := by
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, hn⟩
      refine ⟨k, ?_⟩
      push_cast [two_nsmul] at hn
      linear_combination 2⁻¹ * hn - (k - x) * inv_mul_cancel₀ (NeZero.ne (2 : R))
    · rintro ⟨k, rfl⟩
      exact ⟨2 * k + 1, by simp, by simp [NeZero.ne]⟩
  simp_rw [mem_E8, key]

theorem Submodule.E8_eq_sup (R : Type*) [Field R] [CharZero R] :
    E8 R = (checkerboardLattice R 8 ⊔ Submodule.span ℤ {fun _ ↦ (2⁻¹ : R)}) := by
  refine le_antisymm (fun x hx ↦ ?_) (sup_le (fun v hv ↦ ?_) (span_le.2 ?_))
  · obtain ⟨hx | hx, hx'⟩ := mem_E8''.1 hx
    · exact mem_sup_left ((mem_checkerboardLattice 8).2 ⟨hx, hx'⟩)
    choose z hz using hx
    have hsum : ∑ i, x i = ∑ i, (z i : R) + (2 : ℤ) • 2 := by
      simp [← hz, Finset.sum_add_distrib]; norm_num
    refine mem_sup.2 ⟨fun i ↦ z i, (mem_checkerboardLattice 8).2 ⟨fun i ↦ ⟨z i, rfl⟩, ?_⟩, _,
      mem_span_singleton_self _, by ext i; simp [hz]⟩
    rw [hsum] at hx'
    exact (AddCommGroup.add_zsmul_modEq _).symm.trans hx'
  · have h := (mem_checkerboardLattice 8).1 hv
    exact mem_E8.2 ⟨.inl h.1, h.2⟩
  · have h1 : (8 * 2⁻¹ : R) = (2 : ℤ) • 2 := by norm_num
    simpa [mem_E8, h1] using AddCommGroup.zsmul_modEq_zero (p := (2 : R)) 2

section E8_basis

/-- An explicit matrix whose rows form a `ℤ`-basis of the `E₈` lattice, see `span_E8Matrix`. -/
def E8Matrix (R : Type*) [Field R] : Matrix (Fin 8) (Fin 8) R := !![
    2,   0,   0,   0,   0,   0,   0,   0;
   -1,   1,   0,   0,   0,   0,   0,   0;
    0,  -1,   1,   0,   0,   0,   0,   0;
    0,   0,  -1,   1,   0,   0,   0,   0;
    0,   0,   0,  -1,   1,   0,   0,   0;
    0,   0,   0,   0,  -1,   1,   0,   0;
    0,   0,   0,   0,   0,  -1,   1,   0;
  2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹]

lemma E8Matrix_row_mem_E8 [Field R] [CharZero R] :
    ∀ i, (E8Matrix R).row i ∈ Submodule.E8 R := by
  have h2 : ∃ n : ℤ, (n : R) = 2 := ⟨2, by simp⟩
  have hneg1 : ∃ n : ℤ, (n : R) = -1 := ⟨-1, by simp⟩
  rw [Fin.forall_fin_succ']
  simp_rw [Submodule.E8_eq_sup]
  refine ⟨fun i ↦ Submodule.mem_sup_left ?_, Submodule.mem_sup_right (Submodule.subset_span ?_)⟩
  · fin_cases i <;> simp [E8Matrix, Submodule.mem_checkerboardLattice, Fin.forall_fin_succ, h2,
      hneg1, Fin.sum_univ_eight]
  · simp [E8Matrix, funext_iff, Fin.forall_fin_succ]

lemma E8Matrix_eq_cast (R : Type*) [Field R] [CharZero R] :
    E8Matrix R = (E8Matrix ℚ).map (Rat.castHom R) := by
  rw [← Matrix.ext_iff]
  norm_num [Fin.forall_fin_succ, E8Matrix]

lemma lowerTriangular_E8Matrix {R : Type*} [Field R] :
    (E8Matrix R).BlockTriangular OrderDual.toDual := by
  simp [Matrix.BlockTriangular, E8Matrix, Fin.forall_fin_succ]

theorem E8Matrix_unimodular (R : Type*) [Field R] [NeZero (2 : R)] : (E8Matrix R).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ lowerTriangular_E8Matrix]
  simp [E8Matrix, Fin.prod_univ_eight, (NeZero.ne (2 : R))]

private lemma E8Matrix_is_basis (R : Type*) [Field R] [NeZero (2 : R)] :
    LinearIndependent R (E8Matrix R).row ∧
    Submodule.span R (Set.range (E8Matrix R).row) = ⊤ := by
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det_apply]
  change IsUnit (E8Matrix R).det
  simp [E8Matrix_unimodular]

lemma linearIndependent_E8Matrix (R : Type*) [Field R] [NeZero (2 : R)] :
    LinearIndependent R (E8Matrix R).row := (E8Matrix_is_basis _).1

lemma span_E8Matrix_eq_top (R : Type*) [Field R] [NeZero (2 : R)] :
    Submodule.span R (Set.range (E8Matrix R).row) = ⊤ := (E8Matrix_is_basis _).2

/-- The rows of `E8Matrix`, as a basis of `Fin 8 → R` over `R`. -/
noncomputable def E8Basis (R : Type*) [Field R] [NeZero (2 : R)] : Basis (Fin 8) R (Fin 8 → R) :=
  Basis.mk (linearIndependent_E8Matrix R) (span_E8Matrix_eq_top R).ge

lemma E8Basis_apply [Field R] [NeZero (2 : R)] (i : Fin 8) :
    E8Basis R i = (E8Matrix R).row i :=
  Basis.mk_apply _ _ _

lemma of_basis_eq_matrix [Field R] [CharZero R] : Matrix.of (E8Basis R) = E8Matrix R := by
  ext i j; simp [E8Basis_apply]

theorem range_E8Matrix_row_subset (R : Type*) [Field R] [CharZero R] :
    Set.range (E8Matrix R).row ⊆ Submodule.E8 R := by
  simpa [Set.subset_def] using E8Matrix_row_mem_E8 (R := R)

private def E8Inverse (R : Type*) [Field R] : Matrix (Fin 8) (Fin 8) R := !![
  2⁻¹, 0, 0, 0, 0, 0, 0, 0;
  2⁻¹, 1, 0, 0, 0, 0, 0, 0;
  2⁻¹, 1, 1, 0, 0, 0, 0, 0;
  2⁻¹, 1, 1, 1, 0, 0, 0, 0;
  2⁻¹, 1, 1, 1, 1, 0, 0, 0;
  2⁻¹, 1, 1, 1, 1, 1, 0, 0;
  2⁻¹, 1, 1, 1, 1, 1, 1, 0;
  -7 * 2⁻¹, -6, -5, -4, -3, -2, -1, 2]

private lemma E8Inverse_eq_cast (R : Type*) [Field R] [CharZero R] :
    E8Inverse R = (E8Inverse ℚ).map (Rat.castHom R) := by
  rw [← Matrix.ext_iff]
  norm_num [Fin.forall_fin_succ, E8Inverse]

private lemma E8Inverse_mul_E8Matrix_rat : E8Inverse ℚ * E8Matrix ℚ = 1 := by decide +kernel

private lemma E8Inverse_mul_E8Matrix {R : Type*} [Field R] [CharZero R] :
    E8Inverse R * E8Matrix R = 1 := by
  rw [E8Matrix_eq_cast, E8Inverse_eq_cast, ← Matrix.map_mul, E8Inverse_mul_E8Matrix_rat]
  simp

private lemma E8Matrix_mul_E8Inverse {R : Type*} [Field R] [CharZero R] :
    E8Matrix R * E8Inverse R = 1 := by
  rw [mul_eq_one_comm, E8Inverse_mul_E8Matrix]

private lemma exists_cast_eq_vecMul_E8Inverse_aux {R : Type*} [Field R] [CharZero R]
    (v : Fin 8 → R) (w : Fin 8 → ℤ) (hv : v ∈ Submodule.E8 R)
    (hw : ∑ i, w i = 0) :
    ∃ c : ℤ, c = ∑ i, v i * w i := by
  obtain ⟨hv' | hv', -⟩ := Submodule.mem_E8''.1 hv <;> choose v' hv' using hv'
  · exact ⟨∑ i, v' i * w i, by simp [← hv']⟩
  · have hw' : ∑ i, (w i : R) = 0 := by exact_mod_cast hw
    exact ⟨∑ i, v' i * w i, by simp [← hv', add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hw']⟩

private lemma exists_cast_eq_vecMul_E8Inverse {R : Type*} [Field R] [CharZero R]
    (v : Fin 8 → R) (hv : v ∈ Submodule.E8 R) :
    ∃ c : Fin 8 → ℤ, (fun i ↦ (c i : R)) = Matrix.vecMul v (E8Inverse R) := by
  set c' := Matrix.vecMul v (E8Inverse R)
  obtain ⟨c0, hc0⟩ : ∃ n : ℤ, (n : R) = c' 0 := by
    have h0 : c' 0 = (∑ i, v i) * 2⁻¹ - 4 * v 7 := by
      simp [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse]
      ring
    obtain ⟨hv7, hs⟩ := Submodule.mem_E8''.1 hv
    obtain ⟨a, ha⟩ := AddCommGroup.modEq_zero_iff_eq_zsmul.1 hs
    rw [h0, ha, zsmul_eq_mul, mul_inv_cancel_right₀ two_ne_zero]
    obtain hv7 | hv7 := hv7 <;> obtain ⟨n, hn⟩ := hv7 7 <;> rw [← hn]
    · exact ⟨a - 4 * n, by push_cast; ring⟩
    · exact ⟨a - 4 * n - 2, by push_cast; ring⟩
  obtain ⟨c7, hc7⟩ : ∃ n : ℤ, (n : R) = c' 7 := by
    have h7 : c' 7 = 2 * v 7 := by
      simp [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse, mul_comm]
    obtain ⟨hv7 | hv7, -⟩ := Submodule.mem_E8''.1 hv <;> obtain ⟨n, hn⟩ := hv7 7
    · exact ⟨2 * n, by simp [h7, ← hn]⟩
    · exact ⟨2 * n + 1, by simp [h7, ← hn, mul_add]⟩
  have key (i : Fin 8) (w : Fin 8 → ℤ) (hw : ∑ j, w j = 0)
      (h : ∀ j, (w j : R) = E8Inverse R j i := by simp [Fin.forall_fin_succ, E8Inverse]) :
      ∃ n : ℤ, (n : R) = c' i := by
    simpa [c', Matrix.vecMul, dotProduct, h] using exists_cast_eq_vecMul_E8Inverse_aux v w hv hw
  obtain ⟨c1, hc1⟩ := key 1 ![0, 1, 1, 1, 1, 1, 1, -6] rfl
  obtain ⟨c2, hc2⟩ := key 2 ![0, 0, 1, 1, 1, 1, 1, -5] rfl
  obtain ⟨c3, hc3⟩ := key 3 ![0, 0, 0, 1, 1, 1, 1, -4] rfl
  obtain ⟨c4, hc4⟩ := key 4 ![0, 0, 0, 0, 1, 1, 1, -3] rfl
  obtain ⟨c5, hc5⟩ := key 5 ![0, 0, 0, 0, 0, 1, 1, -2] rfl
  obtain ⟨c6, hc6⟩ := key 6 ![0, 0, 0, 0, 0, 0, 1, -1] rfl
  refine ⟨![c0, c1, c2, c3, c4, c5, c6, c7], ?_⟩
  rw [funext_iff]
  simp [Fin.forall_fin_succ, *]

theorem span_E8Matrix (R : Type*) [Field R] [CharZero R] :
    Submodule.span ℤ (Set.range (E8Matrix R).row) = Submodule.E8 R := by
  refine Submodule.span_eq_of_le _ (range_E8Matrix_row_subset R) fun v hv ↦ ?_
  obtain ⟨c, hc⟩ := exists_cast_eq_vecMul_E8Inverse v hv
  refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, ?_⟩
  rw [← Matrix.vecMul_one v, ← E8Inverse_mul_E8Matrix, ← Matrix.vecMul_vecMul, ← hc]
  simp [Matrix.vecMul_eq_sum, Matrix.row, ← Int.cast_smul_eq_zsmul R]

theorem span_E8Basis (R : Type*) [Field R] [CharZero R] :
    Submodule.span ℤ (Set.range (E8Basis R)) = Submodule.E8 R := by
  rw [show ⇑(E8Basis R) = (E8Matrix R).row from funext E8Basis_apply, span_E8Matrix]

/-- The Gram matrix of the rows of `E8Matrix`, i.e. the matrix of their dot products, see
`dotProduct_eq_inn`. -/
def E8.inn : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, -2, 0, 0, 0, 0, 0, 1;
    -2, 2, -1, 0, 0, 0, 0, 0;
    0, -1, 2, -1, 0, 0, 0, 0;
    0, 0, -1, 2, -1, 0, 0, 0;
    0, 0, 0, -1, 2, -1, 0, 0;
    0, 0, 0, 0, -1, 2, -1, 0;
    0, 0, 0, 0, 0, -1, 2, 0;
    1, 0, 0, 0, 0, 0, 0, 2]

lemma E8Matrix_mul_E8Matrix_transpose_rat :
    E8Matrix ℚ * (E8Matrix ℚ).transpose = E8.inn.map (↑) := by
  decide +kernel

lemma E8Matrix_mul_E8Matrix_transpose [Field R] [CharZero R] :
    E8Matrix R * (E8Matrix R).transpose = E8.inn.map (↑) := by
  rw [E8Matrix_eq_cast, ← Matrix.transpose_map, ← Matrix.map_mul,
    E8Matrix_mul_E8Matrix_transpose_rat, Matrix.map_map]
  congr! 1
  ext n
  simp

lemma dotProduct_eq_inn {R : Type*} [Field R] [CharZero R] (i j : Fin 8) :
    (E8Matrix R).row i ⬝ᵥ (E8Matrix R).row j = E8.inn i j := by
  simpa [Matrix.mul_apply', Matrix.row] using congr($(E8Matrix_mul_E8Matrix_transpose (R := R)) i j)

lemma dotProduct_is_integer {R : Type*} [Field R] [CharZero R] (i j : Fin 8) :
    ∃ z : ℤ, z = (E8Matrix R).row i ⬝ᵥ (E8Matrix R).row j :=
  ⟨_, (dotProduct_eq_inn _ _).symm⟩

end E8_basis

/-- The `E₈` lattice as a submodule of eight-dimensional Euclidean space. This additional
definition is valuable, since it puts the correct metric space structure on the lattice. -/
noncomputable abbrev E8Lattice : Submodule ℤ (EuclideanSpace ℝ (Fin 8)) :=
  (Submodule.E8 ℝ).map (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm.toLinearMap

lemma E8Lattice_eq_comap :
    E8Lattice = ZLattice.comap ℝ (Submodule.E8 ℝ) (EuclideanSpace.equiv (Fin 8) ℝ).toLinearMap :=
  Submodule.ext fun _ ↦ ⟨fun ⟨_, hv, h⟩ ↦ h ▸ hv, fun hx ↦ ⟨_, hx, rfl⟩⟩

/-- The `E₈` lattice is even: `‖v‖ ^ 2` is an even integer for every `v ∈ E₈`. -/
theorem isEven_E8Lattice : ZLattice.IsEven E8Lattice := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hx
  change ∃ n : ℤ, v ⬝ᵥ v = 2 * n
  rw [← span_E8Matrix, Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, rfl⟩ := hv
  simp_rw [sum_dotProduct, dotProduct_sum, dotProduct_smul, smul_dotProduct, dotProduct_eq_inn,
    zsmul_eq_mul]
  norm_cast
  simp_rw [← even_iff_exists_two_mul]
  simp only [E8.inn, Int.reduceNeg, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_fin_one, Fin.sum_univ_eight, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, mul_neg, mul_zero, add_zero, mul_one, zero_add]
  ring_nf
  have h4 : Even (4 : ℤ) := ⟨2, rfl⟩
  simp [h4, parity_simps]

/-- The `E₈` lattice is integral: `⟪v, w⟫` is an integer for all `v, w ∈ E₈`. -/
theorem isIntegral_E8Lattice : ZLattice.IsIntegral E8Lattice :=
  isEven_E8Lattice.isIntegral

lemma E8_norm_lower_bound (v : Fin 8 → ℝ) (hv : v ∈ Submodule.E8 ℝ) :
    v = 0 ∨ √2 ≤ ‖WithLp.toLp 2 v‖ :=
  or_iff_not_imp_left.2 fun hv₀ ↦
    isEven_E8Lattice.sqrt_two_le_norm (Submodule.mem_map_of_mem hv) (by simpa using hv₀)

instance instDiscreteE8Lattice : DiscreteTopology E8Lattice :=
  isEven_E8Lattice.discreteTopology

lemma span_E8_eq_top : Submodule.span ℝ (Submodule.E8 ℝ : Set (Fin 8 → ℝ)) = ⊤ :=
  eq_top_iff.2 <| (span_E8Matrix_eq_top ℝ).ge.trans <|
    Submodule.span_mono (range_E8Matrix_row_subset ℝ)

instance instDiscreteE8 : DiscreteTopology (Submodule.E8 ℝ) :=
  (inferInstance : DiscreteTopology (Submodule.span ℤ (Set.range (E8Basis ℝ)))).of_subset
    (span_E8Basis ℝ).ge

instance instIsZLatticeE8 : IsZLattice ℝ (Submodule.E8 ℝ) := ⟨span_E8_eq_top⟩

lemma span_E8_eq_top' :
    Submodule.span ℝ (E8Lattice : Set (EuclideanSpace ℝ (Fin 8))) = ⊤ := by
  rw [E8Lattice_eq_comap]
  exact IsZLattice.span_top

lemma span_E8Matrix_eq_E8Lattice :
    Submodule.span ℤ
      (Set.range fun i ↦ (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i)) =
      E8Lattice := by
  rw [E8Lattice, ← span_E8Matrix ℝ, Submodule.map_span, ← Set.range_comp]
  rfl

instance instIsZLatticeE8Lattice : IsZLattice ℝ E8Lattice where
  span_top := span_E8_eq_top'

/-- The rows of `E8Matrix`, as a `ℤ`-basis of `E8Lattice`. -/
noncomputable def E8LatticeBasis : Basis (Fin 8) ℤ E8Lattice := by
  refine Basis.mk
      (v := fun i ↦ ⟨(WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i), ?_⟩) ?_ ?_
  · exact Submodule.mem_map_of_mem (E8Matrix_row_mem_E8 i)
  · refine LinearIndependent.of_comp (Submodule.subtype _) ?_
    refine LinearIndependent.of_comp (M' := (Fin 8 → ℝ)) (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)) ?_
    exact (linearIndependent_E8Matrix ℝ).restrict_scalars' ℤ
  · rw [← Submodule.map_le_map_iff_of_injective (f := E8Lattice.subtype) (by simp)]
    simp only [Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_span, ← Set.range_comp]
    exact span_E8Matrix_eq_E8Lattice.ge

lemma coe_E8LatticeBasis_apply (i : Fin 8) :
    E8LatticeBasis i = (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i) := by
  rw [E8LatticeBasis, Basis.coe_mk]

lemma E8LatticeBasis_ofZLatticeBasis_apply (i : Fin 8) :
    E8LatticeBasis.ofZLatticeBasis ℝ E8Lattice i =
      (WithLp.toLp 2) ((E8Matrix ℝ).row i) := by
  simp [coe_E8LatticeBasis_apply]

lemma E8Basis_apply_norm : ∀ i : Fin 8, ‖WithLp.toLp 2 (E8Basis ℝ i)‖ ≤ 2 := by
  have : √2 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  simp [E8Basis, E8Matrix, EuclideanSpace.norm_eq, Fin.forall_fin_succ, Fin.sum_univ_eight]
  norm_num [this]

lemma E8LatticeBasis_apply_norm : ∀ i : Fin 8, ‖E8LatticeBasis i‖ ≤ 2 := fun i ↦ by
  simpa [coe_E8LatticeBasis_apply, E8Basis_apply] using E8Basis_apply_norm i

open MeasureTheory in
theorem covolume_E8 : ZLattice.covolume (Submodule.E8 ℝ) = 1 := by
  rw [← span_E8Basis, ZLattice.covolume_eq_measure_fundamentalDomain _ _
    (ZSpan.isAddFundamentalDomain (E8Basis ℝ) volume), ZSpan.volume_real_fundamentalDomain,
    of_basis_eq_matrix, E8Matrix_unimodular, abs_one]

theorem covolume_E8Lattice : ZLattice.covolume E8Lattice = 1 := by
  rw [E8Lattice_eq_comap, ZLattice.covolume_comap _ _ _ (PiLp.volume_preserving_ofLp (Fin 8)),
    covolume_E8]
