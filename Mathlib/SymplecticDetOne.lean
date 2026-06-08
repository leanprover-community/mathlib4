import Mathlib

namespace SymplecticMatrixDet

open Matrix

/-- Given A ∈ symplecticGroup l R, write A = fromBlocks P Q R S and extract
    the block conditions:
    (1) Pᵀ * R = Rᵀ * P
    (2) Qᵀ * S = Sᵀ * Q
    (3) Pᵀ * S - Rᵀ * Q = 1 -/
theorem symplectic_block_conditions
    {l k : Type*} [DecidableEq l] [Fintype l] [CommRing k]
    {P Q R S : Matrix l l k}
    (hA : fromBlocks P Q R S ∈ symplecticGroup l k) :
    (Pᵀ * R = Rᵀ * P) ∧
    (Qᵀ * S = Sᵀ * Q) ∧
    (Pᵀ * S - Rᵀ * Q = 1) := by
  have h_main : (fromBlocks Pᵀ Rᵀ Qᵀ Sᵀ) * (fromBlocks 0 (-1) 1 0) * (fromBlocks P Q R S) =
      (fromBlocks 0 (-1) 1 0) := by
    rw [← fromBlocks_transpose]
    exact SymplecticGroup.mem_iff.1 (SymplecticGroup.transpose_mem hA)
  have h_final : fromBlocks (Rᵀ * P - Pᵀ * R) (Rᵀ * Q - Pᵀ * S)
      (Sᵀ * P - Qᵀ * R) (Sᵀ * Q - Qᵀ * S) = fromBlocks 0 (-1) 1 0 := by
    simpa only [sub_eq_add_neg, fromBlocks_inj, fromBlocks_multiply, mul_zero, mul_one, zero_add,
      mul_neg, add_zero, neg_mul] using h_main
  obtain ⟨h_eq1, h_eq2, _, h_eq3⟩ := fromBlocks_inj.1 h_final
  refine ⟨(sub_eq_zero.1 h_eq1).symm, (sub_eq_zero.1 h_eq3).symm, ?_⟩
  rw [sub_eq_iff_comm, sub_neg_eq_add] at h_eq2
  rw [← h_eq2, sub_eq_iff_eq_add']

/-- If the top-left n×n block P of a symplectic matrix A is invertible, then det(A) = 1.
    Proof: use the Schur complement formula and the block condition Pᵀ S - Rᵀ Q = 1
    to show det(S - R * P⁻¹ * Q) = det(P)⁻¹, hence det(A) = det(P) * det(P)⁻¹ = 1. -/
theorem symplectic_det_one_when_P_invertible
    {l k : Type*} [DecidableEq l] [Fintype l] [CommRing k]
    {P Q R S : Matrix l l k} [Invertible P]
    (hA : fromBlocks P Q R S ∈ symplecticGroup l k) :
    (fromBlocks P Q R S).det = 1 := by
  have h_block := symplectic_block_conditions hA
  rw [det_fromBlocks₁₁ P Q R S, invOf_eq_nonsing_inv,
    ← P.det_transpose, ← det_mul, mul_sub, ← mul_assoc, ← mul_assoc,
    h_block.1, mul_assoc Rᵀ, mul_inv_of_invertible, mul_one, h_block.2.2,
    det_one]

/-- The symmetric shear matrix L_X = [[I, X], [0, I]] is symplectic when X is symmetric. -/
theorem symmetric_shear_is_symplectic
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    {X : Matrix l l R} (hX : X.transpose = X) :
    fromBlocks 1 X 0 1 ∈ symplecticGroup l R := by
  rw [SymplecticGroup.mem_iff, fromBlocks_transpose, hX]
  simp [fromBlocks_multiply, J]

/-- det(L_X) = 1 for the symmetric shear L_X = [[I, X], [0, I]]. -/
theorem symmetric_shear_det_one
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    {X : Matrix l l R} :
    (fromBlocks 1 X 0 1).det = 1 := by
  rw [Matrix.det_fromBlocks_zero₂₁ 1 X 1, det_one, one_mul]

/-- Multiplying a symplectic matrix by the symmetric shear on the left:
    L_X * A = [[P + X*R, Q + X*S], [R, S]] -/
theorem shear_mul_symplectic_blocks
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    {P Q Rmat S X : Matrix l l R} :
    fromBlocks 1 X 0 1 * fromBlocks P Q Rmat S =
    fromBlocks (P + X * Rmat) (Q + X * S) Rmat S := by
  simp [fromBlocks_multiply]


lemma round1_rank_normal_form {l k : Type*} [DecidableEq l] [Fintype l] [Field k]
  (M : Matrix l l k) :
  ∃ (V U : Matrix l l k) (s : Finset l),
    IsUnit V.det ∧ IsUnit U.det ∧
    V * M * U = diagonal (fun i : l ↦ if i ∈ s then 1 else 0) := by
  classical
  obtain ⟨L, L', D, hM_eq⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  let A_left : Matrix l l k := (List.map TransvectionStruct.toMatrix L).prod
  let B_right : Matrix l l k := (List.map TransvectionStruct.toMatrix L').prod
  have hA_left_unit : IsUnit A_left.det := by
    rw [TransvectionStruct.det_toMatrix_prod L]; exact isUnit_one
  have hB_right_unit : IsUnit B_right.det := by
    rw [TransvectionStruct.det_toMatrix_prod L']; exact isUnit_one
  set E : l → k := fun i ↦ if D i = 0 then 1 else (D i)⁻¹ with E_def
  set S : Matrix l l k := diagonal E with S_def
  have hE_ne_zero (i : l) : E i ≠ 0 := by
    by_cases h : D i = 0
    · simp only [E_def, if_pos h, ne_eq, one_ne_zero, not_false_eq_true]
    · simpa only [E_def, if_neg h, ne_eq, inv_eq_zero]
  have hS_unit : IsUnit S.det := by
    rw [det_diagonal]
    exact IsUnit.mk0 _ <| Finset.prod_ne_zero_iff.2 fun i _ ↦ hE_ne_zero i
  set s : Finset l := Finset.filter (fun i : l ↦ D i ≠ 0) Finset.univ with s_def
  have h2 : S * diagonal D = diagonal (fun i : l ↦ if i ∈ s then (1 : k) else 0) := by
    ext i j
    simp only [E_def, mul_diagonal, diagonal_apply, ite_mul, one_mul, zero_mul, ne_eq,
      Finset.mem_filter, Finset.mem_univ, true_and, ite_not, S_def, s_def]
    split_ifs with h1 h2
    · rw [← h1, h2]
    · rw [← h1, inv_mul_cancel₀ h2]
    · rfl
  refine ⟨S * A_left⁻¹, B_right⁻¹, s, ?_, isUnit_nonsing_inv_det _ hB_right_unit, ?_⟩
  · simpa using (hS_unit.mul (isUnit_nonsing_inv_det _ hA_left_unit))
  · rw [hM_eq, mul_assoc, mul_assoc _ B_right, mul_nonsing_inv _ hB_right_unit, mul_one,
    ← mul_assoc, mul_assoc _ A_left⁻¹, nonsing_inv_mul _ hA_left_unit, mul_one, h2]

lemma round1_transfer_rank {l k : Type*} [DecidableEq l] [Fintype l] [Field k]
  {P R P1 R1 : Matrix l l k}
  {U V : Matrix l l k}
  (hU : IsUnit U.det) (hV : IsUnit V.det)
  (hP1 : P1 = (Vᵀ)⁻¹ * P * U)
  (hR1 : R1 = V * R * U)
  (h_rank : ∀ (x : l → k), (P *ᵥ x = 0) → (R *ᵥ x = 0) → x = 0) :
  ∀ (x : l → k), (P1 *ᵥ x = 0) → (R1 *ᵥ x = 0) → x = 0 := by
  intro x h1 h2
  refine mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det U).2 hU) ?_
  rw [mulVec_zero]
  refine h_rank (U *ᵥ x) ?_ ?_
  · rw [mulVec_mulVec, ← one_mul (P * U), ← mul_nonsing_inv _ (isUnit_det_transpose _ hV),
      mul_assoc, ← mul_assoc _ P, ← hP1, ← mulVec_mulVec, h1, mulVec_zero]
  · rw [mulVec_mulVec, ← one_mul (R * U), ← nonsing_inv_mul _ hV,
      mul_assoc, ← mul_assoc _ R, ← hR1, ← mulVec_mulVec, h2, mulVec_zero]

lemma round1_transfer_symm {l k : Type*} [DecidableEq l] [Fintype l] [CommRing k]
  {P R P1 R1 U V : Matrix l l k} (hV : IsUnit V.det)
  (hP1 : P1 = (Vᵀ)⁻¹ * P * U)
  (hR1 : R1 = V * R * U)
  (h_symm : Pᵀ * R = Rᵀ * P) :
  P1ᵀ * R1 = R1ᵀ * P1 := by
  rw [hR1, hP1, transpose_mul, transpose_mul, transpose_mul, transpose_mul,
    transpose_nonsing_inv, transpose_transpose]
  convert_to Uᵀ * (Pᵀ * (V⁻¹ * V) * R * U) = Uᵀ * (Rᵀ * (Vᵀ * Vᵀ⁻¹) * P * U)
  · ac_rfl
  · ac_rfl
  · rw [nonsing_inv_mul _ hV, mul_nonsing_inv _ (isUnit_det_transpose _ hV),
      mul_one, mul_one, h_symm]

lemma round1_core_entrywise {l k : Type*} [DecidableEq l] [Fintype l] [Field k]
  {P1 : Matrix l l k} {s : Finset l}
  (hR1 : let R1 : Matrix l l k := Matrix.diagonal (fun i : l ↦ if i ∈ s then (1 : k) else 0)
    P1ᵀ * R1 = R1 * P1) :
  (∀ (i j : l), i ∈ s → j ∉ s → P1 i j = 0) ∧
  (∀ (i j : l), i ∈ s → j ∈ s → P1 i j = P1 j i) := by
  have h_main1 : ∀ (i j : l), (if j ∈ s then P1 j i else 0) = (if i ∈ s then P1 i j else 0) := by
    intro i j
    convert ext_iff.2 hR1 i j
    · simp only [mul_diagonal, transpose_apply, mul_ite, mul_one, mul_zero]
    · simp only [diagonal_mul, ite_mul, one_mul, zero_mul]
  constructor <;> intro i j hi hj
  · have := (h_main1 i j).symm
    rwa [if_pos hi, if_neg hj] at this
  · have := (h_main1 i j).symm
    rwa [if_pos hj, if_pos hi] at this

lemma _root_.Matrix.mulVec_apply {m n R : Type*} [Finite m] [Fintype n] [Semiring R]
  (M : Matrix m n R) (x : n → R) (i : m) : (M *ᵥ x) i = ∑ j : n, M i j * x j := rfl

lemma round1_main_step {l k : Type*} [DecidableEq l] [Fintype l] [Field k]
  {P1 : Matrix l l k} {s : Finset l}
  (h1 : ∀ (i j : l), i ∈ s → j ∉ s → P1 i j = 0)
  (h2 : ∀ (i j : l), i ∈ s → j ∈ s → P1 i j = P1 j i)
  (h_rank1 : ∀ (x : l → k), (P1 *ᵥ x = 0) →
    ((diagonal (fun i : l ↦ if i ∈ s then 1 else 0)) *ᵥ x = 0) → x = 0) :
  ∃ (X1 : Matrix l l k), X1ᵀ = X1 ∧
    IsUnit (P1 + X1 * (diagonal (fun i : l ↦ if i ∈ s then 1 else 0))).det := by
  set R1 : Matrix l l k := diagonal (fun i : l ↦ if i ∈ s then 1 else 0) with R1_def
  set X1 : Matrix l l k := fun i j ↦
    if i ∈ s ∧ j ∈ s then (if i = j then 1 else 0) - P1 i j else 0 with X1_def
  have hX1_symm : X1ᵀ = X1 := by
    ext i j
    simp only [X1_def, transpose_apply, and_comm, eq_comm]
    split_ifs with hif1 hif2
    · rw [hif2]
    · rw [h2 i j hif1.1 hif1.2]
    · rfl
  have hM1 : ∀ (i : l), i ∈ s → ∀ (j : l), (P1 + X1 * R1) i j = if i = j then 1 else 0 := by
    intro i hi j
    simp only [X1_def, R1_def, add_apply, mul_apply, diagonal_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    split
    · next hj => rw [if_pos ⟨hi, hj⟩, add_sub_cancel]
    · next hj => rw [h1 i j hi hj, if_neg (ne_of_mem_of_not_mem hi hj), add_zero]
  set M : Matrix l l k := P1 + X1 * R1 with M_def
  refine ⟨X1, hX1_symm, M.isUnit_iff_isUnit_det.1 <|
    isUnit_toLin'_iff.1 <| M.toLin'.isUnit_iff_ker_eq_bot.2 <|
      ker_toLin'_eq_bot_iff.2 <| fun x hx ↦ ?_⟩
  have hR1x : R1 *ᵥ x = 0 := by
    ext i
    convert_to (if i ∈ s then x i else 0) = _
    · simp only [mulVec_apply, R1_def, diagonal_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    · refine ite_eq_right_iff.2 fun hi ↦ ?_
      simpa only [hM1 i hi, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte] using (show ∑ j : l, M i j * x j = 0 from congrFun hx i)
  have hP1x : P1 *ᵥ x = 0 := by
    convert_to P1 *ᵥ x + (X1 * R1) *ᵥ x = 0
    · rw [left_eq_add, (mulVec_mulVec x X1 R1).symm, hR1x, mulVec_zero]
    · rw [← add_mulVec, hx]
  exact h_rank1 x hP1x hR1x

/-- Over a field k, given n×n matrices P, R such that:
    (1) rank of the 2n×n matrix [P; R] is n (i.e., the columns are linearly independent)
    (2) PᵀR = RᵀP (symmetric)
    there exists a symmetric n×n matrix X such that P + X*R is invertible.

    Proof strategy (from nl-advisor):
    - Let r = rank(R). Over k, find invertible U, V with V R U = [[I_r, 0], [0, 0]]
    - Define R₁ := V R U, P₁ := V⁻ᵀ P U
    - Verify rank([P₁; R₁]) = n and P₁ᵀ R₁ = R₁ᵀ P₁
    - Partition P₁ = [[A, B], [C, D]] conformally
    - Deduce Aᵀ = A and B = 0 from P₁ᵀ R₁ = R₁ᵀ P₁
    - Prove D is invertible using rank([P₁; R₁]) = n
    - Set X₁ = [[I_r - A, 0], [0, 0]] (symmetric)
    - Show P₁ + X₁ * R₁ = [[I_r, 0], [C, D]] is block lower triangular with invertible diagonals
    - Set X = Vᵀ X₁ V (symmetric)
    - Show V⁻ᵀ (P + X R) U = P₁ + X₁ R₁ is invertible, hence P + X R is invertible -/
theorem field_exists_symmetric_X_invertible_sum
    {l k : Type*} [DecidableEq l] [Fintype l] [Field k]
    {P R : Matrix l l k}
    (h_rank : ∀ (x : l → k), (P *ᵥ x = 0) → (R *ᵥ x = 0) → x = 0)
    (h_symm : Pᵀ * R = Rᵀ * P) :
    ∃ (X : Matrix l l k), Xᵀ = X ∧ IsUnit (P + X * R).det := by
  rcases round1_rank_normal_form (M := R) with ⟨V, U, s, hV, hU, hR1_eq⟩
  set R1 := V * R * U with R1_def
  set D := diagonal (fun i ↦ if i ∈ s then 1 else 0) with D_def
  set P1 := Vᵀ⁻¹ * P * U with P1_def
  have h_main1 : (∀ (i j : l), i ∈ s → j ∉ s → P1 i j = 0) ∧
      (∀ (i j : l), i ∈ s → j ∈ s → P1 i j = P1 j i) := by
    refine round1_core_entrywise ?_
    have h_symm1 : P1ᵀ * R1 = R1ᵀ * P1 :=
      round1_transfer_symm hV rfl rfl h_symm
    rwa [hR1_eq, diagonal_transpose] at h_symm1
  obtain ⟨X1, hX1_symm, hM1⟩ := round1_main_step h_main1.1 h_main1.2 <| fun x hP1x hDx ↦
    round1_transfer_rank hU hV rfl rfl h_rank x hP1x (hR1_eq ▸ hDx : R1 *ᵥ x = 0)
  refine ⟨Vᵀ * X1 * V, ?_, ?_⟩
  · rw [transpose_mul, transpose_mul, hX1_symm, transpose_transpose, mul_assoc]
  · convert_to IsUnit (Vᵀ * (P1 + X1 * R1) * U⁻¹).det
    · simp only [mul_assoc, mul_nonsing_inv_cancel_right U _ hU,
    mul_nonsing_inv_cancel_left Vᵀ _ (isUnit_det_transpose V hV),
    mul_add, add_mul, mul_assoc, P1_def, R1_def]
    rw [det_mul, det_mul]
    exact IsUnit.mul (IsUnit.mul (det_transpose V ▸ hV) (by rwa [hR1_eq]))
      (isUnit_nonsing_inv_det U hU)

lemma lift_symmetric_matrix
    {l R S : Type*} [DecidableEq l] [Fintype l] [Semiring R] [Semiring S]
    (f : R →+* S) (hf : Function.Surjective f)
    (Y : Matrix l l S) (hY : Yᵀ = Y) :
    ∃ (X : Matrix l l R), Xᵀ = X ∧ f.mapMatrix X = Y := by
  choose s hs using hf
  have _ : LinearOrder l := (Cardinal.exists_ord_eq_type_lt l).choose
  set X : Matrix l l R := fun i j ↦ if i ≤ j then s (Y i j) else s (Y j i) with X_def
  refine ⟨X, ?_, ?_⟩ <;> ext i j
  · simp only [X_def, transpose_apply]
    split_ifs with h1 h2 h3
    · rw [le_antisymm h1 h2]
    · rfl
    · rfl
    · tauto
  · have h3 : Y j i = Y i j := ((fun _ ↦ ext_iff.2 hY i j) ∘ Y i) i
    simp only [X_def, RingHom.mapMatrix_apply, map_apply, h3, ite_self, hs]

/-- Over a local ring R, there exists a symmetric X such that P + X*Rmat is invertible.
    Proof:
    1. Let k = ResidueField R. Reduce mod maximal ideal.
    2. Over k, the rank of [P̄; R̄mat] = n (because A is symplectic, hence invertible, so its first
      n columns are linearly independent mod m).
    3. Also P̄ᵀ R̄mat = R̄matᵀ P̄ (reduced from hA).
    4. By field_exists_symmetric_X_invertible_sum, ∃ X̄ symmetric with P̄ + X̄ * R̄mat invertible.
    5. Lift X̄ to X ∈ Matrix l l R, symmetrize if needed.
    6. Then det(P + X * Rmat) maps to nonzero in k, hence is a unit in R. -/
theorem exists_symmetric_shear_making_P_invertible
    {l D : Type*} [DecidableEq l] [Fintype l] [CommRing D] [IsLocalRing D]
    {P Q R S : Matrix l l D}
    (hA : fromBlocks P Q R S ∈ symplecticGroup l D) :
    ∃ (X : Matrix l l D), Xᵀ = X ∧ IsUnit (P + X * R).det := by
  set k := IsLocalRing.ResidueField D; set f := IsLocalRing.residue D
  set A := fromBlocks P Q R S; set P' := f.mapMatrix P with P'_def; set Q' := f.mapMatrix Q
  set R' := f.mapMatrix R; set S' := f.mapMatrix S; set A' := fromBlocks P' Q' R' S' with A'_def
  have h15' : IsUnit A' := by
    refine A'.isUnit_iff_isUnit_det.2 ?_
    convert (SymplecticGroup.symplectic_det hA).map f
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.fromBlocks_map]; rfl
  have h_rank (x : l → k) (hx1 : P' *ᵥ x = 0) (hx2 : R' *ᵥ x = 0) : x = 0 := by
    set v : l ⊕ l → k := Sum.elim x (fun _ ↦ 0) with v_def
    have h_v0 : A' *ᵥ v = 0 := by
      ext s; cases s with
      | inl i =>
        rw [mulVec_apply, Fintype.sum_sum_type, Finset.sum_congr rfl fun _ _ ↦ rfl]
        simp only [A'_def, fromBlocks, of_apply, Sum.elim_inl, v_def, Sum.elim_inr, mul_zero,
          Finset.sum_const_zero, add_zero, Pi.zero_apply]
        rw [← mulVec_apply, hx1, Pi.zero_apply]
      | inr i =>
        rw [mulVec_apply, Fintype.sum_sum_type, Finset.sum_congr rfl fun _ _ ↦ rfl]
        simp only [A'_def, fromBlocks_apply₂₁, v_def, Sum.elim_inl, fromBlocks_apply₂₂,
          Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero, Pi.zero_apply]
        rw [← mulVec_apply, hx2, Pi.zero_apply]
    funext i
    convert_to v (Sum.inl i) = _
    · rw [v_def, Sum.elim_inl]
    · exact congrFun ((mulVec_injective_iff_isUnit).2 h15' (A'.mulVec_zero.symm ▸ h_v0)) _
  obtain ⟨Xbar, hXbar_symm, hXbar_det⟩ := field_exists_symmetric_X_invertible_sum h_rank <| by
    change f.mapMatrix Pᵀ * f.mapMatrix R = f.mapMatrix Rᵀ * f.mapMatrix P
    rw [← map_mul, (symplectic_block_conditions hA).1, map_mul]
  obtain ⟨X, hX_symm, hX_lift⟩ := lift_symmetric_matrix f
    IsLocalRing.residue_surjective Xbar hXbar_symm
  refine ⟨X, hX_symm, (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_⟩
  rw [RingHom.map_det, map_add, map_mul, hX_lift]
  exact hXbar_det.ne_zero

/-- Over any local ring, every symplectic matrix has determinant 1.
    Proof:
    1. Write A = fromBlocks P Q Rmat S
    2. Use exists_symmetric_shear_making_P_invertible to get X symmetric with P + X*Rmat invertible
    3. Let A' = L_X * A = fromBlocks (P + X*Rmat) (Q + X*S) Rmat S
    4. A' is symplectic (product of symplectic matrices)
    5. det(A') = 1 by SchurInvertible (since upper-left block is invertible)
    6. det(A') = det(L_X) * det(A) = 1 * det(A)
    7. Therefore det(A) = 1 -/
theorem symplectic_det_one_local_ring
    {l D : Type*} [DecidableEq l] [Fintype l] [CommRing D] [IsLocalRing D]
    {A : Matrix (l ⊕ l) (l ⊕ l) D}
    (hA : A ∈ symplecticGroup l D) :
    A.det = 1 := by
  let P : Matrix l l D := fun i j ↦ A (Sum.inl i) (Sum.inl j)
  let Q : Matrix l l D := fun i j ↦ A (Sum.inl i) (Sum.inr j)
  let R : Matrix l l D := fun i j ↦ A (Sum.inr i) (Sum.inl j)
  let S : Matrix l l D := fun i j ↦ A (Sum.inr i) (Sum.inr j)
  have hA_blocks : A = fromBlocks P Q R S := by
    ext i j; cases i <;> cases j <;> rfl
  rcases exists_symmetric_shear_making_P_invertible (hA_blocks ▸ hA) with ⟨X, hX_symm, hP_isUnit⟩
  let Lx : Matrix (l ⊕ l) (l ⊕ l) D := fromBlocks 1 X 0 1
  set A' : Matrix (l ⊕ l) (l ⊕ l) D := Lx * A with A'_def
  have h_fromBlocks2_in : fromBlocks (P + X * R) (Q + X * S) R S ∈ symplecticGroup l D := by
    rw [← shear_mul_symplectic_blocks, ← hA_blocks, ← A'_def]
    exact (symplecticGroup l D).mul_mem (symmetric_shear_is_symplectic hX_symm) hA
  letI : Invertible (P + X * R) := (P + X * R).invertibleOfIsUnitDet hP_isUnit
  have h_main : A'.det = 1 := by
    rw [A'_def, hA_blocks, shear_mul_symplectic_blocks]
    exact symplectic_det_one_when_P_invertible h_fromBlocks2_in
  rwa [det_mul, symmetric_shear_det_one, one_mul] at h_main

end SymplecticMatrixDet

open Matrix

lemma _root_.Matrix.J_map {l R S : Type*} [DecidableEq l] [Fintype l] [CommRing R] [CommRing S]
    (f : R →+* S) : f.mapMatrix (J l R) = J l S := by
  unfold J
  rw [RingHom.mapMatrix_apply, fromBlocks_map, Matrix.map_zero f f.map_zero,
    Matrix.map_one f f.map_zero f.map_one, Matrix.map_neg f f.map_neg,
    Matrix.map_one f f.map_zero f.map_one]

/-- The symplectic condition is preserved under ring homomorphisms. -/
lemma symplecticGroup_map
    {l R S : Type*} [DecidableEq l] [Fintype l] [CommRing R] [CommRing S]
    (f : R →+* S) {A : Matrix (l ⊕ l) (l ⊕ l) R}
    (hA : A ∈ Matrix.symplecticGroup l R) :
    f.mapMatrix A ∈ Matrix.symplecticGroup l S := by
  rw [SymplecticGroup.mem_iff] at hA ⊢
  rw [← J_map f, ← map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
    ← transpose_map, ← Matrix.map_mul, hA]; rfl

/-- **Symplectic matrices have determinant 1.** For any commutative ring `R`
and `2n × 2n` symplectic matrix `A` over `R`, `A.det = 1`. -/
theorem symplectic_matrix_det_main_statement
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    {A : Matrix (l ⊕ l) (l ⊕ l) R} (hA : A ∈ Matrix.symplecticGroup l R) :
    A.det = 1 := by
  refine sub_eq_zero.1 <| eq_zero_of_localization (A.det - 1) fun J _ ↦ ?_
  rw [map_sub, RingHom.map_det, SymplecticMatrixDet.symplectic_det_one_local_ring
    <| symplecticGroup_map (algebraMap R (Localization.AtPrime J)) hA, map_one, sub_self]
