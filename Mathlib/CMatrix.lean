module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open Matrix

namespace CartanMatrixEigenvalueFour

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private lemma dot_mulVec_eq_sum_sum {K : Type*} [CommSemiring K]
    (A : Matrix n n K) (x : n → K) :
    x ⬝ᵥ (A *ᵥ x) = ∑ i, ∑ j, x i * A i j * x j := by
  simp_rw [Matrix.dotProduct_mulVec, dotProduct, vecMul_eq_sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma abs_quadratic_le_twisted
    (H : Matrix n n ℚ) (d x : n → ℚ)
    (hH_nonneg : ∀ i j, 0 ≤ H i j) (hd_nonneg : ∀ i, 0 ≤ d i) :
    (|x ·|) ⬝ᵥ (((2 - H) * diagonal d) *ᵥ (|x ·|))
      ≤ x ⬝ᵥ (((2 + H) * diagonal d) *ᵥ x) := by
  simp_rw [dot_mulVec_eq_sum_sum, mul_diagonal]
  refine Finset.sum_le_sum (fun i hi ↦ Finset.sum_le_sum (fun j hj ↦ ?_))
  rw [mul_comm, mul_comm _ (x j), ← mul_assoc, ← mul_assoc (x j), sub_apply, add_apply,
    sub_eq_add_neg]
  by_cases hij : i = j
  · rw [← hij, abs_mul_abs_self]
    gcongr
    · exact mul_self_nonneg (x i)
    · exact hd_nonneg i
    exact neg_le_self_iff.2 (hH_nonneg i i)
  · have hbase : -(|x i| * |x j|) ≤ x i * x j :=
      neg_le_of_abs_le (le_of_eq (abs_mul ..))
    have hmul := mul_le_mul_of_nonneg_left hbase (mul_nonneg (hH_nonneg i j) (hd_nonneg j))
    simp only [mul_neg, ofNat_apply, hij, ↓reduceIte, CharP.cast_eq_zero, zero_add,
      neg_mul, ge_iff_le] at hmul ⊢
    convert hmul using 1 <;> ac_rfl

private lemma det_two_add_ne_zero_of_posDef_two_sub
    (H : Matrix n n ℚ) (d : n → ℚ)
    (hH_nonneg : ∀ i j, 0 ≤ H i j) (hd_nonneg : ∀ i, 0 ≤ d i)
    (hpos : ∀ x : n → ℚ, x ≠ 0 →
      0 < x ⬝ᵥ (((2 - H) * diagonal d) *ᵥ x)) :
    ((2 + H) * diagonal d).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx_ne, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  let y : n → ℚ := abs ∘ x
  have hpos_y : 0 < y ⬝ᵥ (((2 - H) * diagonal d) *ᵥ y) := by
    refine hpos y ?_
    rwa [← Function.support_nonempty_iff, Function.support_comp_eq _ abs_eq_zero,
      Function.support_nonempty_iff]
  have hle : y ⬝ᵥ (((2 - H) * diagonal d) *ᵥ y) ≤
    x ⬝ᵥ (((2 + H) * diagonal d) *ᵥ x) :=
      abs_quadratic_le_twisted H d x hH_nonneg hd_nonneg
  have hx_dot : x ⬝ᵥ (((2 + H) * diagonal d) *ᵥ x) = 0 := by simp [hx]
  linarith

private lemma cartanMatrix_mul_rootLength_dot_pos
    {ι R M N : Type*} [Fintype ι] [DecidableEq ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module ℚ M] [IsScalarTower ℚ R M] [Module ℚ N] [IsScalarTower ℚ R N]
    {P : RootPairing ι R M N}
    [P.IsRootSystem] [P.IsCrystallographic]
    (b : P.Base) :
    ∀ x : b.support → ℚ, x ≠ 0 →
      0 < x ⬝ᵥ
    (((b.cartanMatrix.map (algebraMap ℤ ℚ)) *
      diagonal (fun i : b.support ↦ (P.posRootForm ℚ).rootLength i)) *ᵥ x) := by
  intro x hx
  let B := P.posRootForm ℚ
  let v : b.support → P.rootSpan ℚ := fun i ↦ P.rootSpanMem ℚ i
  set y : P.rootSpan ℚ := ∑ i, x i • v i with y_def
  have hliQ : LinearIndependent ℚ v :=
    LinearIndependent.of_comp (P.rootSpan ℚ).subtype <|
      b.linearIndepOn_root.linearIndependent.restrict_scalars' ℚ
  have hy_ne : y ≠ 0 := by
    contrapose hx
    exact funext fun i ↦ Fintype.linearIndependent_iff.mp hliQ x (hx ▸ y_def) i
  have hpos : 0 < B.posForm y y := P.posRootForm_posForm_pos_of_ne_zero ℚ hy_ne
  have htwo (i j : b.support) :
      2 * B.posForm (v i) (v j) =
        (b.cartanMatrix i j : ℚ) * B.rootLength (j : ι) := by
    apply FaithfulSMul.algebraMap_injective ℚ R
    simp only [map_mul, map_ofNat, B.algebraMap_posForm, B.algebraMap_rootLength, B, v,
      RootPairing.Base.cartanMatrixIn_def]
    convert B.toInvariantForm.two_mul_apply_root_root i j
    exact (RootPairing.pairingIn_rat P ↑i ↑j).symm ▸ (P.algebraMap_pairingIn ℚ i j)
  have hdot : x ⬝ᵥ (((b.cartanMatrix.map (algebraMap ℤ ℚ)) *
    diagonal (fun i : b.support ↦ B.rootLength i)) *ᵥ x) =
      2 * B.posForm y y := by
    simp_rw [dot_mulVec_eq_sum_sum, mul_diagonal]
    convert_to _ = ∑ i, ∑ j, x i * (2 * B.posForm (v i) (v j)) * x j
    · simp only [y_def, Finset.univ_eq_attach, map_sum, map_smul, LinearMap.coe_sum,
      LinearMap.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_)
      rw [← B.isSymm_posForm.1 (v j) (v i), RingHom.id_apply]; ac_rfl
    simp_rw [htwo, algebraMap_int_eq, Int.coe_castRingHom, map_apply]
  rwa [hdot, Rat.mul_pos_iff_of_pos_left rfl]

lemma cartanMatrix_det_four_sub_ne_zero
    {ι R M N : Type*} [Finite ι] [DecidableEq ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N}
    [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) :
    (4 - b.cartanMatrix).det ≠ 0 := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  let _ : Module ℚ N := Module.compHom N (algebraMap ℚ R)
  set A := b.cartanMatrix.map (algebraMap ℤ ℚ) with A_def
  set H := 2 - A with H_def
  let d : b.support → ℚ := fun i ↦ (P.posRootForm ℚ).rootLength i
  have hd_nonneg : ∀ i, 0 ≤ d i := fun i ↦ le_of_lt ((P.posRootForm ℚ).rootLength_pos i)
  have hH_nonneg : ∀ i j, 0 ≤ H i j := by
    intro i j
    by_cases hij : i = j
    · simp [hij, H_def, A_def, Matrix.ofNat_apply]
    · simp [H_def, Matrix.ofNat_apply, hij, b.cartanMatrix_le_zero_of_ne i j hij, A_def]
  have hCD : ((2 + H) * diagonal d).det ≠ 0 := by
    refine det_two_add_ne_zero_of_posDef_two_sub H d hH_nonneg hd_nonneg (fun x hx ↦ ?_)
    convert cartanMatrix_mul_rootLength_dot_pos b x hx
    rw [H_def, sub_sub_cancel]
  contrapose hCD
  have hmap : 4 - A = (algebraMap ℤ ℚ).mapMatrix (4 - b.cartanMatrix) := by
    ext i j
    simp only [A_def, algebraMap_int_eq, Int.coe_castRingHom, sub_apply, map_apply,
      RingHom.mapMatrix_apply, Int.cast_sub, sub_left_inj, Matrix.ofNat_apply]
    split_ifs <;> rfl
  rw [H_def, ← add_sub_assoc, two_add_two_eq_four, hmap, Matrix.det_mul, ← RingHom.map_det, hCD,
    map_zero, zero_mul]

end CartanMatrixEigenvalueFour

end
