/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johnathon Kyle Armstrong
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum

import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Spectral classification and interlacing for bipartite Coxeter elements

Let `A : Matrix ι κ ℝ` be a real matrix between finite index sets `ι` and `κ`. The associated
bipartite symmetric bilinear form on `ι ⊕ κ` is
`B = [[2, -A], [-Aᵀ, 2]]` (`Matrix.BipartiteCoxeter.form A`),
the products of the reflections in the two parts are
`s₊ = [[-1, A], [0, 1]]` and `s₋ = [[1, 0], [Aᵀ, -1]]`,
and the bipartite Coxeter element is `w = s₊ s₋` (`Matrix.BipartiteCoxeter.coxeter A`).

Following A'Campo (1976) and McMullen (2002), we prove:
* **Eigenvalue correspondence** (`eigenvalue_quadratic_of_ne_neg_one`): every complex eigenvalue
  `λ ≠ -1` of `w` satisfies `λ² - (ν - 2) λ + 1 = 0` for some real eigenvalue `ν ≥ 0` of `A Aᵀ`.
* **Spectral classification**:
  - `posDef_form_iff`: `B` is positive definite (spherical) iff every complex eigenvalue of `w`
    has modulus `1` and `1` is not an eigenvalue;
  - `posSemidef_and_not_posDef_form_iff`: `B` is positive semidefinite and degenerate (affine)
    iff every complex eigenvalue of `w` has modulus `1` and `1` is an eigenvalue;
  - `not_posSemidef_form_iff`: `B` is indefinite (hyperbolic / higher rank) iff `w` has a real
    eigenvalue `λ > 1`.
* **Submatrix spectral interlacing**:
  - `exists_eigenvalue_norm_le_of_submatrix`: for injective `f : ι' → ι` and `g : κ' → κ`, every
    complex eigenvalue `λ'` of `w(A.submatrix f g)` is dominated in modulus by an eigenvalue `λ`
    of `w(A)`: `‖λ'‖ ≤ ‖λ‖`.
  - `exists_eigenvalue_norm_lt_of_submatrix`: strict inequality `‖λ'‖ < ‖λ‖` when `B(A)` is not
    positive semidefinite and `B(A.submatrix f g)` is positive semidefinite.

## References
* N. A'Campo, *Sur les valeurs propres de la transformation de Coxeter*, Invent. Math. 33 (1976),
  61–67.
* C. T. McMullen, *Coxeter groups, Salem numbers and the Hilbert metric*, Publ. Math. IHÉS 95
  (2002), 151–183.
-/

open Matrix

@[expose] public section

namespace Matrix.BipartiteCoxeter

section General

variable {α : Type*} [Fintype α]

/-- `M : Matrix α α ℝ` has `lam : ℂ` as a complex eigenvalue on `α → ℂ`. -/
def HasComplexEigenvalue (M : Matrix α α ℝ) (lam : ℂ) : Prop :=
  ∃ v : α → ℂ, v ≠ 0 ∧ (M.map (↑) : Matrix α α ℂ) *ᵥ v = lam • v

private lemma dot_self_nonneg (v : α → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (v i)

private lemma dot_self_pos {v : α → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (dot_self_nonneg v) (fun h ↦ hv (dotProduct_self_eq_zero.mp h.symm))

omit [Fintype α] in
private lemma mulVec_map_ofReal {β : Type*} [Fintype β] (M : Matrix α β ℝ) (v : β → ℝ) :
    (M.map (↑) : Matrix α β ℂ) *ᵥ (fun i ↦ (v i : ℂ)) = fun i ↦ ((M *ᵥ v) i : ℂ) := by
  funext i
  simp [mulVec, dotProduct]

private lemma hasComplexEigenvalue_of_real {M : Matrix α α ℝ} {lam : ℝ} {v : α → ℝ}
    (hv : v ≠ 0) (h : M *ᵥ v = lam • v) : HasComplexEigenvalue M lam := by
  refine ⟨fun i ↦ (v i : ℂ), fun h0 ↦ hv (funext fun i ↦ by
    simpa using congr_fun h0 i), ?_⟩
  rw [mulVec_map_ofReal, h]
  funext i
  simp

private lemma re_mulVec_map (M : Matrix α α ℝ) (x : α → ℂ) (i : α) :
    (((M.map (↑) : Matrix α α ℂ) *ᵥ x) i).re = (M *ᵥ fun j ↦ (x j).re) i := by
  simp [mulVec, dotProduct, Complex.re_sum]

private lemma im_mulVec_map (M : Matrix α α ℝ) (x : α → ℂ) (i : α) :
    (((M.map (↑) : Matrix α α ℂ) *ᵥ x) i).im = (M *ᵥ fun j ↦ (x j).im) i := by
  simp [mulVec, dotProduct, Complex.im_sum]

private lemma real_parts_of_eigen (M : Matrix α α ℝ) (x : α → ℂ) (ν : ℂ)
    (h : (M.map (↑) : Matrix α α ℂ) *ᵥ x = ν • x) :
    M *ᵥ (fun j ↦ (x j).re) = ν.re • (fun j ↦ (x j).re) - ν.im • (fun j ↦ (x j).im) ∧
    M *ᵥ (fun j ↦ (x j).im) = ν.im • (fun j ↦ (x j).re) + ν.re • (fun j ↦ (x j).im) := by
  constructor
  · funext i
    rw [← re_mulVec_map, h]
    simp
  · funext i
    rw [← im_mulVec_map, h]
    simp [add_comm]

private lemma real_eigen_of_complex (M : Matrix α α ℝ) (hM : Mᵀ = M) (x : α → ℂ) (hx : x ≠ 0)
    (ν : ℂ) (h : (M.map (↑) : Matrix α α ℂ) *ᵥ x = ν • x) :
    ν.im = 0 ∧ ∃ a : α → ℝ, a ≠ 0 ∧ M *ᵥ a = ν.re • a := by
  obtain ⟨h1, h2⟩ := real_parts_of_eigen M x ν h
  set a : α → ℝ := fun j ↦ (x j).re
  set b : α → ℝ := fun j ↦ (x j).im
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hx
    funext j
    apply Complex.ext
    · simpa [a] using congr_fun hc.1 j
    · simpa [b] using congr_fun hc.2 j
  have hsym : a ⬝ᵥ (M *ᵥ b) = b ⬝ᵥ (M *ᵥ a) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]
  rw [h1, h2] at hsym
  simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hsym
  have hpos : 0 < a ⬝ᵥ a + b ⬝ᵥ b := by
    rcases hab with ha | hb
    · exact add_pos_of_pos_of_nonneg (dot_self_pos ha) (dot_self_nonneg b)
    · exact add_pos_of_nonneg_of_pos (dot_self_nonneg a) (dot_self_pos hb)
  have hcomm : a ⬝ᵥ b = b ⬝ᵥ a := dotProduct_comm a b
  rw [hcomm] at hsym
  have him : ν.im * (a ⬝ᵥ a + b ⬝ᵥ b) = 0 := by linarith
  have him0 : ν.im = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · linarith
  refine ⟨him0, ?_⟩
  rw [him0, zero_smul, sub_zero] at h1
  rw [him0, zero_smul, zero_add] at h2
  rcases hab with ha | hb
  · exact ⟨a, ha, h1⟩
  · exact ⟨b, hb, h2⟩

private lemma norm_eq_one_of_quadratic (lam : ℂ) (b : ℝ) (hb : b ^ 2 ≤ 4)
    (h : lam ^ 2 - b * lam + 1 = 0) : ‖lam‖ = 1 := by
  have hre := congr_arg Complex.re h
  have him := congr_arg Complex.im h
  simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.zero_re] at hre
  simp only [pow_two, Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_im, Complex.zero_im] at him
  have hsq : lam.re ^ 2 + lam.im ^ 2 = 1 := by
    by_cases hc : lam.im = 0
    · rw [hc] at hre
      have : (2 * lam.re - b) ^ 2 = b ^ 2 - 4 := by nlinarith
      have h1 : (2 * lam.re - b) ^ 2 = 0 := by nlinarith [sq_nonneg (2 * lam.re - b)]
      have h2 : 2 * lam.re = b := by nlinarith [sq_nonneg (2 * lam.re - b)]
      rw [hc]; nlinarith
    · have h2 : 2 * lam.re = b := by
        have : lam.im * (2 * lam.re - b) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hc
        · linarith
      linear_combination -hre + lam.re * h2
  have hn : ‖lam‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith
  have hn0 : 0 ≤ ‖lam‖ := norm_nonneg _
  nlinarith

private lemma exists_eigen_nonpos_of_not_posDef (N : Matrix α α ℝ)
    (hN : N.IsHermitian) (h : ¬ N.PosDef) :
    ∃ θ : ℝ, θ ≤ 0 ∧ ∃ u : α → ℝ, u ≠ 0 ∧ N *ᵥ u = θ • u := by
  classical
  rw [hN.posDef_iff_eigenvalues_pos] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  refine ⟨hN.eigenvalues i, hi, ⇑(hN.eigenvectorBasis i), ?_, hN.mulVec_eigenvectorBasis i⟩
  intro h0
  apply (hN.eigenvectorBasis).orthonormal.ne_zero i
  ext j
  simpa using congr_fun h0 j

private lemma exists_eigen_neg_of_not_posSemidef (N : Matrix α α ℝ)
    (hN : N.IsHermitian) (h : ¬ N.PosSemidef) :
    ∃ θ : ℝ, θ < 0 ∧ ∃ u : α → ℝ, u ≠ 0 ∧ N *ᵥ u = θ • u := by
  classical
  rw [hN.posSemidef_iff_eigenvalues_nonneg] at h
  simp only [Pi.le_def, Pi.zero_apply, not_forall, not_le] at h
  obtain ⟨i, hi⟩ := h
  refine ⟨hN.eigenvalues i, hi, ⇑(hN.eigenvectorBasis i), ?_, hN.mulVec_eigenvectorBasis i⟩
  intro h0
  apply (hN.eigenvectorBasis).orthonormal.ne_zero i
  ext j
  simpa using congr_fun h0 j

omit [Fintype α] in
private lemma isHermitian_of_transpose_eq {N : Matrix α α ℝ} (h : Nᵀ = N) : N.IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, h]

end General

/-! ### Bipartite bilinear form and Coxeter element -/

section Bipartite

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ)

/-- The symmetric bilinear form `[[2, -A], [-Aᵀ, 2]]` associated to a bipartite matrix `A`. -/
def form : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  fromBlocks (2 • (1 : Matrix ι ι ℝ)) (-A) (-Aᵀ) (2 • (1 : Matrix κ κ ℝ))

/-- The product `s₊ = [[-1, A], [0, 1]]` of the reflections in the first part `ι`. -/
def reflLeft : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := fromBlocks (-1) A 0 1

/-- The product `s₋ = [[1, 0], [Aᵀ, -1]]` of the reflections in the second part `κ`. -/
def reflRight : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := fromBlocks 1 0 Aᵀ (-1)

/-- The bipartite Coxeter element `w = s₊ s₋`. -/
def coxeter : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := reflLeft A * reflRight A

theorem coxeter_eq : coxeter A = fromBlocks (A * Aᵀ - 1) (-A) Aᵀ (-1) := by
  simp only [coxeter, reflLeft, reflRight, fromBlocks_multiply]
  congr 1 <;> simp [sub_eq_add_neg, add_comm]

omit [Fintype ι] [Fintype κ] in
theorem form_transpose : (form A)ᵀ = form A := by
  simp [form, fromBlocks_transpose]

omit [Fintype ι] [Fintype κ] in
theorem form_isHermitian : (form A).IsHermitian :=
  isHermitian_of_transpose_eq (form_transpose A)

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
private lemma AAt_transpose : (A * Aᵀ)ᵀ = A * Aᵀ := by
  rw [transpose_mul, transpose_transpose]

omit [DecidableEq ι] [DecidableEq κ] in
private lemma dot_AAt (a : ι → ℝ) : a ⬝ᵥ ((A * Aᵀ) *ᵥ a) = (Aᵀ *ᵥ a) ⬝ᵥ (Aᵀ *ᵥ a) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]

private lemma qf_form (x : ι → ℝ) (y : κ → ℝ) :
    Sum.elim x y ⬝ᵥ (form A *ᵥ Sum.elim x y) =
      2 * (x ⬝ᵥ x) - 2 * ((Aᵀ *ᵥ x) ⬝ᵥ y) + 2 * (y ⬝ᵥ y) := by
  simp only [form, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim, smul_mulVec, one_mulVec, neg_mulVec, dotProduct_add,
    dotProduct_neg, dotProduct_smul]
  have h1 : x ⬝ᵥ (A *ᵥ y) = (Aᵀ *ᵥ x) ⬝ᵥ y := by
    rw [dotProduct_mulVec, mulVec_transpose]
  have h2 : y ⬝ᵥ (Aᵀ *ᵥ x) = (Aᵀ *ᵥ x) ⬝ᵥ y := dotProduct_comm _ _
  rw [h1, h2]
  ring

private lemma qf_form' (v : ι ⊕ κ → ℝ) :
    v ⬝ᵥ (form A *ᵥ v) = 2 * ((v ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inl)) -
      2 * ((Aᵀ *ᵥ (v ∘ Sum.inl)) ⬝ᵥ (v ∘ Sum.inr)) +
      2 * ((v ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inr)) := by
  conv_lhs => rw [← Sum.elim_comp_inl_inr v]
  exact qf_form A _ _

private lemma qf_nonneg_of_bound (hb : ∀ a : ι → ℝ, (Aᵀ *ᵥ a) ⬝ᵥ (Aᵀ *ᵥ a) ≤ 4 * (a ⬝ᵥ a))
    (v : ι ⊕ κ → ℝ) : 0 ≤ v ⬝ᵥ (form A *ᵥ v) := by
  rw [qf_form']
  set x := v ∘ Sum.inl
  set y := v ∘ Sum.inr
  have h0 := dot_self_nonneg (Aᵀ *ᵥ x - (2 : ℝ) • y)
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul] at h0
  have hc : y ⬝ᵥ (Aᵀ *ᵥ x) = (Aᵀ *ᵥ x) ⬝ᵥ y := dotProduct_comm _ _
  have := hb x
  nlinarith

private lemma qf_test_vector (a : ι → ℝ) (t : ℝ) (ht : 0 < t)
    (ha : (A * Aᵀ) *ᵥ a = (t ^ 2) • a) :
    Sum.elim a (t⁻¹ • (Aᵀ *ᵥ a)) ⬝ᵥ (form A *ᵥ Sum.elim a (t⁻¹ • (Aᵀ *ᵥ a))) =
      2 * (a ⬝ᵥ a) * (2 - t) := by
  rw [qf_form]
  have hAA : (Aᵀ *ᵥ a) ⬝ᵥ (Aᵀ *ᵥ a) = t ^ 2 * (a ⬝ᵥ a) := by
    rw [← dot_AAt, ha, dotProduct_smul, smul_eq_mul]
  simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul, hAA]
  field_simp
  ring

omit [DecidableEq ι] [DecidableEq κ] in
private lemma eigen_AAt_nonneg {a : ι → ℝ} (ha0 : a ≠ 0) {ν : ℝ}
    (ha : (A * Aᵀ) *ᵥ a = ν • a) : 0 ≤ ν := by
  have h := dot_AAt A a
  rw [ha, dotProduct_smul, smul_eq_mul] at h
  have h1 := dot_self_pos ha0
  have h2 := dot_self_nonneg (Aᵀ *ᵥ a)
  by_contra hν
  push Not at hν
  nlinarith

private lemma eigen_AAt_le_four (hpsd : (form A).PosSemidef) {a : ι → ℝ} (ha0 : a ≠ 0)
    {ν : ℝ} (ha : (A * Aᵀ) *ᵥ a = ν • a) : ν ≤ 4 := by
  have hν0 := eigen_AAt_nonneg A ha0 ha
  rcases eq_or_lt_of_le hν0 with h | hpos
  · rw [← h]; norm_num
  set t := Real.sqrt ν
  have ht : 0 < t := Real.sqrt_pos.mpr hpos
  have ht2 : t ^ 2 = ν := Real.sq_sqrt hν0
  have hq := qf_test_vector A a t ht (by rw [ht2]; exact ha)
  have hnn : 0 ≤ Sum.elim a (t⁻¹ • (Aᵀ *ᵥ a)) ⬝ᵥ (form A *ᵥ Sum.elim a (t⁻¹ • (Aᵀ *ᵥ a))) := by
    simpa [star_trivial] using hpsd.dotProduct_mulVec_nonneg (Sum.elim a (t⁻¹ • (Aᵀ *ᵥ a)))
  rw [hq] at hnn
  have h1 := dot_self_pos ha0
  have ht' : t ≤ 2 := by
    by_contra hc; push Not at hc; nlinarith
  nlinarith

private lemma eigen_AAt_lt_four (hpd : (form A).PosDef) {a : ι → ℝ} (ha0 : a ≠ 0)
    {ν : ℝ} (ha : (A * Aᵀ) *ᵥ a = ν • a) : ν < 4 := by
  have hν0 := eigen_AAt_nonneg A ha0 ha
  rcases eq_or_lt_of_le hν0 with h | hpos
  · rw [← h]; norm_num
  set t := Real.sqrt ν
  have ht : 0 < t := Real.sqrt_pos.mpr hpos
  have ht2 : t ^ 2 = ν := Real.sq_sqrt hν0
  have hq := qf_test_vector A a t ht (by rw [ht2]; exact ha)
  have hne : Sum.elim a (t⁻¹ • (Aᵀ *ᵥ a)) ≠ 0 := by
    intro h0; apply ha0; funext i; simpa using congr_fun h0 (Sum.inl i)
  have hpos' : 0 < Sum.elim a (t⁻¹ • (Aᵀ *ᵥ a)) ⬝ᵥ (form A *ᵥ Sum.elim a (t⁻¹ • (Aᵀ *ᵥ a))) := by
    simpa [star_trivial] using (posDef_iff_dotProduct_mulVec.mp hpd).2 hne
  rw [hq] at hpos'
  have h1 := dot_self_pos ha0
  have ht' : t < 2 := by
    by_contra hc; push Not at hc; nlinarith
  nlinarith

private lemma coxeter_mulVec_of_AAt_mulVec (u : ι → ℝ) (ν lam : ℝ)
    (hu : (A * Aᵀ) *ᵥ u = ν • u) (hlam : lam ^ 2 - (ν - 2) * lam + 1 = 0) :
    coxeter A *ᵥ Sum.elim ((lam + 1) • u) (Aᵀ *ᵥ u) =
      lam • Sum.elim ((lam + 1) • u) (Aᵀ *ᵥ u) := by
  rw [coxeter_eq, fromBlocks_mulVec]
  funext k
  cases k with
  | inl i =>
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inl, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, sub_mulVec, one_mulVec, Matrix.neg_mul, neg_mulVec, mulVec_smul,
      mulVec_mulVec, hu, Pi.sub_apply, Pi.neg_apply]
    linear_combination -u i * hlam
  | inr j =>
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inr, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, mulVec_smul, neg_mulVec, one_mulVec, Pi.neg_apply]
    ring

private lemma coxeter_map :
    ((coxeter A).map (↑) : Matrix _ _ ℂ) =
      fromBlocks ((A.map (↑)) * (A.map (↑))ᵀ - 1) (-(A.map (↑))) (A.map (↑))ᵀ (-1) := by
  rw [coxeter_eq]
  ext (i | i) (j | j) <;>
    simp [fromBlocks, Matrix.mul_apply, Matrix.one_apply] <;>
    split_ifs <;> simp

/-- Every complex eigenvalue `λ ≠ -1` of the bipartite Coxeter element `coxeter A` satisfies
`λ² - (ν - 2) λ + 1 = 0` for a real eigenvalue `ν ≥ 0` of `A Aᵀ`. -/
theorem eigenvalue_quadratic_of_ne_neg_one {lam : ℂ} (h : HasComplexEigenvalue (coxeter A) lam)
    (hlam : lam ≠ -1) :
    ∃ ν : ℝ, 0 ≤ ν ∧ (∃ a : ι → ℝ, a ≠ 0 ∧ (A * Aᵀ) *ᵥ a = ν • a) ∧
      lam ^ 2 - ((ν : ℂ) - 2) * lam + 1 = 0 := by
  obtain ⟨v, hv0, hv⟩ := h
  rw [coxeter_map, fromBlocks_mulVec] at hv
  set Ac : Matrix ι κ ℂ := A.map (↑)
  set x := v ∘ Sum.inl
  set y := v ∘ Sum.inr
  have E1 : (Ac * Acᵀ - 1) *ᵥ x + (-Ac) *ᵥ y = lam • x := by
    funext i; simpa [x, y] using congr_fun hv (Sum.inl i)
  have E2 : Acᵀ *ᵥ x + (-1 : Matrix κ κ ℂ) *ᵥ y = lam • y := by
    funext i; simpa [x, y] using congr_fun hv (Sum.inr i)
  have hl1 : lam + 1 ≠ 0 := fun h ↦ hlam (by linear_combination h)
  have E2' : Acᵀ *ᵥ x = (lam + 1) • y := by
    rw [neg_mulVec, one_mulVec] at E2
    rw [add_smul, one_smul, ← E2]; abel
  have hx0 : x ≠ 0 := by
    intro hx
    apply hv0
    have hy : y = 0 := by
      rw [hx, mulVec_zero] at E2'
      funext j
      have := congr_fun E2' j
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hl1
    funext k
    cases k with
    | inl i => exact congr_fun hx i
    | inr j => exact congr_fun hy j
  have E3 : lam • ((Ac * Acᵀ) *ᵥ x) = ((lam + 1) ^ 2) • x := by
    have := congr_arg ((lam + 1) • ·) E1
    simp only [sub_mulVec, one_mulVec, neg_mulVec, smul_add, smul_sub, smul_neg] at this
    have hAc : (lam + 1) • (Ac *ᵥ y) = Ac *ᵥ (Acᵀ *ᵥ x) := by
      rw [← mulVec_smul, ← E2']
    rw [hAc, mulVec_mulVec] at this
    funext i
    have hi := congr_fun this i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    linear_combination hi
  have hl0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at E3
    apply hx0
    funext i
    have := congr_fun E3 i
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, zero_add, one_pow,
      one_mul] at this
    exact this.symm
  set ν : ℂ := (lam + 1) ^ 2 / lam
  have E4 : (Ac * Acᵀ) *ᵥ x = ν • x := by
    funext i
    have := congr_fun E3 i
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    simp only [ν]
    field_simp
    linear_combination this
  have hmap : ((A * Aᵀ).map (↑) : Matrix ι ι ℂ) = Ac * Acᵀ := by
    ext i j; simp [Ac, Matrix.mul_apply]
  rw [← hmap] at E4
  obtain ⟨him, a, ha0, ha⟩ := real_eigen_of_complex (A * Aᵀ) (AAt_transpose A) x hx0 ν E4
  refine ⟨ν.re, eigen_AAt_nonneg A ha0 ha, ⟨a, ha0, ha⟩, ?_⟩
  have hνc : (ν.re : ℂ) = ν := Complex.ext (by simp) (by simp [him])
  rw [hνc]
  simp only [ν]
  field_simp
  ring

/-! ### Spectral classification (A'Campo) -/

private lemma norm_eq_one_of_posSemidef (hpsd : (form A).PosSemidef) (lam : ℂ)
    (h : HasComplexEigenvalue (coxeter A) lam) : ‖lam‖ = 1 := by
  by_cases hl : lam = -1
  · rw [hl]; simp
  obtain ⟨ν, hν0, ⟨a, ha0, ha⟩, hq⟩ := eigenvalue_quadratic_of_ne_neg_one A h hl
  have hν4 := eigen_AAt_le_four A hpsd ha0 ha
  refine norm_eq_one_of_quadratic lam (ν - 2) (by nlinarith) ?_
  push_cast
  exact hq

private lemma not_eigen_one_of_posDef (hpd : (form A).PosDef) :
    ¬ HasComplexEigenvalue (coxeter A) 1 := by
  intro h
  obtain ⟨ν, _, ⟨a, ha0, ha⟩, hq⟩ := eigenvalue_quadratic_of_ne_neg_one A h (by norm_num)
  have hν : (ν : ℂ) = 4 := by linear_combination -hq
  have hν' : ν = 4 := by exact_mod_cast hν
  have := eigen_AAt_lt_four A hpd ha0 ha
  linarith

private lemma eigen_one_of_posSemidef_not_posDef (hpsd : (form A).PosSemidef)
    (hnpd : ¬ (form A).PosDef) : HasComplexEigenvalue (coxeter A) 1 := by
  have hker : ∃ v : ι ⊕ κ → ℝ, v ≠ 0 ∧ v ⬝ᵥ (form A *ᵥ v) = 0 := by
    rw [posDef_iff_dotProduct_mulVec] at hnpd
    push Not at hnpd
    obtain ⟨v, hv0, hle⟩ := hnpd (form_isHermitian A)
    have hge : 0 ≤ v ⬝ᵥ (form A *ᵥ v) := by
      simpa [star_trivial] using hpsd.dotProduct_mulVec_nonneg v
    simp only [star_trivial] at hle
    exact ⟨v, hv0, le_antisymm hle hge⟩
  obtain ⟨v, hv0, hv⟩ := hker
  have hBv : form A *ᵥ v = 0 := by
    set w := form A *ᵥ v
    by_contra hw0
    have ha : 0 < w ⬝ᵥ w := dot_self_pos hw0
    set b := w ⬝ᵥ (form A *ᵥ w)
    have hb : 0 ≤ b := by simpa [star_trivial] using hpsd.dotProduct_mulVec_nonneg w
    set t : ℝ := -(w ⬝ᵥ w) / (b + 1)
    have hnonneg : 0 ≤ (v + t • w) ⬝ᵥ (form A *ᵥ (v + t • w)) := by
      simpa [star_trivial] using hpsd.dotProduct_mulVec_nonneg (v + t • w)
    have hexp : (v + t • w) ⬝ᵥ (form A *ᵥ (v + t • w)) =
        v ⬝ᵥ (form A *ᵥ v) + 2 * t * (w ⬝ᵥ w) + t ^ 2 * b := by
      simp only [b, w, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul]
      have hsym : v ⬝ᵥ (form A *ᵥ w) = w ⬝ᵥ (form A *ᵥ v) := by
        rw [dotProduct_mulVec, ← mulVec_transpose, form_transpose, dotProduct_comm]
      rw [hsym]
      ring
    rw [hv, zero_add] at hexp
    have hneg : 2 * t * (w ⬝ᵥ w) + t ^ 2 * b < 0 := by
      have hden : 0 < b + 1 := by linarith
      have hnum : -(w ⬝ᵥ w) ^ 2 * (b + 2) < 0 := by nlinarith
      have heq : 2 * t * (w ⬝ᵥ w) + t ^ 2 * b = -(w ⬝ᵥ w) ^ 2 * (b + 2) / (b + 1) ^ 2 := by
        simp only [t]; field_simp; ring
      rw [heq]
      exact div_neg_of_neg_of_pos hnum (sq_pos_of_pos hden)
    linarith
  rw [← Sum.elim_comp_inl_inr v] at hBv
  rw [form, fromBlocks_mulVec] at hBv
  set x := v ∘ Sum.inl
  set y := v ∘ Sum.inr
  have e1 : (2 : ℝ) • x = A *ᵥ y := by
    funext i
    have := congr_fun hBv (Sum.inl i)
    rw [two_smul, add_mulVec, one_mulVec] at this
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inl, Pi.add_apply, Pi.zero_apply,
      neg_mulVec, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  have e2 : Aᵀ *ᵥ x = (2 : ℝ) • y := by
    funext j
    have := congr_fun hBv (Sum.inr j)
    have h2 : ((2 • (1 : Matrix κ κ ℝ)) *ᵥ y) j = 2 * y j := by
      rw [two_smul, add_mulVec, one_mulVec]; simp; ring
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inr, Pi.add_apply, Pi.zero_apply,
      neg_mulVec, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [h2] at this
    linarith
  have hw : coxeter A *ᵥ v = (1 : ℝ) • v := by
    rw [one_smul, coxeter_eq]
    conv_lhs => rw [← Sum.elim_comp_inl_inr v]
    rw [fromBlocks_mulVec]
    conv_rhs => rw [← Sum.elim_comp_inl_inr v]
    congr 1
    · simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
      rw [sub_mulVec, ← mulVec_mulVec, e2, mulVec_smul, ← e1, neg_mulVec, ← e1, one_mulVec]
      funext i; simp [x]; ring
    · simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
      rw [e2, neg_mulVec, one_mulVec]
      funext j; simp [y]; ring
  simpa using hasComplexEigenvalue_of_real hv0 hw

private lemma real_eigen_of_AAt_gt_four {u : ι → ℝ} (hu0 : u ≠ 0) {ν : ℝ}
    (hu : (A * Aᵀ) *ᵥ u = ν • u) (hν : 4 < ν) :
    1 < ((ν - 2) + Real.sqrt ((ν - 2) ^ 2 - 4)) / 2 ∧
      HasComplexEigenvalue (coxeter A) (((ν - 2) + Real.sqrt ((ν - 2) ^ 2 - 4)) / 2 : ℝ) := by
  set lam : ℝ := ((ν - 2) + Real.sqrt ((ν - 2) ^ 2 - 4)) / 2
  have hdisc : 0 ≤ (ν - 2) ^ 2 - 4 := by nlinarith
  have hs := Real.sq_sqrt hdisc
  have hlam : lam ^ 2 - (ν - 2) * lam + 1 = 0 := by
    simp only [lam]; nlinarith
  have hgt : 1 < lam := by
    have := Real.sqrt_nonneg ((ν - 2) ^ 2 - 4)
    simp only [lam]; linarith
  have heig := coxeter_mulVec_of_AAt_mulVec A u ν lam hu hlam
  refine ⟨hgt, hasComplexEigenvalue_of_real (v := Sum.elim ((lam + 1) • u) (Aᵀ *ᵥ u)) ?_ heig⟩
  intro h0
  apply hu0
  funext i
  have := congr_fun h0 (Sum.inl i)
  simp only [Sum.elim_inl, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  have hl1 : lam + 1 ≠ 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left hl1

private lemma real_eigen_gt_one_of_not_posSemidef (h : ¬ (form A).PosSemidef) :
    ∃ lam : ℝ, 1 < lam ∧ HasComplexEigenvalue (coxeter A) lam := by
  have hv : ∃ v : ι ⊕ κ → ℝ, v ⬝ᵥ (form A *ᵥ v) < 0 := by
    rw [posSemidef_iff_dotProduct_mulVec] at h
    push Not at h
    obtain ⟨v, hv⟩ := h (form_isHermitian A)
    exact ⟨v, by simpa [star_trivial] using hv⟩
  obtain ⟨v, hv⟩ := hv
  set N : Matrix ι ι ℝ := (4 : ℝ) • 1 - A * Aᵀ
  have hNt : Nᵀ = N := by simp [N, transpose_sub]
  have hN := isHermitian_of_transpose_eq hNt
  have hnot : ¬ N.PosSemidef := by
    intro hpsd
    have hb : ∀ a : ι → ℝ, (Aᵀ *ᵥ a) ⬝ᵥ (Aᵀ *ᵥ a) ≤ 4 * (a ⬝ᵥ a) := by
      intro a
      have := hpsd.dotProduct_mulVec_nonneg a
      simp only [star_trivial, N, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul, dot_AAt] at this
      linarith
    exact absurd (qf_nonneg_of_bound A hb v) (not_le.mpr hv)
  obtain ⟨θ, hθ, u, hu0, hu⟩ := exists_eigen_neg_of_not_posSemidef N hN hnot
  have huν : (A * Aᵀ) *ᵥ u = (4 - θ) • u := by
    have : (A * Aᵀ) *ᵥ u = (4 : ℝ) • u - N *ᵥ u := by
      simp [N, sub_mulVec, smul_mulVec]
    rw [this, hu, ← sub_smul]
  exact ⟨_, real_eigen_of_AAt_gt_four A hu0 huν (by linarith)⟩

/-- **A'Campo's spherical characterization**: `form A` is positive definite if and only if every
complex eigenvalue of `coxeter A` has modulus `1` and `1` is not an eigenvalue. -/
theorem posDef_form_iff :
    (form A).PosDef ↔
      (∀ lam, HasComplexEigenvalue (coxeter A) lam → ‖lam‖ = 1) ∧
        ¬ HasComplexEigenvalue (coxeter A) 1 := by
  constructor
  · intro hpd
    exact ⟨norm_eq_one_of_posSemidef A hpd.posSemidef, not_eigen_one_of_posDef A hpd⟩
  · rintro ⟨hn, h1⟩
    by_contra hnpd
    by_cases hpsd : (form A).PosSemidef
    · exact h1 (eigen_one_of_posSemidef_not_posDef A hpsd hnpd)
    · obtain ⟨lam, hl, he⟩ := real_eigen_gt_one_of_not_posSemidef A hpsd
      have := hn _ he
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
      linarith

/-- **A'Campo's affine characterization**: `form A` is positive semidefinite and degenerate if and
only if every complex eigenvalue of `coxeter A` has modulus `1` and `1` is an eigenvalue. -/
theorem posSemidef_and_not_posDef_form_iff :
    ((form A).PosSemidef ∧ ¬ (form A).PosDef) ↔
      (∀ lam, HasComplexEigenvalue (coxeter A) lam → ‖lam‖ = 1) ∧
        HasComplexEigenvalue (coxeter A) 1 := by
  constructor
  · rintro ⟨hpsd, hnpd⟩
    exact ⟨norm_eq_one_of_posSemidef A hpsd, eigen_one_of_posSemidef_not_posDef A hpsd hnpd⟩
  · rintro ⟨hn, h1⟩
    refine ⟨?_, fun hpd ↦ not_eigen_one_of_posDef A hpd h1⟩
    by_contra hpsd
    obtain ⟨lam, hl, he⟩ := real_eigen_gt_one_of_not_posSemidef A hpsd
    have := hn _ he
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
    linarith

/-- **A'Campo's hyperbolic/indefinite characterization**: `form A` is not positive semidefinite
if and only if `coxeter A` has a real eigenvalue `λ > 1`. -/
theorem not_posSemidef_form_iff :
    ¬ (form A).PosSemidef ↔ ∃ lam : ℝ, 1 < lam ∧ HasComplexEigenvalue (coxeter A) lam := by
  constructor
  · exact real_eigen_gt_one_of_not_posSemidef A
  · rintro ⟨lam, hl, he⟩ hpsd
    have := norm_eq_one_of_posSemidef A hpsd _ he
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
    linarith

/-! ### Submatrix spectral interlacing (McMullen) -/

private lemma rplus_mono {x y : ℝ} (hx : 4 ≤ x) (hxy : x ≤ y) :
    ((x - 2) + Real.sqrt ((x - 2) ^ 2 - 4)) / 2 ≤
      ((y - 2) + Real.sqrt ((y - 2) ^ 2 - 4)) / 2 := by
  have : Real.sqrt ((x - 2) ^ 2 - 4) ≤ Real.sqrt ((y - 2) ^ 2 - 4) :=
    Real.sqrt_le_sqrt (by nlinarith)
  linarith

private lemma complex_eigen_of_AAt (u : ι → ℝ) (ν : ℝ) (hu : (A * Aᵀ) *ᵥ u = ν • u) (lam : ℂ)
    (hlam : lam ^ 2 - ((ν : ℂ) - 2) * lam + 1 = 0) :
    ((coxeter A).map (↑) : Matrix _ _ ℂ) *ᵥ
        Sum.elim (fun i ↦ (lam + 1) * (u i : ℂ)) (fun j ↦ ((Aᵀ *ᵥ u) j : ℂ)) =
      lam • Sum.elim (fun i ↦ (lam + 1) * (u i : ℂ)) (fun j ↦ ((Aᵀ *ᵥ u) j : ℂ)) := by
  rw [coxeter_map, fromBlocks_mulVec]
  have hmap : ((A * Aᵀ).map (↑) : Matrix ι ι ℂ) = A.map (↑) * (A.map (↑))ᵀ := by
    ext i j; simp [Matrix.mul_apply]
  have hAA : ∀ i, ((A.map (↑) * (A.map (↑))ᵀ : Matrix ι ι ℂ) *ᵥ
      (fun i ↦ (u i : ℂ))) i = (ν : ℂ) * u i := by
    intro i
    rw [← hmap, mulVec_map_ofReal, hu]
    simp
  have hA : ∀ i, ((A.map (↑) : Matrix ι κ ℂ) *ᵥ
      (fun j ↦ ((Aᵀ *ᵥ u) j : ℂ))) i = (ν : ℂ) * u i := by
    intro i
    rw [mulVec_map_ofReal, mulVec_mulVec, hu]
    simp
  have hAt : ((A.map (↑) : Matrix ι κ ℂ)ᵀ *ᵥ (fun i ↦ (lam + 1) * (u i : ℂ))) =
      fun j ↦ (lam + 1) * ((Aᵀ *ᵥ u) j : ℂ) := by
    have : (fun i ↦ (lam + 1) * (u i : ℂ)) = (lam + 1) • (fun i ↦ (u i : ℂ)) := by
      funext i; simp
    rw [this, mulVec_smul, ← transpose_map, mulVec_map_ofReal]
    funext j; simp
  funext k
  cases k with
  | inl i =>
    have hx : (fun i ↦ (lam + 1) * (u i : ℂ)) = (lam + 1) • (fun i ↦ (u i : ℂ)) := by
      funext i; simp
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inl, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, sub_mulVec, one_mulVec, neg_mulVec, Pi.sub_apply, Pi.neg_apply]
    rw [hx, mulVec_smul, Pi.smul_apply, hAA, hA]
    simp only [smul_eq_mul]
    linear_combination -(u i : ℂ) * hlam
  | inr j =>
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inr, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, neg_mulVec, one_mulVec, Pi.neg_apply, hAt]
    ring

private lemma exists_eigen_norm_ge_one (hne : Nonempty (ι ⊕ κ)) :
    ∃ lam : ℂ, HasComplexEigenvalue (coxeter A) lam ∧ 1 ≤ ‖lam‖ := by
  by_cases hp : Nonempty ι
  · obtain ⟨i₀⟩ := hp
    set M := A * Aᵀ
    have hM := isHermitian_of_transpose_eq (AAt_transpose A)
    set u : ι → ℝ := ⇑(hM.eigenvectorBasis i₀)
    set ν := hM.eigenvalues i₀
    have hu : M *ᵥ u = ν • u := hM.mulVec_eigenvectorBasis i₀
    have hu0 : u ≠ 0 := by
      intro h0
      apply (hM.eigenvectorBasis).orthonormal.ne_zero i₀
      ext j
      simpa using congr_fun h0 j
    have hν0 : 0 ≤ ν := eigen_AAt_nonneg A hu0 hu
    by_cases hν4 : 4 < ν
    · obtain ⟨hgt, he⟩ := real_eigen_of_AAt_gt_four A hu0 hu hν4
      refine ⟨_, he, ?_⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      exact hgt.le
    · push Not at hν4
      by_cases hAu : Aᵀ *ᵥ u = 0
      · refine ⟨((-1 : ℝ) : ℂ), hasComplexEigenvalue_of_real (v := Sum.elim u 0) ?_ ?_, by simp⟩
        · intro h0; apply hu0; funext i; simpa using congr_fun h0 (Sum.inl i)
        · rw [coxeter_eq, fromBlocks_mulVec]
          funext k
          cases k with
          | inl i =>
            have : (A * Aᵀ) *ᵥ u = 0 := by rw [← mulVec_mulVec, hAu, mulVec_zero]
            simp [sub_mulVec, this]
          | inr j => simp [hAu]
      · set b : ℝ := ν - 2
        have hb : b ^ 2 ≤ 4 := by simp only [b]; nlinarith
        set lam : ℂ := ⟨b / 2, Real.sqrt (4 - b ^ 2) / 2⟩
        have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 4 - b ^ 2)
        have hlam : lam ^ 2 - ((ν : ℂ) - 2) * lam + 1 = 0 := by
          rw [show ((ν : ℂ) - 2) = (b : ℂ) by simp [b]]
          apply Complex.ext
          · simp only [lam, pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re,
              Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.zero_re]
            rw [show √(4 - b * b) / 2 * (√(4 - b * b) / 2) = √(4 - b ^ 2) ^ 2 / 4 by
              rw [show b * b = b ^ 2 by ring]; ring, hs]
            ring
          · simp [lam, pow_two, b]; ring
        refine ⟨lam, ⟨_, ?_, complex_eigen_of_AAt A u ν hu lam hlam⟩, ?_⟩
        · intro h0
          apply hAu
          funext j
          simpa using congr_fun h0 (Sum.inr j)
        · rw [norm_eq_one_of_quadratic lam b hb (by
            have : ((ν : ℂ) - 2) = (b : ℂ) := by simp [b]
            rw [← this]; exact hlam)]
  · have hq : Nonempty κ := by
      obtain ⟨k⟩ := hne
      cases k with
      | inl i => exact absurd ⟨i⟩ hp
      | inr j => exact ⟨j⟩
    obtain ⟨j₀⟩ := hq
    refine ⟨((-1 : ℝ) : ℂ),
      hasComplexEigenvalue_of_real (v := Sum.elim 0 (Pi.single j₀ 1)) ?_ ?_, by simp⟩
    · intro h0
      have := congr_fun h0 (Sum.inr j₀)
      simp at this
    · rw [coxeter_eq, fromBlocks_mulVec]
      funext k
      cases k with
      | inl i => exact absurd ⟨i⟩ hp
      | inr j =>
        have h0 : (Pi.single (Sum.inr j₀) (1 : ℝ) : ι ⊕ κ → ℝ) ∘ Sum.inl = 0 := by
          funext i; simp
        simp [h0, neg_mulVec, one_mulVec]

private lemma sum_mul_extend {α β : Type*} [Fintype α] [Fintype β] (f : α → β)
    (hf : Function.Injective f) (a' : α → ℝ) (h : β → ℝ) :
    ∑ r, h r * Function.extend f a' 0 r = ∑ r', h (f r') * a' r' := by
  classical
  have hsub : Finset.univ.map ⟨f, hf⟩ ⊆ Finset.univ := Finset.subset_univ _
  have hzero : ∀ r ∈ (Finset.univ : Finset β), r ∉ Finset.univ.map ⟨f, hf⟩ →
      h r * Function.extend f a' 0 r = 0 := by
    intro r _ hr
    have hnr : ¬ ∃ r', f r' = r := by simpa using hr
    simp [Function.extend_apply' _ _ _ hnr]
  rw [← Finset.sum_subset hsub hzero, Finset.sum_map]
  simp [hf.extend_apply]

/-- **Spectral interlacing for induced submatrices**: for injective `f : ι' → ι` and
`g : κ' → κ`, every complex eigenvalue `λ'` of `coxeter (A.submatrix f g)` is dominated in
modulus by a complex eigenvalue `λ` of `coxeter A`. -/
theorem exists_eigenvalue_norm_le_of_submatrix {ι' κ' : Type*} [Fintype ι'] [Fintype κ']
    [DecidableEq ι'] [DecidableEq κ'] (f : ι' → ι) (g : κ' → κ)
    (hf : Function.Injective f) (hg : Function.Injective g) (lam' : ℂ)
    (h' : HasComplexEigenvalue (coxeter (A.submatrix f g)) lam') :
    ∃ lam : ℂ, HasComplexEigenvalue (coxeter A) lam ∧ ‖lam'‖ ≤ ‖lam‖ := by
  set A' := A.submatrix f g
  have hne : Nonempty (ι ⊕ κ) := by
    obtain ⟨v, hv0, _⟩ := h'
    obtain ⟨k, _⟩ := Function.ne_iff.mp hv0
    cases k with
    | inl i => exact ⟨Sum.inl (f i)⟩
    | inr j => exact ⟨Sum.inr (g j)⟩
  by_cases hsmall : ‖lam'‖ ≤ 1
  · obtain ⟨lam, he, hn⟩ := exists_eigen_norm_ge_one A hne
    exact ⟨lam, he, hsmall.trans hn⟩
  push Not at hsmall
  have hl1 : lam' ≠ -1 := by intro h; rw [h] at hsmall; simp at hsmall
  obtain ⟨ν', hν'0, ⟨a', ha'0, ha'⟩, hq⟩ := eigenvalue_quadratic_of_ne_neg_one A' h' hl1
  have hν'4 : 4 < ν' := by
    by_contra hc
    push Not at hc
    have := norm_eq_one_of_quadratic lam' (ν' - 2) (by nlinarith) (by push_cast; exact hq)
    linarith
  set d := Real.sqrt ((ν' - 2) ^ 2 - 4)
  have hd2 : d ^ 2 = (ν' - 2) ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  set rp : ℝ := ((ν' - 2) + d) / 2
  set rm : ℝ := ((ν' - 2) - d) / 2
  have hfac : (lam' - rp) * (lam' - rm) = 0 := by
    have e1 : (rp : ℂ) + rm = ν' - 2 := by simp only [rp, rm]; push_cast; ring
    have e2 : (rp : ℂ) * rm = 1 := by
      have : rp * rm = 1 := by simp only [rp, rm]; nlinarith
      exact_mod_cast this
    linear_combination hq - lam' * e1 + e2
  have hrm_le : rm ≤ rp := by simp only [rm, rp]; linarith
  have hrm_pos : 0 < rm := by
    simp only [rm]
    have : d < ν' - 2 := by
      rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ ν' - 2)]
      exact Real.sqrt_lt_sqrt (by nlinarith) (by linarith)
    linarith
  have hnorm' : ‖lam'‖ ≤ rp := by
    rcases mul_eq_zero.mp hfac with h | h
    · rw [sub_eq_zero.mp h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    · rw [sub_eq_zero.mp h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrm_pos]
      exact hrm_le
  set a : ι → ℝ := Function.extend f a' 0
  have ha0 : a ≠ 0 := by
    intro h0
    apply ha'0
    funext i
    have := congr_fun h0 (f i)
    simpa [a, hf.extend_apply] using this
  have hAa : ∀ c', (Aᵀ *ᵥ a) (g c') = (A'ᵀ *ᵥ a') c' := by
    intro c'
    simp only [mulVec, dotProduct, transpose_apply, A', submatrix_apply]
    exact sum_mul_extend f hf a' (fun r ↦ A r (g c'))
  have haa : a ⬝ᵥ a = a' ⬝ᵥ a' := by
    simp only [dotProduct]
    have := sum_mul_extend f hf a' a
    simp only [a, hf.extend_apply] at this ⊢
    exact this
  have hle : (A'ᵀ *ᵥ a') ⬝ᵥ (A'ᵀ *ᵥ a') ≤ (Aᵀ *ᵥ a) ⬝ᵥ (Aᵀ *ᵥ a) := by
    simp only [dotProduct]
    rw [show (∑ c', (A'ᵀ *ᵥ a') c' * (A'ᵀ *ᵥ a') c') =
        ∑ c ∈ Finset.univ.map ⟨g, hg⟩, (Aᵀ *ᵥ a) c * (Aᵀ *ᵥ a) c by
      rw [Finset.sum_map]; simp [hAa]]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun c _ _ ↦ mul_self_nonneg _)
  have hray : ν' * (a ⬝ᵥ a) ≤ a ⬝ᵥ ((A * Aᵀ) *ᵥ a) := by
    rw [dot_AAt, haa]
    have := dot_AAt A' a'
    rw [ha', dotProduct_smul, smul_eq_mul] at this
    linarith
  set N : Matrix ι ι ℝ := ν' • 1 - A * Aᵀ
  have hNt : Nᵀ = N := by simp [N, transpose_sub]
  have hN := isHermitian_of_transpose_eq hNt
  have hnot : ¬ N.PosDef := by
    intro hpd
    have := (posDef_iff_dotProduct_mulVec.mp hpd).2 ha0
    simp only [star_trivial, N, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul] at this
    linarith
  obtain ⟨θ, hθ, u, hu0, hu⟩ := exists_eigen_nonpos_of_not_posDef N hN hnot
  have huν : (A * Aᵀ) *ᵥ u = (ν' - θ) • u := by
    have : (A * Aᵀ) *ᵥ u = ν' • u - N *ᵥ u := by
      simp [N, sub_mulVec, smul_mulVec]
    rw [this, hu, ← sub_smul]
  obtain ⟨_, he⟩ := real_eigen_of_AAt_gt_four A hu0 huν (by linarith)
  refine ⟨_, he, ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hnorm'.trans (le_trans (rplus_mono (by linarith) (by linarith : ν' ≤ ν' - θ))
    (le_abs_self _))

/-- **Strict spectral interlacing**: if `form A` is not positive semidefinite while the induced
submatrix form `form (A.submatrix f g)` is positive semidefinite, then every eigenvalue of
`coxeter (A.submatrix f g)` has modulus strictly smaller than some eigenvalue of `coxeter A`. -/
theorem exists_eigenvalue_norm_lt_of_submatrix {ι' κ' : Type*} [Fintype ι'] [Fintype κ']
    [DecidableEq ι'] [DecidableEq κ'] (f : ι' → ι) (g : κ' → κ)
    (hA : ¬ (form A).PosSemidef) (hA' : (form (A.submatrix f g)).PosSemidef)
    (lam' : ℂ) (h' : HasComplexEigenvalue (coxeter (A.submatrix f g)) lam') :
    ∃ lam : ℂ, HasComplexEigenvalue (coxeter A) lam ∧ ‖lam'‖ < ‖lam‖ := by
  have h1 := norm_eq_one_of_posSemidef _ hA' lam' h'
  obtain ⟨lam, hl, he⟩ := real_eigen_gt_one_of_not_posSemidef A hA
  refine ⟨lam, he, ?_⟩
  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  exact hl

end Bipartite

end Matrix.BipartiteCoxeter
