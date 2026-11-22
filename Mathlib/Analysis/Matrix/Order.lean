/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar, De Song
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The partial order on matrices

This file constructs the partial order and star ordered instances on matrices on `𝕜`.
This allows us to use more general results from C⋆-algebras, like `CFC.sqrt`.

## Main results

* `Matrix.instPartialOrder`: the partial order on matrices given by `x ≤ y := (y - x).PosSemidef`.
* `Matrix.toMatrixInnerProductSpace`: the inner product on matrices induced by a
  positive semi-definite matrix `M`: `⟪x, y⟫ = (y * M * xᴴ).trace`.
* `Matrix.PosDef.det_re_mono`: **Minkowski's determinant inequality**: the determinant is
  monotone with respect to this order on positive definite matrices.
* `Matrix.PosDef.det_re_le_det_re_mul_det_re_fromBlocks`: **Fischer's inequality**.
* `Matrix.PosDef.det_re_le_prod_diag_re`: **Hadamard's determinant inequality**.

## Implementation notes

Note that the partial order instance is scoped to `MatrixOrder`.
Please `open scoped MatrixOrder` to use this.
-/

@[expose] public section

variable {𝕜 m n : Type*} [RCLike 𝕜]

open scoped ComplexOrder
open Matrix

namespace Matrix

section PartialOrder

/-- The preorder on matrices given by `A ≤ B := (B - A).PosSemidef`. -/
abbrev instPreOrder : Preorder (Matrix n n 𝕜) where
  le A B := (B - A).PosSemidef
  le_refl A := sub_self A ▸ PosSemidef.zero
  le_trans A B C h₁ h₂ := sub_add_sub_cancel C B A ▸ h₂.add h₁

scoped[MatrixOrder] attribute [instance] Matrix.instPreOrder

open MatrixOrder

lemma le_iff {A B : Matrix n n 𝕜} : A ≤ B ↔ (B - A).PosSemidef := Iff.rfl

lemma nonneg_iff_posSemidef {A : Matrix n n 𝕜} : 0 ≤ A ↔ A.PosSemidef := by rw [le_iff, sub_zero]

protected alias ⟨LE.le.posSemidef, PosSemidef.nonneg⟩ := nonneg_iff_posSemidef

attribute [aesop safe forward (rule_sets := [CStarAlgebra])] PosSemidef.nonneg

private lemma le_antisymm_aux {A : Matrix n n 𝕜} (h₁ : A.PosSemidef) (h₂ : (-A).PosSemidef) :
    A = 0 := by
  classical
  ext i j
  have hdiag i : A i i = 0 :=
    le_antisymm (by simpa using h₂.diag_nonneg) (by simpa using h₁.diag_nonneg)
  have h1 := h₁.2 (.single i 1 + .single j (A j i))
  have h2 := h₂.2 (.single i 1 + .single j (A j i))
  simp [Finsupp.sum_add_index, mul_add, add_mul,
      -neg_add_rev, hdiag, ← h₁.1.apply j i, -RCLike.star_def] at *
  simpa using le_antisymm h2 h1

/-- The partial order on matrices given by `A ≤ B := (B - A).PosSemidef`. -/
abbrev instPartialOrder : PartialOrder (Matrix n n 𝕜) where
  le_antisymm A B h₁ h₂ := by
    simpa [sub_eq_zero, eq_comm] using le_antisymm_aux h₁
     (by simpa only [← neg_sub B, le_iff] using h₂)

scoped[MatrixOrder] attribute [instance] Matrix.instPartialOrder

lemma instIsOrderedAddMonoid : IsOrderedAddMonoid (Matrix n n 𝕜) where
  add_le_add_left _ _ _ _ := by rwa [le_iff, add_sub_add_right_eq_sub]

scoped[MatrixOrder] attribute [instance] Matrix.instIsOrderedAddMonoid

@[deprecated isClosed_setOfPred_posSemidef +typeChanged (since := "2026-10-28")]
lemma posSemidef_is_closed : IsClosed {A : Matrix n n 𝕜 | A.PosSemidef} :=
  isClosed_setOfPred_posSemidef

lemma instOrderClosedTopology : OrderClosedTopology (Matrix n n 𝕜) where
  isClosed_le' := isClosed_le_of_isClosed_nonneg <| by
    simpa [nonneg_iff_posSemidef] using isClosed_setOfPred_posSemidef

scoped[MatrixOrder] attribute [instance] Matrix.instOrderClosedTopology

variable [Fintype n]

lemma instNonnegSpectrumClass : NonnegSpectrumClass ℝ (Matrix n n 𝕜) where
  quasispectrum_nonneg_of_nonneg A hA := by
    classical
    simp only [quasispectrum_eq_spectrum_union_zero ℝ A, Set.union_singleton, Set.mem_insert_iff,
      forall_eq_or_imp, le_refl, true_and]
    intro x hx
    obtain ⟨i, rfl⟩ := Set.ext_iff.mp
      hA.posSemidef.1.spectrum_real_eq_range_eigenvalues x |>.mp hx
    exact hA.posSemidef.eigenvalues_nonneg _

scoped[MatrixOrder] attribute [instance] instNonnegSpectrumClass

lemma instStarOrderedRing : StarOrderedRing (Matrix n n 𝕜) :=
  .of_nonneg_iff' add_le_add_right fun A ↦
    ⟨fun hA ↦ by
      classical
      obtain ⟨X, hX, -, rfl⟩ :=
        sub_zero A ▸ CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hA.isHermitian
          (QuasispectrumRestricts.nnreal_of_nonneg hA.nonneg)
      exact ⟨X, hX.star_eq.symm ▸ rfl⟩,
    fun ⟨A, hA⟩ => hA ▸ (posSemidef_conjTranspose_mul_self A).nonneg⟩

scoped[MatrixOrder] attribute [instance] instStarOrderedRing

end PartialOrder

open scoped MatrixOrder

namespace PosSemidef
variable [Fintype n]

section sqrtDeprecated

variable [DecidableEq n] {A : Matrix n n 𝕜} (hA : PosSemidef A)

include hA

lemma inv_sqrt : (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹ := by
  rw [eq_comm, CFC.sqrt_eq_iff _ _ hA.inv.nonneg (CFC.sqrt_nonneg A).posSemidef.inv.nonneg, ← sq,
    inv_pow', CFC.sq_sqrt A]

end sqrtDeprecated

theorem det_sqrt [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    (CFC.sqrt A).det = RCLike.sqrt A.det := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ A, hA.1.cfc_eq, RCLike.sqrt_of_nonneg hA.det_nonneg]
  simp only [IsHermitian.cfc, Real.coe_sqrt, Real.coe_toNNReal', det_map, det_diagonal,
    Function.comp_apply, hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod,
    RCLike.ofReal_re, Real.sqrt_prod _ fun _ _ ↦ hA.eigenvalues_nonneg _]
  grind

end PosSemidef

section
variable [Fintype n]

theorem IsHermitian.det_abs [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    det (CFC.abs A) = ‖det A‖ := by
  rw [CFC.abs_eq_cfc_norm A, hA.cfc_eq]
  simp [IsHermitian.cfc, -Unitary.conjStarAlgAut_apply, hA.det_eq_prod_eigenvalues]

theorem posSemidef_iff_isHermitian_and_spectrum_nonneg [DecidableEq n] {A : Matrix n n 𝕜} :
    A.PosSemidef ↔ A.IsHermitian ∧ spectrum 𝕜 A ⊆ {a : 𝕜 | 0 ≤ a} := by
  refine ⟨fun h => ⟨h.isHermitian, fun a => ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · simp only [h.isHermitian.spectrum_eq_image_range, Set.mem_image, Set.mem_range,
      exists_exists_eq_and, Set.mem_ofPred_eq, forall_exists_index]
    rintro i rfl
    exact mod_cast h.eigenvalues_nonneg _
  · rw [h1.posSemidef_iff_eigenvalues_nonneg]
    intro i
    simpa [h1.spectrum_eq_image_range] using @h2 (h1.eigenvalues i)

theorem isStrictlyPositive_iff_posDef [DecidableEq n] {x : Matrix n n 𝕜} :
    IsStrictlyPositive x ↔ x.PosDef :=
  ⟨fun h => h.nonneg.posSemidef.posDef_iff_isUnit.mpr h.isUnit,
  fun h => h.isUnit.isStrictlyPositive h.posSemidef.nonneg⟩

alias ⟨IsStrictlyPositive.posDef, PosDef.isStrictlyPositive⟩ := isStrictlyPositive_iff_posDef

attribute [aesop safe forward (rule_sets := [CStarAlgebra])] PosDef.isStrictlyPositive

end

section kronecker
open scoped Kronecker

/-- The kronecker product of two positive semi-definite matrices is positive semi-definite. -/
theorem PosSemidef.kronecker {x : Matrix n n 𝕜} {y : Matrix m m 𝕜}
    (hx : x.PosSemidef) (hy : y.PosSemidef) : (x ⊗ₖ y).PosSemidef := by
  classical
  rw [posSemidef_iff_submatrix_of_forall_finset
    (fun p : Finset n × Finset m ↦ Prod.map ((↑) : p.1 → n) ((↑) : p.2 → m))]
  · rintro ⟨s, t⟩
    obtain ⟨a, ha⟩ :=
      CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hx.submatrix ((↑) : s → n)).nonneg
    obtain ⟨b, hb⟩ :=
      CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hy.submatrix ((↑) : t → m)).nonneg
    simpa [← kroneckerMap_submatrix_submatrix, ha, hb, mul_kronecker_mul, ← conjTranspose_kronecker,
      star_eq_conjTranspose] using posSemidef_conjTranspose_mul_self _
  · intro s
    exact ⟨(s.image Prod.fst, s.image Prod.snd), fun _ ↦ by simp [Set.range_prodMap]; grind⟩

open Matrix in
/-- The kronecker of two positive definite matrices is positive definite. -/
theorem PosDef.kronecker {x : Matrix n n 𝕜} {y : Matrix m m 𝕜}
    (hx : x.PosDef) (hy : y.PosDef) : (x ⊗ₖ y).PosDef := by
  classical
  rw [posDef_iff_submatrix_of_forall_finset
    (fun p : Finset n × Finset m ↦ Prod.map ((↑) : p.1 → n) ((↑) : p.2 → m))
    (fun _ ↦ Subtype.coe_injective.prodMap Subtype.coe_injective)]
  · rintro ⟨s, t⟩
    have hx' := hx.submatrix (Subtype.coe_injective (p := (· ∈ s)))
    have hy' := hy.submatrix (Subtype.coe_injective (p := (· ∈ t)))
    exact (hx'.posSemidef.kronecker hy'.posSemidef).posDef_iff_isUnit.mpr
      (hx'.isUnit.kronecker hy'.isUnit)
  · intro s
    exact ⟨(s.image Prod.fst, s.image Prod.snd), fun _ ↦ by simp [Set.range_prodMap]; grind⟩

end kronecker

section hadamard

variable {ι : Type*}

/-- [**Schur product theorem**][schur1911] (positive semidefinite version): the Hadamard (entrywise)
product of positive semidefinite matrices is positive semidefinite. -/
theorem PosSemidef.hadamard {A B : Matrix ι ι 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A ⊙ B).PosSemidef :=
  (hA.kronecker hB).submatrix fun i ↦ (i, i)

/-- **Schur product theorem**: the Hadamard (entrywise) product of positive definite
matrices is positive definite. -/
theorem PosDef.hadamard {A B : Matrix ι ι 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) : (A ⊙ B).PosDef :=
  (hA.kronecker hB).submatrix (e := fun i ↦ (i, i)) fun _ _ h ↦ congrArg Prod.fst h

end hadamard

/-! ### Determinant inequalities -/

section Determinant

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant of `1 + Q` for a positive semidefinite matrix `Q` is the product of
`1 + λ` over the eigenvalues `λ` of `Q`. -/
theorem PosSemidef.det_one_add_eq_prod {Q : Matrix ι ι 𝕜} (hQ : Q.PosSemidef) :
    (1 + Q).det = ((∏ i, (1 + hQ.isHermitian.eigenvalues i) : ℝ) : 𝕜) := by
  have h1 : (1 + Q) = Unitary.conjStarAlgAut 𝕜 _ hQ.isHermitian.eigenvectorUnitary
      (1 + diagonal (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues)) := by
    rw [map_add, map_one, ← hQ.isHermitian.spectral_theorem]
  have hd : (1 + diagonal (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues) : Matrix ι ι 𝕜) =
      diagonal fun i => ((1 + hQ.isHermitian.eigenvalues i : ℝ) : 𝕜) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [h1, Unitary.conjStarAlgAut_apply, hd, det_mul, det_mul, det_diagonal, RCLike.ofReal_prod,
    mul_comm (det _) (∏ _, _), mul_assoc, ← det_mul,
    Unitary.mul_star_self_of_mem hQ.isHermitian.eigenvectorUnitary.property, det_one, mul_one]

/-- **Minkowski's determinant inequality**: the determinant is monotone with respect to the
Loewner order on positive definite matrices: if `G` is positive definite and `H - G` is
positive semidefinite, then `(G.det).re ≤ (H.det).re`. -/
theorem PosDef.det_re_mono {G H : Matrix ι ι 𝕜} (hG : G.PosDef) (hGH : (H - G).PosSemidef) :
    RCLike.re G.det ≤ RCLike.re H.det := by
  set S := CFC.sqrt G
  have hS0 : S.PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hSh : Sᴴ = S := hS0.1
  have hdetG : G.det = S.det * S.det := by rw [← hSS, det_mul]
  have hGpos := hG.det_pos
  have hSdet : S.det ≠ 0 := fun h => by rw [hdetG, h, zero_mul] at hGpos; exact lt_irrefl _ hGpos
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet
  have hQ : (S⁻¹ * (H - G) * (S⁻¹)ᴴ).PosSemidef := hGH.mul_mul_conjTranspose_same _
  have hinvh : (S⁻¹)ᴴ = S⁻¹ := by rw [conjTranspose_nonsing_inv, hSh]
  have h2 : S * (S⁻¹ * (H - G) * (S⁻¹)ᴴ) * S = H - G := by
    rw [hinvh, show S * (S⁻¹ * (H - G) * S⁻¹) * S = (S * S⁻¹) * (H - G) * (S⁻¹ * S) by
      simp only [Matrix.mul_assoc]]
    rw [mul_nonsing_inv S hSu, nonsing_inv_mul S hSu, Matrix.one_mul, Matrix.mul_one]
  have hH : H = S * (1 + S⁻¹ * (H - G) * (S⁻¹)ᴴ) * S := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSS, h2]; abel
  have hdetH : H.det = G.det * (1 + S⁻¹ * (H - G) * (S⁻¹)ᴴ).det := by
    conv_lhs => rw [hH]
    rw [det_mul, det_mul, hdetG]; ring
  rw [hdetH, hQ.det_one_add_eq_prod]
  obtain ⟨hre, -⟩ := RCLike.pos_iff.mp hGpos
  rw [RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im, mul_zero, sub_zero]
  have h1 : (1 : ℝ) ≤ ∏ i, (1 + hQ.isHermitian.eigenvalues i) :=
    calc
      (1 : ℝ) = ∏ _i : ι, (1 : ℝ) := by simp
      _ ≤ ∏ i, (1 + hQ.isHermitian.eigenvalues i) :=
        Finset.prod_le_prod₀ (f := fun _ : ι => (1 : ℝ))
          (g := fun i => 1 + hQ.isHermitian.eigenvalues i)
          (fun i _ => zero_le_one) (fun i _ => by linarith [hQ.eigenvalues_nonneg i])
  nlinarith

/-- **Fischer's inequality**: for a positive definite block matrix `[[A, B], [C, D]]`
(necessarily `C = Bᴴ`), the determinant is at most the product of the determinants of the
diagonal blocks: `((fromBlocks A B C D).det).re ≤ (A.det).re * (D.det).re`. -/
theorem PosDef.det_re_le_det_re_mul_det_re_fromBlocks
    {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    {A : Matrix m m 𝕜} {B : Matrix m k 𝕜} {C : Matrix k m 𝕜} {D : Matrix k k 𝕜}
    (h : (fromBlocks A B C D).PosDef) :
    RCLike.re (fromBlocks A B C D).det ≤ RCLike.re A.det * RCLike.re D.det := by
  have hA : A.PosDef := by
    have := h.submatrix (e := (Sum.inl : m → m ⊕ k)) Sum.inl_injective
    have e : (fromBlocks A B C D).submatrix Sum.inl Sum.inl = A := by ext; simp
    rwa [e] at this
  have hD : D.PosDef := by
    have := h.submatrix (e := (Sum.inr : k → m ⊕ k)) Sum.inr_injective
    have e : (fromBlocks A B C D).submatrix Sum.inr Sum.inr = D := by ext; simp
    rwa [e] at this
  have hC : C = Bᴴ := ((isHermitian_fromBlocks_iff.mp h.isHermitian).2.1).symm
  subst hC
  have : Invertible A := hA.isUnit.invertible
  have hS : (D - Bᴴ * A⁻¹ * B).PosSemidef := (PosDef.fromBlocks₁₁ B D hA).mp h.posSemidef
  have hdet : (fromBlocks A B Bᴴ D).det = A.det * (D - Bᴴ * A⁻¹ * B).det := by
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hSne : (D - Bᴴ * A⁻¹ * B).det ≠ 0 := by
    intro h0
    have := h.det_pos
    rw [hdet, h0, mul_zero] at this
    exact lt_irrefl _ this
  have hSd : (D - Bᴴ * A⁻¹ * B).PosDef := hS.posDef_iff_det_ne_zero.mpr hSne
  have hdiff : (D - (D - Bᴴ * A⁻¹ * B)).PosSemidef := by
    rw [sub_sub_cancel]
    exact hA.inv.posSemidef.conjTranspose_mul_mul_same B
  have hmono := hSd.det_re_mono hdiff
  have hAre : 0 ≤ RCLike.re A.det := (RCLike.pos_iff.mp hA.det_pos).1.le
  have hAim : RCLike.im A.det = 0 := (RCLike.pos_iff.mp hA.det_pos).2
  rw [hdet, RCLike.mul_re, hAim, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left hmono hAre

/-- Block version of Fischer's inequality for a matrix indexed by `Fin (a + b)`. -/
theorem PosDef.det_re_le_submatrix_det_re_mul_submatrix_det_re {a b : ℕ}
    {M : Matrix (Fin (a + b)) (Fin (a + b)) 𝕜} (hM : M.PosDef) :
    RCLike.re M.det ≤ RCLike.re (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det *
      RCLike.re (M.submatrix (Fin.natAdd a) (Fin.natAdd a)).det := by
  have hE : M.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (M.submatrix (Fin.castAdd b) (Fin.castAdd b))
        (M.submatrix (Fin.castAdd b) (Fin.natAdd a))
        (M.submatrix (Fin.natAdd a) (Fin.castAdd b))
        (M.submatrix (Fin.natAdd a) (Fin.natAdd a)) := by
    ext (i | i) (j | j) <;> simp
  have hP : (M.submatrix finSumFinEquiv finSumFinEquiv).PosDef :=
    hM.submatrix finSumFinEquiv.injective
  rw [hE] at hP
  have := hP.det_re_le_det_re_mul_det_re_fromBlocks
  rwa [← hE, det_submatrix_equiv_self] at this

/-- **Hadamard's determinant inequality** for positive definite matrices:
the determinant is at most the product of the diagonal entries. -/
theorem PosDef.det_re_le_prod_diag_re {k : ℕ} {D : Matrix (Fin k) (Fin k) 𝕜}
    (hD : D.PosDef) :
    RCLike.re D.det ≤ ∏ j : Fin k, RCLike.re (D j j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := hD.det_re_le_submatrix_det_re_mul_submatrix_det_re (a := k) (b := 1)
    have h2 := ih (hD.submatrix (Fin.castAdd_injective k 1))
    have h3 : (D.submatrix (Fin.natAdd k) (Fin.natAdd k : Fin 1 → Fin (k + 1))).det =
        D (Fin.last k) (Fin.last k) := by
      rw [det_unique]; rfl
    have h4 : 0 ≤ RCLike.re (D (Fin.last k) (Fin.last k)) :=
      (RCLike.pos_iff.mp hD.diag_pos).1.le
    rw [h3] at h1
    rw [Fin.prod_univ_castSucc]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 h4)

/-- Hadamard's inequality for an arbitrary split of the index set: the determinant is at most
the determinant of the leading block times the product of the remaining diagonal entries. -/
theorem PosDef.det_re_le_submatrix_det_re_mul_prod_diag_re {a b : ℕ}
    {M : Matrix (Fin (a + b)) (Fin (a + b)) 𝕜} (hM : M.PosDef) :
    RCLike.re M.det ≤ RCLike.re (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det *
      ∏ j : Fin b, RCLike.re (M (Fin.natAdd a j) (Fin.natAdd a j)) := by
  have h1 := hM.det_re_le_submatrix_det_re_mul_submatrix_det_re
  have h2 := (hM.submatrix (e := Fin.natAdd a) (Fin.natAdd_injective b a)).det_re_le_prod_diag_re
  have h0 : 0 ≤ RCLike.re (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det :=
    (RCLike.pos_iff.mp (hM.submatrix (Fin.castAdd_injective a b)).det_pos).1.le
  exact h1.trans (mul_le_mul_of_nonneg_left h2 h0)

end Determinant

section tracePositiveLinearMap
variable (n α 𝕜 : Type*) [Fintype n] [Semiring α] [RCLike 𝕜] [Module α 𝕜]

/-- `Matrix.trace` as a positive linear map. -/
def tracePositiveLinearMap : Matrix n n 𝕜 →ₚ[α] 𝕜 :=
  .mk₀ (traceLinearMap n α 𝕜) fun _ h ↦ h.posSemidef.trace_nonneg

@[simp] lemma toLinearMap_tracePositiveLinearMap :
    (tracePositiveLinearMap n α 𝕜).toLinearMap = traceLinearMap n α 𝕜 := rfl

@[simp] lemma tracePositiveLinearMap_apply (x) : tracePositiveLinearMap n α 𝕜 x = trace x := rfl

end tracePositiveLinearMap

section
variable [Fintype m] [Fintype n]
variable (m)

set_option backward.privateInPublic true in
/-- The pre-inner product space structure implementation. Only an auxiliary for
`Matrix.toMatrixSeminormedAddCommGroup`, `Matrix.toMatrixNormedAddCommGroup`,
and `Matrix.toMatrixInnerProductSpace`. -/
private abbrev PosSemidef.matrixPreInnerProductSpace {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    PreInnerProductSpace.Core 𝕜 (Matrix m n 𝕜) where
  inner x y := (y * M * xᴴ).trace
  conj_inner_symm _ _ := by
    simp only [Matrix.mul_assoc, starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul,
      conjTranspose_conjTranspose, hM.isHermitian.eq]
  re_inner_nonneg x := RCLike.nonneg_iff.mp (hM.mul_mul_conjTranspose_same x).trace_nonneg |>.1
  add_left := by simp [Matrix.mul_add]
  smul_left := by simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A positive definite matrix `M` induces a norm on `Matrix m n 𝕜`
`‖x‖ = sqrt (x * M * xᴴ).trace`. -/
@[instance_reducible]
noncomputable def toMatrixSeminormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    SeminormedAddCommGroup (Matrix m n 𝕜) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup _ _ _ _ _ (hM.matrixPreInnerProductSpace m)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A positive definite matrix `M` induces a norm on `Matrix m n 𝕜`:
`‖x‖ = sqrt (x * M * xᴴ).trace`. -/
@[instance_reducible]
noncomputable def toMatrixNormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosDef) :
    NormedAddCommGroup (Matrix m n 𝕜) :=
  letI : InnerProductSpace.Core 𝕜 (Matrix m n 𝕜) :=
  { __ := hM.posSemidef.matrixPreInnerProductSpace m
    definite x hx := by
      classical
      obtain ⟨y, hy, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
        hM.isStrictlyPositive
      simp +instances only at hx
      rw [← Matrix.mul_assoc, ← conjTranspose_conjTranspose x, star_eq_conjTranspose,
        ← conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
        trace_conjTranspose_mul_self_eq_zero_iff] at hx
      lift y to (Matrix n n 𝕜)ˣ using hy
      simpa [← mul_assoc] using congr(y⁻¹.val * $hx) }
  this.toNormedAddCommGroup

/-- A positive semi-definite matrix `M` induces an inner product on `Matrix m n 𝕜`:
`⟪x, y⟫ = (y * M * xᴴ).trace`. -/
@[instance_reducible]
def toMatrixInnerProductSpace (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    letI : SeminormedAddCommGroup (Matrix m n 𝕜) := M.toMatrixSeminormedAddCommGroup m hM
    InnerProductSpace 𝕜 (Matrix m n 𝕜) :=
  InnerProductSpace.ofCore _

open scoped Norms.L2Operator in
/-- The isometric continuous functional calculus on `Matrix n n 𝕜` arising from the operator norm
given by the identification with (continuous) linear endomorphisms of `EuclideanSpace 𝕜 n`. -/
instance instIsometricContinuousFunctionalCalculus [DecidableEq n] :
    IsometricContinuousFunctionalCalculus ℝ (Matrix n n 𝕜) IsSelfAdjoint where
  isometric A hA := by
    rw [← isHermitian_iff_isSelfAdjoint] at hA
    rw [IsHermitian.cfcHom_eq_cfcAux hA, AddMonoidHomClass.isometry_iff_norm]
    intro f
    simp only [IsHermitian.cfcAux_apply, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]
    rw [((algebraMap_isometry ℝ 𝕜).postcomp_pi).norm_map_of_map_zero (by ext; simp)]
    let : Fintype (spectrum ℝ A) := .ofFinite _
    rw [ContinuousMap.norm_eq_norm_coeFn]
    refine Function.Surjective.pi_norm_comp ?_ _
    rw [← Function.Surjective.of_comp_iff'
      (Set.equivOfEq hA.spectrum_real_eq_range_eigenvalues).bijective]
    exact Set.codRestrict_range_surjective hA.eigenvalues

scoped[Matrix.Norms.L2Operator] attribute [instance]
  Matrix.instIsometricContinuousFunctionalCalculus

end

end Matrix
