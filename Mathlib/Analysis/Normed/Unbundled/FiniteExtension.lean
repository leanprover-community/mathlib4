/-
Copyright (c) 2025 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
import Mathlib.Analysis.Normed.Unbundled.SeminormFromBounded
import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Finsupp.VectorSpace


/-!
# Basis.norm

In this file, we prove [BGR, Lemma 3.2.1./3][bosch-guntzer-remmert] : if `K` is a normed field
with a nonarchimedean power-multiplicative norm and `L/K` is a finite extension, then there exists
at least one power-multiplicative `K`-algebra norm on `L` extending the norm on `K`.

## Main Definitions
* `Basis.norm` : the function sending an element `x : L` to the maximum of the norms of its
  coefficients with respect to the `K`-basis `B` of `L`.

## Main Results
* `norm_mul_le_const_mul_norm` : For any `K`-basis of `L`, `B.norm` is bounded with respect to
  multiplication. That is, `∃ (c : ℝ), c > 0` such that
  ` ∀ (x y : L), B.norm (x * y) ≤ c * B.norm x * B.norm y`.
* `exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional` : if `K` is a normed field with a
  nonarchimedean power-multiplicative norm and `L/K` is a finite extension, then there exists at
  least one power-multiplicative `K`-algebra norm on `L` extending the norm on `K`. This is
  [BGR, Lemma 3.2.1./3].

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

Basis.norm, nonarchimedean
-/

noncomputable section

open Finset Module

section Ring

variable {K L : Type*} [NormedField K] [Ring L] [Algebra K L]

namespace Module.Basis

variable {ι : Type*} [Fintype ι] [Nonempty ι] (B : Basis ι K L)

/-- The function sending an element `x : L` to the maximum of the norms of its coefficients
with respect to the `K`-basis `B` of `L`. -/
def norm (x : L) : ℝ :=
  Finset.sup' univ univ_nonempty (fun i : ι ↦ ‖B.repr x i‖)

/-- The norm of a coefficient `x_i` is less than or equal to the norm of `x`. -/
theorem norm_repr_le_norm {x : L} (i : ι) : ‖B.repr x i‖ ≤ B.norm x :=
  Finset.le_sup' (fun i : ι ↦ ‖B.repr x i‖) (mem_univ i)

/-- For any `K`-basis of `L`, we have `B.norm 0 = 0`. -/
protected theorem norm_zero : B.norm 0 = 0 := by
  simp [norm, map_zero, norm_zero]

/-- For any `K`-basis of `L`, and any `x : L`, we have `B.norm (-x) = B.norm x`. -/
protected theorem norm_neg (x : L) : B.norm (-x) = B.norm x := by
  simp [norm, map_neg, Pi.neg_apply, _root_.norm_neg]

/-- For any `K`-basis of `L`, and any `x : L`, we have `0 ≤ B.norm x`. -/
protected theorem norm_nonneg (x : L) : 0 ≤ B.norm x := by
  simp only [norm, le_sup'_iff, mem_univ, norm_nonneg, and_self, exists_const]

variable {B}

/-- For any `K`-basis `B` of `L` containing `1`, `B.norm` extends the norm on `K`. -/
theorem norm_extends {i : ι} (hBi : B i = (1 : L)) (x : K) :
    B.norm ((algebraMap K L) x) = ‖x‖ := by
  classical
  simp only [norm, repr_algebraMap _ hBi]
  apply le_antisymm
  · aesop
  · exact le_sup'_of_le _ (mem_univ i) (by simp)

/-- For any `K`-basis of `L`, if the norm on `K` is nonarchimedean, then so is `B.norm`. -/
theorem norm_isNonarchimedean (hna : IsNonarchimedean (Norm.norm : K → ℝ)) :
    IsNonarchimedean B.norm := fun x y ↦ by
  obtain ⟨ixy, _, hixy⟩ := exists_mem_eq_sup' univ_nonempty (fun i ↦ ‖(B.repr (x + y)) i‖)
  have hxy : ‖B.repr (x + y) ixy‖ ≤ max ‖B.repr x ixy‖ ‖B.repr y ixy‖ := by
    rw [LinearEquiv.map_add, Finsupp.coe_add, Pi.add_apply]; exact hna _ _
  rw [Basis.norm, hixy]
  rcases le_max_iff.mp hxy with (hx | hy)
  · exact le_max_of_le_left (le_trans hx (norm_repr_le_norm B ixy))
  · exact le_max_of_le_right (le_trans hy (norm_repr_le_norm B ixy))

/-- For any `K`-basis of `L`, `B.norm` is bounded with respect to multiplication. That is,
  `∃ (c : ℝ), c > 0` such that ` ∀ (x y : L), B.norm (x * y) ≤ c * B.norm x * B.norm y`. -/
theorem norm_mul_le_const_mul_norm {i : ι} (hBi : B i = (1 : L))
    (hna : IsNonarchimedean (Norm.norm : K → ℝ)) :
    ∃ (c : ℝ) (_ : 0 < c), ∀ x y : L, B.norm (x * y) ≤ c * B.norm x * B.norm y := by
  -- The bounding constant `c` will be the maximum of the products `B.norm (B i * B j)`.
  obtain ⟨c, _, hc⟩ := exists_mem_eq_sup' univ_nonempty (fun i : ι × ι ↦ B.norm (B i.1 * B i.2))
  use B.norm (B c.1 * B c.2)
  constructor
  -- ∀ (x y : L), B.norm (x * y) ≤ B.norm (⇑B c.fst * ⇑B c.snd) * B.norm x * B.norm y
  · intro x y
    -- `ixy` is an index for which `‖B.repr (x*y) i‖` is maximum.
    obtain ⟨ixy, _, hixy_def⟩ := exists_mem_eq_sup' univ_nonempty (fun i ↦ ‖(B.repr (x * y)) i‖)
    -- We rewrite the LHS using `ixy`.
    conv_lhs => simp only [Basis.norm]; rw [hixy_def, ← Basis.sum_repr B x, ← Basis.sum_repr B y]
    rw [sum_mul, map_finset_sum]
    simp_rw [smul_mul_assoc, LinearEquiv.map_smul, mul_sum, map_finset_sum,
      mul_smul_comm, LinearEquiv.map_smul]
    have hna' : IsNonarchimedean (NormedField.toMulRingNorm K) := hna
    /- Since the norm is nonarchimidean, the norm of a finite sum is bounded by the maximum of the
          norms of the summands. -/
    obtain ⟨k, -, (hk : ‖∑ i : ι, (B.repr x i • ∑ i_1 : ι,
      B.repr y i_1 • B.repr (B i * B i_1)) ixy‖ ≤
      ‖(B.repr x k • ∑ j : ι, B.repr y j • B.repr (B k * B j)) ixy‖)⟩ :=
      IsNonarchimedean.finset_image_add hna'
        (fun i ↦ (B.repr x i • ∑ i_1 : ι, B.repr y i_1 • B.repr (B i * B i_1)) ixy)
        (univ : Finset ι)
    simp only [Finsupp.coe_smul, Finsupp.coe_finset_sum, Pi.smul_apply, sum_apply, smul_eq_mul,
      norm_mul] at hk ⊢
    apply le_trans hk
    -- We use the above property again.
    obtain ⟨k', hk'⟩ : ∃ (k' : ι),
        ‖∑ j : ι, B.repr y j • B.repr (B k * B j) ixy‖ ≤
          ‖B.repr y k' • B.repr (B k * B k') ixy‖ := by
      obtain ⟨k, hk0, hk⟩ := IsNonarchimedean.finset_image_add hna'
        (fun i ↦ B.repr y i • B.repr (B k * B i) ixy) (univ : Finset ι)
      exact ⟨k, hk⟩
    apply le_trans (mul_le_mul_of_nonneg_left hk' (norm_nonneg _))
    -- Now an easy computation leads to the desired conclusion.
    rw [norm_smul, mul_assoc, mul_comm (B.norm (B c.fst * B c.snd)), ← mul_assoc]
    exact mul_le_mul (mul_le_mul (B.norm_repr_le_norm _) (B.norm_repr_le_norm _)
      (norm_nonneg _) (B.norm_nonneg _)) (le_trans (B.norm_repr_le_norm _)
        (hc ▸ Finset.le_sup' (fun i : ι × ι ↦ B.norm (B i.1 * B i.2)) (mem_univ (k, k'))))
      (norm_nonneg _) (mul_nonneg (B.norm_nonneg _) (B.norm_nonneg _))
    -- `B c.1 * B c.2` is positive.
  · have h_pos : (0 : ℝ) < B.norm (B i * B i) := by
      have h1 : (1 : L) = (algebraMap K L) 1 := by rw [map_one]
      rw [hBi, mul_one, h1, Basis.norm_extends hBi]
      simp [norm_one, zero_lt_one]
    exact lt_of_lt_of_le h_pos
      (hc ▸ Finset.le_sup' (fun i : ι × ι ↦ B.norm (B i.1 * B i.2)) (mem_univ (i, i)))

/-- For any `k : K`, `y : L`, we have
  `B.norm ((algebra_map K L) k * y) = B.norm ((algebra_map K L) k) * B.norm y`. -/
theorem norm_smul {ι : Type*} [Fintype ι] [Nonempty ι] {B : Basis ι K L} {i : ι}
    (hBi : B i = (1 : L)) (k : K) (y : L) :
    B.norm ((algebraMap K L) k * y) = B.norm ((algebraMap K L) k) * B.norm y := by
  by_cases hk : k = 0
  · rw [hk, map_zero, MulZeroClass.zero_mul, B.norm_zero, MulZeroClass.zero_mul]
  · rw [norm_extends hBi]
    obtain ⟨i, _, hi⟩ := exists_mem_eq_sup' univ_nonempty (fun i ↦ ‖B.repr y i‖)
    obtain ⟨j, _, hj⟩ := exists_mem_eq_sup' univ_nonempty
      (fun i ↦ ‖B.repr ((algebraMap K L) k * y) i‖)
    have hij : ‖B.repr y i‖ = ‖B.repr y j‖ := by
      rw [← hi]
      apply le_antisymm _ (norm_repr_le_norm B j)
      have hj' := Finset.le_sup' (fun i ↦ ‖B.repr ((algebraMap K L) k * y) i‖) (mem_univ i)
      simp only [repr_smul', norm_mul, ← hi] at hj hj'
      exact (mul_le_mul_left (lt_of_le_of_ne (norm_nonneg _)
        (Ne.symm (norm_ne_zero_iff.mpr hk)))).mp (hj ▸ hj')
    simp only [norm, hj]
    rw [repr_smul', norm_mul, hi, hij]

end Module.Basis

end Ring

section Field

variable {K L : Type*} [NormedField K] [Field L] [Algebra K L]

/-- If `K` is a nonarchimedean normed field `L/K` is a finite extension, then there exists a
power-multiplicative nonarchimedean `K`-algebra norm on `L` extending the norm on `K`. -/
theorem exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional (hfd : FiniteDimensional K L)
    (hna : IsNonarchimedean (norm : K → ℝ)) :
    ∃ f : AlgebraNorm K L, IsPowMul f ∧ (∀ (x : K), f ((algebraMap K L) x) = ‖x‖) ∧
      IsNonarchimedean f := by
  -- Choose a basis B = {1, e2,..., en} of the K-vector space L
  set h1 : LinearIndepOn K id ({1} : Set L) :=
    LinearIndepOn.id_singleton _ one_ne_zero
  set ι := { x // x ∈ LinearIndepOn.extend h1 (Set.subset_univ ({1} : Set L)) }
  set B : Basis ι K L := Basis.extend h1
  letI hfin : Fintype ι := FiniteDimensional.fintypeBasisIndex B
  haveI hem : Nonempty ι := B.index_nonempty
  have h1L : (1 : L) ∈ LinearIndepOn.extend h1 _ :=
    Basis.subset_extend _ (Set.mem_singleton (1 : L))
  have hB1 : B ⟨1, h1L⟩ = (1 : L) := by rw [Basis.coe_extend, Subtype.coe_mk]
  -- Define a function g : L → ℝ by setting g (∑ki • ei) = maxᵢ ‖ ki ‖
  set g : L → ℝ := B.norm
  -- g 0 = 0seminormFromBounded
  have hg0 : g 0 = 0 := B.norm_zero
  -- g takes nonnegative values
  have hg_nonneg : ∀ x : L, 0 ≤ g x := fun x ↦ by simp only [g, Basis.norm]; aesop
  -- g extends the norm on K
  have hg_ext : ∀ (x : K), g ((algebraMap K L) x) = ‖x‖ := Basis.norm_extends hB1
  -- g is nonarchimedean
  have hg_na : IsNonarchimedean g := Basis.norm_isNonarchimedean hna
  -- g satisfies the triangle inequality
  have hg_add : ∀ a b : L, g (a + b) ≤ g a + g b :=
    fun _ _ ↦ IsNonarchimedean.add_le hg_nonneg hg_na
  -- g (-a) = g a
  have hg_neg : ∀ a : L, g (-a) = g a := B.norm_neg
  -- g is multiplicatively bounded
  obtain ⟨_, _, hg_bdd⟩ := Basis.norm_mul_le_const_mul_norm hB1 hna
  -- g is a K-module norm
  have hg_mul : ∀ (k : K) (y : L), g ((algebraMap K L) k * y) = g ((algebraMap K L) k) * g y :=
    fun k y ↦ Basis.norm_smul hB1 k y
  -- Using BGR Prop. 1.2.1/2, we can smooth g to a ring norm f on L that extends the norm on K.
  set f := seminormFromBounded hg0 hg_nonneg hg_bdd hg_add hg_neg
  have hf_na : IsNonarchimedean f := seminormFromBounded_isNonarchimedean hg_nonneg hg_bdd hg_na
  have hf_1 : f 1 ≤ 1 := seminormFromBounded_one_le hg_nonneg hg_bdd
  have hf_ext : ∀ (x : K), f ((algebraMap K L) x) = ‖x‖ :=
    fun k ↦ hg_ext k ▸ seminormFromBounded_of_mul_apply hg_nonneg hg_bdd (hg_mul k)
  -- Using BGR Prop. 1.3.2/1, we obtain from f  a power multiplicative K-algebra norm on L
  -- extending the norm on K.
  set F' := smoothingSeminorm f hf_1 hf_na with hF'
  have hF'_ext : ∀ k : K, F' ((algebraMap K L) k) = ‖k‖ := by
    intro k
    rw [← hf_ext _]
    exact smoothingSeminorm_apply_of_map_mul_eq_mul f hf_1 hf_na
      (seminormFromBounded_of_mul_is_mul hg_nonneg hg_bdd (hg_mul k))
  have hF'_1 : F' 1 = 1 := by
    have h1 : (1 : L) = (algebraMap K L) 1 := by rw [map_one]
    simp only [h1, hF'_ext (1 : K), norm_one]
  have hF'_0 : F' ≠ 0 := DFunLike.ne_iff.mpr ⟨(1 : L), by rw [hF'_1]; exact one_ne_zero⟩
  set F : AlgebraNorm K L :=
    { RingSeminorm.toRingNorm F' hF'_0 with
      smul' := fun k y ↦ by
        have hk : ∀ y : L, f (algebraMap K L k * y) = f (algebraMap K L k) * f y :=
          seminormFromBounded_of_mul_is_mul hg_nonneg hg_bdd (hg_mul k)
        have hfk : ‖k‖ = (smoothingSeminorm f hf_1 hf_na) ((algebraMap K L) k) := by
          rw [← hf_ext k, eq_comm, smoothingSeminorm_apply_of_map_mul_eq_mul f hf_1 hf_na hk]
        simp only [hfk, hF']
        -- TODO: There are missing `simp` lemmas here, that should be able to convert
        -- `((smoothingSeminorm f hf_1 hf_na).toRingNorm ⋯).toRingSeminorm y` to
        -- `(smoothingSeminorm f hf_1 hf_na y)`, after which the `erw` would work as a `rw`.
        erw [← smoothingSeminorm_of_mul f hf_1 hf_na hk y]
        rw [Algebra.smul_def]
        rfl }
  have hF_ext (k : K) : F ((algebraMap K L) k) = ‖k‖ := by
    rw [← hf_ext]
    exact smoothingSeminorm_apply_of_map_mul_eq_mul f hf_1 hf_na
      (seminormFromBounded_of_mul_is_mul hg_nonneg hg_bdd (hg_mul k))
  exact ⟨F, isPowMul_smoothingFun f hf_1, hF_ext, isNonarchimedean_smoothingFun f hf_1 hf_na⟩

end Field
