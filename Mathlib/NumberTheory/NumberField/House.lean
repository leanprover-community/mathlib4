/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.EquivReindex

/-!

# House of an algebraic number
This file defines the house of an algebraic number `α`, which is
the largest of the modulus of its conjugates.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [Keng, H. L, *Introduction to number theory*][keng1982house]

## Tagshouse
number field, algebraic number, house
-/

variable {K : Type*} [Field K] [NumberField K]

namespace NumberField

noncomputable section

open Module.Free Module canonicalEmbedding Matrix Finset

attribute [local instance] Matrix.seminormedAddCommGroup

/-- The house of an algebraic number as the norm of its image by the canonical embedding. -/
def house (α : K) : ℝ := ‖canonicalEmbedding K α‖

/-- The house is the largest of the modulus of the conjugates of an algebraic number. -/
theorem house_eq_sup' (α : K) :
    house α = univ.sup' univ_nonempty (fun φ : K →+* ℂ ↦ ‖φ α‖₊) := by
  rw [house, ← coe_nnnorm, nnnorm_eq, ← sup'_eq_sup univ_nonempty]

theorem house_sum_le_sum_house {ι : Type*} (s : Finset ι) (α : ι → K) :
    house (∑ i ∈ s, α i) ≤ ∑ i ∈ s, house (α i) := by
  simp only [house, map_sum]; apply norm_sum_le_of_le; intros; rfl

theorem house_nonneg (α : K) : 0 ≤ house α := norm_nonneg _

theorem house_mul_le (α β : K) : house (α * β) ≤ house α * house β := by
  simp only [house, _root_.map_mul]; apply norm_mul_le

@[simp] theorem house_intCast (x : ℤ) : house (x : K) = |x| := by
  simp only [house, map_intCast, Pi.intCast_def, pi_norm_const, Complex.norm_eq_abs,
    Complex.abs_intCast, Int.cast_abs]

end

end NumberField

namespace NumberField.house

noncomputable section

variable (K)

open Module.Free Module canonicalEmbedding Matrix Finset

attribute [local instance] Matrix.seminormedAddCommGroup

section DecidableEq

variable [DecidableEq (K →+* ℂ)]

/-- `c` is defined as the product of the maximum absolute
  value of the entries of the inverse of the matrix `basisMatrix` and  `finrank ℚ K`. -/
private def c := (finrank ℚ K) * ‖((basisMatrix K).transpose)⁻¹‖

private theorem c_nonneg : 0 ≤ c K := by
  rw [c, mul_nonneg_iff]; left
  exact ⟨by simp only [Nat.cast_nonneg], norm_nonneg ((basisMatrix K).transpose)⁻¹⟩

theorem basis_repr_abs_le_const_mul_house (α : 𝓞 K) (i : K →+* ℂ) :
    Complex.abs (((integralBasis K).reindex (equivReindex K).symm).repr α i) ≤
      (c K) * house (algebraMap (𝓞 K) K α) := by
  let σ := canonicalEmbedding K
  calc
    _ ≤ ∑ j, ‖((basisMatrix K).transpose)⁻¹‖ * Complex.abs (σ (algebraMap (𝓞 K) K α) j) := ?_
    _ ≤ ∑ _ : K →+* ℂ, ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖
        * house (algebraMap (𝓞 K) K α) := ?_
    _ = ↑(finrank ℚ K) * ‖((basisMatrix K).transpose)⁻¹‖ * house (algebraMap (𝓞 K) K α) := ?_

  · rw [← inverse_basisMatrix_mulVec_eq_repr]
    apply le_trans
    · apply le_trans (AbsoluteValue.sum_le Complex.abs _ _)
      · exact sum_le_sum (fun _ _ => (AbsoluteValue.map_mul Complex.abs _ _).le)
    · apply sum_le_sum (fun _ _ => mul_le_mul_of_nonneg_right ?_
        (AbsoluteValue.nonneg Complex.abs _))
      · exact norm_entry_le_entrywise_sup_norm ((basisMatrix K).transpose)⁻¹
  · apply sum_le_sum; intros j _
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg fun i j ↦ ((basisMatrix K).transpose)⁻¹ i j)
    · exact norm_le_pi_norm (σ ((algebraMap (𝓞 K) K) α)) j
  · rw [sum_const, card_univ, nsmul_eq_mul, Embeddings.card, mul_assoc]

/-- `newBasis K` defines a reindexed basis of the ring of integers of `K`,
  adjusted by the inverse of the equivalence `equivReindex`. -/
private def newBasis := (RingOfIntegers.basis K).reindex (equivReindex K).symm

/-- `supOfBasis K` calculates the supremum of the absolute values of
  the elements in `newBasis K`. -/
private def supOfBasis : ℝ := univ.sup' univ_nonempty
  fun r ↦ house (algebraMap (𝓞 K) K (newBasis K r))

end DecidableEq

private theorem supOfBasis_nonneg : 0 ≤ supOfBasis K := by
  simp only [supOfBasis, le_sup'_iff, mem_univ, and_self,
    exists_const, house_nonneg]

variable {α : Type*} {β : Type*} (a : Matrix α β (𝓞 K))

/-- `a' K a` returns the integer coefficients of the basis vector in the
  expansion of the product of an algebraic integer and a basis vectors. -/
private def a' : α → β → (K →+* ℂ) → (K →+* ℂ) → ℤ := fun k l r =>
  (newBasis K).repr (a k l * (newBasis K) r)

/--`asiegel K a` the integer matrix of the coefficients of the
  product of matrix elements and basis vectors -/
private def asiegel : Matrix (α × (K →+* ℂ)) (β × (K →+* ℂ)) ℤ := fun k l => a' K a k.1 l.1 l.2 k.2

variable (ha : a ≠ 0)

include ha in
private theorem asiegel_ne_0 : asiegel K a ≠ 0 := by
  simp (config := { unfoldPartialApp := true }) only [asiegel, a']
  simp only [ne_eq]
  rw [funext_iff]; intros hs
  simp only [Prod.forall] at hs
  apply ha
  rw [← Matrix.ext_iff]; intros k' l
  specialize hs k'
  let ⟨b⟩ := Fintype.card_pos_iff.1 (Fintype.card_pos (α := (K →+* ℂ)))
  have := ((newBasis K).repr.map_eq_zero_iff (x := (a k' l * (newBasis K) b))).1 <| by
    ext b'
    specialize hs b'
    rw [funext_iff] at hs
    simp only [Prod.forall] at hs
    apply hs
  simp only [mul_eq_zero] at this
  exact this.resolve_right (Basis.ne_zero (newBasis K) b)

variable {p q : ℕ} (h0p : 0 < p) (hpq : p < q) (x : β × (K →+* ℂ) → ℤ) (hxl : x ≠ 0)

/-- `ξ` is the product of `x (l, r)` and the `r`-th basis element of the newBasis of `K`. -/
private def ξ : β → 𝓞 K := fun l => ∑ r : K →+* ℂ, x (l, r) * (newBasis K r)

include hxl in
private theorem ξ_ne_0 : ξ K x ≠ 0 := by
  intro H
  apply hxl
  ext ⟨l, r⟩
  rw [funext_iff] at H
  have hblin := Basis.linearIndependent (newBasis K)
  simp only [zsmul_eq_mul, Fintype.linearIndependent_iff] at hblin
  exact hblin (fun r ↦ x (l,r)) (H _) r

private theorem lin_1 (l k r) : a k l * (newBasis K) r =
    ∑ u, (a' K a k l r u) * (newBasis K) u := by
  simp only [Basis.sum_repr (newBasis K) (a k l * (newBasis K) r), a', ← zsmul_eq_mul]

variable [Fintype β] (cardβ : Fintype.card β = q) (hmulvec0 : asiegel K a *ᵥ x = 0)

include hxl hmulvec0 in
private theorem ξ_mulVec_eq_0 : a *ᵥ ξ K x = 0 := by
  funext k; simp only [Pi.zero_apply]; rw [eq_comm]

  have lin_0 : ∀ u, ∑ r, ∑ l, (a' K a k l r u * x (l, r) : 𝓞 K) = 0 := by
    intros u
    have hξ := ξ_ne_0 K x hxl
    rw [Ne, funext_iff, not_forall] at hξ
    rcases hξ with ⟨l, hξ⟩
    rw [funext_iff] at hmulvec0
    specialize hmulvec0 ⟨k, u⟩
    simp only [Fintype.sum_prod_type, mulVec, dotProduct, asiegel] at hmulvec0
    rw [sum_comm] at hmulvec0
    exact mod_cast hmulvec0

  have : 0 = ∑ u, (∑ r, ∑ l, a' K a k l r u * x (l, r) : 𝓞 K) * (newBasis K) u := by
    simp only [lin_0, zero_mul, sum_const_zero]

  have : 0 = ∑ r, ∑ l, x (l, r) * ∑ u, a' K a k l r u * (newBasis K) u := by
    conv at this => enter [2, 2, u]; rw [sum_mul]
    rw [sum_comm] at this
    rw [this]; congr 1; ext1 r
    conv => enter [1, 2, l]; rw [sum_mul]
    rw [sum_comm]; congr 1; ext1 r
    rw [mul_sum]; congr 1; ext1 r
    ring
  rw [sum_comm] at this
  rw [this]; congr 1; ext1 l
  rw [ξ, mul_sum]; congr 1; ext1 l
  rw [← lin_1]; ring

variable {A : ℝ} (habs : ∀ k l, (house ((algebraMap (𝓞 K) K) (a k l))) ≤ A)

variable [DecidableEq (K →+* ℂ)]

/-- `c₂` is the product of the maximum of `1` and `c`, and `supOfBasis`. -/
private abbrev c₂ := max 1 (c K) * (supOfBasis K)

private theorem c₂_nonneg : 0 ≤ c₂ K :=
  mul_nonneg (le_trans zero_le_one (le_max_left ..)) (supOfBasis_nonneg _)

variable [Fintype α] (cardα : Fintype.card α = p) (Apos : 0 ≤ A)
  (hxbound : ‖x‖ ≤ (q * finrank ℚ K * ‖asiegel K a‖) ^ ((p : ℝ) / (q - p)))

include habs Apos in
private theorem asiegel_remark : ‖asiegel K a‖ ≤ c₂ K * A := by
  rw [Matrix.norm_le_iff]
  · intro kr lu
    calc
      ‖asiegel K a kr lu‖ = |asiegel K a kr lu| := ?_
      _ ≤ (c K) *
        house ((algebraMap (𝓞 K) K) (a kr.1 lu.1 * ((newBasis K) lu.2))) := ?_
      _ ≤ (c K) * house ((algebraMap (𝓞 K) K) (a kr.1 lu.1)) *
        house ((algebraMap (𝓞 K) K) ((newBasis K) lu.2)) := ?_
      _ ≤ (c K) * A * house ((algebraMap (𝓞 K) K) ((newBasis K) lu.2)) := ?_
      _ ≤ (c K) * A * (supOfBasis K) := ?_
      _ ≤ (c₂ K) * A := ?_
    · simp only [Int.cast_abs, ← Real.norm_eq_abs (asiegel K a kr lu)]; rfl
    · have remark := basis_repr_abs_le_const_mul_house K
      simp only [Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
        integralBasis_repr_apply, eq_intCast, Rat.cast_intCast,
          Complex.abs_intCast] at remark
      exact mod_cast remark ((a kr.1 lu.1 * ((newBasis K) lu.2))) kr.2
    · simp only [house, _root_.map_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (c_nonneg K)
    · rw [mul_assoc, mul_assoc]
      apply mul_le_mul_of_nonneg_left ?_ (c_nonneg K)
      · apply mul_le_mul_of_nonneg_right (habs kr.1 lu.1) ?_
        · exact norm_nonneg ((canonicalEmbedding K) ((algebraMap (𝓞 K) K)
            ((newBasis K) lu.2)))
    ·  apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg (c_nonneg K) Apos)
       · simp only [supOfBasis, le_sup'_iff, mem_univ]; use lu.2
    · rw [mul_right_comm]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right ..) (supOfBasis_nonneg K)) Apos
  · rw [mul_nonneg_iff]; left; exact ⟨c₂_nonneg K, Apos⟩

/-- `c₁ K` is the product of `finrank ℚ K` and  `c₂ K` and depends on `K`. -/
private def c₁ := finrank ℚ K * c₂ K

include habs Apos hxbound hpq in
private theorem house_le_bound : ∀ l, house (ξ K x l).1 ≤ (c₁ K) *
    ((c₁ K * q * A)^((p : ℝ) / (q - p))) := by
  let h := finrank ℚ K
  intros l
  calc _ = house (algebraMap (𝓞 K) K (∑ r, (x (l, r)) * ((newBasis K) r))) := rfl
       _ ≤ ∑ r, house (((algebraMap (𝓞 K) K) (x (l, r))) *
        ((algebraMap (𝓞 K) K) ((newBasis K) r))) := ?_
       _ ≤ ∑ r, ‖x (l,r)‖ * house ((algebraMap (𝓞 K) K) ((newBasis K) r)) := ?_
       _ ≤ ∑ r, ‖x (l, r)‖ * (supOfBasis K) := ?_
       _ ≤ ∑ _r : K →+* ℂ, ((↑q * h * ‖asiegel K a‖) ^ ((p : ℝ) / (q - p))) * supOfBasis K := ?_
       _ ≤ h * (c₂ K) * ((q * c₁ K * A) ^ ((p : ℝ) / (q - p))) := ?_
       _ ≤ c₁ K * ((c₁ K * ↑q * A) ^ ((p : ℝ) / (q - p))) := ?_
  · simp_rw [← _root_.map_mul, map_sum]; apply house_sum_le_sum_house
  · apply sum_le_sum; intros r _; convert house_mul_le ..
    simp only [map_intCast, house_intCast, Int.cast_abs, Int.norm_eq_abs]
  · apply sum_le_sum; intros r _; unfold supOfBasis
    apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg (x (l,r)))
    · simp only [le_sup'_iff, mem_univ, true_and]; use r
  · apply sum_le_sum; intros r _
    apply mul_le_mul_of_nonneg_right ?_ (supOfBasis_nonneg K)
    exact le_trans (norm_le_pi_norm x ⟨l, r⟩) hxbound
  · simp only [Nat.cast_mul, sum_const, card_univ, nsmul_eq_mul]
    rw [Embeddings.card, mul_comm _ (supOfBasis K), c₂, c₁, ← mul_assoc]
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg' _)
      · exact le_mul_of_one_le_left (supOfBasis_nonneg K) (le_max_left ..)
    · apply Real.rpow_le_rpow (mul_nonneg (mul_nonneg (Nat.cast_nonneg' _) (Nat.cast_nonneg' _))
        (norm_nonneg _))
      · rw [← mul_assoc, mul_assoc (_*_)]
        apply mul_le_mul_of_nonneg_left (asiegel_remark K a habs Apos)
          (mul_nonneg (Nat.cast_nonneg' _) (Nat.cast_nonneg _))
      · exact div_nonneg (Nat.cast_nonneg' _) (sub_nonneg.2 (mod_cast hpq.le))
    · apply Real.rpow_nonneg
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg' _) (Nat.cast_nonneg' _))
        (norm_nonneg _)
    · exact mul_nonneg (Nat.cast_nonneg' _) (mul_nonneg (le_trans zero_le_one (le_max_left ..))
        (supOfBasis_nonneg _))
  · rw [mul_comm (q : ℝ) (c₁ K)]; rfl

include hpq h0p cardα cardβ ha habs in
/-- There exists a "small" non-zero algebraic integral solution of an
 non-trivial underdetermined system of linear equations with algebraic integer coefficients.-/
theorem exists_ne_zero_int_vec_house_le :
    ∃ (ξ : β → 𝓞 K), ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧
    ∀ l, house (ξ l).1 ≤ c₁ K * ((c₁ K * q * A) ^ ((p : ℝ) / (q - p))) := by
  classical
  let h := finrank ℚ K
  have hphqh : p * h < q * h := mul_lt_mul_of_pos_right hpq finrank_pos
  have h0ph : 0 < p * h := by rw [mul_pos_iff]; constructor; exact ⟨h0p, finrank_pos⟩
  have hfinp : Fintype.card (α × (K →+* ℂ)) = p * h := by
    rw [Fintype.card_prod, cardα, Embeddings.card]
  have hfinq : Fintype.card (β × (K →+* ℂ)) = q * h := by
    rw [Fintype.card_prod, cardβ, Embeddings.card]
  have ⟨x, hxl, hmulvec0, hxbound⟩ :=
    Int.Matrix.exists_ne_zero_int_vec_norm_le' (asiegel K a)
      (by rwa [hfinp, hfinq]) (by rwa [hfinp]) (asiegel_ne_0 K a ha)
  simp only [hfinp, hfinq, Nat.cast_mul] at hmulvec0 hxbound
  rw [← sub_mul, mul_div_mul_right _ _ (mod_cast finrank_pos.ne')] at hxbound
  have Apos : 0 ≤ A := by
    have ⟨k⟩ := Fintype.card_pos_iff.1 (cardα ▸ h0p)
    have ⟨l⟩ := Fintype.card_pos_iff.1 (cardβ ▸ h0p.trans hpq)
    exact le_trans (house_nonneg _) (habs k l)
  use ξ K x, ξ_ne_0 K x hxl, ξ_mulVec_eq_0 K a x hxl hmulvec0,
    house_le_bound K a hpq x habs Apos hxbound

end

end NumberField.house
