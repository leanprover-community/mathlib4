/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.SiegelsLemma
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.EquivReindex

/-!

# House of an algebraic number
This file defines the house of an algebraic number `α`, which is
the largest of the modulus of its conjugates.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [Hua, L.-K., *Introduction to number theory*][hua1982house]

## Tags
number field, algebraic number, house
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

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
  simp only [house, map_mul]; apply norm_mul_le

lemma house_prod_le (s : Finset K) : house (∏ x ∈ s, x) ≤ ∏ x ∈ s, house x := by
  simpa [house, map_prod] using Finset.norm_prod_le _ _

theorem house_add_le (α β : K) : house (α + β) ≤ house α + house β := by
  simp only [house, map_add]; apply norm_add_le

theorem house_pow_le (α : K) (i : ℕ) : house (α ^ i) ≤ house α ^ i := by
  simpa only [house, map_pow] using norm_pow_le ((canonicalEmbedding K) α) i

theorem house_nat_mul (α : K) (c : ℕ) : house (c * α) = c * house α := by
  rw [house_eq_sup', house_eq_sup', Finset.sup'_eq_sup, Finset.sup'_eq_sup]
  norm_cast
  simp [NNReal.mul_finset_sup]

@[simp] theorem house_intCast (x : ℤ) : house (x : K) = |x| := by
  simp only [house, map_intCast, Pi.intCast_def, pi_norm_const, Complex.norm_intCast, Int.cast_abs]

/-- Let `α` be a non-zero algebraic integer. Then `α` has a conjugate `σ α` with `‖σ α‖ ≥ 1`. -/
lemma exists_conjugate_one_le_norm {α : 𝓞 K} (hα0 : α ≠ 0) :
    ∃ σ : K →+* ℂ, 1 ≤ ‖σ α‖ := by
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace K, 1 ≤ w α := by
    by_contra! h_neg
    let w₀ := Classical.arbitrary (InfinitePlace K)
    have h_ge_one : 1 ≤ w₀ α := InfinitePlace.one_le_of_lt_one hα0 (fun z _ ↦ h_neg z)
    exact (h_neg w₀).not_ge h_ge_one
  use w.embedding
  rwa [InfinitePlace.norm_embedding_eq]

lemma norm_embedding_le_house (α : K) (σ : K →+* ℂ) : ‖σ α‖ ≤ house α := by
  rw [house_eq_sup']
  exact Finset.le_sup' (f := (‖· α‖₊)) (Finset.mem_univ σ)

lemma one_le_house_of_isIntegral {α : K} (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) :
    1 ≤ house α := by
  have ⟨σ, hσ⟩ : ∃ σ : K →+* ℂ, 1 ≤ ‖σ α‖ := by
    apply exists_conjugate_one_le_norm (K := K) (α := ⟨α, hα⟩)
    simpa [RingOfIntegers.ext_iff]
  apply hσ.trans (norm_embedding_le_house α σ)

lemma norm_norm_le_norm_mul_house_pow (α : K) (σ : K →+* ℂ) :
    ‖Algebra.norm ℚ α‖ ≤ ‖σ α‖ * house α ^ (Module.finrank ℚ K - 1) := by
  classical
  set σ' := σ.toRatAlgHom
  calc _ = ‖∏ τ : K →ₐ[ℚ] ℂ, τ α‖ := ?_
       _ = ‖(σ' α) * ∏ τ ∈ univ.erase σ', τ α‖ := by rw [mul_prod_erase univ (· α) (mem_univ σ')]
       _ ≤ ‖σ' α‖ * ∏ τ ∈ univ.erase σ', ‖τ α‖ := ?_
       _ ≤ ‖σ' α‖ * ∏ τ ∈ univ.erase σ', house α := by gcongr; apply norm_embedding_le_house
       _ = ‖σ' α‖ * house α ^ (Module.finrank ℚ K - 1) := by simp
  · rw [← Algebra.norm_eq_prod_embeddings, ← Rat.norm_cast_real,
      Real.norm_eq_abs, eq_ratCast, Complex.norm_ratCast]
  · rw [Complex.norm_mul]
    gcongr
    exact norm_prod_le (univ.erase σ') (· α)

end

end NumberField

namespace NumberField.house

noncomputable section

variable (K)

open Module.Free Module canonicalEmbedding Matrix Finset

attribute [local instance] Matrix.seminormedAddCommGroup

section DecidableEq

variable [DecidableEq (K →+* ℂ)]

set_option backward.privateInPublic true in
/-- `c` is defined as the product of the maximum absolute
  value of the entries of the inverse of the matrix `basisMatrix` and  `finrank ℚ K`. -/
private def c := (finrank ℚ K) * ‖((basisMatrix K).transpose)⁻¹‖

private theorem c_nonneg : 0 ≤ c K := by
  rw [c]
  positivity

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem basis_repr_norm_le_const_mul_house (α : 𝓞 K) (i : K →+* ℂ) :
    ‖(((integralBasis K).reindex (equivReindex K).symm).repr α i : ℂ)‖ ≤
      (c K) * house (algebraMap (𝓞 K) K α) := by
  let σ := canonicalEmbedding K
  calc
    _ ≤ ∑ j, ‖(basisMatrix K)ᵀ⁻¹ i j‖ * ‖σ (algebraMap (𝓞 K) K α) j‖ := by
      rw [← inverse_basisMatrix_mulVec_eq_repr]
      exact norm_sum_le_of_le _ fun _ _ ↦ (norm_mul _ _).le
    _ ≤ ∑ j, ‖((basisMatrix K).transpose)⁻¹‖ * ‖σ (algebraMap (𝓞 K) K α) j‖ := by
      gcongr
      exact norm_entry_le_entrywise_sup_norm ((basisMatrix K).transpose)⁻¹
    _ ≤ ∑ _ : K →+* ℂ, ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖
        * house (algebraMap (𝓞 K) K α) := by
      gcongr with j
      exact norm_le_pi_norm (σ ((algebraMap (𝓞 K) K) α)) j
    _ = ↑(finrank ℚ K) * ‖((basisMatrix K).transpose)⁻¹‖ * house (algebraMap (𝓞 K) K α) := by
      simp [Embeddings.card, mul_assoc]

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


set_option backward.privateInPublic true

/-- `asiegel K a` is the integer matrix of the coefficients of the
product of matrix elements and basis vectors. -/
private def asiegel : Matrix (α × (K →+* ℂ)) (β × (K →+* ℂ)) ℤ := fun k l => a' K a k.1 l.1 l.2 k.2

variable (ha : a ≠ 0)

set_option backward.isDefEq.respectTransparency false in
include ha in
private theorem asiegel_ne_0 : asiegel K a ≠ 0 := by
  simp +unfoldPartialApp only [asiegel, a']
  simp only [ne_eq]
  rw [funext_iff]; intro hs
  simp only [Prod.forall] at hs
  apply ha
  rw [← Matrix.ext_iff]; intro k' l
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
  exact hblin (fun r ↦ x (l, r)) (H _) r

private theorem lin_1 (l k r) : a k l * (newBasis K) r =
    ∑ u, (a' K a k l r u) * (newBasis K) u := by
  simp only [Basis.sum_repr (newBasis K) (a k l * (newBasis K) r), a', ← zsmul_eq_mul]

variable [Fintype β] (cardβ : Fintype.card β = q) (hmulvec0 : asiegel K a *ᵥ x = 0)

include hxl hmulvec0 in
private theorem ξ_mulVec_eq_0 : a *ᵥ ξ K x = 0 := by
  funext k; simp only [Pi.zero_apply]; rw [eq_comm]
  have lin_0 : ∀ u, ∑ r, ∑ l, (a' K a k l r u * x (l, r) : 𝓞 K) = 0 := by
    intro u
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
  have := c_nonneg K
  rw [Matrix.norm_le_iff]
  · intro kr lu
    calc
      ‖asiegel K a kr lu‖ = |asiegel K a kr lu| := ?_
      _ ≤ c K * house ((algebraMap (𝓞 K) K) (a kr.1 lu.1 * ((newBasis K) lu.2))) := ?_
      _ ≤ c K * house ((algebraMap (𝓞 K) K) (a kr.1 lu.1)) *
        house ((algebraMap (𝓞 K) K) ((newBasis K) lu.2)) := ?_
      _ ≤ c K * A * house ((algebraMap (𝓞 K) K) ((newBasis K) lu.2)) := ?_
      _ ≤ c K * A * supOfBasis K := ?_
      _ ≤ c₂ K * A := ?_
    · simp only [Int.cast_abs, ← Real.norm_eq_abs (asiegel K a kr lu)]; rfl
    · have remark := basis_repr_norm_le_const_mul_house K
      simp only [Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
        integralBasis_repr_apply, eq_intCast, Rat.cast_intCast,
          Complex.norm_intCast] at remark
      exact mod_cast remark ((a kr.1 lu.1 * ((newBasis K) lu.2))) kr.2
    · simp only [house, map_mul, mul_assoc]
      gcongr
      apply norm_mul_le
    · rw [mul_assoc, mul_assoc]
      gcongr _ * (?_ * _)
      · apply house_nonneg
      · exact habs kr.1 lu.1
    · gcongr
      simp only [supOfBasis, le_sup'_iff, mem_univ]; use lu.2
    · rw [mul_right_comm, c₂]
      gcongr
      exacts [supOfBasis_nonneg _, le_max_right ..]
  · exact mul_nonneg (c₂_nonneg _) Apos

/-- `c₁ K` is the product of `finrank ℚ K` and  `c₂ K` and depends on `K`. -/
private def c₁ := finrank ℚ K * c₂ K

include habs Apos hxbound hpq in
private theorem house_le_bound : ∀ l, house (ξ K x l).1 ≤ (c₁ K) *
    ((c₁ K * q * A) ^ ((p : ℝ) / (q - p))) := by
  let h := finrank ℚ K
  intro l
  have H₀ : 0 ≤ NumberField.house.supOfBasis K := supOfBasis_nonneg _
  have H₁ : 0 < (q - p : ℝ) := sub_pos.mpr <| mod_cast hpq
  calc _ = house (algebraMap (𝓞 K) K (∑ r, (x (l, r)) * ((newBasis K) r))) := rfl
       _ ≤ ∑ r, house (((algebraMap (𝓞 K) K) (x (l, r))) *
        ((algebraMap (𝓞 K) K) ((newBasis K) r))) := ?_
       _ ≤ ∑ r, ‖x (l, r)‖ * house ((algebraMap (𝓞 K) K) ((newBasis K) r)) := ?_
       _ ≤ ∑ r, ‖x (l, r)‖ * (supOfBasis K) := ?_
       _ ≤ ∑ _r : K →+* ℂ, ((↑q * h * ‖asiegel K a‖) ^ ((p : ℝ) / (q - p))) * supOfBasis K := ?_
       _ ≤ h * (c₂ K) * ((q * c₁ K * A) ^ ((p : ℝ) / (q - p))) := ?_
       _ ≤ c₁ K * ((c₁ K * ↑q * A) ^ ((p : ℝ) / (q - p))) := ?_
  · simp_rw [← map_mul, map_sum]; apply house_sum_le_sum_house
  · gcongr with r _; convert house_mul_le ..
    simp only [map_intCast, house_intCast, Int.cast_abs, Int.norm_eq_abs]
  · unfold supOfBasis
    gcongr with r _
    simp only [le_sup'_iff, mem_univ, true_and]; use r
  · gcongr with r _
    exact le_trans (norm_le_pi_norm x ⟨l, r⟩) hxbound
  · simp only [sum_const, card_univ, nsmul_eq_mul]
    rw [Embeddings.card, mul_comm _ (supOfBasis K), c₂, c₁, ← mul_assoc,
      ← mul_assoc (q : ℝ), mul_assoc (q * _ : ℝ)]
    gcongr
    · exact le_mul_of_one_le_left (supOfBasis_nonneg K) (le_max_left ..)
    · exact asiegel_remark K a habs Apos
  · rw [mul_comm (q : ℝ) (c₁ K)]; rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
include hpq h0p cardα cardβ ha habs in
/-- There exists a "small" non-zero algebraic integral solution of an
non-trivial underdetermined system of linear equations with algebraic integer coefficients. -/
theorem exists_ne_zero_int_vec_house_le :
    ∃ (ξ : β → 𝓞 K), ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧
    ∀ l, house (ξ l).1 ≤ c₁ K * ((c₁ K * q * A) ^ ((p : ℝ) / (q - p))) := by
  classical
  let h := finrank ℚ K
  have hphqh : p * h < q * h := by gcongr; exact finrank_pos
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
