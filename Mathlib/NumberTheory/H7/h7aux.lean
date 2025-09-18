/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.H7.House

set_option autoImplicit true
set_option linter.style.multiGoal false
set_option linter.style.cases false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars true
set_option linter.style.longFile 0

open BigOperators Module.Free Fintype NumberField FiniteDimensional
  Matrix Set Polynomial Finset IntermediateField Complex

noncomputable section

lemma ExistsAlgInt {K : Type*} [Field K] [NumberField K] (α : K) :
  ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ (k • α) := by
  obtain ⟨y, hy, hf⟩ := exists_integral_multiples ℤ ℚ (L := K) {α}
  refine ⟨y, hy, hf α (mem_singleton_self _)⟩

def c'_both {K : Type*} [Field K] [NumberField K] (α : K) :
   {c : ℤ | c ≠ 0 ∧ IsIntegral ℤ (c • α)} :=
  ⟨(ExistsAlgInt α).choose, (ExistsAlgInt α).choose_spec⟩

lemma adjoin_le_adjoin_more (α β : ℂ) (_ : IsAlgebraic ℚ α) (_ : IsAlgebraic ℚ β) :
  (adjoin _ {α} ≤ adjoin ℚ {α, β}) ∧ (adjoin _ {β} ≤ adjoin ℚ {α, β}) :=
  ⟨by apply adjoin.mono; intros x hx; left; exact hx,
   by apply adjoin.mono; intros x hx; right; exact hx⟩

lemma isNumberField_adjoin_alg_numbers (α β γ : ℂ)
  (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β) (hγ : IsAlgebraic ℚ γ) :
    NumberField (adjoin ℚ {α, β, γ}) :=  {
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  to_finiteDimensional := finiteDimensional_adjoin (fun x hx => by
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with ⟨ha, hb⟩; · simp_rw [isAlgebraic_iff_isIntegral.1 hα]
    rename_i hb
    rcases hb with ⟨hb,hc⟩; · simp_rw [isAlgebraic_iff_isIntegral.1 hβ]
    rename_i hc
    simp_rw [mem_singleton_iff.1 hc, isAlgebraic_iff_isIntegral.1 hγ]
    )}

--#check canonicalEmbedding

lemma getElemsInNF (α β γ : ℂ) (hα : IsAlgebraic ℚ α)
    (hβ : IsAlgebraic ℚ β) (hγ : IsAlgebraic ℚ γ) :
      ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (σ : K →+* ℂ) (_ : DecidableEq (K →+* ℂ)),
    ∃ (α' β' γ' : K), α = σ α' ∧ β = σ β' ∧ γ = σ γ' := by
  have  hab := adjoin.mono ℚ {α, β} {α, β, γ}
    fun x hxab => by
      rcases hxab with ⟨hxa, hxb⟩; left;
      simp only
      rename_i h
      simp only [mem_singleton_iff] at h
      subst h
      simp_all only [mem_insert_iff, mem_singleton_iff, true_or, or_true]
  have hac := adjoin.mono ℚ {α, γ} {α, β, γ}
    fun x hx => by rcases hx with ⟨hsf, hff⟩; left; rfl ; rename_i h; aesop;
  use adjoin ℚ {α, β, γ}
  constructor
  use isNumberField_adjoin_alg_numbers α β γ hα hβ hγ
  use { toFun := fun x => x.1, map_one' := rfl, map_mul' := fun x y => rfl
        map_zero' := rfl, map_add' := fun x y => rfl}
  use Classical.typeDecidableEq (↥ℚ⟮α, β, γ⟯ →+* ℂ)
  simp only [exists_and_left, exists_and_right, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, Subtype.exists, exists_prop, exists_eq_right']
  exact ⟨adjoin_simple_le_iff.1 fun _ hx =>
     hab ((adjoin_le_adjoin_more α β hα hβ).1 hx),
    adjoin_simple_le_iff.1 fun _ hx =>  hab (by
    apply adjoin.mono; intros x hx;
    · right; exact hx;
    · exact hx),
    adjoin_simple_le_iff.1 fun _ hx =>
    hac ((adjoin_le_adjoin_more α γ hα hγ).2 hx)⟩

lemma IsIntegral_assoc (K : Type) [Field K]
{x y : ℤ} (z : ℤ) (α : K) (ha : IsIntegral ℤ (z • α)) :
  IsIntegral ℤ ((x * y * z : ℤ) • α) := by
  have : ((x * y * z : ℤ) • α) = (x * y) • (z • α) := by
    simp only [Int.cast_mul, zsmul_eq_mul, mul_assoc (↑x * ↑y : K) z α]
  conv => enter [2]; rw [this]
  apply IsIntegral.smul _ ha

-- lemma IsIntegral_assoc' (K : Type) [Field K]
-- {x y : ℤ} (z : ℤ) (α : K) (ha : IsIntegral ℤ (z • α)) :
--   IsIntegral ℤ (abs (x * y * z : ℤ) • α) := by
--   have : ((x * y * z : ℤ) • α) = (x * y) • (z • α) := by
--     simp only [Int.cast_mul, zsmul_eq_mul, mul_assoc (↑x * ↑y : K) z α]
--   conv => enter [2]; rw [this]
--   apply IsIntegral.smul _ ha

lemma IsIntegral.Cast (K : Type) [Field K] (a : ℤ) : IsIntegral ℤ (a : K) :=
  map_isIntegral_int (algebraMap ℤ K) (Algebra.IsIntegral.isIntegral _)

lemma IsIntegral.Nat (K : Type) [Field K] (a : ℕ) : IsIntegral ℤ (a : K) := by
  have : (a : K) = ((a : ℤ) : K) := by simp only [Int.cast_natCast]
  rw [this]; apply IsIntegral.Cast

lemma triple_comm (K : Type) [Field K] (a b c : ℤ) (x y z : K) :
 ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
  simp only [zsmul_eq_mul, Int.cast_mul]; ring

-- Lemma 3.6. Let α be a non-zero algebraic integer. Then α has a conjugate α(i)
-- with |α(i)| ≥ 1.
-- Proof. Let α(1), . . . , α(d) be the conjugates of α. Then by Lemma 3.4, the minimal
-- polynomial of α, fα = ∏d
-- i=1(X − α(i)) has its coefficients in Z. In particular, the
-- product α(1) · · · α(d) = ±f (0) is a non-zero rational integer, whence has absolute
-- value at least 1. This implies the lemma.

-- Lemma 3.6. Let α be a non-zero algebraic integer. Then α has a conjugate α(i)
-- with |α(i)| ≥ 1.

-- Proof. Let α(1), ..., α(d) be the conjugates of α. Then by Lemma 3.4, the minimal
-- polynomial of α, fα = ∏_{i=1}^d (X − α(i)), has its coefficients in ℤ.
--#moogle "product of elements in a set of complex numbers."
--#check minpoly.ne_zero
--In particular, the
-- product α(1) ··· α(d) = ±f(0) is a non-zero rational integer, whence has absolute
-- value at least 1. This implies the lemma.
--#check NumberField.Embeddings.range_eval_eq_rootSet_minpoly
variable [Field K] [NumberField K]

/-- Lemma 3.6: Let α be a non-zero algebraic integer.
Then α has a conjugate α(i) with |α(i)| > 1. -/
lemma exists_conjugate_abs_gt_one {α : 𝓞 K} (hα0 : α ≠ 0) :
    ∃ σ : K →+* ℂ, 1 ≤ norm (σ α) := by
  have HI : IsIntegral ℤ α := RingOfIntegers.isIntegral α
  let S := ((minpoly ℤ α).rootSet ℚ).toFinset
  let a : ℚ := by {
    apply Finset.prod S
    exact fun a ↦ a}
  have haneq0 : a ≠ 0 := by {
    dsimp [a,S]
    intros H
    sorry
  }
  have Hpoly := minpoly.ne_zero HI
  have : 1 ≤ norm (a) := by {
    dsimp [a]
    simp only [norm_prod]
    sorry
  }
  -- Let α₁, ..., α_d be the conjugates of α.
  let d := Module.finrank ℚ K
  sorry
  --let σs := NumberField.Embeddings K ℂ
  -- The conjugates are σ α for σ ∈ σs.
  --let α_conj := fun σ : K →+* ℂ => σ α
  -- The minimal polynomial of α has integer coefficients,
  -- and the product of the conjugates is ±fα(0), a nonzero integer.

    --NumberField.prod_embeddings_eq_minpoly_eval_zero hα
  -- Since α ≠ 0, the product is a nonzero integer, so at least one conjugate has |σ α| ≥ 1.
  -- have h_prod_nonzero : (minpoly ℚ α).eval 0 ≠ 0 :=
  --   minpoly.eval_ne_zero_of_isIntegral_of_ne_zero hα hα0
  -- have h_abs_prod : 1 ≤ |∏ σ in Finset.univ, α_conj σ| :=
  --   by
  --     rw [h_prod]
  --     have : (minpoly ℚ α).eval 0 ∈ ℤ := minpoly.eval_int_of_isIntegral hα
  --     have h0 : (minpoly ℚ α).eval 0 ≠ 0 := h_prod_nonzero
  --     exact Int.one_le_abs_of_ne_zero h0
  -- -- If all |σ α| ≤ 1, then |product| ≤ 1, contradiction.
  -- by_contra H
  -- push_neg at H
  -- have h_le : |∏ σ in Finset.univ, α_conj σ| ≤ 1 :=
  --   by
  --     apply Finset.abs_prod_le_prod_abs
  --     intros σ _
  --     exact H σ
  -- linarith
  -- -- Therefore, there exists σ such that |σ α| > 1.
  -- obtain ⟨σ, hσ⟩ := exists_gt_of_prod_le_and_one_le
  -- (Finset.univ) (fun σ => |α_conj σ|) h_abs_prod h_le
  -- use σ
  -- exact hσ

lemma house_gt_one_of_isIntegral {α : K}
    (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) :
  1 ≤ house α := by {
  -- By Lemma 3.6, there is a conjugate σ such that |σ α| > 1.
  unfold house
  sorry
  }

lemma house_alg_int_leq_pow (α : K) (n m : ℕ) (h : n ≤ m) (hα0 : α ≠ 0)
   (H : IsIntegral ℤ α)  :
house α ^ n ≤ house α ^ m := by {
  refine Bound.pow_le_pow_right_of_le_one_or_one_le ?_
  left
  constructor
  · apply house_gt_one_of_isIntegral
    exact H
    exact hα0
  · apply h}

lemma house_leq_pow_pow (α : K) (n : ℕ) (hn : n ≠ 0) (hα0 : α ≠ 0)
   (H : IsIntegral ℤ α) :
house α ≤ house α ^ n := by {
  refine le_self_pow₀ ?_ ?_
  · exact house_gt_one_of_isIntegral H hα0
  · exact hn}

lemma house_leq_one_pow (α : K) (n : ℕ) (hn : n ≠ 0) (hα0 : α ≠ 0)
   (H : IsIntegral ℤ α) :
  1 ≤ house α ^ n := by {
  trans
  · apply house_gt_one_of_isIntegral H hα0
  · exact house_leq_pow_pow α n hn hα0 H
}
