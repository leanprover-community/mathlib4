/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.H7.House
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

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

variable [Field K] [NumberField K]

/-- Let α be a non-zero algebraic integer. Then α has a conjugate α(i) with |α(i)| ≥ 1. -/
lemma exists_conjugate_abs_gt_one {α : 𝓞 K} (hα0 : α ≠ 0) :
    ∃ σ : K →+* ℂ, 1 ≤ norm (σ α) := by
  have h_exists_w : ∃ w : InfinitePlace K, 1 ≤ w α := by
    by_contra h_neg; push_neg at h_neg
    let w₀ := (inferInstance : Nonempty (InfinitePlace K)).some
    have h_ge_one : 1 ≤ w₀ α :=
      NumberField.InfinitePlace.one_le_of_lt_one hα0 (fun z _ => h_neg z)
    linarith [h_neg w₀, h_ge_one]
  rcases h_exists_w with ⟨w, hw⟩
  use w.embedding
  rw [← InfinitePlace.norm_embedding_eq] at hw
  exact hw

lemma house_gt_one_of_isIntegral {α : K} (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) :
  1 ≤ house α := by
  have ⟨σ, hσ⟩ : ∃ σ : K →+* ℂ, 1 ≤ ‖σ α‖ := by
    let a : 𝓞 K := ⟨α, hα⟩
    have hα_int_0 : a ≠ 0 := by
      intros H
      apply hα0
      injection H
    apply exists_conjugate_abs_gt_one (K := K) hα_int_0
  rw [house_eq_sup']
  have h_le_sup := Finset.le_sup' (fun φ : K →+* ℂ ↦ ‖φ α‖₊) (Finset.mem_univ σ)
  exact le_trans hσ h_le_sup

lemma house_alg_int_leq_pow (α : K) (n m : ℕ) (h : n ≤ m) (hα0 : α ≠ 0) (H : IsIntegral ℤ α) :
  house α ^ n ≤ house α ^ m :=
Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl ⟨house_gt_one_of_isIntegral H hα0, h⟩)

lemma house_alg_int_leq_pow' (α : K) (n m : Int) (h_exp : n ≤ m)
    (hα0 : α ≠ 0) (h_int : IsIntegral ℤ α) :
  house α ^ n ≤ house α ^ m := by
  have h_base : 1 ≤ house α := house_gt_one_of_isIntegral h_int hα0
  exact zpow_le_zpow_right₀ h_base h_exp

lemma house_alg_int_leq_pow_real (α : K) (r s : ℝ) (h_exp : r ≤ s)
    (hα0 : α ≠ 0) (h_int : IsIntegral ℤ α) :
  house α ^ r ≤ house α ^ s := by
  have h_base : 1 ≤ house α := house_gt_one_of_isIntegral h_int hα0
  exact Real.rpow_le_rpow_of_exponent_le h_base h_exp

lemma house_leq_pow_pow (α : K) (n : ℕ) (hn : n ≠ 0) (hα0 : α ≠ 0)
  (H : IsIntegral ℤ α) : house α ≤ house α ^ n :=
le_self_pow₀ (house_gt_one_of_isIntegral H hα0) hn

lemma house_leq_one_pow (α : K) (n : ℕ) (hn : n ≠ 0) (hα0 : α ≠ 0)
  (H : IsIntegral ℤ α) :
  1 ≤ house α ^ n :=
(house_gt_one_of_isIntegral H hα0).trans (house_leq_pow_pow α n hn hα0 H)
