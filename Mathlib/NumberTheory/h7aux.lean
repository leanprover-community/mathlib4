/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.NumberField.Basic

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
    cases' hx with ha hb; · simp_rw [ha, isAlgebraic_iff_isIntegral.1 hα]
    cases' hb with hb hc; · simp_rw [hb, isAlgebraic_iff_isIntegral.1 hβ]
    simp_rw [mem_singleton_iff.1 hc, isAlgebraic_iff_isIntegral.1 hγ])}

--#check canonicalEmbedding

lemma getElemsInNF (α β γ : ℂ) (hα : IsAlgebraic ℚ α)
    (hβ : IsAlgebraic ℚ β) (hγ : IsAlgebraic ℚ γ) :
      ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (σ : K →+* ℂ) (_ : DecidableEq (K →+* ℂ)),
    ∃ (α' β' γ' : K), α = σ α' ∧ β = σ β' ∧ γ = σ γ' := by
  have  hab := adjoin.mono ℚ {α, β} {α, β, γ}
    fun x hxab => by cases' hxab with hxa hxb; left; exact hxa; right; left; exact hxb
  have hac := adjoin.mono ℚ {α, γ} {α, β, γ}
    fun x hx => by cases' hx with hsf hff; left; exact hsf; right; right; exact hff
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

lemma IsIntegral.Cast(K : Type) [Field K]  (a : ℤ) : IsIntegral ℤ (a : K) :=
  map_isIntegral_int (algebraMap ℤ K) (Algebra.IsIntegral.isIntegral _)

lemma IsIntegral.Nat (K : Type) [Field K] (a : ℕ) : IsIntegral ℤ (a : K) := by
  have : (a : K) = ((a : ℤ) : K) := by simp only [Int.cast_natCast]
  rw [this]; apply IsIntegral.Cast

lemma triple_comm (K : Type) [Field K]  (a b c : ℤ) (x y z : K) :
 ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
  simp only [zsmul_eq_mul, Int.cast_mul]; ring
