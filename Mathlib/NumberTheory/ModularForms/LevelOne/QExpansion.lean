/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

/-!
# Injectivity of the `q`-expansion on the graded ring of level one modular forms

## Main results

* `ModularForm.levelOne_qExpansionAlgHom_injective`: the `q`-expansion map
  `ModularForm.qExpansionAlgHom` is injective on the graded ring `⨁ k, ModularForm 𝒮ℒ k`.

## Implementation notes

The proof has two steps. The map `levelOneCoeAddHom` sends `F : ⨁ k, ModularForm 𝒮ℒ k` to the
function `∑ k, F k : ℍ → ℂ`, which is periodic, holomorphic and bounded at infinity, and whose
`q`-expansion is `qExpansionAlgHom F`. Hence `qExpansionAlgHom F = 0` gives `∑ k, F k = 0`.

It remains to see that modular forms of distinct weights are linearly independent, i.e. that
`levelOneCoeAddHom` is injective. Fixing `z`, the slash equations say that `∑ k, F k` evaluated at
`γ • z` is the polynomial `∑ k, (F k z) • X ^ k` evaluated at `denom γ z`. Taking
`γ = !![0, -1; 1, n]`, whose `denom` at `z` is `z + n`, exhibits infinitely many roots of that
polynomial, so all its coefficients `F k z` vanish.
-/

noncomputable section

open UpperHalfPlane MatrixGroups CongruenceSubgroup DirectSum Polynomial Set

open scoped Manifold MatrixGroups Polynomial PowerSeries

namespace ModularForm

variable {k : ℤ}

def levelOneCoeAddHom : (⨁ k, ModularForm 𝒮ℒ k) →+ (ℍ → ℂ) :=
  toAddMonoid fun _ ↦
    { toFun := fun f ↦ f
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

@[simp]
theorem levelOneCoeAddHom_of (k) (f : ModularForm 𝒮ℒ k) :
    levelOneCoeAddHom (of _ k f) = f := by
  simp [levelOneCoeAddHom]

theorem levelOneCoeAddHom_periodic (F : ⨁ k, ModularForm 𝒮ℒ k) :
    Function.Periodic (levelOneCoeAddHom F ∘ ofComplex) 1 := by
  induction F using DirectSum.induction_on with
  | zero => simp [levelOneCoeAddHom, Function.Periodic]
  | of k f =>
      simpa using (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
  | add F G hF hG =>
      intro z
      simpa using congrArg₂ (· + ·) (hF z) (hG z)

theorem levelOneCoeAddHom_holo (F : ⨁ k, ModularForm 𝒮ℒ k) :
    MDiff (levelOneCoeAddHom F) := by
  induction F using DirectSum.induction_on with
  | zero => exact mdifferentiable_const
  | of k f => simpa using ModularFormClass.holo f
  | add F G hF hG => simpa using hF.add hG

theorem levelOneCoeAddHom_bdd (F : ⨁ k, ModularForm 𝒮ℒ k) :
    IsBoundedAtImInfty (levelOneCoeAddHom F) := by
  induction F using DirectSum.induction_on with
  | zero => exact Asymptotics.isBigO_zero _ atImInfty
  | of k f => simpa using ModularFormClass.bdd_at_infty f
  | add F G hF hG => exact map_add levelOneCoeAddHom F G ▸ hF.add hG

theorem levelOneCoeAddHom_analyticAt (F : ⨁ k, ModularForm 𝒮ℒ k) :
    AnalyticAt ℂ (cuspFunction 1 (levelOneCoeAddHom F)) 0 :=
  analyticAt_cuspFunction_zero one_pos (levelOneCoeAddHom_periodic F) (levelOneCoeAddHom_holo F)
    (levelOneCoeAddHom_bdd F)

theorem qExpansion_levelOneCoeAddHom (F : ⨁ k, ModularForm 𝒮ℒ k) :
    qExpansion 1 (levelOneCoeAddHom F) =
      qExpansionAlgHom 1 one_pos one_mem_strictPeriods_SL F := by
  induction F using DirectSum.induction_on with
  | zero => exact qExpansion_zero 1
  | of k f => simp
  | add F G hF hG =>
      rw [map_add, map_add, qExpansion_add (levelOneCoeAddHom_analyticAt F)
        (levelOneCoeAddHom_analyticAt G), hF, hG]

def levelOneWeightPolynomial (z : ℍ) : (⨁ k, ModularForm 𝒮ℒ k) →+ ℂ[X] :=
  toAddMonoid fun k ↦ if hk : 0 ≤ k then
    { toFun := fun f ↦ Polynomial.monomial k.toNat (f z)
      map_zero' := by simp
      map_add' := by simp }
  else 0

theorem levelOneWeightPolynomial_eval (F : ⨁ k, ModularForm 𝒮ℒ k) (z : ℍ) (γ : SL(2, ℤ)) :
    (levelOneWeightPolynomial z F).eval (denom γ z) = levelOneCoeAddHom F (γ • z) := by
  induction F using DirectSum.induction_on with
  | zero => simp
  | of k f =>
      by_cases hk : 0 ≤ k
      · let : SlashInvariantFormClass (ModularForm 𝒮ℒ k) Γ(1) k :=
          Gamma_one_coe_eq_SL ▸ inferInstance
        have hf := SlashInvariantForm.slash_action_eqn_SL'' f (mem_Gamma_one γ) z
        have hp : (denom γ z) ^ k = (denom γ z) ^ k.toNat := by
          rw [← zpow_natCast, Int.toNat_of_nonneg hk]
        rw [hp] at hf
        simpa [levelOneWeightPolynomial, hk, Polynomial.eval_monomial, mul_comm] using hf.symm
      · have hf : f = 0 := (coe_eq_zero_iff f).mp
          (ModularFormClass.levelOne_neg_weight_eq_zero (lt_of_not_ge hk) f)
        simp [levelOneWeightPolynomial, hf]
  | add F G hF hG => simpa using congrArg₂ (· + ·) hF hG

theorem levelOneWeightPolynomial_coeff (F : ⨁ k, ModularForm 𝒮ℒ k) (z : ℍ) (hk : 0 ≤ k) :
    (levelOneWeightPolynomial z F).coeff k.toNat = F k z := by
  induction F using DirectSum.induction_on with
  | zero => simp
  | of j f =>
      rcases eq_or_ne j k with rfl | hjk
      · simp [levelOneWeightPolynomial, hk]
      · rw [of_eq_of_ne j k f (fun h ↦ hjk h.symm)]
        by_cases hj : 0 ≤ j
        · have hnat : j.toNat ≠ k.toNat := by lia
          simp [levelOneWeightPolynomial, hj, Polynomial.coeff_monomial, hnat]
        · simp [levelOneWeightPolynomial, hj]
  | add F G hF hG => simpa using congrArg₂ (· + ·) hF hG

/-- The matrix `!![0, -1; 1, n] ∈ SL(2, ℤ)`, whose `denom` at `z` is `z + n`. -/
def levelOneShift (n : ℕ) : SL(2, ℤ) := ⟨!![0, -1; 1, n], by simp [Matrix.det_fin_two]⟩

theorem denom_levelOneShift (n : ℕ) (z : ℍ) : denom (levelOneShift n) z = (z : ℂ) + n := by
  rw [ModularGroup.denom_apply]
  simp [levelOneShift]

theorem levelOneCoeAddHom_injective : Function.Injective levelOneCoeAddHom := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  refine DirectSum.ext fun k ↦ ?_
  by_cases hk : 0 ≤ k
  · refine ext fun z ↦ ?_
    have hpoly : levelOneWeightPolynomial z F = 0 :=
      Polynomial.eq_zero_of_infinite_isRoot _ <| Set.infinite_of_injective_forall_mem
        (f := fun n : ℕ ↦ (z : ℂ) + n) (fun n m hnm ↦ by exact_mod_cast add_left_cancel hnm)
        fun n ↦ by
          simpa [IsRoot, ← denom_levelOneShift n z, levelOneWeightPolynomial_eval] using
            congrFun hF (levelOneShift n • z)
    simpa [hpoly] using (levelOneWeightPolynomial_coeff F z hk).symm
  · exact (coe_eq_zero_iff (F k)).mp
      (ModularFormClass.levelOne_neg_weight_eq_zero (lt_of_not_ge hk) (F k))

/-- The `q`-expansion homomorphism on the graded ring of level-one modular forms is injective. -/
public theorem levelOne_qExpansionAlgHom_injective : Function.Injective
    (qExpansionAlgHom 1 one_pos one_mem_strictPeriods_SL) := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  refine levelOneCoeAddHom_injective (map_zero levelOneCoeAddHom ▸ ?_)
  refine (qExpansion_eq_zero_iff one_pos (levelOneCoeAddHom_periodic F)
    (levelOneCoeAddHom_holo F) (levelOneCoeAddHom_bdd F)).mp ?_
  rw [qExpansion_levelOneCoeAddHom, hF]

end ModularForm
