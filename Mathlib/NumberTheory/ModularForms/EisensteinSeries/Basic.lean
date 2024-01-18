/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Eisenstein Series

## Main definitions

* We define Eisenstein series of level `Γ(N)` for any `N : ℕ` and weight `k : ℤ` as the infinite sum
  `∑' v : (Fin 2 → ℤ), (1 / (v 0 * z + v 1) ^ k)`, where `z : ℍ` and `v` ranges over all pairs of
  coprime integers congruent to a fixed pair `(a, b)` modulo `N`.
* We show that they define a slash invariant form of level `Γ(N)` and weight `k`.

## References
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005]
-/

noncomputable section

open ModularForm UpperHalfPlane Complex Matrix

open scoped MatrixGroups

namespace EisensteinSeries

variable (N : ℕ) (a : Fin 2 → ZMod N)

section gammaSet_def

/-- The set of pairs of coprime integers congruent to `a` mod `N`. -/
def gammaSet := {v : Fin 2 → ℤ | (↑·) ∘ v = a ∧ IsCoprime (v 0) (v 1)}

lemma pairwise_disjoint_gammaSet : Pairwise (Disjoint on gammaSet N) := by
  refine fun u v huv ↦ ?_
  contrapose! huv
  obtain ⟨f, hf⟩ := Set.not_disjoint_iff.mp huv
  exact hf.1.1.symm.trans hf.2.1

/-- For level `N = 1`, the gamma sets are all equal. -/
lemma gammaSet_one_eq (a a' : Fin 2 → ZMod 1) : gammaSet 1 a = gammaSet 1 a' :=
  congr_arg _ (Subsingleton.elim _ _)

/-- For level `N = 1`, the gamma sets are all equivalent; this is the equivalence -/
def gammaSet_one_equiv (a a' : Fin 2 → ZMod 1) : gammaSet 1 a ≃ gammaSet 1 a' :=
  Equiv.Set.ofEq (gammaSet_one_eq a a')

end gammaSet_def

variable {N a}

section gamma_action

/-- Right-multiplying by `γ ∈ SL(2, ℤ)` sends `gammaSet N a` to `gammaSet N (vecMul a γ)`. -/
lemma vecMul_SL2_mem_gammaSet {v : Fin 2 → ℤ} (hv : v ∈ gammaSet N a) (γ : SL(2, ℤ)) :
    vecMul v γ ∈ gammaSet N (vecMul a γ) := by
  refine ⟨?_, γ.SL2_gcd hv.2⟩
  have := RingHom.map_vecMul (m := Fin 2) (n := Fin 2) (Int.castRingHom (ZMod N)) γ v
  simp only [eq_intCast, Int.coe_castRingHom] at this
  simp_rw [Function.comp, this, hv.1]
  rfl

variable (a) in
/-- The bijection between `GammaSets` given by multiplying by an element of `SL(2, ℤ)` -/
def gammaSetEquiv (γ : SL(2, ℤ)) : gammaSet N a ≃ gammaSet N (vecMul a γ) where
  toFun := fun v ↦ ⟨vecMul v.1 γ, vecMul_SL2_mem_gammaSet v.2 γ⟩
  invFun := fun v ↦ ⟨vecMul v.1 ↑(γ⁻¹), by
      have := vecMul_SL2_mem_gammaSet v.2 γ⁻¹
      rw [vecMul_vecMul, ← SpecialLinearGroup.coe_mul] at this
      simpa only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
        map_inv, mul_right_inv, SpecialLinearGroup.coe_one, vecMul_one]⟩
  left_inv v := by simp_rw [vecMul_vecMul, ← SpecialLinearGroup.coe_mul, mul_inv_self,
    SpecialLinearGroup.coe_one, vecMul_one]
  right_inv v := by simp_rw [vecMul_vecMul, ← SpecialLinearGroup.coe_mul, inv_mul_self,
    SpecialLinearGroup.coe_one, vecMul_one]

end gamma_action

section eis_summand

/-- The function on `(Fin 2 → ℤ)` whose sum defines an Eisenstein series.-/
def eis_summand (k : ℤ) (v : Fin 2 → ℤ) (z : ℍ) : ℂ := 1 / (v 0 * z.1 + v 1) ^ k

/-- How the `eis_summand` function changes under the Moebius action -/
theorem eis_summand_SL2_apply (k : ℤ) (i : (Fin 2 → ℤ)) (A : SL(2, ℤ)) (z : ℍ) :
    eis_summand k i (A • z) = (z.denom A) ^ k * eis_summand k (vecMul i A) z := by
  simp only [eis_summand, specialLinearGroup_apply, algebraMap_int_eq, eq_intCast, ofReal_int_cast,
    one_div, vecMul, vec2_dotProduct, Int.cast_add, Int.cast_mul]
  have h (a b c d u v : ℂ) (hc : c * z + d ≠ 0) : ((u * ((a * z + b) / (c * z + d)) + v) ^ k)⁻¹ =
      (c * z + d) ^ k * (((u * a + v * c) * z + (u * b + v * d)) ^ k)⁻¹
  · field_simp [hc]
    ring_nf
  apply h (hc := z.denom_ne_zero A)

end eis_summand

variable (a)

/-- An Eisenstein series of weight `k` and level `Γ(N)`, with congruence condition `a`. -/
def eisenstein_series (k : ℤ) (z : ℍ) : ℂ := ∑' x : gammaSet N a, eis_summand k x z

lemma eisenstein_slash_apply (k : ℤ) (γ : SL(2, ℤ)) :
    eisenstein_series a k ∣[k] γ = eisenstein_series (vecMul a γ) k := by
  ext1 z
  simp_rw [SL_slash, slash_def, slash, det_coe', ofReal_one, one_zpow, mul_one, zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| z.denom_ne_zero _), mul_comm,
    eisenstein_series, ← UpperHalfPlane.sl_moeb, eis_summand_SL2_apply, tsum_mul_left]
  erw [(gammaSetEquiv a γ).tsum_eq (eis_summand k · z)]

/-- The SlashInvariantForm defined by an Eisenstein series of weight `k : ℤ`, level `Γ(N)`,
  and congruence condition given by `a : Fin 2 → ZMod N`. -/
def eisenstein_series_SIF (k : ℤ) : SlashInvariantForm (Gamma N) k where
  toFun := eisenstein_series a k
  slash_action_eq' A := by rw [subgroup_slash, ← SL_slash, eisenstein_slash_apply,
      (Gamma_mem' N A).mp A.2, SpecialLinearGroup.coe_one, vecMul_one]
