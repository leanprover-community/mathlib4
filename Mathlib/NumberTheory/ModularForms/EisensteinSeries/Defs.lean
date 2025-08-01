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
  coprime integers congruent to a fixed pair `(a, b)` modulo `N`. Note that by using `(Fin 2 → ℤ)`
  instead of `ℤ × ℤ` we can state all of the required equivalences using matrices and vectors, which
  makes working with them more convenient.

* We show that they define a slash invariant form of level `Γ(N)` and weight `k`.

## References
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005]
-/

noncomputable section

open ModularForm UpperHalfPlane Complex Matrix CongruenceSubgroup Set

open scoped MatrixGroups

namespace EisensteinSeries

variable (N : ℕ) (a : Fin 2 → ZMod N)

section gammaSet_def

/-- The set of pairs of coprime integers congruent to `a` mod `N`. -/
def gammaSet := {v : Fin 2 → ℤ | (↑) ∘ v = a ∧ IsCoprime (v 0) (v 1)}

open scoped Function in -- required for scoped `on` notation
lemma pairwise_disjoint_gammaSet : Pairwise (Disjoint on gammaSet N) := by
  refine fun u v huv ↦ ?_
  contrapose! huv
  obtain ⟨f, hf⟩ := Set.not_disjoint_iff.mp huv
  exact hf.1.1.symm.trans hf.2.1

/-- For level `N = 1`, the gamma sets are all equal. -/
lemma gammaSet_one_eq (a a' : Fin 2 → ZMod 1) : gammaSet 1 a = gammaSet 1 a' :=
  congr_arg _ (Subsingleton.elim _ _)

/-- For level `N = 1`, the gamma sets are all equivalent; this is the equivalence. -/
def gammaSet_one_equiv (a a' : Fin 2 → ZMod 1) : gammaSet 1 a ≃ gammaSet 1 a' :=
  Equiv.setCongr (gammaSet_one_eq a a')

open Pointwise
def gammaSetN (N : ℕ) : Set (Fin 2 → ℤ) := ({N} : Set ℕ) • gammaSet 1 0

noncomputable def gammaSetN_map (N : ℕ) (v : gammaSetN N) : gammaSet 1 0 := by
  have hv2 := v.2
  simp only [gammaSetN, singleton_smul, mem_smul_set, nsmul_eq_mul] at hv2
  refine ⟨hv2.choose, hv2.choose_spec.1⟩

lemma gammaSet_top_mem (v : Fin 2 → ℤ) : v ∈ gammaSet 1 0 ↔ IsCoprime (v 0) (v 1) := by
  simpa [gammaSet] using fun h ↦ Subsingleton.eq_zero (Int.cast ∘ v)

lemma gammaSetN_map_eq {N : ℕ} (v : gammaSetN N) : v.1 = N • gammaSetN_map N v := by
  have hv2 := v.2
  simp only [gammaSetN, singleton_smul, mem_smul_set, nsmul_eq_mul] at hv2
  exact (hv2.choose_spec.2).symm

noncomputable def gammaSetN_Equiv {N : ℕ} (hN : N ≠ 0) : gammaSetN N ≃ gammaSet 1 0 where
  toFun v := gammaSetN_map N v
  invFun v := by
    use N • v
    simp only [gammaSetN, singleton_smul, nsmul_eq_mul, mem_smul_set]
    refine ⟨v, by simp⟩
  left_inv v := by
    simp_rw [← gammaSetN_map_eq v]
  right_inv v := by
    have H : N • v.1 ∈ gammaSetN N := by
      simp only [gammaSetN, singleton_smul, nsmul_eq_mul, mem_smul_set]
      refine ⟨v.1, by simp⟩
    simp [gammaSetN, mem_smul_set] at *
    let x := H.choose
    have hx := H.choose_spec
    have hxv : ⟨H.choose, H.choose_spec.1⟩ = v := by
      ext i
      simpa [hN] using (congr_fun H.choose_spec.2 i)
    simp_all only [gammaSetN_map]

private def fin_to_GammaSetN (v : Fin 2 → ℤ) : Σ n : ℕ, gammaSetN n := by
  refine ⟨(v 0).gcd (v 1), ⟨(v 0).gcd (v 1) • ![(v 0)/(v 0).gcd (v 1), (v 1)/(v 0).gcd (v 1)], ?_⟩⟩
  by_cases hn : 0 < (v 0).gcd (v 1)
  · apply Set.smul_mem_smul (by aesop)
    rw [gammaSet_top_mem, Int.isCoprime_iff_gcd_eq_one]
    apply Int.gcd_div_gcd_div_gcd hn
  · simp only [gammaSetN, Fin.isValue, (nonpos_iff_eq_zero.mp (not_lt.mp hn)), singleton_smul,
    Nat.succ_eq_add_one, Nat.reduceAdd, CharP.cast_eq_zero, zero_nsmul]
    refine ⟨![1,1], by simpa [gammaSet_top_mem] using Int.isCoprime_iff_gcd_eq_one.mpr rfl⟩

def GammaSet_one_Equiv : (Fin 2 → ℤ) ≃ (Σ n : ℕ, gammaSetN n) where
  toFun v := fin_to_GammaSetN v
  invFun v := v.2
  left_inv v := by
            ext i
            fin_cases i
            · exact Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)
            · exact Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)
  right_inv v := by
          ext i
          · have hv2 := v.2.2
            simp only [gammaSetN, singleton_smul, mem_smul_set, nsmul_eq_mul] at hv2
            obtain ⟨x, hx⟩ := hv2
            simp [← hx.2, fin_to_GammaSetN, Fin.isValue, Int.gcd_mul_left,
              Int.isCoprime_iff_gcd_eq_one.mp hx.1.2]
          · fin_cases i
            · exact Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)
            · exact Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)


end gammaSet_def

variable {N a}

section gamma_action

/-- Right-multiplying by `γ ∈ SL(2, ℤ)` sends `gammaSet N a` to `gammaSet N (a ᵥ* γ)`. -/
lemma vecMul_SL2_mem_gammaSet {v : Fin 2 → ℤ} (hv : v ∈ gammaSet N a) (γ : SL(2, ℤ)) :
    v ᵥ* γ ∈ gammaSet N (a ᵥ* γ) := by
  refine ⟨?_, hv.2.vecMulSL γ⟩
  have := RingHom.map_vecMul (m := Fin 2) (n := Fin 2) (Int.castRingHom (ZMod N)) γ v
  simp only [eq_intCast, Int.coe_castRingHom] at this
  simp_rw [Function.comp_def, this, hv.1]
  simp

variable (a) in
/-- The bijection between `GammaSets` given by multiplying by an element of `SL(2, ℤ)`. -/
def gammaSetEquiv (γ : SL(2, ℤ)) : gammaSet N a ≃ gammaSet N (a ᵥ* γ) where
  toFun v := ⟨v.1 ᵥ* γ, vecMul_SL2_mem_gammaSet v.2 γ⟩
  invFun v := ⟨v.1 ᵥ* ↑(γ⁻¹), by
      have := vecMul_SL2_mem_gammaSet v.2 γ⁻¹
      rw [vecMul_vecMul, ← SpecialLinearGroup.coe_mul] at this
      simpa only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
        map_inv, mul_inv_cancel, SpecialLinearGroup.coe_one, vecMul_one]⟩
  left_inv v := by simp_rw [vecMul_vecMul, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
    SpecialLinearGroup.coe_one, vecMul_one]
  right_inv v := by simp_rw [vecMul_vecMul, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
    SpecialLinearGroup.coe_one, vecMul_one]

end gamma_action

section eisSummand

/-- The function on `(Fin 2 → ℤ)` whose sum defines an Eisenstein series. -/
def eisSummand (k : ℤ) (v : Fin 2 → ℤ) (z : ℍ) : ℂ := (v 0 * z + v 1) ^ (-k)

/-- How the `eisSummand` function changes under the Moebius action. -/
theorem eisSummand_SL2_apply (k : ℤ) (i : (Fin 2 → ℤ)) (A : SL(2, ℤ)) (z : ℍ) :
    eisSummand k i (A • z) = (denom A z) ^ k * eisSummand k (i ᵥ* A) z := by
  simp only [eisSummand, vecMul, vec2_dotProduct, denom, UpperHalfPlane.specialLinearGroup_apply]
  have h (a b c d u v : ℂ) (hc : c * z + d ≠ 0) : (u * ((a * z + b) / (c * z + d)) + v) ^ (-k) =
      (c * z + d) ^ k * ((u * a + v * c) * z + (u * b + v * d)) ^ (-k) := by
    field_simp [hc]
    ring_nf
  simpa using h (hc := denom_ne_zero A z) ..

end eisSummand

variable (a)

/-- An Eisenstein series of weight `k` and level `Γ(N)`, with congruence condition `a`. -/
def _root_.eisensteinSeries (k : ℤ) (z : ℍ) : ℂ := ∑' x : gammaSet N a, eisSummand k x z

lemma eisensteinSeries_slash_apply (k : ℤ) (γ : SL(2, ℤ)) :
    eisensteinSeries a k ∣[k] γ = eisensteinSeries (a ᵥ* γ) k := by
  ext1 z
  simp_rw [SL_slash_apply, zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z),
    eisensteinSeries, eisSummand_SL2_apply, tsum_mul_left, mul_comm (_ ^ k)]
  congr 1
  exact (gammaSetEquiv a γ).tsum_eq (eisSummand k · z)

/-- The SlashInvariantForm defined by an Eisenstein series of weight `k : ℤ`, level `Γ(N)`,
  and congruence condition given by `a : Fin 2 → ZMod N`. -/
def eisensteinSeries_SIF (k : ℤ) : SlashInvariantForm (Gamma N) k where
  toFun := eisensteinSeries a k
  slash_action_eq' A hA := by simp only [eisensteinSeries_slash_apply, Gamma_mem'.mp hA,
    SpecialLinearGroup.coe_one, vecMul_one]

lemma eisensteinSeries_SIF_apply (k : ℤ) (z : ℍ) :
    eisensteinSeries_SIF a k z = eisensteinSeries a k z := rfl

end EisensteinSeries
