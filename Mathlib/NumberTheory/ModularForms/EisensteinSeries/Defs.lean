/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.RingTheory.EuclideanDomain

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

variable (N r : ℕ) (a : Fin 2 → ZMod N)

section gammaSet_def

/-- The set of pairs of integers congruent to `a` mod `N` and with `gcd` equal to `r`. -/
def gammaSet := {v : Fin 2 → ℤ | (↑) ∘ v = a ∧ (v 0).gcd (v 1) = r}

open scoped Function in -- required for scoped `on` notation
lemma pairwise_disjoint_gammaSet : Pairwise (Disjoint on gammaSet N r) := by
  refine fun u v huv ↦ ?_
  contrapose! huv
  obtain ⟨f, hf⟩ := Set.not_disjoint_iff.mp huv
  exact hf.1.1.symm.trans hf.2.1

/-- For level `N = 1`, the gamma sets are all equal. -/
lemma gammaSet_one_const (a a' : Fin 2 → ZMod 1) : gammaSet 1 r a = gammaSet 1 r a' :=
  congr_arg _ (Subsingleton.elim _ _)

/-- For level `N = 1`, the gamma sets simplify to only a `gcd` condition. -/
lemma gammaSet_one_eq (a : Fin 2 → ZMod 1) :
    gammaSet 1 r a = {v : Fin 2 → ℤ | (v 0).gcd (v 1) = r} := by
  simp [gammaSet, Subsingleton.eq_zero]

lemma gammaSet_one_mem_iff (v : Fin 2 → ℤ) : v ∈ gammaSet 1 r 0 ↔ (v 0).gcd (v 1) = r := by
  simp [gammaSet, Subsingleton.eq_zero]

/-- For level `N = 1`, the gamma sets are all equivalent; this is the equivalence. -/
def gammaSet_one_equiv (a a' : Fin 2 → ZMod 1) : gammaSet 1 r a ≃ gammaSet 1 r a' :=
  Equiv.setCongr (gammaSet_one_const r a a')

/-- The map from `Fin 2 → ℤ` sending `![a,b]` to `a.gcd b`. -/
abbrev finGcdMap (v : Fin 2 → ℤ) : ℕ := (v 0).gcd (v 1)

lemma finGcdMap_div {r : ℕ} [NeZero r] (v : Fin 2 → ℤ) (hv : finGcdMap v = r) :
    IsCoprime ((v / r) 0 ) ((v / r) 1) := by
  rw [← hv]
  apply isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
  have := NeZero.ne r
  aesop

lemma finGcdMap_smul {r : ℕ} (a : ℤ) {v : Fin 2 → ℤ} (hv : finGcdMap v = r) :
    finGcdMap (a • v) = a.natAbs * r := by
  simp [finGcdMap, Int.gcd_mul_left, hv]

/-- An abbreviation of the map which divides a integer vector by an integer. -/
abbrev divIntMap (r : ℤ) {m : ℕ} (v : Fin m → ℤ) : Fin m → ℤ := v / r

lemma mem_gammaSet_one (v : Fin 2 → ℤ) : v ∈ gammaSet 1 1 0 ↔ IsCoprime (v 0) (v 1) := by
  rw [gammaSet_one_mem_iff, Int.isCoprime_iff_gcd_eq_one]

lemma gammaSet_div_gcd {r : ℕ} {v : Fin 2 → ℤ} (hv : v ∈ (gammaSet 1 r 0)) (i : Fin 2) :
   (r : ℤ) ∣ v i := by
  fin_cases i <;> simp [← hv.2, Int.gcd_dvd_left, Int.gcd_dvd_right]

lemma gammaSet_div_gcd_to_gammaSet10_bijection (r : ℕ) [NeZero r] :
    Set.BijOn (divIntMap r) (gammaSet 1 r 0) (gammaSet 1 1 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [divIntMap, mem_gammaSet_one] at *
    exact finGcdMap_div _ hx.2
  · intro x hx v hv hv2
    ext i
    exact (Int.ediv_left_inj (gammaSet_div_gcd hx i) (gammaSet_div_gcd hv i)).mp
      (congr_fun hv2 i)
  · intro x hx
    use r • x
    simp only [nsmul_eq_mul, divIntMap, Int.cast_natCast]
    constructor
    · rw [mem_gammaSet_one, Int.isCoprime_iff_gcd_eq_one] at hx
      exact ⟨Subsingleton.eq_zero _, by simp [Int.gcd_mul_left, hx]⟩
    · ext i
      simp_all [NeZero.ne r]

lemma gammaSet_eq_gcd_mul_divIntMap {r : ℕ} {v : Fin 2 → ℤ} (hv : v ∈ gammaSet 1 r 0) :
    v = r • (divIntMap r v) := by
  by_cases hr : r = 0
  · have hv := hv.2
    simp only [hr, Fin.isValue, Int.gcd_eq_zero_iff, CharP.cast_eq_zero, zero_smul] at *
    ext i
    fin_cases i <;> simp [hv]
  · ext i
    simp_all [Pi.smul_apply, divIntMap, ← Int.mul_ediv_assoc _ (gammaSet_div_gcd hv i)]

/-- The equivalence between `gammaSet 1 r 0` and `gammaSet 1 1 0` for non-zero `r`. -/
def gammaSetDivGcdEquiv (r : ℕ) [NeZero r] : gammaSet 1 r 0 ≃ gammaSet 1 1 0 :=
    Set.BijOn.equiv _ (gammaSet_div_gcd_to_gammaSet10_bijection r)

/-- The equivalence between `(Fin 2 → ℤ)` and `Σ n : ℕ, gammaSet 1 n 0)` . -/
def gammaSetDivGcdSigmaEquiv : (Fin 2 → ℤ) ≃ (Σ r : ℕ, gammaSet 1 r 0) := by
  apply (Equiv.sigmaFiberEquiv finGcdMap).symm.trans
  refine Equiv.sigmaCongrRight fun b => ?_
  apply Equiv.setCongr
  rw [gammaSet_one_eq]
  rfl

@[simp]
lemma gammaSetDivGcdSigmaEquiv_symm_eq (v : Σ r : ℕ, gammaSet 1 r 0) :
    (gammaSetDivGcdSigmaEquiv.symm v) = v.2 := rfl

end gammaSet_def

variable {N a r} [NeZero r]

section gamma_action

/-- Right-multiplying a vector by a matrix in `SL(2, ℤ)` doesn't change its gcd. -/
lemma vecMulSL_gcd {v : Fin 2 → ℤ} (hab : finGcdMap v = r) (A : SL(2, ℤ)) :
    finGcdMap (v ᵥ* A.1) = r := by
  have hvr : v = r • (v / r) := by
    ext i
    refine Eq.symm (Int.mul_ediv_cancel' ?_)
    fin_cases i <;> simp [← hab, Int.gcd_dvd_left, Int.gcd_dvd_right]
  rw [hvr, smul_vecMul]
  simpa using finGcdMap_smul r (Int.isCoprime_iff_gcd_eq_one.mp ((finGcdMap_div v hab).vecMulSL A))

/-- Right-multiplying by `γ ∈ SL(2, ℤ)` sends `gammaSet N a` to `gammaSet N (a ᵥ* γ)`. -/
lemma vecMul_SL2_mem_gammaSet {v : Fin 2 → ℤ} (hv : v ∈ gammaSet N r a)
    (γ : SL(2, ℤ)) : v ᵥ* γ ∈ gammaSet N r (a ᵥ* γ) := by
  refine ⟨?_, vecMulSL_gcd hv.2 γ⟩
  have := RingHom.map_vecMul (m := Fin 2) (n := Fin 2) (Int.castRingHom (ZMod N)) γ v
  simp only [eq_intCast, Int.coe_castRingHom] at this
  simp_rw [Function.comp_def, this, hv.1]
  simp

variable (a) in
/-- The bijection between `GammaSets` given by multiplying by an element of `SL(2, ℤ)`. -/
def gammaSetEquiv (γ : SL(2, ℤ)) : gammaSet N r a ≃ gammaSet N r (a ᵥ* γ) where
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
    replace hc : z * c + d ≠ 0 := by convert hc using 1; ring
    field_simp
    simp [div_zpow]
    ring_nf
  simpa using h (hc := denom_ne_zero A z) ..

end eisSummand

variable (a)

/-- An Eisenstein series of weight `k` and level `Γ(N)`, with congruence condition `a`. -/
def _root_.eisensteinSeries (k : ℤ) (z : ℍ) : ℂ := ∑' x : gammaSet N 1 a, eisSummand k x z

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
