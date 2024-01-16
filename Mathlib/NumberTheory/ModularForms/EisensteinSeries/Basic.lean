/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

noncomputable section

open ModularForm UpperHalfPlane Complex Matrix Classical Nat

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

namespace EisensteinSeries

/--Subtype of functions valued in pars of coprime integers congruent to `a,b`.-/
def gammaSet (N : ℕ) (a b : ℤ ) := {f : (Fin 2) → ℤ | (f 0 : ZMod N) = a ∧ (f 1 : ZMod N) = b ∧
  IsCoprime (f 0) (f 1)}
@[simp]
lemma gammaSet_mem' (N : ℕ) (a b : ℤ ) (f : (Fin 2) → ℤ ) : f ∈ gammaSet N a b ↔
    (f 0 : ZMod N) = a ∧ (f 1 : ZMod N) = b ∧ IsCoprime (f 0) (f 1) := by rfl

lemma gammaSet_mem (N : ℕ) (a b : ℤ ) (f : (Fin 2) → ℤ ) : f ∈ gammaSet N a b ↔
    (f 0 : ZMod N) = a ∧ (f 1 : ZMod N) = b ∧ (f 0).gcd (f 1) = 1 := by
  rw [Int.gcd_eq_one_iff_coprime]
  rfl

lemma gammaSet_mem_iff (N : ℕ) (a b c d : ℤ) (v : (gammaSet N a b)) : v.1 ∈ gammaSet N c d ↔
  (a : ZMod N) = c ∧ (b : ZMod N) = d := by
  simp only [gammaSet_mem', v.2.1, v.2.2.1, v.2.2.2, and_true]

lemma gammaSet_one_eq (a b c d : ℤ ) : gammaSet 1 a b = gammaSet 1 c d := by
  simp [gammaSet, eq_iff_true_of_subsingleton]

/--For level one the gamma sets are all equivalent, this is the equivalence-/
def gammaSet_one_equiv (a b c d : ℤ) : (gammaSet 1 a b) ≃ (gammaSet 1 c d) := by
  refine Equiv.Set.ofEq (gammaSet_one_eq a b c d)

/-- The function on `(Fin 2 → ℤ)` whose sum defines an Eisenstein series.-/
def eise (k : ℤ) (z : ℍ) : (Fin 2 → ℤ) → ℂ := fun x => 1 / (x 0 * z.1 + x 1) ^ k

/--The Moebius transformation defined by a matrix in `SL(2, ℤ)` sending a function (or vector)
  `v` to `A v`-/
def moebiusEquiv (A : SL(2, ℤ)) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) :=
  (Matrix.SpecialLinearGroup.toLin' (A.transpose))

theorem moebius_aux_lem (k : ℤ) (a b c d i1 i2 : ℂ) (z : ℍ) (h : c * z + d ≠ 0) :
    ((i1 * ((a * z + b) / (c * z + d)) + i2) ^ k)⁻¹ =
      (c * z + d) ^ k * (((i1 * a + i2 * c ) * z + ( i1 * b + i2 * d)) ^ k)⁻¹ := by
  have h1 : i1 * ((a * z + b) / (c * z + d)) + i2 = i1 * (a * z + b) / (c * z + d) + i2 := by ring;
  have h2 : i1 * (a * z + b) / (c * z + d) + i2 = i1 * (a * z + b) / (c * z + d) + i2 := by ring;
  have h3 := div_add' (i1 * (a * z + b)) i2 (c * z + d) h
  rw [h1,h2,h3, div_eq_inv_mul, mul_comm]
  ring_nf
  field_simp

-- How the Eise function changes under the Moebius action
theorem eise_Moebius (k : ℤ) (z : ℍ) (A : SL(2, ℤ)) (i : (Fin 2 → ℤ)) :
    eise k (A • z) i =
      (A.1 1 0 * z.1 + A.1 1 1) ^ k * eise k z (moebiusEquiv A i) :=
  by
  simp only [eise, specialLinearGroup_apply, algebraMap_int_eq, eq_intCast, ofReal_int_cast,
    one_div, moebiusEquiv, Matrix.SpecialLinearGroup.transpose, EquivLike.coe_coe,
    Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply', Matrix.mulVecLin_transpose,
    Matrix.vecMulLinear_apply, Matrix.vecMul, Matrix.vec2_dotProduct, Int.cast_add, Int.cast_mul]
  apply moebius_aux_lem k (A 0 0) (A 0 1) (A 1 0) (A 1 1) (i 0) (i 1) z ?_
  apply UpperHalfPlane.denom_ne_zero A

/--The permutation of a gammaSet given by multiplying by an element `Γ(N)` -/
def gammaMoebiusFun (N : ℕ) (a b : ℤ) (γ : Gamma N) (f : gammaSet N a b) : (gammaSet N a b) := by
  use Matrix.vecMul f.1 γ.1.1
  simp only [gammaSet_mem', Matrix.vecMul, Matrix.vec2_dotProduct, Int.cast_add, Int.cast_mul]
  have hγ := (Gamma_mem N _).1 γ.2
  rw [hγ.1, hγ.2.2.1, hγ.2.2.2, hγ.2.1, f.2.1, f.2.2.1]
  simp only [mul_one, mul_zero, add_zero, zero_add, true_and]
  have := Matrix.SpecialLinearGroup.SL2_gcd (f.1 0) (f.1 1) f.2.2.2 γ
  convert this
  repeat{
  simp_rw [Matrix.vecMul, Matrix.dotProduct, Matrix.vecCons]
  simp only [Fin.sum_univ_two, Fin.cons_zero, Fin.cons_one]}

lemma gammaMoebiusFun_eq_Moebequiv (N : ℕ) (a b : ℤ) (γ : Gamma N) (f : gammaSet N a b) :
    (gammaMoebiusFun N a b γ f).1 = (moebiusEquiv γ.1 f.1) := by
  simp only [gammaMoebiusFun, moebiusEquiv, Matrix.SpecialLinearGroup.transpose, EquivLike.coe_coe,
    Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply', Matrix.mulVecLin_transpose,
    Matrix.vecMulLinear_apply]

lemma gamma_left_inv (N : ℕ) (a b : ℤ ) (γ : Gamma N) (v : gammaSet N a b) :
    gammaMoebiusFun N a b γ⁻¹ (gammaMoebiusFun N a b γ v) = v := by
  simp_rw [gammaMoebiusFun, Matrix.vecMul_vecMul]
  apply Subtype.ext
  simp only [InvMemClass.coe_inv, SpecialLinearGroup.coe_inv, mul_adjugate,
    SpecialLinearGroup.det_coe, one_smul, vecMul_one]


lemma gamma_right_inv (N : ℕ) (a b : ℤ ) (γ : Gamma N) (v : gammaSet N a b) :
  gammaMoebiusFun N a b γ (gammaMoebiusFun N a b γ⁻¹ v) = v := by
  simp only [gammaMoebiusFun, InvMemClass.coe_inv, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.vecMul_vecMul]
  apply Subtype.ext
  simp only [adjugate_mul, SpecialLinearGroup.det_coe, one_smul, vecMul_one]

/--The equivalence of gammaSets given by an element of `Γ(N)`-/
def gammaMoebiusEquiv (N : ℕ) (a b : ℤ ) (γ : Gamma N) : (gammaSet N a b) ≃ (gammaSet N a b)
    where
  toFun := gammaMoebiusFun N a b γ
  invFun := gammaMoebiusFun N a b γ⁻¹
  left_inv v:= by
    apply gamma_left_inv
  right_inv v:= by
    apply gamma_right_inv

/-- The Eisenstein series of weight `k : ℤ` and level `Γ(N)`, for `N : ℕ`. -/
def EisensteinLevelNtsum (k : ℤ) (N : ℕ) (a b : ℤ) : ℍ → ℂ := fun z => ∑' x : (gammaSet N a b),
  (eise k z x)

/-- The SlashInvariantForm defined by an Eisenstein series of weight `k : ℤ`, level `Γ(N)`,
  and congruence condition given by `a b : ℤ`. -/
def eisensteinLevelNSIF (N : ℕ) (k a b : ℤ) : SlashInvariantForm (Gamma N) k
    where
  toFun := EisensteinLevelNtsum k N a b
  slash_action_eq' := by
    intro A
    ext1 x
    simp_rw [slash_action_eq'_iff, EisensteinLevelNtsum, UpperHalfPlane.subgroup_to_sl_moeb,
      UpperHalfPlane.sl_moeb, ← (Equiv.tsum_eq (gammaMoebiusEquiv N a b A) (fun v => eise k x v)),
      ← tsum_mul_left]
    apply tsum_congr
    intro v
    have := eise_Moebius k x A v
    simp only [sl_moeb] at this
    rw [this]
    congr
    symm
    apply gammaMoebiusFun_eq_Moebequiv
