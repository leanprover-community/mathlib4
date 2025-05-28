import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

import Mathlib.Sandbox
import Mathlib.RB

section rootsOfUnityEquivQuot

open Ideal NumberField

variable {K : Type*} [Field K] (I : Ideal (𝓞 K))

variable (n : ℕ)

def Ideal.rootsOfUnityMapQuot : (rootsOfUnity n (𝓞 K)) →* ((𝓞 K) ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).restrict (rootsOfUnity n (𝓞 K))

@[simp]
theorem Ideal.rootsOfUnityMapQuot_apply {x : (𝓞 K)ˣ} (hx : x ∈ rootsOfUnity n (𝓞 K)) :
    rootsOfUnityMapQuot I n ⟨x, hx⟩ = Ideal.Quotient.mk I x := rfl

variable {I n} [NumberField K]

theorem Ideal.rootsOfUnityMapQuot_injective [NeZero n] (hI₁ : absNorm I ≠ 1)
    (hI₂ : (absNorm I).Coprime n) :
    Function.Injective (rootsOfUnityMapQuot I n) := by
  refine (injective_iff_map_eq_one _).mpr fun ζ h ↦ ?_
  obtain ⟨t, ht₀, ht, hζ⟩ := isPrimitiveRoot_of_mem_rootsOfUnity ζ.prop
  by_cases ht' : 2 ≤ t
  · rw [Units.ext_iff, rootsOfUnityMapQuot_apply, Units.val_one] at h
    rw [show 1 = Ideal.Quotient.mk I 1 by rfl] at h
    rw [Ideal.Quotient.eq] at h
    have h₁ := Ideal.absNorm_dvd_norm_of_mem h
    obtain ⟨p, hp, h₂⟩ := Nat.exists_prime_and_dvd hI₁
    have h₃ : (p : ℤ) ∣ (Algebra.norm ℤ) ((ζ.val : 𝓞 K) - 1) := by
      rw [← Int.natCast_dvd_natCast] at h₂
      exact Int.dvd_trans h₂ h₁
    have : Fact (Nat.Prime p) := { out := hp }
    have h₄ := IsPrimitiveRoot.prime_dvd_of_dvd_norm_sub_one (K := K) ht' (by simpa using hζ) h₃
    have h₅ : p ∣ n := by exact dvd_trans h₄ ht
    have h₆ := Nat.dvd_gcd h₂ h₅
    rw [hI₂] at h₆
    exact (hp.not_dvd_one h₆).elim
  · have : t = 1 := by
      apply le_antisymm
      exact Nat.le_of_lt_succ (not_le.mp ht')
      exact Nat.one_le_iff_ne_zero.mpr ht₀
    simpa [this] using hζ

theorem IsPrimitiveRoot.dvd_absNorm_sub_one [NeZero n] {ζ : (𝓞 K)} (hζ : IsPrimitiveRoot ζ n)
    {P : Ideal (𝓞 K)} (hP₀ : P ≠ ⊥) (hP₁ : P.IsPrime) (hP₂ : (absNorm P).Coprime n) :
    ↑n ∣ absNorm P - 1 := by
  have hP₃ : absNorm P ≠ 1 := by
    rw [ne_eq, absNorm_eq_one_iff]
    exact IsPrime.ne_top hP₁
  have := Ideal.rootsOfUnityMapQuot_injective hP₃ hP₂
  have h := Subgroup.card_dvd_of_injective _ this
  rw [Nat.card_eq_fintype_card, hζ.card_rootsOfUnity] at h
  have : P.IsMaximal := by
    apply Ring.DimensionLEOne.maximalOfPrime
    exact hP₀
    exact hP₁
  letI := Ideal.Quotient.field P
  rw [Nat.card_units] at h
  exact h

noncomputable def Ideal.rootsOfUnityEquivQuot [NeZero n] {ζ : (𝓞 K)} (hζ : IsPrimitiveRoot ζ n)
    (hI₀ : I ≠ ⊥) (hI₁ : absNorm I ≠ 1) (hI₂ : (absNorm I).Coprime n)
    (hI₃ : Nat.card (𝓞 K ⧸ I)ˣ = n) :
    (rootsOfUnity n (𝓞 K)) ≃* ((𝓞 K) ⧸ I)ˣ := by
  refine MulEquiv.ofBijective (rootsOfUnityMapQuot  I _) ?_
  have : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI₀
  have : Fintype (𝓞 K ⧸ I)ˣ := Fintype.ofFinite (𝓞 K ⧸ I)ˣ
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨rootsOfUnityMapQuot_injective hI₁ hI₂, ?_⟩
  · have := IsPrimitiveRoot.card_rootsOfUnity hζ
    rw [this, ← hI₃, Nat.card_eq_fintype_card]

@[simp]
theorem Ideal.rootsOfUnityEquivQuot_apply [NeZero n] {ζ : (𝓞 K)} (hζ : IsPrimitiveRoot ζ n)
    (hI₀ : I ≠ ⊥) (hI₁ : absNorm I ≠ 1) (hI₂ : (absNorm I).Coprime n)
    (hI₃ : Nat.card (𝓞 K ⧸ I)ˣ = n) (μ : (𝓞 K)ˣ) (hμ : μ ∈ rootsOfUnity n (𝓞 K)) :
    rootsOfUnityEquivQuot hζ hI₀ hI₁ hI₂ hI₃ ⟨μ, hμ⟩ = Ideal.Quotient.mk I μ := rfl

end rootsOfUnityEquivQuot

namespace Stick

open Polynomial Ideal NumberField RingOfIntegers IsCyclotomicExtension

variable (p : ℕ) [hF : Fact (Nat.Prime p)] (f : ℕ) [NeZero f]

attribute [local instance] Ideal.Quotient.field

local instance : NeZero (p ^ f - 1) := sorry

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p ^ f - 1} ℚ K]

theorem inertiaDeg_eq_of_liesOver {P : Ideal (𝓞 K)}
    (hP : P ∈ Ideal.primesOver (span {(p : ℤ)}) (𝓞 K)) :
    inertiaDeg (span {(p : ℤ)}) P = f := by
  have hm {m : ℕ} (hm : m ≠ 0) : 0 < p ^ m - 1 := by
    refine Nat.sub_pos_iff_lt.mpr ?_
    refine Nat.one_lt_pow hm ?_
    apply Nat.Prime.one_lt
    exact hF.out
--  have : NeZero (p ^ f - 1) := sorry -- ⟨(hm hf).ne'⟩
  let ζ := (zeta_spec (p ^ f - 1) ℚ K).toInteger
  have hζ := (zeta_spec (p ^ f - 1) ℚ K).toInteger_isPrimitiveRoot
--  let hζ := (IsCyclotomicExtension.zeta_spec (p ^ f) ℚ K)
  have h₁ : exponent ζ = 1 := by
    rw [exponent_eq_one_iff]
    sorry
    -- rw [← ((zeta_spec (p ^ f - 1) ℚ K).integralPowerBasis).adjoin_gen_eq_top]
    -- rw [IsPrimitiveRoot.integralPowerBasis_gen]
  have h₂ : ¬ p ∣ exponent ζ := by
    rw [h₁, Nat.dvd_one]
    exact Nat.Prime.ne_one hF.out
  obtain ⟨Q, hQ, rfl⟩ := Ideal.exists_mem_monicFactorsMod h₂ hP
  rw [Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' h₂]
  rw [Multiset.mem_toFinset] at hQ
  rw [Polynomial.mem_normalizedFactors_iff
    (map_monic_ne_zero (minpoly.monic ζ.isIntegral))] at hQ
  have : (minpoly ℤ ζ).map (Int.castRingHom (ZMod p)) = cyclotomic (p ^ f - 1) (ZMod p) := by
    have : minpoly ℤ ζ = cyclotomic (p ^ f - 1) ℤ := by
      have := cyclotomic_eq_minpoly (zeta_spec (p ^ f - 1) ℚ K) (NeZero.pos _)
--      rw [PNat.sub_coe, if_pos, PNat.val_ofNat] at this
--      rw [PNat.pow_coe, ← (zeta_spec _ ℚ K).coe_toInteger] at this
      simpa [this] using (minpoly.algebraMap_eq RingOfIntegers.coe_injective ζ).symm
--      rw [one_lt_pow_iff hf]
--      apply Nat.Prime.one_lt
--      exact hF.out
    rw [this, map_cyclotomic_int]
  rw [this] at hQ
  have : (p ^ 1).Coprime (p ^ f - 1) := sorry
  have := foo (K := ZMod p) (p := p) (f := 1) (n := p ^ f - 1) (P := Q) (by simp) this hQ.2.2 hQ.1
    hQ.2.1
  rw [← this]
  sorry
  -- rw [orderOf_eq_iff (Nat.zero_lt_of_ne_zero hf)]
  -- simp_rw [ne_eq, Units.ext_iff, pow_one, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
  -- rw [← Int.cast_natCast, ← Int.cast_natCast, Units.val_one,
  --   show (1 : ZMod (p ^ f - 1)) = (1 : ℤ) by sorry]

  -- simp_rw [← Int.cast_pow]
  -- simp_rw [eq_comm (b := ((1 : ℤ) : ZMod (p ^ f - 1)))]
  -- simp_rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  -- refine ⟨?_, ?_⟩
  -- · rw [Nat.cast_pred, Nat.cast_pow, Int.cast_pow, Int.cast_natCast]
  --   exact Nat.pos_of_neZero (p ^ f)
  -- · intro m hm₁ hm₂ h
  --   rw [Nat.cast_pred] at h
  --   simp at h
  --   have := (Int.le_iff_pos_of_dvd ?_ h).mpr ?_
  --   have t₁ := Nat.pow_lt_pow_right (a := p) sorry hm₁
  --   linarith
  --   sorry
  --   sorry
  --   exact Nat.pos_of_neZero _

noncomputable def teichmullerAt₀ {P : Ideal (𝓞 K)}
  (hP : P ∈ Ideal.primesOver (span {(p : ℤ)}) (𝓞 K)) :
    ((𝓞 K) ⧸ P)ˣ ≃* (rootsOfUnity (p ^ f - 1) (𝓞 K)) := by
  have inst₁ := hP.1
  have inst₂ := hP.2
  have inst₃ := hF.out
  have h₁ : absNorm P = p ^ f := by
    rw [absNorm_eq_pow_inertiaDeg' P hF.out, inertiaDeg_eq_of_liesOver p f hP]
  have h₂ : 1 < p ^ f := Nat.one_lt_pow (NeZero.ne _) (Nat.Prime.one_lt inst₃)
  refine MulEquiv.symm ?_
  apply Ideal.rootsOfUnityEquivQuot
  · exact (zeta_spec (p ^ f - 1) ℚ K).toInteger_isPrimitiveRoot
  · rw [ne_eq, ← absNorm_eq_zero_iff, h₁]
    linarith
  · rw [h₁]
    exact h₂.ne'
  · rw [h₁]
    rw [Nat.coprime_iff]
    refine ⟨1, -1, ?_⟩
    rw [Nat.cast_sub h₂.le]
    norm_num
  · have : IsMaximal P := by
      refine IsPrime.isMaximal inferInstance ?_
      exact Ideal.ne_bot_of_liesOver_of_ne_bot (p := span {(p :ℤ)}) (by simp [NeZero.ne p]) P
    rw [Nat.card_units (𝓞 K ⧸ P), ← h₁]
    rfl



end Stick
