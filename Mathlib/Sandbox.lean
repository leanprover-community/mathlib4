import Mathlib

namespace relNorm

open Ideal

attribute [local instance] FractionRing.liftAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [NoZeroSMulDivisors R S] [Module.Finite R S]
  [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
  (P : Ideal S) (p : Ideal R) [hPp : P.LiesOver p]

lemma exists_relNorm_eq_pow_of_liesOver [p.IsPrime] : ∃ s, relNorm R P = p ^ s := by
  by_cases hp : p = ⊥
  · use 1
    rw [hp] at hPp ⊢
    rw [eq_bot_of_liesOver_bot R P, relNorm_bot, bot_pow (one_ne_zero)]
  have h : relNorm R (map (algebraMap R S) p) ≤ relNorm R P :=
    relNorm_mono _ <| map_le_iff_le_comap.mpr <| le_of_eq <| (liesOver_iff _ _).mp hPp
  rw [relNorm_algebraMap S, ← dvd_iff_le, dvd_prime_pow (prime_of_isPrime hp inferInstance)] at h
  obtain ⟨s, _, hs⟩ := h
  exact ⟨s, by rwa [associated_iff_eq] at hs⟩

lemma res2 [p.IsMaximal] [P.IsPrime] [IsGalois (FractionRing R) (FractionRing S)] :
    relNorm R P = p ^ p.inertiaDeg P := by
  by_cases hp : p = ⊥
  · have h : p.inertiaDeg P ≠ 0 :=  by
      rw [Nat.ne_zero_iff_zero_lt]
      exact Ideal.inertiaDeg_pos p P
    have hP : P = ⊥ := by
      rw [hp] at hPp
      exact eq_bot_of_liesOver_bot R P
    rw [hp, hP, relNorm_bot, bot_pow]
    rwa [hp, hP] at h
  have t₁ := congr_arg (relNorm R ·) <| Ideal.map_algebraMap_eq_finset_prod_pow S hp
  have t₂ := relNorm_algebraMap S p
  have h := t₁.symm.trans t₂
  dsimp at h
  simp_rw [map_prod, map_pow] at h
  obtain ⟨s, hs⟩ := res1 p P hp
  have {Q} (hQ : Q ∈ (p.primesOver S).toFinset) :
      relNorm R Q ^ ramificationIdx (algebraMap R S) p Q = p ^ ((p.ramificationIdxIn S) * s) := by
    rw [Set.mem_toFinset] at hQ
    have : Q.IsPrime := hQ.1
    have : Q.LiesOver p := hQ.2
    rw [← ramificationIdxIn_eq_ramificationIdx p Q (FractionRing R) (FractionRing S)]
    obtain ⟨σ, rfl⟩ := Ideal.exists_map_eq_of_isGalois p P Q (FractionRing R) (FractionRing S)
    have := relNorm_smul R P σ
    rw [Ideal.smul_def] at this
    rw [this]
    rw [hs, ← pow_mul, mul_comm]
  simp_rw +contextual [this] at h
  rw [Finset.prod_const, ← pow_mul] at h
  have : IsLeftRegular p := IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hp
  have := IsLeftRegular.pow_inj this ?_
  · rw [this.eq_iff] at h
    rw [← Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp S] at h
    rw [← Set.ncard_eq_toFinset_card', mul_comm, mul_right_inj',
      mul_right_inj'] at h
    · rwa [h, inertiaDegIn_eq_inertiaDeg p P (FractionRing R) (FractionRing S)] at hs
    · rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P (FractionRing R) (FractionRing S)]
      exact ramificationIdx_ne_zero_of_liesOver hp _
    · exact primesOver_ncard_ne_zero p S
  · rw [one_eq_top]
    exact IsMaximal.ne_top inferInstance


end relNorm
