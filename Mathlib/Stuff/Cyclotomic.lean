import Mathlib.Stuff.Inertia
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.Stuff.Factorization

set_option linter.style.header false

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid Ideal

variable {n : ℕ+} {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

namespace IsCyclotomicExtension.Rat

local notation3 "θ" => (zeta_spec n ℚ K).toInteger

variable (n K) in
lemma minpoly : minpoly ℤ θ = cyclotomic n ℤ := by
  have := cyclotomic_eq_minpoly (zeta_spec n ℚ K) (by norm_num)
  rw [← (zeta_spec n ℚ K).coe_toInteger] at this
  simpa [this] using (minpoly.algebraMap_eq RingOfIntegers.coe_injective θ).symm

variable [hn : Fact (Nat.Prime n)]

variable (n) in
lemma exponent : exponent θ = 1 := by
  simp [exponent_eq_one_iff, ← ((zeta_spec n ℚ K).integralPowerBasis').adjoin_gen_eq_top]

lemma ne_dvd_exponent (p : ℕ) [hp : Fact p.Prime] : ¬ (p ∣ RingOfIntegers.exponent θ) := by
  rw [exponent, dvd_one]
  exact hp.1.ne_one

variable (n)

theorem pid1 (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, (hp : p.Prime) → p ≠ n →
    haveI : Fact (p.Prime) := ⟨hp⟩
      ∃ P, ∃ hP : P ∈ monicFactorsMod θ p, ⌊(M K)⌋₊ < p ^ P.natDegree ∨
        Submodule.IsPrincipal ((primesOverSpanEquivMonicFactorsMod (ne_dvd_exponent p)).symm
          ⟨P, hP⟩).1) : IsPrincipalIdealRing (𝓞 K) := by
  have : IsGalois ℚ K := isGalois n ℚ K
  refine blahgalois (exponent n) (fun p hple hp ↦ ?_)
  have : Fact (p.Prime) := ⟨hp⟩
  by_cases hpn : p = n
  · let Q : ℤ[X] := X - 1
    have hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p := by
      simp only [Polynomial.map_sub, map_X, Polynomial.map_one, mem_toFinset, Q]
      refine (Polynomial.mem_normalizedFactors_iff ((Monic.map _ <|
        minpoly n K ▸ monic ↑n ℤ).ne_zero)).mpr ⟨irreducible_of_degree_eq_one (by compute_degree!),
        by monicity, ⟨(X - 1) ^ (p - 2), ?_⟩⟩
      simp only [minpoly n K, map_cyclotomic]
      rw [← mul_one n, PNat.mul_coe, PNat.one_coe, ←pow_one (n : ℕ), ← hpn,
        cyclotomic_mul_prime_pow_eq (ZMod p) hp.not_dvd_one one_pos]
      simp only [cyclotomic_one, pow_one, tsub_self, pow_zero]
      rw [← pow_succ' (X - 1)]
      congr
      have := hp.two_le
      omega
    refine ⟨Q.map (Int.castRingHom (ZMod p)), hQ, ?_⟩
    right
    rw [primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span (ne_dvd_exponent p) hQ]
    simp only [map_sub, aeval_X, map_one, Q]
    refine ⟨θ - 1, le_antisymm (span_le.mpr <| fun x hx ↦ ?_) (span_le.mpr ?_)⟩
    · rcases hx with rfl | rfl
      · subst hpn
        simp [mem_span_singleton, (zeta_spec n ℚ K).toInteger_sub_one_dvd_prime']
      · exact subset_span (by simp)
    · simp only [Set.singleton_subset_iff, SetLike.mem_coe, Q]
      exact subset_span (by simp)
  · exact h p hple hp hpn

theorem pid2 (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, (hp : p.Prime) → p ≠ n →
    haveI : Fact (p.Prime) := ⟨hp⟩
      ∃ P : ℤ[X], P.Monic ∧ P.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p ∧
        (⌊(M K)⌋₊ < p ^ P.natDegree ∨
          Submodule.IsPrincipal (span {↑p, aeval θ P}))) : IsPrincipalIdealRing (𝓞 K) := by
    refine pid1 n (fun p hple hp hpn ↦ ?_)
    have : Fact (p.Prime) := ⟨hp⟩
    obtain ⟨P, hPmo, hP, hM⟩ := h p hple hp hpn
    refine ⟨P.map (Int.castRingHom (ZMod p)), hP, ?_⟩
    rcases hM with H | H
    · left
      convert H
      simp [hPmo.leadingCoeff]
    · right
      simpa [primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span (ne_dvd_exponent p) hP]

theorem pid3 (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, (hp : p.Prime) → (hpn : p ≠ n) →
    haveI : Fact (p.Prime) := ⟨hp⟩
      ∃ P Q A : ℤ[X], P.Monic ∧ orderOf (ZMod.unitOfCoprime _ (uff hn.1 hpn)) = P.natDegree
      ∧ P * Q + p * A = cyclotomic n ℤ ∧
        (⌊(M K)⌋₊ < p ^ P.natDegree ∨
          Submodule.IsPrincipal (span {↑p, aeval θ P}))) : IsPrincipalIdealRing (𝓞 K) := by
  refine pid2 n (fun p hple hp hpn ↦ ?_)
  have : Fact (p.Prime) := ⟨hp⟩
  obtain ⟨P, Q, A, hPmo, hP, hQA, hM⟩ := h p hple hp hpn
  have : P.map (Int.castRingHom (ZMod p)) ∣ cyclotomic n (ZMod p) := by
    refine ⟨Q.map (Int.castRingHom (ZMod p)), ?_⟩
    simp [← map_cyclotomic n (Int.castRingHom (ZMod p)), ← hQA]
  refine ⟨P, hPmo, mem_toFinset.mpr <| (Polynomial.mem_normalizedFactors_iff
    (((minpoly.monic (isIntegral θ)).map _).ne_zero)).mpr ⟨?_, hPmo.map _,
    by simp [minpoly, ← hQA]⟩, hM⟩
  exact baz'' hn.1 hpn this <| by simp [← hP, hPmo]

theorem pid4 (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, (hp : p.Prime) → (hpn : p ≠ n) →
    haveI : Fact (p.Prime) := ⟨hp⟩
      ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
        P.Monic ∧ orderOf (ZMod.unitOfCoprime _ (uff hn.1 hpn)) = P.natDegree
          ∧ P * Q + p * A = cyclotomic n ℤ ∧
          (⌊(M K)⌋₊ < p ^ P.natDegree ∨
            (p = G * Qp + Rp * (cyclotomic n ℤ) ∧
             P = G * QP + RP * (cyclotomic n ℤ) ∧
             G = C1 * P + C2 * p ))) : IsPrincipalIdealRing (𝓞 K) := by
  refine pid3 n (fun p hple hp hpn ↦ ?_)
  obtain ⟨P, Q, A, G, Qp, Rp, QP, RP, C1, C2, hPmo, hP, hQA, hM⟩ := h p hple hp hpn
  refine ⟨P, Q, A, hPmo, hP, hQA, ?_⟩
  rcases hM with H | ⟨Hp, HP, HG⟩
  · left
    assumption
  · right
    refine ⟨aeval θ G, le_antisymm (span_le.mpr <| fun x hx ↦ ?_) (span_le.mpr ?_)⟩
    · rcases hx with rfl | rfl
      · simp only [submodule_span_eq, SetLike.mem_coe, mem_span_singleton]
        refine ⟨aeval θ Qp, ?_⟩
        rw [← aeval_mul, ← sub_eq_iff_eq_add.mpr Hp]
        simp [← minpoly n K]
      · simp only [submodule_span_eq, SetLike.mem_coe, mem_span_singleton]
        refine ⟨aeval θ QP, ?_⟩
        rw [← aeval_mul, ← sub_eq_iff_eq_add.mpr HP]
        simp [← minpoly n K]
    · simp only [Set.singleton_subset_iff, SetLike.mem_coe, HG, _root_.map_add, map_mul,
        map_natCast]
      exact add_mem (mul_mem_left _ _ (subset_span (by simp)))
        (mul_mem_left _ _ (subset_span (by simp)))

end IsCyclotomicExtension.Rat
