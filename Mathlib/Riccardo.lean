import Mathlib

variable {K : Type*} [Field K] [Fintype K] {p f n : ℕ} [hp : Fact p.Prime]
  (hK : Fintype.card K = p ^ f) (hn : (p ^ f).Coprime n)

open Polynomial ZMod AdjoinRoot FiniteField

include hK in
theorem foo {P : K[X]} (hP : P ∣ cyclotomic n K) (hPirr : Irreducible P) (hPmo : P.Monic) :
    P.natDegree = orderOf (unitOfCoprime _ hn) := by
  rw [eq_comm]
  have : Fact (Irreducible P) := ⟨hPirr⟩
  have := hPmo.finite_adjoinRoot
  have : Finite (AdjoinRoot P) := Module.finite_of_finite K
  have hf : f ≠ 0 := fun h0 ↦ not_subsingleton K <|
    Fintype.card_le_one_iff_subsingleton.mp <| by simpa [h0] using hK.le
  have hζ : IsPrimitiveRoot (root P) n := by
    have : NeZero (n : AdjoinRoot P) := by
      suffices NeZero (n : K) by
        simpa using NeZero.of_injective (algebraMap K (AdjoinRoot P)).injective
      have : CharP K p :=
        (CharP.charP_iff_prime_eq_zero hp.out).mpr (by simpa [hf, hK] using cast_card_eq_zero K)
      exact ⟨fun h0 ↦ Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p, hp.out, dvd_pow_self p hf, (CharP.cast_eq_zero_iff K p n).mp h0⟩ hn⟩
    simpa [← isRoot_cyclotomic_iff] using (isRoot_root P).dvd
      (by simpa using map_dvd (algebraMap K (AdjoinRoot P)) hP)
  let pB := powerBasis hPirr.ne_zero
  rw [← powerBasis_dim hPirr.ne_zero, ← pB.finrank, ← orderOf_frobeniusAlgEquivOfAlgebraic]
  have hζ' := isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, pos_of_ne_zero (fun h0 ↦ by simp [h0, hp.out.ne_one, hf] at hn), hζ.pow_eq_one⟩
  refine dvd_antisymm (orderOf_dvd_iff_pow_eq_one.mpr <| Units.ext ?_)
    (orderOf_dvd_iff_pow_eq_one.mpr <| AlgEquiv.coe_algHom_injective <| pB.algHom_ext ?_)
  · let φ := frobeniusAlgEquivOfAlgebraic K (AdjoinRoot P)
    have : (φ ^ orderOf φ) (root P) = root P := by simp [pow_orderOf_eq_one φ]
    simp only [AlgEquiv.coe_pow, φ, coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, hK] at this
    rw [Units.val_one, ← Nat.cast_one, Units.val_pow_eq_pow_val, coe_unitOfCoprime,
      ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff, hζ.eq_orderOf, ← hζ'.pow_eq_pow_iff_modEq,
      this, pow_one]
  · simp only [AlgHom.coe_coe, AlgEquiv.coe_pow, AlgEquiv.one_apply,
      coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, hK]
    nth_rewrite 2 [← pow_one pB.gen]
    rw [powerBasis_gen hPirr.ne_zero, hζ'.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf,
      ← ZMod.natCast_eq_natCast_iff]
    simpa using Units.val_inj.mpr <| pow_orderOf_eq_one (unitOfCoprime _ hn)

#exit

include hK in
theorem bar {P : K[X]} (hP : P ∣ cyclotomic n K) (hPirr : Irreducible P) :
    orderOf (unitOfCoprime _ hn) = P.natDegree := by
  obtain ⟨A, hA⟩ := hP
  have hQ : P * C P.leadingCoeff⁻¹ ∣ cyclotomic n K := by
    refine ⟨A * C P.leadingCoeff, ?_⟩
    calc
      _ = P * A := hA
      _ = P * (C P.leadingCoeff⁻¹ * C P.leadingCoeff) * A := by
        field_simp [← C_mul, leadingCoeff_ne_zero.mpr hPirr.ne_zero]
        sorry
      _ = _ := by ring
  simpa [← natDegree_mul_leadingCoeff_self_inv P] using foo hK hn hQ
    (irreducible_mul_leadingCoeff_inv.mpr hPirr) (monic_mul_leadingCoeff_inv hPirr.ne_zero)

include hK in
open UniqueFactorizationMonoid in
theorem baz {P : K[X]} (hP : P ∣ cyclotomic n K)
  (hPdeg : P.natDegree = orderOf (unitOfCoprime _ hn)) :
    Irreducible P := by
  classical
  have hP0 : P ≠ 0 := ne_zero_of_dvd_ne_zero (cyclotomic_ne_zero n K) hP
  obtain ⟨Q, HQ⟩ := exists_mem_normalizedFactors hP0 <| not_isUnit_of_natDegree_pos _ <|
    pos_of_ne_zero <| fun h ↦ orderOf_eq_zero_iff.mp (h ▸ hPdeg.symm) <| isOfFinOrder_of_finite ..
  refine (associated_of_dvd_of_natDegree_le (dvd_of_mem_normalizedFactors HQ) hP0 ?_).irreducible
    (irreducible_of_normalized_factor Q HQ)
  rw [hPdeg, ← bar hK hn ?_ (irreducible_of_normalized_factor Q HQ)]
  exact dvd_of_mem_normalizedFactors <| Multiset.mem_of_le
    ((dvd_iff_normalizedFactors_le_normalizedFactors hP0 (cyclotomic_ne_zero n K)).mp hP) HQ
