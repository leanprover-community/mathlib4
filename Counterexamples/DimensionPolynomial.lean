/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Krull dimension of polynomial ring

We show that not all commutative rings `R` satisfy
`ringKrullDim (Polynomial R) = ringKrullDim R + 1`,
following the construction in the reference link.

## References

<https://math.stackexchange.com/questions/1267419/examples-of-rings-whose-polynomial-rings-have-large-dimension>
-/

namespace Counterexample

namespace CounterexampleDimensionPolynomial

open PowerSeries Polynomial

variable (k : Type*) [Field k]

abbrev A := (RatFunc.C (K := k)).range.comap PowerSeries.constantCoeff

lemma ringKrullDim_eq_one_iff_of_isLocalRing_isDomain {R : Type*}
    [CommRing R] [IsLocalRing R] [IsDomain R] : ringKrullDim R = 1 ↔ ¬ IsField R ∧
    ∀ (x : R), x ≠ 0 → IsLocalRing.maximalIdeal R ≤ Ideal.radical (Ideal.span {x}) := by
  refine ⟨fun h ↦ ⟨fun h' ↦ ?_, ?_⟩, fun ⟨hn, h⟩ ↦ ?_⟩
  · exact zero_ne_one ((ringKrullDim_eq_zero_of_isField h') ▸ h)
  · intro x hx
    rw [Ideal.radical_eq_sInf]
    refine le_sInf (fun J ⟨hJ1, hJ2⟩ ↦ ?_)
    have : J.IsMaximal := by
      refine Ring.krullDimLE_one_iff_of_noZeroDivisors.mp (Ring.krullDimLE_iff.mpr (by simp [h]))
        J (fun hJ3 ↦ hx (by simp_all)) hJ2
    exact le_of_eq (IsLocalRing.eq_maximalIdeal this).symm
  · have : ¬ ringKrullDim R ≤ 0 := fun h ↦ by
      have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr h
      exact hn Ring.KrullDimLE.isField_of_isDomain
    suffices h : Ring.KrullDimLE 1 R by
      rw [Ring.krullDimLE_iff] at h
      exact le_antisymm h (Order.succ_le_of_lt (lt_of_not_ge this))
    refine Ring.krullDimLE_one_iff_of_noZeroDivisors.mpr fun I hI hI_prime ↦ ?_
    obtain ⟨x, hI, hx⟩ : ∃ (x : R), x ∈ I ∧ x ≠ 0 := by
      apply by_contradiction fun h ↦ (hI (le_antisymm (fun x ↦ ?_) bot_le))
      simp only [ne_eq, not_exists, not_and, not_not] at h
      exact fun hx ↦ h x hx
    specialize h x hx
    have : IsLocalRing.maximalIdeal R ≤ I := le_trans h
      ((Ideal.IsRadical.radical_le_iff hI_prime.isRadical).mpr
        ((Ideal.span_singleton_le_iff_mem I).mpr hI))
    have := Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal R) hI_prime.ne_top this
    exact this ▸ (IsLocalRing.maximalIdeal.isMaximal R)

theorem ringKrullDim_A_eq_one : ringKrullDim (A k) = 1 := by
  have h_unit : ∀ (x : (RatFunc k)⟦X⟧) (hx : x ∈ A k), IsUnit x → IsUnit (⟨x, hx⟩ : A k) := by
    intro x ⟨z, hz⟩ ⟨y, hxy⟩
    refine ⟨⟨⟨y.val, hxy ▸ ⟨z, hz⟩⟩, ⟨y.inv, ⟨z⁻¹, ?_⟩⟩, Subtype.ext y.3, Subtype.ext y.4⟩,
      Subtype.ext hxy⟩
    have := hxy ▸ congr(PowerSeries.constantCoeff $(y.3))
    simp only [map_mul, ← hz, constantCoeff_one] at this
    have hz : z ≠ 0 := fun h ↦ by subst h; simp at this
    simpa only [← mul_assoc, ← RatFunc.C.map_mul, inv_mul_cancel₀ hz, RatFunc.C.map_one,
    one_mul, mul_one] using congr(RatFunc.C z⁻¹ * $this.symm)
  have : IsLocalRing (A k) := Subring.isLocalRing_of_unit (A k) h_unit
  have : ¬ IsField (A k) := fun h ↦ by
    let Y : A k := ⟨PowerSeries.X, by simp [A]⟩
    have : Y ≠ 0 := fun h ↦ PowerSeries.X_ne_zero congr(Subtype.val $h)
    obtain ⟨Y_inv, h'⟩ := h.mul_inv_cancel this
    have := congr(PowerSeries.constantCoeff (Subtype.val $(h')))
    simp [Y] at this
  refine ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mpr ⟨this, fun x hx y hy ↦ ?_⟩
  have : ringKrullDim (RatFunc k)⟦X⟧ = 1 := IsPrincipalIdealRing.ringKrullDim_eq_one _
    PowerSeries.not_isField
  have hy_mem : y.val ∈ IsLocalRing.maximalIdeal (RatFunc k)⟦X⟧ :=
    fun h ↦ hy (h_unit y.val y.prop h)
  have hy_const : PowerSeries.constantCoeff y.val = 0 := by
    simpa [← PowerSeries.ker_coeff_eq_max_ideal] using hy_mem
  obtain ⟨n, hn⟩ := (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp this).2 x
    (fun h ↦ hx (Subtype.ext h)) hy_mem
  rw [Ideal.mem_span_singleton'] at hn
  obtain ⟨a, ha⟩ := hn
  refine ⟨n + 1, Ideal.mem_span_singleton'.mpr ⟨⟨a * y.val, ?_⟩, Subtype.ext ?_⟩⟩
  · exact ⟨0, by simp [hy_const]⟩
  · simp only [Subring.coe_mul, SubmonoidClass.coe_pow, pow_succ, ← ha, mul_assoc, mul_comm x.val _]

theorem ringKrullDim_polynomial_A_eq_three : ringKrullDim (A k)[X] = 3 := by
  apply le_antisymm (by simpa [ringKrullDim_A_eq_one k] using Polynomial.ringKrullDim_le (R := A k))
  let φ : (A k) →+* k := by
    refine RingHom.comp ?_ (PowerSeries.constantCoeff.comp (A k).subtype).rangeRestrict
    refine (((⊤ : Subring k).equivMapOfInjective _ RatFunc.C_injective).symm.trans
      Subring.topEquiv).toRingHom.comp (Subring.inclusion ?_)
    exact fun _ ⟨⟨_, ⟨u, _⟩⟩, _⟩ ↦ ⟨u, ⟨by simp, by simp_all⟩⟩
  have h_phi : RatFunc.C.comp φ = PowerSeries.constantCoeff.comp (A k).subtype := RingHom.ext
    fun x ↦ by simp [φ, ← Subring.coe_equivMapOfInjective_apply _ _ RatFunc.C_injective _]
  let f : (A k)[X] →+* (RatFunc k)⟦X⟧ := eval₂RingHom (A k).subtype (PowerSeries.C RatFunc.X)
  let Q : PrimeSpectrum (A k)[X] := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  let g : (A k)[X] →+* k[X] := mapRingHom φ
  let P1 : PrimeSpectrum (A k)[X] := ⟨RingHom.ker g, RingHom.ker_isPrime g⟩
  let P2 : PrimeSpectrum (A k)[X] := ⟨RingHom.ker (Polynomial.constantCoeff.comp g),
    RingHom.ker_isPrime _⟩
  let Y : A k := ⟨PowerSeries.X, by simp⟩
  let tY : A k := ⟨PowerSeries.X * (PowerSeries.C RatFunc.X), by simp⟩
  have Y_ne_zero : Y ≠ 0 := fun h ↦ by simpa [Y] using congr(Subtype.val $h)
  have phi_Y_eq_zero : φ Y = 0 := RatFunc.C_injective (Eq.trans congr($h_phi Y) (by simp [Y]))
  have comp_eq : (algebraMap k[X] (RatFunc k)).comp g = PowerSeries.constantCoeff.comp f :=
    Polynomial.ringHom_ext (fun z ↦ by simpa [f, g] using congr($h_phi z)) (by simp [f, g])
  refine Order.le_krullDim_iff.mpr ⟨⟨3, fun | 0 => ⊥ | 1 => Q | 2 => P1 | 3 => P2, fun i ↦ ?_⟩, rfl⟩
  fin_cases i
  all_goals simp only [Fin.reduceFinMk, Fin.reduceCastSucc, Fin.reduceSucc, Set.mem_setOf_eq,
    lt_iff_le_not_ge]
  · let val0 : (A k)[X] := Polynomial.C Y * Polynomial.X - Polynomial.C tY
    have h1_val0 : val0 ∈ Q.asIdeal := by simp [val0, Q, f, Y, tY]
    have h2_val0 : val0 ≠ 0 := support_nonempty.mp ⟨1, by simpa [val0, Y]⟩
    exact ⟨OrderBot.bot_le Q, fun h ↦ h2_val0 (by simpa using h h1_val0)⟩
  · let val1 : (A k)[X] := Polynomial.C Y
    have h1_val1 : val1 ∈ P1.asIdeal := by simpa [P1, val1, g]
    have h2_val1 : val1 ∉ Q.asIdeal := by simpa [Q, val1, f]
    have : RingHom.ker f ≤ RingHom.ker g := by
      rw [← RingHom.ker_comp_of_injective g (RatFunc.algebraMap_injective k), comp_eq]
      exact fun x ↦ by simp_all
    exact ⟨by simpa [P1, Q] using this, fun h ↦ h2_val1 (h h1_val1)⟩
  · let val2 : (A k)[X] := Polynomial.X
    have h1_val2 : val2 ∈ P2.asIdeal := by simp [P2, val2, g]
    have h2_val2 : val2 ∉ P1.asIdeal := by simp [P1, val2, g]
    exact ⟨fun x ↦ by simp_all [P1, P2], fun h ↦ h2_val2 (h h1_val2)⟩

end CounterexampleDimensionPolynomial

end Counterexample
