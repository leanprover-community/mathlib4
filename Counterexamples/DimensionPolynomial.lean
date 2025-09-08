/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.RingTheory.KrullDimension.Polynomial
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

theorem ringKrullDim_A_eq_one : ringKrullDim (A k) = 1 := by
  sorry

theorem ringKrullDim_polynomial_A_eq_three : ringKrullDim (A k)[X] = 3 := by
  apply le_antisymm (by simpa [ringKrullDim_A_eq_one k] using Polynomial.ringKrullDim_le (R := A k))
  let φ : (A k) →+* k := sorry
  have h_phi : RatFunc.C.comp φ = PowerSeries.constantCoeff.comp (A k).subtype := sorry
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
