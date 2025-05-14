import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.KD
import Mathlib.Data.ZMod.QuotientRing

set_option linter.style.header false

open Ideal NumberField

noncomputable section

variable (p : ℕ+) [Fact (Nat.Prime p)]

variable {K : Type*} [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    [IsCyclotomicExtension {p} ℚ K]

variable (P : Ideal (𝓞 K)) (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K))

open RingOfIntegers

example : Ideal.inertiaDeg (Ideal.span {(p : ℤ)}) P = 1 := by
  have : exponent (IsPrimitiveRoot.toInteger hζ : 𝓞 K) = 1 := by
    rw [exponent_eq_one_iff]
    have := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime hζ
    
#exit
      sorry
    have hp : ¬ p ∣ exponent ζ := sorry
    obtain ⟨Q, hQ, rfl⟩ := Ideal.eq_primesOverSpanEquivMonicFactorsMod_symm_of_primesOver hp hP
    rw [Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply']
    have := th2 p (K := K) (ζ := ζ)
    unfold Polynomial.Splits at this
    have := this.resolve_left sorry hQ.1 hQ.2.2
    exact Polynomial.natDegree_eq_of_degree_eq_some this
