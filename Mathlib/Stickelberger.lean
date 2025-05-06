import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.Data.ZMod.QuotientRing

set_option linter.style.header false

open NumberField

noncomputable section

variable (p : ℕ+) [hp : Fact (Nat.Prime p)]



variable {K : Type*} [Field K] [NumberField K] {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ (p - 1))

variable (P : Ideal (𝓞 K)) [hP : P.LiesOver (Ideal.span {(p : ℤ)})]

#synth Field (ZMod p)

def modp : ℤ →+* ZMod p := sorry -- ℤ ⧸ Ideal.span {(p : ℤ)} ≃+* ZMod p := Int.quotientSpanNatEquivZMod p

example : Polynomial.Splits (modp p) (minpoly ℤ ζ) := sorry

example : Ideal.inertiaDeg (Ideal.span {(p : ℤ)}) P = 1 := by
  let e := KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    (S := 𝓞 K) (I := Ideal.span {(p : ℤ)}) (x := ζ) sorry sorry sorry sorry




  sorry
