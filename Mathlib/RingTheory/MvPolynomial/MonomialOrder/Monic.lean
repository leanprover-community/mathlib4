/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

variable {σ R : Type*} [CommSemiring R] (m : MonomialOrder σ) (f : MvPolynomial σ R)

open MvPolynomial

namespace MonomialOrder

/-- A multivariate polynomial is `Monic` with respect to a monomial order
if its leading coefficient (for that monomial order) is 1 -/
def Monic : Prop :=
  m.leadingCoeff f = 1

theorem Monic.def : m.Monic f ↔ m.leadingCoeff f = 1 :=
  Iff.rfl

instance Monic.decidable [DecidableEq R] : Decidable (m.Monic f) := by unfold Monic; infer_instance

@[simp]
theorem Monic.leadingCoeff {f : MvPolynomial σ R} (hf : m.Monic f) : m.leadingCoeff f = 1 :=
  hf

theorem Monic.coeff_degree {f : MvPolynomial σ R} (hf : m.Monic f) : f.coeff (m.degree f) = 1 :=
  hf

theorem Monic.pow {f : MvPolynomial σ R} {n : ℕ} (hf : m.Monic f) :
    m.Monic (f ^ n) :=
  sorry

@[simp]
theorem monic_X_pow (n : σ →₀ ℕ) : m.Monic (monomial n 1) :=
  sorry

@[simp]
theorem monic_X (s : σ) : m.Monic (X (R := R) s) :=
  sorry

theorem leadingCoeff_one : m.leadingCoeff (1 : MvPolynomial σ R) = 1 :=
  leadingCoeff_C 1

@[simp]
theorem monic_one : Monic (1 : MvPolynomial σ R) :=
  leadingCoeff_C _

theorem Monic.ne_zero [Nontrivial R] {f : MvPolynomial σ R} (hf : m.Monic f) :
    f ≠ 0 := by
  rintro rfl
  simp [Monic] at hf

theorem Monic.ne_zero_of_ne (h : (0 : R) ≠ 1) {f : MvPolynomial σ R} (hf : m.Monic f) : f ≠ 0 := by
  nontriviality R
  exact hf.ne_zero

end MonomialOrder
