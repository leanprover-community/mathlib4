/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.Algebra.Polynomial.Basic

/-!
# Univariate monomials
-/

public section


noncomputable section

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}
variable [Semiring R] {p q r : R[X]}

lemma monomial_one_eq_iff [Nontrivial R] : (monomial m 1 : R[X]) = monomial n 1 ↔ m = n :=
  monomial_left_inj one_ne_zero

instance infinite [Nontrivial R] : Infinite R[X] :=
  Infinite.of_injective (fun i => monomial i 1) fun m n h => by simpa [monomial_one_eq_iff] using h

theorem card_support_le_one_iff_monomial {f : R[X]} :
    Finset.card f.support ≤ 1 ↔ ∃ n a, f = monomial n a := by
  constructor
  · intro H
    rw [Finset.card_le_one_iff_subset_singleton] at H
    rcases H with ⟨n, hn⟩
    refine ⟨n, f.coeff n, ?_⟩
    ext i
    by_cases hi : i = n
    · simp [hi]
    · have : f.coeff i = 0 := by
        rw [← notMem_support_iff]
        exact fun hi' => hi (Finset.mem_singleton.1 (hn hi'))
      simp [this, Ne.symm hi, coeff_monomial]
  · rintro ⟨n, a, rfl⟩
    rw [← Finset.card_singleton n]
    apply Finset.card_le_card
    exact support_monomial_subset _ _

theorem ringHom_ext {S} [Semiring S] {f g : R[X] →+* S} (h₁ : ∀ a, f (C a) = g (C a))
    (h₂ : f X = g X) : f = g :=
  AddMonoidAlgebra.ringHom_ext h₁ fun m ↦ by
    have : (AddMonoidAlgebra.single m 1 : R[X]) = X ^ m := monomial_one_right_eq_X_pow m
    rw [this, map_pow, map_pow, h₂]

-- Since `R[X]` is reducibly `AddMonoidAlgebra R ℕ`, `AddMonoidAlgebra.ringHom_ext'` also applies to
-- ring homs out of `R[X]`. We give this a higher priority so that the goal is phrased via `C`/`X`
-- rather than exposing `AddMonoidAlgebra.single`.
@[ext high + 1]
theorem ringHom_ext' {S} [Semiring S] {f g : R[X] →+* S} (h₁ : f.comp C = g.comp C)
    (h₂ : f X = g X) : f = g :=
  ringHom_ext (RingHom.congr_fun h₁) h₂

end Polynomial
