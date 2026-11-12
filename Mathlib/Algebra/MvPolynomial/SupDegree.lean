/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Junyu Guo
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Degree
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# lemmas about sup-degree of an `MvPolynomial`

This file contains some lemmas of `AddMonoidAlgebra.{supDegree,leadingCoeff,Monic}` that are stated
with notations whose counterparts in `MvPolynomial` are not `abbrev`s of them, while restating them
in notations of `MvPolynomial`. These notations include

- `(AddMonoidAlgebra.coeff _).support`: `MvPolynomial.support`.
- `AddMonoidAlgebra.single`: `MvPolynomial.monomial`.
-/
public section

namespace MvPolynomial

variable {R : Type*} [CommSemiring R] {B : Type*}
variable {σ : Type*} (D : (σ →₀ ℕ) → B)
variable {p : MvPolynomial σ R}

section SupDegree

variable [SemilatticeSup B] [OrderBot B] {D : (σ →₀ ℕ) → B}

theorem supDegree_def : p.supDegree D = p.support.sup D := rfl

theorem supDegree_monomial_ne_zero (a : σ →₀ ℕ) {r : R} (hr : r ≠ 0) :
    (monomial a r).supDegree D = D a :=
  AddMonoidAlgebra.supDegree_single_ne_zero a hr

open Classical in
theorem supDegree_monomial (a : σ →₀ ℕ) (r : R) :
    (monomial a r).supDegree D = if r = 0 then ⊥ else D a :=
  AddMonoidAlgebra.supDegree_single a r

theorem supDegree_withBot_some_comp {s : MvPolynomial σ R} (hs : s.support.Nonempty) :
    s.supDegree (WithBot.some ∘ D) = s.supDegree D :=
  AddMonoidAlgebra.supDegree_withBot_some_comp hs

theorem supDegree_eq_of_isMaxOn {p : MvPolynomial σ R} {a : σ →₀ ℕ} (hmem : a ∈ p.support)
    (hmax : IsMaxOn D p.support a) : p.supDegree D = D a :=
  AddMonoidAlgebra.supDegree_eq_of_isMaxOn hmem hmax

variable {p q : MvPolynomial σ R}

theorem supDegree_eq_of_max {b : B} (hb : b ∈ Set.range D) (hmem : D.invFun b ∈ p.support)
    (hmax : ∀ a ∈ p.support, D a ≤ b) : p.supDegree D = b :=
  AddMonoidAlgebra.supDegree_eq_of_max hb hmem hmax

end SupDegree

section LinearOrder

variable [LinearOrder B] [OrderBot B] {p q : MvPolynomial σ R} {D : (σ →₀ ℕ) → B}

@[simp, nolint simpNF]
theorem monic_one (hD : D.Injective) : (1 : MvPolynomial σ R).Monic D :=
  AddMonoidAlgebra.monic_one hD

variable (D) in
lemma exists_supDegree_mem_support (hp : p ≠ 0) : ∃ a ∈ p.support, p.supDegree D = D a :=
  AddMonoidAlgebra.exists_supDegree_mem_support D hp

@[simp]
theorem leadingCoeff_monomial (hD : D.Injective) (a : σ →₀ ℕ) (r : R) :
    (monomial a r).leadingCoeff D = r := AddMonoidAlgebra.leadingCoeff_single hD a r

end LinearOrder

end MvPolynomial

end
