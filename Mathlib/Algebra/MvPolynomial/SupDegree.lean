/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Junyu Guo
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MonoidAlgebra.Degree

/-!
# lemmas about sup-degree of an `MvPolynomial`

This file contains some lemmas of `AddMonoidAlgebra.{supDegree,leadingCoeff,Monic}`, restated in
notations of `MvPolynomial` which are not `abbrev`s of counterparts of `AddMonoidAlgebra`, such as
`MvPolynomial.{support,coeff}`. Meanwhile, `AddMonoidAlgebra.supDegree` serves directly as the
notation of `supDegree` in `MvPolynomial`.
-/
public section

namespace MvPolynomial

variable {R : Type*} [CommSemiring R] {B : Type*}
variable {R' : Type*} [CommRing R']
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

theorem coeff_eq_zero_of_not_le_supDegree {p : MvPolynomial σ R} {a : σ →₀ ℕ}
    (hlt : ¬ D a ≤ p.supDegree D) : p.coeff a = 0 :=
  AddMonoidAlgebra.apply_eq_zero_of_not_le_supDegree hlt

-- todo: port to `AddMonoidAlgebra`
theorem apply_supDegree_eq_supDegree_comp {B' : Type*} [SemilatticeSup B'] [OrderBot B']
    {g : B → B'} (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) (bot : g ⊥ = ⊥) :
    g (p.supDegree D) = p.supDegree (g ∘ D) :=
  Finset.apply_sup_eq_sup_comp g g_sup bot

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

variable [Add B]

theorem coeff_add_of_supDegree_le (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    [AddLeftStrictMono B] [AddRightStrictMono B]
    (hD : D.Injective) {ap aq : σ →₀ ℕ} (hp : p.supDegree D ≤ D ap) (hq : q.supDegree D ≤ D aq) :
    (p * q).coeff (ap + aq) = p.coeff ap * q aq :=
  AddMonoidAlgebra.apply_add_of_supDegree_le hadd hD hp hq

end SupDegree

section LinearOrder

variable [LinearOrder B] [OrderBot B] {p q : MvPolynomial σ R} {D : (σ →₀ ℕ) → B}

theorem leadingCoeff_def : p.leadingCoeff D = p.coeff (D.invFun <| p.supDegree D) := rfl

theorem monic_def : p.Monic D ↔ p.leadingCoeff D = 1 := by rfl

@[simp]
theorem monic_one (hD : D.Injective) : (1 : MvPolynomial σ R).Monic D :=
  AddMonoidAlgebra.monic_one hD

variable (D) in
lemma exists_supDegree_mem_support (hp : p ≠ 0) : ∃ a ∈ p.support, p.supDegree D = D a :=
  AddMonoidAlgebra.exists_supDegree_mem_support D hp

@[simp]
theorem leadingCoeff_monomial (hD : D.Injective) (a : σ →₀ ℕ) (r : R) :
    (monomial a r).leadingCoeff D = r := AddMonoidAlgebra.leadingCoeff_single hD a r

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → MvPolynomial σ R}

-- todo: port to `AddMonoidAlgebra`
lemma supDegree_add_eq_of_ne (h : p.supDegree D ≠ q.supDegree D) :
    (p + q).supDegree D = p.supDegree D ⊔ q.supDegree D := by
  rcases lt_or_gt_of_ne h with h | h
  · simp [max_eq_right h.le, AddMonoidAlgebra.supDegree_add_eq_right h]
  · simp [max_eq_left h.le, AddMonoidAlgebra.supDegree_add_eq_left h]

lemma leadingCoeff_ne_zero (hD : D.Injective) : p.leadingCoeff D ≠ 0 ↔ p ≠ 0 :=
  AddMonoidAlgebra.leadingCoeff_ne_zero hD

lemma supDegree_sub_lt_of_leadingCoeff_eq (hD : D.Injective) {p q : MvPolynomial σ R'}
    (hd : p.supDegree D = q.supDegree D) (hc : p.leadingCoeff D = q.leadingCoeff D) :
    (p - q).supDegree D < p.supDegree D ∨ p = q :=
  AddMonoidAlgebra.supDegree_sub_lt_of_leadingCoeff_eq hD hd hc

lemma supDegree_leadingCoeff_sum_eq
    (hi : i ∈ s) (hmax : ∀ j ∈ s, j ≠ i → (f j).supDegree D < (f i).supDegree D) :
    (∑ j ∈ s, f j).supDegree D = (f i).supDegree D ∧
    (∑ j ∈ s, f j).leadingCoeff D = (f i).leadingCoeff D :=
  AddMonoidAlgebra.supDegree_leadingCoeff_sum_eq hi hmax

variable [Add B]
variable [AddLeftStrictMono B] [AddRightStrictMono B]

lemma coeff_supDegree_add_supDegree (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) :
    (p * q).coeff (D.invFun (p.supDegree D + q.supDegree D)) =
      p.leadingCoeff D * q.leadingCoeff D :=
  AddMonoidAlgebra.apply_supDegree_add_supDegree hD hadd

end LinearOrder

end MvPolynomial

end
