/-
Copyright (c) 2026 Damiano Testa, Junyu Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Junyu Guo
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MonoidAlgebra.Degree

/-!
# sup-degree of an `MvPolynomial`

This file is directly refactored from `Mathlib.Algebra.MonoidAlgebra.Degree`, specializing
`supDegree` and relative lemmas.

## Definitions

Let `R` be a commutative semi-ring and let `B` be a `SemilatticeSup` with `OrderBot`.
For `f : MvPolynomial σ R` and `D : (σ →₀ ℕ) → B`, this file defines

* `MvPolynomial.supDegree D f`: the sup-degree of `f` w.r.t. `D`, taking values in `B`,
  `⊥` if `f = 0`.
* `MvPolynomial.leadingCoeff D f`: leading coefficient if `D` is injective, or the coefficient at an
  inverse image of `supDegree f` (if such exists) in general.
* `MvPolynomial.Monic D f`: the leading coefficient of `f` is `1`.
-/
public section

namespace MvPolynomial

variable {R : Type*} [CommSemiring R] {B : Type*}
variable {R' : Type*} [CommRing R']
variable {σ : Type*} (D : (σ →₀ ℕ) → B)
variable {p : MvPolynomial σ R}

set_option linter.unusedVariables false in
/-- Let `R` be a commutative semi-ring, let `B` be a `SemilatticeSup` with `OrderBot`, and let
`D : (σ →₀ ℕ) → B` be a "degree" function.
For an element `f : MvPolynomial σ R`, the element `supDegree f : B` is the supremum of all the
elements in the support of `f`, or `⊥` if `f` is zero.

If we equip `σ` with a linear order then the induced linear order on `Lex (σ →₀ ℕ)` equips
`MvPolynomial` ring with a [monomial order](https://en.wikipedia.org/wiki/Monomial_order) (i.e. a
linear order on `σ →₀ ℕ`, the type of (monic) monomials in `MvPolynomial σ R`, that respects
addition). We make use of this monomial order by using `MonomialOrder.lex.degree` instead of
`supDegree` with `D := toLex`, and different monomial orders could be accessed via different
`MonomialOrder`. For an abstract monomial order, `m : MonomialOrder σ` can be used as a hypothesis.
-/
abbrev supDegree [SemilatticeSup B] [OrderBot B] (p : MvPolynomial σ R) : B :=
  AddMonoidAlgebra.supDegree D p

section SupDegree

variable [SemilatticeSup B] [OrderBot B] {D : (σ →₀ ℕ) → B}

theorem supDegree_def (p : MvPolynomial σ R) : p.supDegree D = p.support.sup D := rfl

theorem supDegree_add_le {f g : MvPolynomial σ R} :
    (f + g).supDegree D ≤ (f.supDegree D) ⊔ (g.supDegree D) :=
  AddMonoidAlgebra.supDegree_add_le

@[simp]
theorem supDegree_neg {f : MvPolynomial σ R'} :
    (-f).supDegree D = f.supDegree D := AddMonoidAlgebra.supDegree_neg

theorem supDegree_sub_le {f g : MvPolynomial σ R'} :
    (f - g).supDegree D ≤ f.supDegree D ⊔ g.supDegree D :=
  AddMonoidAlgebra.supDegree_sub_le

theorem supDegree_sum_le {ι} {s : Finset ι} {f : ι → MvPolynomial σ R} :
    (∑ i ∈ s, f i).supDegree D ≤ s.sup (fun i => (f i).supDegree D) :=
  AddMonoidAlgebra.supDegree_sum_le

theorem supDegree_monomial_ne_zero (a : σ →₀ ℕ) {r : R} (hr : r ≠ 0) :
    (monomial a r).supDegree D = D a :=
  AddMonoidAlgebra.supDegree_single_ne_zero a hr

open Classical in
theorem supDegree_monomial (a : σ →₀ ℕ) (r : R) :
    (monomial a r).supDegree D = if r = 0 then ⊥ else D a :=
  AddMonoidAlgebra.supDegree_single a r

theorem apply_eq_zero_of_not_le_supDegree {p : MvPolynomial σ R} {a : σ →₀ ℕ}
    (hlt : ¬ D a ≤ p.supDegree D) : p a = 0 :=
  AddMonoidAlgebra.apply_eq_zero_of_not_le_supDegree hlt

-- todo: port to `AddMonoidAlgebra`
theorem apply_supDegree_eq_supDegree_comp {B' : Type*} [SemilatticeSup B'] [OrderBot B']
    {g : B → B'} (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) (bot : g ⊥ = ⊥) :
    g (p.supDegree D) = p.supDegree (g ∘ D) :=
  Finset.apply_sup_eq_sup_comp g g_sup bot

theorem supDegree_withBot_some_comp {s : MvPolynomial σ R} (hs : s.support.Nonempty) :
    supDegree (WithBot.some ∘ D) s = supDegree D s :=
  AddMonoidAlgebra.supDegree_withBot_some_comp hs

theorem supDegree_eq_of_isMaxOn {p : MvPolynomial σ R} {a : σ →₀ ℕ} (hmem : a ∈ p.support)
    (hmax : IsMaxOn D p.support a) : p.supDegree D = D a :=
  AddMonoidAlgebra.supDegree_eq_of_isMaxOn hmem hmax

variable {p q : MvPolynomial σ R}

@[simp]
theorem supDegree_zero : (0 : MvPolynomial σ R).supDegree D = ⊥ :=
  AddMonoidAlgebra.supDegree_zero

theorem ne_zero_of_supDegree_ne_bot : p.supDegree D ≠ ⊥ → p ≠ 0 :=
  AddMonoidAlgebra.ne_zero_of_supDegree_ne_bot

theorem ne_zero_of_not_supDegree_le {b : B} (h : ¬ p.supDegree D ≤ b) : p ≠ 0 :=
  AddMonoidAlgebra.ne_zero_of_not_supDegree_le h

theorem supDegree_eq_of_max {b : B} (hb : b ∈ Set.range D) (hmem : D.invFun b ∈ p.support)
    (hmax : ∀ a ∈ p.support, D a ≤ b) : p.supDegree D = b :=
  AddMonoidAlgebra.supDegree_eq_of_max hb hmem hmax

variable [Add B]

theorem supDegree_mul_le (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    [AddLeftMono B] [AddRightMono B] : (p * q).supDegree D ≤ p.supDegree D + q.supDegree D :=
  AddMonoidAlgebra.supDegree_mul_le hadd

theorem supDegree_prod_le {B} [AddCommMonoid B] [SemilatticeSup B] [OrderBot B]
    [AddLeftMono B] [AddRightMono B]
    {D : (σ →₀ ℕ) → B} (hzero : D 0 = 0) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    {ι} {s : Finset ι} {f : ι → MvPolynomial σ R} :
    (∏ i ∈ s, f i).supDegree D ≤ ∑ i ∈ s, (f i).supDegree D :=
  AddMonoidAlgebra.supDegree_prod_le hzero hadd

theorem apply_add_of_supDegree_le (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    [AddLeftStrictMono B] [AddRightStrictMono B]
    (hD : D.Injective) {ap aq : σ →₀ ℕ} (hp : p.supDegree D ≤ D ap) (hq : q.supDegree D ≤ D aq) :
    (p * q) (ap + aq) = p ap * q aq :=
  AddMonoidAlgebra.apply_add_of_supDegree_le hadd hD hp hq

end SupDegree

section LinearOrder

variable [LinearOrder B] [OrderBot B] {p q : MvPolynomial σ R} (D : (σ →₀ ℕ) → B)

/-- If `D` is an injection into a linear order `B`, the leading coefficient of
  `f : MvPolynomial σ R` is the nonzero coefficient of highest degree according to `D`, or 0 if
  `f = 0`. In general, it is defined to be the coefficient at an inverse image of `supDegree f`
  (if such exists). -/
@[expose]
noncomputable def leadingCoeff (f : MvPolynomial σ R) : R := f.coeff (D.invFun <| f.supDegree D)

/-- An element `f : MvPolynomial σ R` is monic if its leading coefficient is one. -/
@[expose, reducible] def Monic (f : MvPolynomial σ R) : Prop := f.leadingCoeff D = 1

variable {D}

@[simp]
theorem leadingCoeff_monomial (hD : D.Injective) (a : σ →₀ ℕ) (r : R) :
    (monomial a r).leadingCoeff D = r := AddMonoidAlgebra.leadingCoeff_single hD a r

@[simp]
theorem leadingCoeff_zero : (0 : MvPolynomial σ R).leadingCoeff D = 0 :=
  AddMonoidAlgebra.leadingCoeff_zero

lemma Monic.ne_zero [Nontrivial R] (hp : p.Monic D) : p ≠ 0 := AddMonoidAlgebra.Monic.ne_zero hp

@[simp]
theorem monic_one (hD : D.Injective) : (1 : MvPolynomial σ R).Monic D :=
  AddMonoidAlgebra.monic_one hD

-- todo: port to `AddMonoidAlgebra`
theorem apply_supDegree_eq_supDegree_comp_of_linearOrder
    {B' : Type*} [SemilatticeSup B'] [OrderBot B'] {g : B → B'}
    (mono : Monotone g) (bot : g ⊥ = ⊥) :
    g (p.supDegree D) = p.supDegree (g ∘ D) :=
  Finset.apply_sup_eq_sup_comp_of_linearOrder g mono bot

variable (D) in
lemma exists_supDegree_mem_support (hp : p ≠ 0) : ∃ a ∈ p.support, p.supDegree D = D a :=
  AddMonoidAlgebra.exists_supDegree_mem_support D hp

variable (D) in
lemma supDegree_mem_range (hp : p ≠ 0) : p.supDegree D ∈ Set.range D :=
  AddMonoidAlgebra.supDegree_mem_range D hp

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → MvPolynomial σ R}

lemma supDegree_sum_lt (hs : s.Nonempty) {b : B}
    (h : ∀ i ∈ s, (f i).supDegree D < b) : (∑ i ∈ s, f i).supDegree D < b :=
  AddMonoidAlgebra.supDegree_sum_lt hs h

lemma supDegree_add_eq_left (h : q.supDegree D < p.supDegree D) :
    (p + q).supDegree D = p.supDegree D := AddMonoidAlgebra.supDegree_add_eq_left h

lemma supDegree_add_eq_right (h : p.supDegree D < q.supDegree D) :
    (p + q).supDegree D = q.supDegree D := AddMonoidAlgebra.supDegree_add_eq_right h

-- port to `AddMonoidAlgebra`
lemma supDegree_add_eq_of_ne (h : p.supDegree D ≠ q.supDegree D) :
    (p + q).supDegree D = p.supDegree D ⊔ q.supDegree D := by
  rcases lt_or_gt_of_ne h with h | h
  · simp [max_eq_right h.le, supDegree_add_eq_right h]
  · simp [max_eq_left h.le, supDegree_add_eq_left h]

lemma leadingCoeff_add_eq_left (h : q.supDegree D < p.supDegree D) :
    (p + q).leadingCoeff D = p.leadingCoeff D := AddMonoidAlgebra.leadingCoeff_add_eq_left h

lemma leadingCoeff_add_eq_right (h : p.supDegree D < q.supDegree D) :
    (p + q).leadingCoeff D = q.leadingCoeff D := AddMonoidAlgebra.leadingCoeff_add_eq_right h

lemma supDegree_mem_support (hD : D.Injective) (hp : p ≠ 0) :
    D.invFun (p.supDegree D) ∈ p.support := AddMonoidAlgebra.supDegree_mem_support hD hp

@[simp]
lemma leadingCoeff_eq_zero (hD : D.Injective) : p.leadingCoeff D = 0 ↔ p = 0 :=
  AddMonoidAlgebra.leadingCoeff_eq_zero hD

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

lemma sum_ne_zero_of_injOn_supDegree' (hs : ∃ i ∈ s, f i ≠ 0)
    (hd : (s : Set ι).InjOn (supDegree D ∘ f)) : ∑ i ∈ s, f i ≠ 0 :=
  AddMonoidAlgebra.sum_ne_zero_of_injOn_supDegree' hs hd

lemma sum_ne_zero_of_injOn_supDegree (hs : s.Nonempty)
    (hf : ∀ i ∈ s, f i ≠ 0) (hd : (s : Set ι).InjOn (supDegree D ∘ f)) :
    ∑ i ∈ s, f i ≠ 0 := AddMonoidAlgebra.sum_ne_zero_of_injOn_supDegree hs hf hd

variable [Add B]
variable [AddLeftStrictMono B] [AddRightStrictMono B]

lemma apply_supDegree_add_supDegree (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) :
    (p * q) (D.invFun (p.supDegree D + q.supDegree D)) = p.leadingCoeff D * q.leadingCoeff D :=
  AddMonoidAlgebra.apply_supDegree_add_supDegree hD hadd

lemma supDegree_mul
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hpq : leadingCoeff D p * leadingCoeff D q ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D :=
  AddMonoidAlgebra.supDegree_mul hD hadd hpq hp hq

lemma Monic.supDegree_mul_of_ne_zero_left
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hq : q.Monic D) (hp : p ≠ 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D :=
  AddMonoidAlgebra.Monic.supDegree_mul_of_ne_zero_left hD hadd hq hp

lemma Monic.supDegree_mul_of_ne_zero_right
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hp : p.Monic D) (hq : q ≠ 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D :=
  AddMonoidAlgebra.Monic.supDegree_mul_of_ne_zero_right hD hadd hp hq

lemma Monic.supDegree_mul
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hbot : (⊥ : B) + ⊥ = ⊥) (hp : p.Monic D) (hq : q.Monic D) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D :=
  AddMonoidAlgebra.Monic.supDegree_mul hD hadd hbot hp hq

lemma leadingCoeff_mul [NoZeroDivisors R]
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) :
    (p * q).leadingCoeff D = p.leadingCoeff D * q.leadingCoeff D :=
  AddMonoidAlgebra.leadingCoeff_mul hD hadd

lemma Monic.leadingCoeff_mul_eq_left
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hq : q.Monic D) :
    (p * q).leadingCoeff D = p.leadingCoeff D :=
  AddMonoidAlgebra.Monic.leadingCoeff_mul_eq_left hD hadd hq

lemma Monic.leadingCoeff_mul_eq_right
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hp : p.Monic D) :
    (p * q).leadingCoeff D = q.leadingCoeff D :=
  AddMonoidAlgebra.Monic.leadingCoeff_mul_eq_right hD hadd hp

lemma Monic.mul
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hp : p.Monic D) (hq : q.Monic D) : (p * q).Monic D :=
  AddMonoidAlgebra.Monic.mul hD hadd hp hq

section AddMonoid

variable {B : Type*} [AddMonoid B] [LinearOrder B] [OrderBot B]
  [AddLeftStrictMono B] [AddRightStrictMono B]
  {D : (σ →₀ ℕ) → B} {p : MvPolynomial σ R} {n : ℕ}

lemma Monic.pow
    (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hD : D.Injective)
    (hp : p.Monic D) : (p ^ n).Monic D :=
  AddMonoidAlgebra.Monic.pow hadd hD hp

lemma Monic.supDegree_pow
    (hzero : D 0 = 0) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hD : D.Injective)
    [Nontrivial R] (hp : p.Monic D) :
    (p ^ n).supDegree D = n • p.supDegree D :=
  AddMonoidAlgebra.Monic.supDegree_pow hzero hadd hD hp

end AddMonoid

end LinearOrder

end MvPolynomial

end
