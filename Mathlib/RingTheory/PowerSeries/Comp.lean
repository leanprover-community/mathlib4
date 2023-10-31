/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard M. Hill
-/
import Mathlib.RingTheory.PowerSeries.Basic
/-!
# Definitions

Let $R$ be a commutative semiring. Give two formal power series $f(X)$ and $g(X)$ with coefficients
in $R$, their formal composition, when it exists, is the power series

$$ f ( g ( X ))= ∑_{n=0}^∞ \mathrm{coeff}_n(f) ⬝ g^n.$$

I.e the $d$-th coefficient of the composition is the sum

$$ ∑_{n=0}^∞ \mathrm{coeff}_n(f) ⬝ \mathrm{coeff}_d (g ^ n).$$

The formal composition exists when all of these sums have finite support. This happens for example
when $f$ is a polynomial, or when the constant term of $g$ is nilpotent. There are also other cases
where the composition is defined, although these cases are less easy to classify.

In this file we define
* `PowerSeries.HasComp` : a relation on `R⟦X⟧`, where `f.hasComp g` means that the formal
  composition of `f` and `g` exists.
* `PowerSeries.comp` : a binary operation on `R⟦X⟧`, where `f.comp g` is the formal composition
  in the case `f.HasComp g`, or zero otherwise.

## Notation

The operation `f.comp g` can also be written `f ∘ᶠ g`.


## Main results

* `add_HasComp` if `f.HasComp h` and `g.HasComp h` then `(f+g).HasComp h`.
* `coe_HasComp` if `f` is a polynomial then `(f : R⟦X⟧).HasComp h`.
* `HasComp_of_isNilpotent_constantCoeff` if the constant term of `g`
    is nilpotent then `f.HasComp g`.
* `add_comp` if `f.HasComp h` and `g.HasComp h` then `(f + g) ∘ᶠ h = f ∘ᶠ h + g ∘ᶠ h`.
* `coe_comp_eq_aeval` if `f` is a polynomial then `f ∘ᶠ g = aeval g f`.
-/

open Nat Finset BigOperators Polynomial
open scoped Classical

namespace PowerSeries

section CommutativeSemiring
variable {R : Type*} [CommSemiring R]

/--`f.HasComp g` states that the power series `g` may be substituted into the power series `f`
to give a new power series, whose `d`-coefficient is $∑ fₙ ⬝ {coeff}_d(g^n)$. For the formal
composition to make sense, we require that each of these sums has finite support.
`f.HasComp g` is precisely this condition.

There are two common situations when `f.HasComp g`: either `f` could be a polynomial,
or the constant term of `g` could be zero. However, there are other intermediate cases if `R`
is not an integral domain.
-/
def HasComp (f g : R⟦X⟧) : Prop := ∀ d, ∃ N, ∀ n, N ≤ n → (coeff R n f) * coeff R d (g^n) = 0

/--
Formal composition of power series. If `f.HasComp g` then `f ∘ᶠ g` is defined in the usual way.
If not then `f ∘ᶠ g` defaults to `0`.
-/
noncomputable def comp (f g : R⟦X⟧) : R⟦X⟧ :=
  if f.HasComp g then mk fun d ↦ ∑ᶠ n : ℕ, (coeff R n f) * coeff R d (g^n) else 0

/--
`f ∘ᶠ g` is notation for `f.comp g`, which is the composition of the formal power series
`f` and `g`.

If `f.HasComp g` then `f ∘ᶠ g` is defined in the usual way. If not then `f ∘ᶠ g` defaults to `0`.
-/
scoped infixr:90 " ∘ᶠ "  => PowerSeries.comp

/-!
## Criteria for `HasComp`

The relation `HasComp` seems quite difficult to describe. It is neither symmetric,
reflexive, nor transitive. It can happen that `f.HasComp g` and `g.HasComp h` but
`¬f.HasComp (g ∘ ᶠh)` and `¬(f ∘ᶠ g).HasComp h`.
For example, we may take `g = X` and `h = 1`, and almost any `f`.
-/

private lemma X_pow_dvd_pow_of_isNilpotent_constantCoeff {g} (d : ℕ)
    (hg : IsNilpotent (constantCoeff R g)) :
    ∃ N, X^d ∣ g^N := by
  obtain ⟨N, hN⟩ := hg
  use N * d
  rw [pow_mul]
  apply pow_dvd_pow_of_dvd
  rwa [X_dvd_iff, map_pow]

/--If `g` has nilpotent constant term then `f.HasComp g`.-/
lemma HasComp_of_isNilpotent_constantCoeff {f g : R⟦X⟧} (hg : IsNilpotent (constantCoeff R g)) :
    f.HasComp g := by
  intro d
  obtain ⟨N, hN⟩ := X_pow_dvd_pow_of_isNilpotent_constantCoeff d.succ hg
  use N
  intro n hn
  have : X ^ d.succ ∣ g^n
  · trans g ^ N
    exact hN
    apply pow_dvd_pow (h := hn)
  rw [X_pow_dvd_iff] at this
  rw [this, mul_zero]
  exact lt.base d

/--If the constant term of `g` is zero then `f.HasComp g`.-/
lemma HasComp_of_constantCoeff_eq_zero {f g} (hg : constantCoeff R g = 0) :
    HasComp f g := by
  apply HasComp_of_isNilpotent_constantCoeff
  rw [hg]
  exact IsNilpotent.zero

/--If `f` is a polynomial then `(↑f).HasComp g`-/
lemma coe_HasComp {f : R[X]} {g} : (↑f : R⟦X⟧).HasComp g := by
  intro
  use f.natDegree + 1
  intro _ hn
  rw [Polynomial.coeff_coe, coeff_eq_zero_of_natDegree_lt, zero_mul]
  rw [←succ_le]
  exact hn

lemma zero_HasComp {f} : HasComp 0 f (R := R) := by
  rw [←Polynomial.coe_zero]
  apply coe_HasComp

lemma one_HasComp {f} : HasComp 1 f (R := R):= by
  rw [←Polynomial.coe_one]
  apply coe_HasComp

lemma C_HasComp {f r}: (C R r).HasComp f := by
  rw [←Polynomial.coe_C]
  apply coe_HasComp

lemma X_HasComp {f} : X.HasComp f (R := R):= by
  rw [←Polynomial.coe_X]
  apply coe_HasComp

lemma add_HasComp {f₁ f₂ g : R⟦X⟧} (h₁ : f₁.HasComp g) (h₂ : f₂.HasComp g) :
    (f₁ + f₂).HasComp g := by
  intro d
  obtain ⟨N₁,hN₁⟩ := h₁ d
  obtain ⟨N₂,hN₂⟩ := h₂ d
  use max N₁ N₂
  intro _ hn
  rw [map_add, add_mul, hN₁, hN₂, add_zero]
  exact le_of_max_le_right hn
  exact le_of_max_le_left hn

/-
Some lemmas allowing us to calculate compositions.
-/
lemma coeff_comp {f g n} (h : f.HasComp g (R := R)) :
    coeff R n (f ∘ᶠ g) = ∑ᶠ d : ℕ, coeff R d f * coeff R n (g ^ d) := by
  rw [comp, if_pos h, coeff_mk]

lemma comp_eq_zero {f g} (h : ¬f.HasComp g (R := R)) : f ∘ᶠ g  = 0 := by
  rw [comp, if_neg h]

/--The `n`-th coefficient of `f ∘ᶠ g` may be calculated from a truncation of `f`.-/
lemma coeff_comp_eq_coeff_aeval_trunc {f g n} (h : f.HasComp g) :
    coeff R n (f ∘ᶠ g) = coeff R n (aeval g (trunc (h n).choose f)) := by
  rw [aeval_trunc_eq_sum_range, map_sum, coeff_comp h]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  rw [Function.mem_support] at hd
  rw [coe_range, Set.mem_Iio]
  by_contra' h'
  apply hd
  apply (h n).choose_spec _ h'

private lemma coeff_aeval_trunc_of_zero {N n M f g}
    (hN : ∀ m, N ≤ m → coeff R m f * coeff R n (g^m) = 0) (hM : N ≤ M) :
    coeff R n (aeval g (trunc M f)) = coeff R n (aeval g (trunc N f)) := by
  induction hM with
  | refl => rfl
  | step ih1 ih2 => rw [trunc_succ, aeval_add, aeval_monomial, map_add, ←C_eq_algebraMap,
      coeff_C_mul, ih2, hN _ ih1, add_zero]

/--The `n`-th coefficient of `f ∘ᶠ g` may be calculated from a sufficiently long
truncation of `f`.-/
private lemma coeff_comp_eq_coeff_aeval_of_le {f g : R⟦X⟧} {d n} {h : f.HasComp g}
    (hn : (h d).choose ≤ n) :
    coeff R d (f ∘ᶠ g) = coeff R d (aeval g (trunc n f)) := by
  rw [coeff_comp_eq_coeff_aeval_trunc h]
  symm
  apply coeff_aeval_trunc_of_zero
  apply (h d).choose_spec
  exact hn

private lemma coeff_comp_eq_coeff_aeval_of {f g n N} (h : f.HasComp g (R := R))
    (hN : ∀ m, N ≤ m → coeff R m f * coeff R n (g^m) = 0) :
    coeff R n (f ∘ᶠ g) = coeff R n (aeval g (trunc N f)) := by
  by_cases h' : N ≤ (h n).choose
  · rw [coeff_comp_eq_coeff_aeval_trunc]
    apply coeff_aeval_trunc_of_zero hN h'
  · rw [not_le] at h'
    apply coeff_comp_eq_coeff_aeval_of_le
    apply le_of_lt h'

theorem coe_comp_eq_aeval (f : R[X]) (g : R⟦X⟧):
    f ∘ᶠ g = aeval g f := by
  ext n
  have := trunc_coe_eq_self f.natDegree.lt_succ_self
  nth_rw 3 [←this]
  apply coeff_comp_eq_coeff_aeval_of coe_HasComp
  intro m hm
  rw [succ_le] at hm
  apply mul_eq_zero_of_left
  rw [Polynomial.coeff_coe]
  apply coeff_eq_zero_of_natDegree_lt hm

theorem trunc_comp_eq_sum_range {n f g} :
    (trunc n f) ∘ᶠ g = ∑ i in range n, C R (coeff R i f) * g ^ i := by
  rw [coe_comp_eq_aeval, aeval_trunc_eq_sum_range]
  simp_rw [smul_eq_C_mul]

theorem coe_comp_eq_sum_range (f : R[X]) (g):
    f ∘ᶠ g = ∑ i in range (natDegree f + 1), C R (f.coeff i) * g ^ i := by
  rw [coe_comp_eq_aeval, aeval_eq_sum_range]
  simp_rw [smul_eq_C_mul]

lemma coeff_comp_of_stable {f g : R⟦X⟧} {n N} (h : f.HasComp g)
    (hN : ∀ m, N ≤ m → coeff R m f * coeff R n (g^m) = 0) :
    coeff R n (f ∘ᶠ g) = coeff R n (trunc N f ∘ᶠ g) := by
  rw [coeff_comp_eq_coeff_aeval_of h hN, coe_comp_eq_aeval]

private lemma coeff_comp_stable {f g : R⟦X⟧} (h : f.HasComp g) (d : ℕ) :
    ∃ N, ∀ n, N ≤ n → coeff R d (f ∘ᶠ g) = coeff R d (trunc n f ∘ᶠ g) := by
  use (h d).choose
  intro _ h
  rw [coeff_comp_eq_coeff_aeval_of_le h, coe_comp_eq_aeval]

theorem add_comp {f g h : R⟦X⟧} (hf : f.HasComp h) (hg : g.HasComp h) :
    (f + g) ∘ᶠ h = f ∘ᶠ h + g ∘ᶠ h := by
  have hfg := add_HasComp hf hg
  ext d
  obtain ⟨Nf,hNf⟩ := coeff_comp_stable hf d
  obtain ⟨Ng,hNg⟩ := coeff_comp_stable hg d
  obtain ⟨Nfg,hNfg⟩ := coeff_comp_stable hfg d
  let N := max (max Nf Ng) Nfg
  rw [map_add, hNf N, hNg N, hNfg N, coe_comp_eq_aeval, coe_comp_eq_aeval, coe_comp_eq_aeval,
    trunc_add, aeval_add, map_add]
  apply le_max_right
  apply le_max_of_le_left <| Nat.le_max_right Nf Ng
  apply le_max_of_le_left <| le_max_left Nf Ng

@[simp] theorem one_comp {f : R⟦X⟧} : 1 ∘ᶠ f = 1 := by
  rw [←Polynomial.coe_one, coe_comp_eq_aeval, aeval_one, Polynomial.coe_one]

@[simp] theorem zero_comp {f : R⟦X⟧} : 0 ∘ᶠ f = 0 := by
  rw [←Polynomial.coe_zero, coe_comp_eq_aeval, aeval_zero, Polynomial.coe_zero]

@[simp] lemma C_comp {f : R⟦X⟧} {a} : (C R a) ∘ᶠ f = C R a := by
  rw [←Polynomial.coe_C, coe_comp_eq_aeval, aeval_C, Polynomial.coe_C, C_eq_algebraMap]

@[simp] theorem X_comp (f : R⟦X⟧) : X ∘ᶠ f = f := by
  rw [←Polynomial.coe_X, coe_comp_eq_aeval, aeval_X]

end CommutativeSemiring
end PowerSeries
