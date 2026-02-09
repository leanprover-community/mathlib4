/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Richard M. Hill, Paul Lezeau.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Definitions

Let `R` be a commutative semiring.
Give two formal power series `f(X)` and `g(X)` with coefficients in `R`,
their formal composition, when it exists, is the power series

  `f ( g ( X )) = ∑ₙ fₙ * g^n`

I.e the `d`-th coefficient of the composition is the sum

  `∑ₙ fₙ * coeff d (g ^ n)`.

The formal composition exists when all of these sums have finite support. This happens for example
when `f` is a polynomial, or when the constant term of `g` is nilpotent. There are also other cases
where the composition is defined, although these are less easy to describe and depend very much on
`R`.

In this file we define

- `PowerSeries.hasComp` : a relation on `R⟦X⟧`, where `f.hasComp g` means that the formal
  composition of `f` and `g` exists.

- `PowerSeries.comp` : a binary operation on `R⟦X⟧`, where `f.comp g` is the formal composition in
  the case `f.hasComp g`, or zero otherwise.

- `PowerSeries.hasCompRing g` : the subsemiring of `R⟦X⟧` whose elements are those `f` satisfying
  `f.hasComp g`.

- `PowerSeries.compRinghom g` : the ring homomorphism `g.hasCompRing → R⟦X⟧` defined by
  `f ↦ f.comp g`.


## Notation

The operation `f.comp g` can also be written `f ∘ᶠ g`.


## Main results

  `add_hasComp` if `f.hasComp h` and `g.hasComp h` then `(f+g).hasComp h`.
  `mul_hasComp` if `f.hasComp h` and `g.hasComp h` then `(f*g).hasComp h`.
  `coe_hasComp` if `f` is a polynomial then `f.hasComp h`.
  `hasComp_of_isNilpotent_constantCoeff` if the constant term of `g` is nilpotent then
    `f.hasComp g`.
  `hasComp_iff` if `R` is a domain then `f.hasComp g` iff `f` is a polynomial or `g` has constant
    term `0`.
  `hasComp_iff'` if all zero-divisors of `R` are nilpotent then then `f.hasComp g` iff `f` is a
    polynomial or `g` has milpotent constant term.
  `add_comp` if `f.hasComp h` and `g.hasComp h` then `(f + g) ∘ᶠ h = f ∘ᶠ h + g ∘ᶠ h`.
  `mul_comp` if `f.hasComp h` and `g.hasComp h` then `(f * g) ∘ᶠ h = f ∘ᶠ h * g ∘ᶠ h`.
  `coe_comp_eq_eval₂` if `f` is a polynomial then `f ∘ᶠ g = f.eval₂ (C R) g`.
  `coe_comp_assoc` if `f` is a polynomial and `g.hasComp h` then `(f ∘ᶠ g) ∘ᶠ h = f ∘ᶠ (g ∘ᶠ h)`
  `comp_assoc` if the constant terms of `g` and `h` are nilpotent then
    `(f ∘ᶠ g) ∘ᶠ h = f ∘ᶠ (g ∘ᶠ h)`.

(I do not know whether the associativity is true whenever both sides are
defined; I suspect that for certain `R` this is not true.)

In particular, the results imply that for a fixed `g : R⟦X⟧`, the set of `f` satisfying
`f.hasComp g` is a subring of `R⟦X⟧` containing all polynomials. Furthermore, the map `f ↦ f ∘ᶠ g`
is a ring homomorphism.

## TODO
Prove that if the constant term of `f` is zero and the coefficient of `X` is a unit
then there exists a `g`, such that `f ∘ᶠ g = g ∘ᶠ f = X`. I.e. `g` is an inverse of `f`
for the operation `∘ᶠ`.
-/


open Nat Polynomial Finset Polynomial Finset.Nat

namespace PowerSeries

section CommutativeSemiring
variable {R : Type*} [CommSemiring R]


/-- `f.hasComp g` states that the power series `g` may be substituted into
the power series `f = ∑ₙ fₙ * Xⁿ` to give a new power series, whose `d`-coefficient is

  `∑ₙ fₙ * coeff d (g ^ n)`

For the formal composition to make sense, we require that each of these sums
has finite support. There are two common situations when `f.hasComp g`:
either `f` could be a polynomial or the constant term of `g` could be zero.
However, there are other intermediate cases if `R` is not an integral domain.
-/
def hasComp (f g : R⟦X⟧) : Prop :=
  ∀ d, ∃ (N : ℕ), ∀ n, N ≤ n → (coeff n f) * coeff d (g^n) = 0

open Classical in
/-- Formal composition of power series. If `f.hasComp g` then `f ∘ᶠ g` is defined in the usual way.
If not then `f ∘ᶠ g` defaults to `0`. -/
noncomputable def comp (f g : R⟦X⟧) : R⟦X⟧ :=
  if h : f.hasComp g
    then mk (fun d ↦ coeff d ((trunc (h d).choose f).eval₂ (C (R := R)) g ))
  else 0

@[inherit_doc comp]
scoped infixr:90 " ∘ᶠ "  => PowerSeries.comp

/-
## Criteria for `hasComp`

The relation `hasComp` seems quite difficult to describe. It is neither symmetric,
reflexive, nor transitive. It can happen that `f.hasComp g` and `g.hasComp h` but
`¬f.hasComp (g ∘ ᶠh)` and `¬(f ∘ᶠ g).hasComp h`.
For example, we may take `g = X` and `h = 1`, and almost any `f`.
-/


variable {f g : R⟦X⟧}

private lemma Finite_support_of_hasComp (h : f.hasComp g (R := R)) (d : ℕ) :
  Set.Finite <| Function.support <| fun n ↦ coeff n f * coeff d (g ^ n) := by
  obtain ⟨N, hN⟩ := h d
  apply Set.Finite.subset (s := range N) (finite_toSet (range N))
  intro x
  contrapose
  simpa [coe_range, Set.mem_Iio, not_lt, Function.mem_support, ne_eq, not_not] using hN x

private lemma X_pow_dvd_pow_of_isNilpotent_constantCoeff (d : ℕ)
    (hg : IsNilpotent (constantCoeff g)) : ∃ N, X^d ∣ g^N := by
  obtain ⟨N, hN⟩ := hg
  use N * d
  rw [pow_mul]
  apply pow_dvd_pow_of_dvd
  rwa [X_dvd_iff, map_pow]

lemma hasComp_of_isNilpotent_constantCoeff {f : R⟦X⟧} (hg : IsNilpotent (constantCoeff g)) :
  f.hasComp g := by
  intro d
  obtain ⟨N, hN⟩ := X_pow_dvd_pow_of_isNilpotent_constantCoeff d.succ hg
  use N
  intro n hn
  have : X ^ d.succ ∣ g^n := by
    trans g ^ N
    · exact hN
    · apply pow_dvd_pow (h := hn)
  rw [X_pow_dvd_iff] at this
  rw [this, mul_zero]
  exact lt_add_one d

lemma hasComp_of_constantCoeff_eq_zero (hg : constantCoeff g = 0) : hasComp f g := by
  apply hasComp_of_isNilpotent_constantCoeff
  rw [hg]
  exact IsNilpotent.zero

lemma coe_hasComp {f : R[X]} : (f : R⟦X⟧).hasComp g := by
  intro
  use f.natDegree + 1
  intro _ hn
  rwa [Polynomial.coeff_coe, coeff_eq_zero_of_natDegree_lt, zero_mul]

lemma zero_hasComp : hasComp 0 f (R := R) := by
  rw [←Polynomial.coe_zero]
  apply coe_hasComp

lemma one_hasComp : hasComp 1 f (R := R) := by
  rw [←Polynomial.coe_one]
  apply coe_hasComp

variable {r}

lemma C_hasComp : (C r).hasComp f := by
  rw [←Polynomial.coe_C]
  apply coe_hasComp

lemma X_hasComp : X.hasComp f (R := R) := by
  rw [←Polynomial.coe_X]
  apply coe_hasComp

lemma add_hasComp {f₁ f₂ g : R⟦X⟧} (h₁ : f₁.hasComp g) (h₂ : f₂.hasComp g) :
  (f₁ + f₂).hasComp g := by
  intro d
  obtain ⟨N₁,hN₁⟩ := h₁ d
  obtain ⟨N₂,hN₂⟩ := h₂ d
  use max N₁ N₂
  intro _ hn
  rw [map_add, add_mul, hN₁, hN₂, add_zero]
  · exact le_of_max_le_right hn
  · exact le_of_max_le_left hn

lemma uniform_stable_of_hasComp (hfg : f.hasComp g) (n : ℕ) :
  ∃ N : ℕ, ∀ d m : ℕ, d ≤ n → N ≤ m → (coeff m f) * coeff d (g ^ m) = 0 := by
  have : ((range n.succ).image (fun d ↦ (hfg d).choose)).Nonempty := by grind [Nonempty.image]
  use Finset.max' _ this
  intro d _ hdm hm
  apply (hfg d).choose_spec
  grind [max'_le_iff]


lemma mul_hasComp {f₁ f₂ : R⟦X⟧} (h₁ : f₁.hasComp g) (h₂ : f₂.hasComp g) : (f₁ * f₂).hasComp g := by
  intro d
  obtain ⟨N₁,hN₁⟩ := uniform_stable_of_hasComp h₁ d
  obtain ⟨N₂,hN₂⟩ := uniform_stable_of_hasComp h₂ d
  use N₁ + N₂
  intro _ hm
  rw [coeff_mul, sum_mul, sum_eq_zero]
  intro ⟨i,j⟩ hij
  rw [←mem_antidiagonal.mp hij, pow_add, coeff_mul, mul_sum, sum_eq_zero]
  intro ⟨r,s⟩ hrs
  rw [mul_assoc, mul_comm (coeff j f₂), mul_assoc, ←mul_assoc]
  rw [←mem_antidiagonal.mp hij] at hm
  cases le_or_le_of_add_le_add hm with
  | inl h => grind [mul_eq_zero_of_left, mem_antidiagonal]
  | inr h => grind [mul_eq_zero_of_right, mul_comm, mem_antidiagonal]

/-- The ring of power series `f` for which `f.comp g` exists. -/
def hasCompRing (g : R⟦X⟧) : Subsemiring R⟦X⟧ where
  carrier   := fun f ↦ f.hasComp g
  mul_mem'  := mul_hasComp
  one_mem'  := one_hasComp
  add_mem'  := add_hasComp
  zero_mem' := zero_hasComp

lemma mem_hasCompRing {f g : R⟦X⟧} :
  f ∈ hasCompRing g ↔ f.hasComp g := by
  rfl

variable {A : Type*}

theorem sum_hasComp {S : Finset A} {f : A → R⟦X⟧}
  (h : ∀ s : A, s ∈ S → (f s).hasComp g) :
  (∑ s ∈ S, f s).hasComp g := by
  rw [←mem_hasCompRing]
  exact sum_mem h

theorem prod_hasComp {S : Finset A} {f : A → R⟦X⟧}
  (h : ∀ s : A, s ∈ S → (f s).hasComp g) :
  (∏ s ∈ S, f s).hasComp g := by
  rw [←mem_hasCompRing]
  exact prod_mem h

theorem pow_hasComp {f g : R⟦X⟧} {n : ℕ} (h : f.hasComp g) :
  (f ^ n).hasComp g := by
  rw [←mem_hasCompRing] at h ⊢
  exact pow_mem h n

variable {S : Type*}

theorem map_hasComp_map [CommSemiring S] (γ : R →+* S) (h : f.hasComp g (R := R)) :
  (map γ f).hasComp (map γ g) := by
  intro d
  obtain ⟨N, hN⟩ := h d
  use N
  intro n hn
  rw [coeff_map, ←map_pow, coeff_map, ←map_mul, hN n hn, map_zero]

/--
If every zero-divisor of `R` is nilpotent then `f.hasComg g`
if and only if `f` is a polynomial or `g` has nilpotent constant term.
This criterion on `R` is satisfied for example by a domain, or by `ℤ⧸p^n`
for a prime number `p`.
-/
theorem hasComp_iff' (hR : ∀ x : R, IsNilpotent x ∨ x ∈ nonZeroDivisors R) {f g : R⟦X⟧} :
    f.hasComp g ↔ (∃ p : R[X], f = p) ∨ IsNilpotent (constantCoeff g) where
  mp h := by
    by_contra! h'
    obtain ⟨N, hN⟩ := h 0
    suffices f = trunc N f by grind
    ext d
    rw [Polynomial.coeff_coe, coeff_trunc]
    split_ifs with h''
    · rfl
    · specialize hN d (not_lt.mp h'')
      rwa [coeff_zero_eq_constantCoeff, map_pow, mul_right_mem_nonZeroDivisors_eq_zero_iff] at hN
      apply pow_mem (by grind)
  mpr := by grind [coe_hasComp, hasComp_of_isNilpotent_constantCoeff]

/-- This is a convenient special case of the lemma `hasComp_iff'`
for the case when `R` is a domain. -/
theorem hasComp_iff [IsDomain R] {f g : R⟦X⟧} :
    f.hasComp g ↔ (∃ p : R[X], f = p) ∨ constantCoeff g = 0 := by
  grind [isNilpotent_iff_eq_zero, hasComp_iff', mem_nonZeroDivisors_iff_ne_zero]

/-
Some lemmas allowing us to calculate compositions.
-/

-- PAUL: cleaned up to here.


theorem comp_eq (h : f.hasComp g) :
    f ∘ᶠ g = mk fun n ↦ coeff n ((trunc (h n).choose f).eval₂ C g) := by
  rw [comp, dif_pos h]

lemma comp_eq_zero (h : ¬f.hasComp g) : f ∘ᶠ g  = 0 := by
  rw [comp, dif_neg h]

variable {n : ℕ}

lemma coeff_comp_def (h : f.hasComp g) :
    coeff n (f ∘ᶠ g) = coeff n ((trunc (h n).choose f).eval₂ C g) := by
  rw [comp, dif_pos h, coeff_mk]

lemma coeff_comp_eq_finsum (h : f.hasComp g) :
    coeff n (f ∘ᶠ g) = ∑ᶠ d : ℕ, coeff d f * coeff n (g ^ d) := by
  simp_rw [coeff_comp_def h, eval₂_trunc_eq_sum_range, map_sum, coeff_C_mul]
  symm
  apply finsum_eq_sum_of_support_subset
  grind [Function.mem_support, coe_range]

variable {N M d : ℕ}

private lemma coeff_trunc_eval₂_of_zero
  (hN : ∀ m, N ≤ m → coeff m f * coeff n (g ^ m) = 0) (hM : N ≤ M) :
  coeff n ((trunc M f).eval₂ C g) = coeff n ((trunc N f).eval₂ C g) := by
  induction hM with
  | refl => rfl
  | step ih1 ih2 => simp [trunc_succ, ih2, hN _ ih1]

private lemma coeff_comp_eq_coeff_eval₂_stable {h : f.hasComp g (R := R)}
    (hn : (h d).choose ≤ n := by rfl) :
  coeff d (f ∘ᶠ g) = coeff d ((trunc n f).eval₂ C g) := by
  rw [coeff_comp_def h]
  exact (coeff_trunc_eval₂_of_zero (h d).choose_spec hn).symm

private lemma coeff_comp_eq_coeff_eval₂_of_stable (h : f.hasComp g (R := R))
    (hN : ∀ m, N ≤ m → coeff m f * coeff n (g ^ m) = 0) :
  coeff n (f ∘ᶠ g) = coeff n ((trunc N f).eval₂ C g) := by
  by_cases h' : N ≤ (h n).choose
  · rw [coeff_comp_def h]
    apply coeff_trunc_eval₂_of_zero hN h'
  · apply coeff_comp_eq_coeff_eval₂_stable <| le_of_lt <| not_le.mp h'

theorem coe_comp_eq_eval₂ (f : R[X]) :
  f ∘ᶠ g = f.eval₂ C g := by
  ext n
  nth_rw 2 [← trunc_coe_eq_self f.natDegree.lt_succ_self]
  apply coeff_comp_eq_coeff_eval₂_of_stable coe_hasComp
  intro m hm
  rw [succ_le_iff] at hm
  apply mul_eq_zero_of_left
  rw [Polynomial.coeff_coe]
  apply coeff_eq_zero_of_natDegree_lt hm

theorem trunc_comp_eq_sum_range :
    (trunc n f) ∘ᶠ g = ∑ i ∈ range n, C (coeff i f) * g ^ i := by
  rw [coe_comp_eq_eval₂, eval₂_trunc_eq_sum_range]

theorem coe_comp_eq_sum_range (f : R[X]) :
  f ∘ᶠ g = ∑ i ∈ range (natDegree f + 1), C (f.coeff i) * g ^ i := by
  rw [coe_comp_eq_eval₂, eval₂_eq_sum_range]

theorem coe_comp_hasComp (f : R[X]) (h : R⟦X⟧) (hgh : g.hasComp h (R := R)) :
  (f ∘ᶠ g).hasComp h := by
  rw [coe_comp_eq_eval₂, eval₂_eq_sum]
  apply sum_hasComp (fun _ _ => mul_hasComp C_hasComp <| pow_hasComp hgh)

private lemma coeff_comp_of_constantCoeff_eq_zero (h : constantCoeff g = 0) :
  coeff n (f ∘ᶠ g) = coeff n ((trunc (n+1) f).eval₂ C g) := by
  apply coeff_comp_eq_coeff_eval₂_of_stable
  apply hasComp_of_constantCoeff_eq_zero
  exact h
  intro m hm
  rw [succ_le_iff] at hm
  apply mul_eq_zero_of_right
  have : X^m ∣ g^m := by
    apply pow_dvd_pow_of_dvd
    rw [X_dvd_iff, h]
  rw [X_pow_dvd_iff] at this
  apply this
  exact hm

theorem constantCoeff_comp (h : constantCoeff g = 0) :
  constantCoeff (f ∘ᶠ g) = constantCoeff f := by
  rw [←coeff_zero_eq_constantCoeff, coeff_comp_of_constantCoeff_eq_zero h,
    zero_add, eval₂_trunc_eq_sum_range, sum_range_one,
    pow_zero, mul_one, coeff_zero_C]

lemma coeff_comp_of_stable (h : f.hasComp g) (hN : ∀ m, N ≤ m → coeff m f * coeff n (g ^ m) = 0) :
    coeff n (f ∘ᶠ g) = coeff n (trunc N f ∘ᶠ g) := by
  rw [coeff_comp_eq_coeff_eval₂_of_stable h hN, coe_comp_eq_eval₂]

private lemma coeff_comp_stable (h : f.hasComp g (R := R)) (d : ℕ) :
    ∃ N, ∀ n, N ≤ n → coeff d (f ∘ᶠ g) = coeff d (trunc n f ∘ᶠ g) := by
  use (h d).choose
  intro n hn
  rw [coeff_comp_eq_coeff_eval₂_stable hn, coe_comp_eq_eval₂]

private lemma trunc_comp_stable (hfg : hasComp f g (R := R)) (d : ℕ) :
    ∃ N, ∀ n, N ≤ n → trunc d (f ∘ᶠ g) = trunc d (trunc n f ∘ᶠ g) := by
  obtain ⟨N, hN⟩ := uniform_stable_of_hasComp hfg d
  use N
  intro n hn
  ext m
  rw [coeff_trunc, coeff_trunc]
  split
  · induction hn with
    | refl =>
      apply coeff_comp_of_stable hfg
      intro r
      apply hN
      apply le_of_lt
      assumption
    | step hm ih =>
      rw [coe_comp_eq_eval₂, trunc_succ, eval₂_add, map_add, eval₂_monomial,
  coeff_C_mul, hN, add_zero, ih, coe_comp_eq_eval₂]
      apply le_of_lt
      assumption
      assumption
  rfl

theorem hasComp_C_constantCoeff {f g : R⟦X⟧} (h : f.hasComp g) :
  f.hasComp (C (constantCoeff g)) := by
  intro d
  cases d with
  | zero =>
    obtain ⟨N, hN⟩ := h 0
    use N
    simpa only [coeff_zero_eq_constantCoeff, map_pow, constantCoeff_C] using hN
  | succ n =>
    use 0
    intros
    rw [←map_pow, coeff_C, if_neg n.succ_ne_zero, mul_zero]

theorem C_constantCoeff_comp_eq_constantCoeff_C_comp (h : f.hasComp g (R := R)) :
  C (constantCoeff (f ∘ᶠ g)) = f ∘ᶠ (C (constantCoeff g)) := by
  obtain ⟨N, hN⟩ := h 0
  ext d
  cases d with
  | zero =>
    rw [coeff_zero_eq_constantCoeff, constantCoeff_C,
      ←coeff_zero_eq_constantCoeff, coeff_comp_of_stable h hN,
      coeff_comp_of_stable (g := C _) (N := N),
      coeff_zero_eq_constantCoeff, trunc_comp_eq_sum_range,
      trunc_comp_eq_sum_range,
      map_sum, map_sum]
    apply sum_congr rfl
    intros
    rw [map_mul, map_mul, constantCoeff_C, map_pow, map_pow, constantCoeff_C, ←map_pow]
    · rw [coeff_zero_eq_constantCoeff]
      exact hasComp_C_constantCoeff h
    · intro n hn
      specialize hN n hn
      rw [coeff_zero_eq_constantCoeff, map_pow] at hN
      rwa [coeff_zero_eq_constantCoeff, map_pow, constantCoeff_C]
  | succ n =>
      rw [coeff_C, if_neg n.succ_ne_zero, coeff_comp_def, eval₂_trunc_eq_sum_range,
        map_sum]
      symm
      apply sum_eq_zero
      intros
      rw [←map_pow, ←map_mul, coeff_C, if_neg n.succ_ne_zero]
      all_goals
        exact hasComp_C_constantCoeff h


-- variable {h : R⟦X⟧}

-- /--This is the key lemma used in proving `mul_comp`.-/
-- private lemma coeff_mul_comp_stable (hf :f.hasComp h (R := R)) (hg : g.hasComp h) (d : ℕ) :
--   ∃ N , ∀ M, N ≤ M →
--   coeff d ( (f * g) ∘ᶠ h) = coeff d ( ((trunc M f) * (trunc M g) : R⟦X⟧) ∘ᶠ h ) := by
--   have hfg := mul_hasComp hf hg
--   obtain ⟨Nf,hNf⟩ := uniform_stable_of_hasComp hf d
--   obtain ⟨Ng,hNg⟩ := uniform_stable_of_hasComp hg d
--   obtain ⟨Nfg, hNfg⟩ := uniform_stable_of_hasComp hfg d
--   use max (Nf + Ng) Nfg
--   intro M hM
--   rw [coeff_comp_eq_finsum hfg, coeff_comp_eq_finsum]
--   apply finsum_congr
--   intro n
--   by_cases hn : n.succ ≤ M
--   · rw [coeff_stable hn, ←trunc_trunc_mul_trunc, ←coeff_stable hn]
--   · rw [not_le, lt_succ] at hn
--     rw [hNfg, coeff_mul, sum_mul]
--     · symm
--       apply sum_eq_zero
--       intro ⟨i,j⟩ hij
--       rw [mem_antidiagonal] at hij
--       dsimp at hij ⊢
--       rw [←hij, pow_add, coeff_mul, mul_sum]
--       apply sum_eq_zero
--       intro ⟨r,s⟩ hrs
--       rw [mem_antidiagonal] at hrs
--       dsimp at hrs ⊢
--       rw [mul_assoc, mul_comm (coeff j _), mul_assoc, ←mul_assoc]
--       have : Nf ≤ i ∨ Ng ≤ j
--       · apply le_or_le_of_add_le_add
--         rw [hij]
--         trans M
--         exact le_of_max_le_left hM
--         exact hn
--       cases this with
--       | inl h =>
--         apply mul_eq_zero_of_left
--         rw [Polynomial.coeff_coe, coeff_trunc]
--         split
--         · exact hNf _ _ (le.intro hrs) h
--         · apply zero_mul
--       | inr h =>
--         apply mul_eq_zero_of_right
--         rw [mul_comm, Polynomial.coeff_coe, coeff_trunc]
--         split
--         · apply hNg _ _ (le_of_add_le_right <| le_of_eq hrs) h
--         · apply zero_mul
--     · rfl
--     · trans M
--       apply le_of_max_le_right hM
--       exact hn
--   rw [←Polynomial.coe_mul]
--   exact coe_hasComp
--   sorry


-- theorem mul_comp (hf : f.hasComp h (R := R)) (hg : g.hasComp h) :
--   (f * g) ∘ᶠ h = f ∘ᶠ h * g ∘ᶠ h := by sorry
--   -- ext d
--   -- obtain ⟨Nfg,hNfg⟩ := coeff_mul_comp_stable hf hg d
--   -- have hN_mul := coeff_mul_stable (f ∘ᶠ h) (g ∘ᶠ h) (d := d)
--   -- rw [hN_mul]
--   -- obtain ⟨Nf,hNf⟩ := trunc_comp_stable hf d.succ
--   -- obtain ⟨Ng,hNg⟩ := trunc_comp_stable hg d.succ
--   -- set N := Nfg.max (Nf.max Ng)
--   -- rw [hNf N, hNg N, hNfg N]
--   -- symm
--   -- rw [coeff_stable, trunc_trunc_mul_trunc, coe_comp_eq_eval₂, coe_comp_eq_eval₂,
--   --   ←Polynomial.coe_mul, coe_comp_eq_eval₂, eval₂_mul, ←coeff_stable]
--   -- apply le_max_left
--   -- apply le_of_max_le_right
--   -- apply le_max_right
--   -- apply le_of_max_le_left
--   -- apply le_max_right


-- theorem add_comp (hf : f.hasComp h (R := R)) (hg : g.hasComp h) :
--   (f + g) ∘ᶠ h = f ∘ᶠ h + g ∘ᶠ h := by sorry
--   -- have hfg := add_hasComp hf hg
--   -- ext d
--   -- obtain ⟨Nf,hNf⟩ := coeff_comp_stable hf d
--   -- obtain ⟨Ng,hNg⟩ := coeff_comp_stable hg d
--   -- obtain ⟨Nfg,hNfg⟩ := coeff_comp_stable hfg d
--   -- set N := max (max Nf Ng) Nfg
--   -- rw [map_add, hNf N, hNg N, hNfg N, coe_comp_eq_eval₂, coe_comp_eq_eval₂, coe_comp_eq_eval₂,
--   --   trunc_add, eval₂_add, map_add]
--   -- apply le_max_right
--   -- apply le_max_of_le_left
--   -- apply le_max_right
--   -- apply le_max_of_le_left
--   -- apply le_max_left

-- @[simp]
-- theorem one_comp {f : R⟦X⟧} : 1 ∘ᶠ f = 1 := by
--   rw [←Polynomial.coe_one, coe_comp_eq_eval₂, eval₂_one, Polynomial.coe_one]

-- @[simp]
-- theorem zero_comp {f : R⟦X⟧} : 0 ∘ᶠ f = 0 := by
--   rw [←Polynomial.coe_zero, coe_comp_eq_eval₂, eval₂_zero, Polynomial.coe_zero]

-- /--
-- The map `f ↦ f ∘ᶠ g` as a ring homomorphism.
-- -/
-- noncomputable def compRinghom (g : R⟦X⟧) : hasCompRing g →+* R⟦X⟧ where
--   toFun := fun f ↦ f ∘ᶠ g
--   map_zero' := zero_comp
--   map_one'  := one_comp
--   map_add'  := fun f₁ f₂ ↦ sorry-- add_comp f₁.prop f₂.prop
--   map_mul'  := fun f₁ f₂ ↦ sorry --mul_comp f₁.prop f₂.prop

-- lemma compRinghom_def (f : hasCompRing g (R := R)) :
--   compRinghom g f = f ∘ᶠ g :=
--   rfl

-- lemma comp_eq_compRinghom (hfg : f.hasComp g (R := R)) :
--   f ∘ᶠ g = compRinghom g ⟨f,hfg⟩ :=
--   rfl

-- theorem sum_comp {S : Finset A} {f : A → R⟦X⟧}
--   (h : ∀ s : A, s ∈ S → (f s).hasComp g) :
--   (∑ s ∈ S, f s) ∘ᶠ g = ∑ s ∈ S, (f s) ∘ᶠ g := by
--   /-
--   The obvious proof (using `map_sum` and `AddSubgroup.val_finset_sum`)
--   turns out to be longer than the induction proof given here.
--   -/
--   induction S using Finset.induction
--   case empty =>
--     rw [sum_empty, sum_empty, zero_comp]
--   case insert not_mem ih =>
--     rw [sum_insert not_mem, sum_insert not_mem, add_comp, ih]
--     · intro _ ht
--       apply h _ (mem_insert_of_mem ht)
--     · apply h _ (mem_insert_self _ _)
--     · apply sum_hasComp
--       intro _ ht
--       apply h _ (mem_insert_of_mem ht)

-- theorem prod_comp {S : Finset A} {f : A → R⟦X⟧}
--   (h : ∀ s : A, s ∈ S → (f s).hasComp g) :
--   (∏ s ∈ S, f s) ∘ᶠ g = ∏ s ∈ S, (f s) ∘ᶠ g := by
--   induction S using Finset.induction
--   case empty =>
--     rw [prod_empty, prod_empty, one_comp]
--   case insert not_mem ih =>
--     rw [prod_insert not_mem, prod_insert not_mem, mul_comp, ih]
--     · intro _ ht
--       apply h _ (mem_insert_of_mem ht)
--     · apply h _ (mem_insert_self _ _)
--     · apply prod_hasComp
--       intro _ ht
--       apply h _ (mem_insert_of_mem ht)

-- theorem pow_comp (h : f.hasComp g (R := R)):
--   (f ^ n) ∘ᶠ g = (f ∘ᶠ g) ^ n := by
--   sorry
--   -- rw [comp_eq_compRinghom (pow_hasComp h), comp_eq_compRinghom h, ←map_pow]
--   -- rfl

-- @[simp]
-- theorem comp_zero : f ∘ᶠ 0 = C (constantCoeff f) := by
--   sorry
--   -- ext n
--   -- rw [coeff_comp_of_constantCoeff_eq_zero (by rw [map_zero]),
--   --   eval₂_at_zero, coeff_trunc,
--   --   coeff_zero_eq_constantCoeff, coeff_C]
--   -- split_ifs with h₁ h₂
--   -- · rw [h₁, coeff_zero_eq_constantCoeff, constantCoeff_C]
--   -- · cases h₂ (zero_lt_succ n)
--   -- · rw [coeff_C, if_neg h₁]

-- variable {a : R}

-- @[simp]
-- lemma C_comp : (C a) ∘ᶠ f = C a := by
--   -- rw [←Polynomial.coe_C, coe_comp_eq_eval₂, eval₂_C, Polynomial.coe_C]
--   sorry


-- theorem coe_comp_assoc {f : R[X]} (hgh : g.hasComp h (R := R)) :
--   (f ∘ᶠ g) ∘ᶠ h = f ∘ᶠ (g ∘ᶠ h) := by
--   sorry
--   -- rw [coe_comp_eq_sum_range, sum_comp, coe_comp_eq_sum_range]
--   -- apply sum_congr rfl
--   -- intros
--   -- rw [mul_comp, C_comp, pow_comp]
--   -- · assumption
--   -- · exact C_hasComp
--   -- · apply pow_hasComp hgh
--   -- · intros
--   --   exact mul_hasComp C_hasComp (pow_hasComp hgh)

-- @[simp]
-- theorem comp_X (f : R⟦X⟧) : f ∘ᶠ X = f := by
--   sorry
--   -- ext n
--   -- rw [coeff_comp_of_constantCoeff_eq_zero constantCoeff_X,
--   --   eval₂_C_X_eq_coe, ←coeff_stable]

-- @[simp]
-- theorem X_comp (f : R⟦X⟧) : X ∘ᶠ f = f := by
--   sorry
--   -- rw [←Polynomial.coe_X, coe_comp_eq_eval₂, eval₂_X]


-- theorem IsNilpotent_constantCoeff_comp
--   (hf : IsNilpotent (constantCoeff f)) (hg : IsNilpotent (constantCoeff g)) :
--   IsNilpotent (constantCoeff (f ∘ᶠ g)) := by
--   sorry
--   -- have hfg : f.hasComp g := hasComp_of_isNilpotent_constantCoeff hg
--   -- rw [←coeff_zero_eq_constantCoeff_apply, coeff_comp_def hfg,
--   --   eval₂_trunc_eq_sum_range, map_sum]
--   -- apply isNilpotent_sum
--   -- intro i hi
--   -- rw [coeff_zero_eq_constantCoeff_apply, map_mul]
--   -- cases i with
--   -- | zero =>
--   --   apply Commute.isNilpotent_mul_left
--   --   apply Commute.all
--   --   rw [zero_eq, coeff_zero_eq_constantCoeff, constantCoeff_C]
--   --   exact hf
--   -- | succ n =>
--   --   apply Commute.isNilpotent_mul_right
--   --   apply Commute.all
--   --   rw [map_pow]
--   --   apply IsNilpotent.pow_succ hg

-- private lemma uniform_bound_of_isNilpotent (hg : IsNilpotent (constantCoeff g)) (d : ℕ) :
--   ∃ N, ∀ f : R⟦X⟧, coeff d (f ∘ᶠ g) = ∑ n ∈ range N, coeff n f * coeff d (g ^ n) := by
--   sorry
--   -- obtain ⟨N, hN⟩ := X_pow_dvd_pow_of_isNilpotent_constantCoeff (g := g) d.succ hg
--   -- use N
--   -- intro f
--   -- have hfg : f.hasComp g := hasComp_of_isNilpotent_constantCoeff hg
--   -- rw [coeff_comp_eq_finsum hfg]
--   -- apply finsum_eq_sum_of_support_subset
--   -- intro x
--   -- contrapose
--   -- intro hx
--   -- rw [coe_range, Set.mem_Iio, not_lt] at hx
--   -- rw [Function.mem_support, not_not]
--   -- apply mul_eq_zero_of_right
--   -- have : X^d.succ ∣ g^x
--   -- · trans g^N
--   --   exact hN
--   --   apply pow_dvd_pow (h := hx)
--   -- rw [X_pow_dvd_iff] at this
--   -- exact this d d.lt_succ_self


-- lemma hasComp_comp {f : R⟦X⟧} (hfg : f.hasComp g) (hh : IsNilpotent (constantCoeff h)) :
--   f.hasComp (g ∘ᶠ h) := by
--   sorry
--   -- intro d
--   -- obtain ⟨Nh, hNh⟩ := uniform_bound_of_isNilpotent hh d
--   -- obtain ⟨N, hN⟩ := uniform_stable_of_hasComp hfg Nh
--   -- have hgh : g.hasComp h := hasComp_of_isNilpotent_constantCoeff hh
--   -- use N
--   -- intro n hn
--   -- rw [←pow_comp hgh, hNh, mul_sum]
--   -- apply sum_eq_zero
--   -- intro m hm
--   -- rw [←mul_assoc]
--   -- apply mul_eq_zero_of_left
--   -- apply hN
--   -- apply le_of_lt
--   -- rwa [mem_range] at hm
--   -- exact hn


-- /-
-- Although I don't have a counterexample, it seems unlikely to me that composition
-- of formal power series is always associative, even in the case when none of the terms
-- default to zero.

-- However, composition is associative in the most familiar cases, where constant term
-- is nilpotent.
-- -/
-- theorem comp_assoc (hfg : f.hasComp g (R := R)) (hh : IsNilpotent (constantCoeff h)):
--   (f ∘ᶠ g) ∘ᶠ h = f ∘ᶠ (g ∘ᶠ h) := by sorry
--   -- have hgh : g.hasComp h := hasComp_of_isNilpotent_constantCoeff hh
--   -- have hfgh : f.hasComp (g ∘ᶠ h) := hasComp_comp hfg hh
--   -- ext d
--   -- obtain ⟨Nh, hNh⟩ := uniform_bound_of_isNilpotent (g := h) hh d
--   -- rw [hNh, coeff_comp_eq_finsum hfgh]
--   -- conv =>
--   --   right; right; intro; rw [←pow_comp hgh, hNh, mul_sum]
--   -- rw [finsum_sum_comm]
--   -- apply sum_congr rfl
--   -- intros
--   -- rw [coeff_comp_eq_finsum hfg, finsum_mul]
--   -- apply finsum_congr
--   -- intros
--   -- apply mul_assoc
--   -- · apply Finite_support_of_hasComp hfg
--   -- · intros d _
--   --   apply Set.Finite.subset (hs := Finite_support_of_hasComp hfg d)
--   --   intro
--   --   contrapose
--   --   rw [Function.mem_support, Function.mem_support, not_not, not_not, ←mul_assoc]
--   --   intro hx
--   --   apply mul_eq_zero_of_left hx



-- lemma rescale_eq_comp_mul_X (r : R) :
--   rescale r f = f ∘ᶠ (r • X) := by
--   sorry
--   -- have : constantCoeff (r • X) = 0
--   -- · rw [smul_eq_C_mul, map_mul, constantCoeff_X, mul_zero]
--   -- ext
--   -- rw [coeff_comp_of_constantCoeff_eq_zero this,
--   --   eval₂_trunc_eq_sum_range, map_sum, sum_eq_single _,
--   --   coeff_rescale, coeff_C_mul, smul_pow, coeff_smul,
--   --   coeff_X_pow, if_pos rfl, smul_eq_mul, mul_one, mul_comm]
--   -- · intro _ _ hb
--   --   rw [coeff_C_mul, smul_pow, coeff_smul, coeff_X_pow, if_neg hb.symm,
--   --     smul_zero, mul_zero]
--   -- · intro h
--   --   contrapose h
--   --   rw [not_not, mem_range]
--   --   apply lt_succ_self


-- theorem map_comp' [CommSemiring S]
--   (h : f.hasComp g (R := R)) (γ : R →+* S):
--   map γ (f ∘ᶠ g) = (map γ f) ∘ᶠ (map γ g) := by
--   sorry
--   -- ext d
--   -- obtain ⟨N,hN⟩ := h d
--   -- rw [coeff_map, coeff_comp_of_stable h hN]
--   -- symm
--   -- rw [coeff_comp_of_stable (map_hasComp_map γ h) (N := N), ←coeff_map]
--   -- congr
--   -- rw [trunc_comp_eq_sum_range, trunc_comp_eq_sum_range, map_sum]
--   -- apply sum_congr rfl
--   -- intros
--   -- rw [map_mul, map_pow, coeff_map, map_C]
--   -- intro n hn
--   -- rw [coeff_map, ←map_pow, coeff_map, ←map_mul, hN n hn, map_zero]



-- end CommutativeSemiring


-- variable {R : Type*} (f g : R⟦X⟧)

-- /-NOTE: `instance : Inv R⟦X⟧` is currently only defined
-- when `R` is a field, so the following two results can only be stated in in the case that
-- `R` is a field.
-- The second result `inv_comp` should eventually be extended to the case that
-- `R` is a commutative ring.-/
-- @[simp]
-- theorem inv_comp' [Field R] (hf : constantCoeff f ≠ 0) (hg : constantCoeff g = 0) :
--   f⁻¹ ∘ᶠ g = (f ∘ᶠ g)⁻¹ := by
--   have : (f⁻¹ ∘ᶠ g) * (f ∘ᶠ g) = 1
--   · rw [←mul_comp, PowerSeries.inv_mul_cancel (h := hf), one_comp] <;>
--     apply hasComp_of_constantCoeff_eq_zero (hg := hg)
--   symm
--   rw [MvPowerSeries.inv_eq_iff_mul_eq_one, this]
--   · change constantCoeff (f ∘ᶠ g) ≠ 0
--     by_contra h'
--     have : constantCoeff 1 = 0
--     · rw [←this, map_mul, h', mul_zero]
--     rw [map_one] at this
--     apply one_ne_zero this


-- /-
-- This is the statement which generalizes to all commutative rings
-- (once the instance of `Inv` is created).
-- -/
-- theorem inv_comp [Field R] (hf : IsUnit (constantCoeff f))
--   (hg : IsNilpotent <| constantCoeff g):
--   f⁻¹ ∘ᶠ g = (f ∘ᶠ g)⁻¹ := by
--   apply inv_comp'
--   exact IsUnit.ne_zero hf
--   apply IsReduced.eq_zero
--   assumption



-- end PowerSeries
