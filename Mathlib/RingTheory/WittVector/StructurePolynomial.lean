/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.NumberTheory.Basic
import Mathlib.RingTheory.WittVector.WittPolynomial

#align_import ring_theory.witt_vector.structure_polynomial from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Witt structure polynomials

In this file we prove the main theorem that makes the whole theory of Witt vectors work.
Briefly, consider a polynomial `Φ : MvPolynomial idx ℤ` over the integers,
with polynomials variables indexed by an arbitrary type `idx`.

Then there exists a unique family of polynomials `φ : ℕ → MvPolynomial (idx × ℕ) Φ`
such that for all `n : ℕ` we have (`wittStructureInt_existsUnique`)
```
bind₁ φ (wittPolynomial p ℤ n) = bind₁ (fun i ↦ (rename (prod.mk i) (wittPolynomial p ℤ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

N.b.: As far as we know, these polynomials do not have a name in the literature,
so we have decided to call them the “Witt structure polynomials”. See `wittStructureInt`.

## Special cases

With the main result of this file in place, we apply it to certain special polynomials.
For example, by taking `Φ = X tt + X ff` resp. `Φ = X tt * X ff`
we obtain families of polynomials `witt_add` resp. `witt_mul`
(with type `ℕ → MvPolynomial (Bool × ℕ) ℤ`) that will be used in later files to define the
addition and multiplication on the ring of Witt vectors.

## Outline of the proof

The proof of `wittStructureInt_existsUnique` is rather technical, and takes up most of this file.

We start by proving the analogous version for polynomials with rational coefficients,
instead of integer coefficients.
In this case, the solution is rather easy,
since the Witt polynomials form a faithful change of coordinates
in the polynomial ring `MvPolynomial ℕ ℚ`.
We therefore obtain a family of polynomials `wittStructureRat Φ`
for every `Φ : MvPolynomial idx ℚ`.

If `Φ` has integer coefficients, then the polynomials `wittStructureRat Φ n` do so as well.
Proving this claim is the essential core of this file, and culminates in
`map_wittStructureInt`, which proves that upon mapping the coefficients
of `wittStructureInt Φ n` from the integers to the rationals,
one obtains `wittStructureRat Φ n`.
Ultimately, the proof of `map_wittStructureInt` relies on
```
dvd_sub_pow_of_dvd_sub {R : Type*} [CommRing R] {p : ℕ} {a b : R} :
    (p : R) ∣ a - b → ∀ (k : ℕ), (p : R) ^ (k + 1) ∣ a ^ p ^ k - b ^ p ^ k
```

## Main results

* `wittStructureRat Φ`: the family of polynomials `ℕ → MvPolynomial (idx × ℕ) ℚ`
  associated with `Φ : MvPolynomial idx ℚ` and satisfying the property explained above.
* `wittStructureRat_prop`: the proof that `wittStructureRat` indeed satisfies the property.
* `wittStructureInt Φ`: the family of polynomials `ℕ → MvPolynomial (idx × ℕ) ℤ`
  associated with `Φ : MvPolynomial idx ℤ` and satisfying the property explained above.
* `map_wittStructureInt`: the proof that the integral polynomials `with_structure_int Φ`
  are equal to `wittStructureRat Φ` when mapped to polynomials with rational coefficients.
* `wittStructureInt_prop`: the proof that `wittStructureInt` indeed satisfies the property.
* Five families of polynomials that will be used to define the ring structure
  on the ring of Witt vectors:
  - `WittVector.wittZero`
  - `WittVector.wittOne`
  - `WittVector.wittAdd`
  - `WittVector.wittMul`
  - `WittVector.wittNeg`
  (We also define `WittVector.wittSub`, and later we will prove that it describes subtraction,
  which is defined as `fun a b ↦ a + -b`. See `WittVector.sub_coeff` for this proof.)

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


open MvPolynomial Set

open Finset (range)

open Finsupp (single)

-- This lemma reduces a bundled morphism to a "mere" function,
-- and consequently the simplifier cannot use a lot of powerful simp-lemmas.
-- We disable this locally, and probably it should be disabled globally in mathlib.
attribute [-simp] coe_eval₂Hom

variable {p : ℕ} {R : Type*} {idx : Type*} [CommRing R]

open scoped Witt

open scoped BigOperators

section PPrime

variable (p) [hp : Fact p.Prime]

-- Notation with ring of coefficients explicit
set_option quotPrecheck false in
scoped[Witt] notation "W_" => wittPolynomial p

-- Notation with ring of coefficients implicit
set_option quotPrecheck false in
scoped[Witt] notation "W" => wittPolynomial p _

/-- `wittStructureRat Φ` is a family of polynomials `ℕ → MvPolynomial (idx × ℕ) ℚ`
that are uniquely characterised by the property that
```
bind₁ (wittStructureRat p Φ) (wittPolynomial p ℚ n) =
bind₁ (fun i ↦ (rename (prod.mk i) (wittPolynomial p ℚ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `wittStructureRat Φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

See `wittStructureRat_prop` for this property,
and `wittStructureRat_existsUnique` for the fact that `wittStructureRat`
gives the unique family of polynomials with this property.

These polynomials turn out to have integral coefficients,
but it requires some effort to show this.
See `wittStructureInt` for the version with integral coefficients,
and `map_wittStructureInt` for the fact that it is equal to `wittStructureRat`
when mapped to polynomials over the rationals. -/
noncomputable def wittStructureRat (Φ : MvPolynomial idx ℚ) (n : ℕ) : MvPolynomial (idx × ℕ) ℚ :=
  bind₁ (fun k => bind₁ (fun i => rename (Prod.mk i) (W_ ℚ k)) Φ) (xInTermsOfW p ℚ n)
#align witt_structure_rat wittStructureRat

theorem wittStructureRat_prop (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    bind₁ (wittStructureRat p Φ) (W_ ℚ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℚ n)) Φ :=
  calc
    bind₁ (wittStructureRat p Φ) (W_ ℚ n) =
        bind₁ (fun k => bind₁ (fun i => (rename (Prod.mk i)) (W_ ℚ k)) Φ)
          (bind₁ (xInTermsOfW p ℚ) (W_ ℚ n)) :=
      by rw [bind₁_bind₁]; exact eval₂Hom_congr (RingHom.ext_rat _ _) rfl rfl
         -- ⊢ ↑(bind₁ (wittStructureRat p Φ)) (W_ ℚ n) = ↑(bind₁ fun i => ↑(bind₁ fun k => …
                           -- 🎉 no goals
    _ = bind₁ (fun i => rename (Prod.mk i) (W_ ℚ n)) Φ := by
      rw [bind₁_xInTermsOfW_wittPolynomial p _ n, bind₁_X_right]
      -- 🎉 no goals
#align witt_structure_rat_prop wittStructureRat_prop

theorem wittStructureRat_existsUnique (Φ : MvPolynomial idx ℚ) :
    ∃! φ : ℕ → MvPolynomial (idx × ℕ) ℚ,
      ∀ n : ℕ, bind₁ φ (W_ ℚ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℚ n)) Φ := by
  refine' ⟨wittStructureRat p Φ, _, _⟩
  -- ⊢ (fun φ => ∀ (n : ℕ), ↑(bind₁ φ) (W_ ℚ n) = ↑(bind₁ fun i => ↑(rename (Prod.m …
  · intro n; apply wittStructureRat_prop
    -- ⊢ ↑(bind₁ (wittStructureRat p Φ)) (W_ ℚ n) = ↑(bind₁ fun i => ↑(rename (Prod.m …
             -- 🎉 no goals
  · intro φ H
    -- ⊢ φ = wittStructureRat p Φ
    funext n
    -- ⊢ φ n = wittStructureRat p Φ n
    rw [show φ n = bind₁ φ (bind₁ (W_ ℚ) (xInTermsOfW p ℚ n)) by
        rw [bind₁_wittPolynomial_xInTermsOfW p, bind₁_X_right]]
    rw [bind₁_bind₁]
    -- ⊢ ↑(bind₁ fun i => ↑(bind₁ φ) (W_ ℚ i)) (xInTermsOfW p ℚ n) = wittStructureRat …
    exact eval₂Hom_congr (RingHom.ext_rat _ _) (funext H) rfl
    -- 🎉 no goals
#align witt_structure_rat_exists_unique wittStructureRat_existsUnique

theorem wittStructureRat_rec_aux (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    wittStructureRat p Φ n * C ((p : ℚ) ^ n) =
      bind₁ (fun b => rename (fun i => (b, i)) (W_ ℚ n)) Φ -
        ∑ i in range n, C ((p : ℚ) ^ i) * wittStructureRat p Φ i ^ p ^ (n - i) := by
  have := xInTermsOfW_aux p ℚ n
  -- ⊢ wittStructureRat p Φ n * ↑C (↑p ^ n) = ↑(bind₁ fun b => ↑(rename fun i => (b …
  replace := congr_arg (bind₁ fun k : ℕ => bind₁ (fun i => rename (Prod.mk i) (W_ ℚ k)) Φ) this
  -- ⊢ wittStructureRat p Φ n * ↑C (↑p ^ n) = ↑(bind₁ fun b => ↑(rename fun i => (b …
  rw [AlgHom.map_mul, bind₁_C_right] at this
  -- ⊢ wittStructureRat p Φ n * ↑C (↑p ^ n) = ↑(bind₁ fun b => ↑(rename fun i => (b …
  rw [wittStructureRat, this]; clear this
  -- ⊢ ↑(bind₁ fun k => ↑(bind₁ fun i => ↑(rename (Prod.mk i)) (W_ ℚ k)) Φ) (X n -  …
                               -- ⊢ ↑(bind₁ fun k => ↑(bind₁ fun i => ↑(rename (Prod.mk i)) (W_ ℚ k)) Φ) (X n -  …
  conv_lhs => simp only [AlgHom.map_sub, bind₁_X_right]
  -- ⊢ ↑(bind₁ fun i => ↑(rename (Prod.mk i)) (W_ ℚ n)) Φ - ↑(bind₁ fun k => ↑(bind …
  rw [sub_right_inj]
  -- ⊢ ↑(bind₁ fun k => ↑(bind₁ fun i => ↑(rename (Prod.mk i)) (W_ ℚ k)) Φ) (∑ x in …
  simp only [AlgHom.map_sum, AlgHom.map_mul, bind₁_C_right, AlgHom.map_pow]
  -- ⊢ ∑ x in Finset.range n, ↑C (↑p ^ x) * ↑(bind₁ fun k => ↑(bind₁ fun i => ↑(ren …
  rfl
  -- 🎉 no goals
#align witt_structure_rat_rec_aux wittStructureRat_rec_aux

/-- Write `wittStructureRat p φ n` in terms of `wittStructureRat p φ i` for `i < n`. -/
theorem wittStructureRat_rec (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    wittStructureRat p Φ n =
      C (1 / (p : ℚ) ^ n) *
        (bind₁ (fun b => rename (fun i => (b, i)) (W_ ℚ n)) Φ -
          ∑ i in range n, C ((p : ℚ) ^ i) * wittStructureRat p Φ i ^ p ^ (n - i)) := by
  calc
    wittStructureRat p Φ n = C (1 / (p : ℚ) ^ n) * (wittStructureRat p Φ n * C ((p : ℚ) ^ n)) := ?_
    _ = _ := by rw [wittStructureRat_rec_aux]
  rw [mul_left_comm, ← C_mul, div_mul_cancel, C_1, mul_one]
  -- ⊢ ↑p ^ n ≠ 0
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.1.ne_zero)
  -- 🎉 no goals
#align witt_structure_rat_rec wittStructureRat_rec

/-- `wittStructureInt Φ` is a family of polynomials `ℕ → MvPolynomial (idx × ℕ) ℤ`
that are uniquely characterised by the property that
```
bind₁ (wittStructureInt p Φ) (wittPolynomial p ℤ n) =
bind₁ (fun i ↦ (rename (prod.mk i) (wittPolynomial p ℤ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `wittStructureInt Φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

See `wittStructureInt_prop` for this property,
and `wittStructureInt_existsUnique` for the fact that `wittStructureInt`
gives the unique family of polynomials with this property. -/
noncomputable def wittStructureInt (Φ : MvPolynomial idx ℤ) (n : ℕ) : MvPolynomial (idx × ℕ) ℤ :=
  Finsupp.mapRange Rat.num (Rat.coe_int_num 0) (wittStructureRat p (map (Int.castRingHom ℚ) Φ) n)
#align witt_structure_int wittStructureInt

variable {p}

theorem bind₁_rename_expand_wittPolynomial (Φ : MvPolynomial idx ℤ) (n : ℕ)
    (IH :
      ∀ m : ℕ,
        m < n + 1 →
          map (Int.castRingHom ℚ) (wittStructureInt p Φ m) =
            wittStructureRat p (map (Int.castRingHom ℚ) Φ) m) :
    bind₁ (fun b => rename (fun i => (b, i)) (expand p (W_ ℤ n))) Φ =
      bind₁ (fun i => expand p (wittStructureInt p Φ i)) (W_ ℤ n) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  -- ⊢ ↑(map (Int.castRingHom ℚ)) (↑(bind₁ fun b => ↑(rename fun i => (b, i)) (↑(ex …
  simp only [map_bind₁, map_rename, map_expand, rename_expand, map_wittPolynomial]
  -- ⊢ ↑(bind₁ fun i => ↑(expand p) (↑(rename fun i_1 => (i, i_1)) (W_ ℚ n))) (↑(ma …
  have key := (wittStructureRat_prop p (map (Int.castRingHom ℚ) Φ) n).symm
  -- ⊢ ↑(bind₁ fun i => ↑(expand p) (↑(rename fun i_1 => (i, i_1)) (W_ ℚ n))) (↑(ma …
  apply_fun expand p at key
  -- ⊢ ↑(bind₁ fun i => ↑(expand p) (↑(rename fun i_1 => (i, i_1)) (W_ ℚ n))) (↑(ma …
  simp only [expand_bind₁] at key
  -- ⊢ ↑(bind₁ fun i => ↑(expand p) (↑(rename fun i_1 => (i, i_1)) (W_ ℚ n))) (↑(ma …
  rw [key]; clear key
  -- ⊢ ↑(bind₁ fun i => ↑(expand p) (wittStructureRat p (↑(map (Int.castRingHom ℚ)) …
            -- ⊢ ↑(bind₁ fun i => ↑(expand p) (wittStructureRat p (↑(map (Int.castRingHom ℚ)) …
  apply eval₂Hom_congr' rfl _ rfl
  -- ⊢ ∀ (i : ℕ), i ∈ vars (W_ ℚ n) → i ∈ vars (W_ ℚ n) → ↑(expand p) (wittStructur …
  rintro i hi -
  -- ⊢ ↑(expand p) (wittStructureRat p (↑(map (Int.castRingHom ℚ)) Φ) i) = ↑(expand …
  rw [wittPolynomial_vars, Finset.mem_range] at hi
  -- ⊢ ↑(expand p) (wittStructureRat p (↑(map (Int.castRingHom ℚ)) Φ) i) = ↑(expand …
  simp only [IH i hi]
  -- 🎉 no goals
#align bind₁_rename_expand_witt_polynomial bind₁_rename_expand_wittPolynomial

theorem C_p_pow_dvd_bind₁_rename_wittPolynomial_sub_sum (Φ : MvPolynomial idx ℤ) (n : ℕ)
    (IH :
      ∀ m : ℕ,
        m < n →
          map (Int.castRingHom ℚ) (wittStructureInt p Φ m) =
            wittStructureRat p (map (Int.castRingHom ℚ) Φ) m) :
    (C (p ^ n : ℤ) : MvPolynomial (idx × ℕ) ℤ) ∣
      bind₁ (fun b : idx => rename (fun i => (b, i)) (wittPolynomial p ℤ n)) Φ -
        ∑ i in range n, C ((p : ℤ) ^ i) * wittStructureInt p Φ i ^ p ^ (n - i) := by
  cases' n with n
  -- ⊢ ↑C ↑(p ^ Nat.zero) ∣ ↑(bind₁ fun b => ↑(rename fun i => (b, i)) (W_ ℤ Nat.ze …
  · simp only [isUnit_one, Int.ofNat_zero, Int.ofNat_succ, zero_add, pow_zero, C_1, IsUnit.dvd,
      Nat.cast_one, Nat.zero_eq]
  -- prepare a useful equation for rewriting
  have key := bind₁_rename_expand_wittPolynomial Φ n IH
  -- ⊢ ↑C ↑(p ^ Nat.succ n) ∣ ↑(bind₁ fun b => ↑(rename fun i => (b, i)) (W_ ℤ (Nat …
  apply_fun map (Int.castRingHom (ZMod (p ^ (n + 1)))) at key
  -- ⊢ ↑C ↑(p ^ Nat.succ n) ∣ ↑(bind₁ fun b => ↑(rename fun i => (b, i)) (W_ ℤ (Nat …
  conv_lhs at key => simp only [map_bind₁, map_rename, map_expand, map_wittPolynomial]
  -- ⊢ ↑C ↑(p ^ Nat.succ n) ∣ ↑(bind₁ fun b => ↑(rename fun i => (b, i)) (W_ ℤ (Nat …
  -- clean up and massage
  rw [Nat.succ_eq_add_one, C_dvd_iff_zmod, RingHom.map_sub, sub_eq_zero, map_bind₁]
  -- ⊢ ↑(bind₁ fun i => ↑(map (Int.castRingHom (ZMod (p ^ (n + 1))))) (↑(rename fun …
  simp only [map_rename, map_wittPolynomial, wittPolynomial_zmod_self]
  -- ⊢ ↑(bind₁ fun i => ↑(rename fun i_1 => (i, i_1)) (↑(expand p) (W_ (ZMod (p ^ ( …
  rw [key]; clear key IH
  -- ⊢ ↑(map (Int.castRingHom (ZMod (p ^ (n + 1))))) (↑(bind₁ fun i => ↑(expand p)  …
            -- ⊢ ↑(map (Int.castRingHom (ZMod (p ^ (n + 1))))) (↑(bind₁ fun i => ↑(expand p)  …
  rw [bind₁, aeval_wittPolynomial, map_sum, map_sum, Finset.sum_congr rfl]
  -- ⊢ ∀ (x : ℕ), x ∈ Finset.range (n + 1) → ↑(map (Int.castRingHom (ZMod (p ^ (n + …
  intro k hk
  -- ⊢ ↑(map (Int.castRingHom (ZMod (p ^ (n + 1))))) (↑p ^ k * ↑(expand p) (wittStr …
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  -- ⊢ ↑(map (Int.castRingHom (ZMod (p ^ (n + 1))))) (↑p ^ k * ↑(expand p) (wittStr …
  -- Porting note: was much slower
  -- simp only [← sub_eq_zero, ← RingHom.map_sub, ← C_dvd_iff_zmod, C_eq_coe_nat, ← mul_sub, ←
  --   Nat.cast_pow]
  rw [← sub_eq_zero, ← RingHom.map_sub, ← C_dvd_iff_zmod, C_eq_coe_nat, ← Nat.cast_pow,
    ← Nat.cast_pow, C_eq_coe_nat, ← mul_sub]
  have : p ^ (n + 1) = p ^ k * p ^ (n - k + 1) := by
    rw [← pow_add, ← add_assoc]; congr 2; rw [add_comm, ← tsub_eq_iff_eq_add_of_le hk]
  rw [this]
  -- ⊢ ↑(p ^ k * p ^ (n - k + 1)) ∣ ↑(p ^ k) * (↑(expand p) (wittStructureInt p Φ k …
  simp only -- Porting note: without this, the next `rw` doesn't do anything
  -- ⊢ ↑(p ^ k * p ^ (n - k + 1)) ∣ ↑(p ^ k) * (↑(expand p) (wittStructureInt p Φ k …
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  -- ⊢ ↑p ^ k * ↑p ^ (n - k + 1) ∣ ↑p ^ k * (↑(expand p) (wittStructureInt p Φ k) ^ …
  apply mul_dvd_mul_left ((p : MvPolynomial (idx × ℕ) ℤ) ^ k)
  -- ⊢ ↑p ^ (n - k + 1) ∣ ↑(expand p) (wittStructureInt p Φ k) ^ p ^ (n - k) - witt …
  rw [show p ^ (n + 1 - k) = p * p ^ (n - k) by rw [← pow_succ, ← tsub_add_eq_add_tsub hk]]
  -- ⊢ ↑p ^ (n - k + 1) ∣ ↑(expand p) (wittStructureInt p Φ k) ^ p ^ (n - k) - witt …
  rw [pow_mul]
  -- ⊢ ↑p ^ (n - k + 1) ∣ ↑(expand p) (wittStructureInt p Φ k) ^ p ^ (n - k) - (wit …
  rw [← Nat.cast_pow] -- Porting note: added
  -- ⊢ ↑(p ^ (n - k + 1)) ∣ ↑(expand p) (wittStructureInt p Φ k) ^ p ^ (n - k) - (w …
  -- the machine!
  apply dvd_sub_pow_of_dvd_sub
  -- ⊢ ↑p ∣ ↑(expand p) (wittStructureInt p Φ k) - wittStructureInt p Φ k ^ p
  rw [← C_eq_coe_nat, C_dvd_iff_zmod, RingHom.map_sub, sub_eq_zero, map_expand, RingHom.map_pow,
    MvPolynomial.expand_zmod]
set_option linter.uppercaseLean3 false in
#align C_p_pow_dvd_bind₁_rename_witt_polynomial_sub_sum C_p_pow_dvd_bind₁_rename_wittPolynomial_sub_sum

variable (p)

@[simp]
theorem map_wittStructureInt (Φ : MvPolynomial idx ℤ) (n : ℕ) :
    map (Int.castRingHom ℚ) (wittStructureInt p Φ n) =
      wittStructureRat p (map (Int.castRingHom ℚ) Φ) n := by
  induction n using Nat.strong_induction_on with | h n IH => ?_
  -- ⊢ ↑(map (Int.castRingHom ℚ)) (wittStructureInt p Φ n) = wittStructureRat p (↑( …
  -- ⊢ ↑(map (Int.castRingHom ℚ)) (wittStructureInt p Φ n) = wittStructureRat p (↑( …
  rw [wittStructureInt, map_mapRange_eq_iff, Int.coe_castRingHom]
  -- ⊢ ∀ (d : idx × ℕ →₀ ℕ), (fun x => ↑x) (coeff d (wittStructureRat p (↑(map (Int …
  intro c
  -- ⊢ (fun x => ↑x) (coeff c (wittStructureRat p (↑(map (Int.castRingHom ℚ)) Φ) n) …
  rw [wittStructureRat_rec, coeff_C_mul, mul_comm, mul_div_assoc', mul_one]
  -- ⊢ (fun x => ↑x) (coeff c (↑(bind₁ fun b => ↑(rename fun i => (b, i)) (W_ ℚ n)) …
  have sum_induction_steps :
      map (Int.castRingHom ℚ)
        (∑ i in range n, C ((p : ℤ) ^ i) * wittStructureInt p Φ i ^ p ^ (n - i)) =
      ∑ i in range n,
        C ((p : ℚ) ^ i) * wittStructureRat p (map (Int.castRingHom ℚ) Φ) i ^ p ^ (n - i) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [IH i hi, RingHom.map_mul, RingHom.map_pow, map_C]
    rfl
  simp only [← sum_induction_steps, ← map_wittPolynomial p (Int.castRingHom ℚ), ← map_rename, ←
    map_bind₁, ← RingHom.map_sub, coeff_map]
  rw [show (p : ℚ) ^ n = ((↑(p ^ n) : ℤ) : ℚ) by norm_cast]
  -- ⊢ ↑(↑(Int.castRingHom ℚ) (coeff c (↑(bind₁ fun i => ↑(rename fun i_1 => (i, i_ …
  rw [← Rat.den_eq_one_iff, eq_intCast, Rat.den_div_cast_eq_one_iff]
  -- ⊢ ↑(p ^ n) ∣ coeff c (↑(bind₁ fun i => ↑(rename fun i_1 => (i, i_1)) (W_ ℤ n)) …
  swap; · exact_mod_cast pow_ne_zero n hp.1.ne_zero
  -- ⊢ ↑(p ^ n) ≠ 0
          -- 🎉 no goals
  revert c; rw [← C_dvd_iff_dvd_coeff]
  -- ⊢ ∀ (c : idx × ℕ →₀ ℕ), ↑(p ^ n) ∣ coeff c (↑(bind₁ fun i => ↑(rename fun i_1  …
            -- ⊢ ↑C ↑(p ^ n) ∣ ↑(bind₁ fun i => ↑(rename fun i_1 => (i, i_1)) (W_ ℤ n)) Φ - ∑ …
  exact C_p_pow_dvd_bind₁_rename_wittPolynomial_sub_sum Φ n IH
  -- 🎉 no goals
#align map_witt_structure_int map_wittStructureInt

theorem wittStructureInt_prop (Φ : MvPolynomial idx ℤ) (n) :
    bind₁ (wittStructureInt p Φ) (wittPolynomial p ℤ n) =
      bind₁ (fun i => rename (Prod.mk i) (W_ ℤ n)) Φ := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  -- ⊢ ↑(map (Int.castRingHom ℚ)) (↑(bind₁ (wittStructureInt p Φ)) (W_ ℤ n)) = ↑(ma …
  have := wittStructureRat_prop p (map (Int.castRingHom ℚ) Φ) n
  -- ⊢ ↑(map (Int.castRingHom ℚ)) (↑(bind₁ (wittStructureInt p Φ)) (W_ ℤ n)) = ↑(ma …
  simpa only [map_bind₁, ← eval₂Hom_map_hom, eval₂Hom_C_left, map_rename, map_wittPolynomial,
    AlgHom.coe_toRingHom, map_wittStructureInt]
#align witt_structure_int_prop wittStructureInt_prop

theorem eq_wittStructureInt (Φ : MvPolynomial idx ℤ) (φ : ℕ → MvPolynomial (idx × ℕ) ℤ)
    (h : ∀ n, bind₁ φ (wittPolynomial p ℤ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℤ n)) Φ) :
    φ = wittStructureInt p Φ := by
  funext k
  -- ⊢ φ k = wittStructureInt p Φ k
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  -- ⊢ ↑(map (Int.castRingHom ℚ)) (φ k) = ↑(map (Int.castRingHom ℚ)) (wittStructure …
  rw [map_wittStructureInt]
  -- ⊢ ↑(map (Int.castRingHom ℚ)) (φ k) = wittStructureRat p (↑(map (Int.castRingHo …
  -- Porting note: was `refine' congr_fun _ k`
  revert k
  -- ⊢ ∀ (k : ℕ), ↑(map (Int.castRingHom ℚ)) (φ k) = wittStructureRat p (↑(map (Int …
  refine' congr_fun _
  -- ⊢ (fun k => ↑(map (Int.castRingHom ℚ)) (φ k)) = fun k => wittStructureRat p (↑ …
  apply ExistsUnique.unique (wittStructureRat_existsUnique p (map (Int.castRingHom ℚ) Φ))
  -- ⊢ ∀ (n : ℕ), ↑(bind₁ fun k => ↑(map (Int.castRingHom ℚ)) (φ k)) (W_ ℚ n) = ↑(b …
  · intro n
    -- ⊢ ↑(bind₁ fun k => ↑(map (Int.castRingHom ℚ)) (φ k)) (W_ ℚ n) = ↑(bind₁ fun i  …
    specialize h n
    -- ⊢ ↑(bind₁ fun k => ↑(map (Int.castRingHom ℚ)) (φ k)) (W_ ℚ n) = ↑(bind₁ fun i  …
    apply_fun map (Int.castRingHom ℚ) at h
    -- ⊢ ↑(bind₁ fun k => ↑(map (Int.castRingHom ℚ)) (φ k)) (W_ ℚ n) = ↑(bind₁ fun i  …
    simpa only [map_bind₁, ← eval₂Hom_map_hom, eval₂Hom_C_left, map_rename, map_wittPolynomial,
      AlgHom.coe_toRingHom] using h
  · intro n; apply wittStructureRat_prop
    -- ⊢ ↑(bind₁ fun k => wittStructureRat p (↑(map (Int.castRingHom ℚ)) Φ) k) (W_ ℚ  …
             -- 🎉 no goals
#align eq_witt_structure_int eq_wittStructureInt

theorem wittStructureInt_existsUnique (Φ : MvPolynomial idx ℤ) :
    ∃! φ : ℕ → MvPolynomial (idx × ℕ) ℤ,
      ∀ n : ℕ,
        bind₁ φ (wittPolynomial p ℤ n) = bind₁ (fun i : idx => rename (Prod.mk i) (W_ ℤ n)) Φ :=
  ⟨wittStructureInt p Φ, wittStructureInt_prop _ _, eq_wittStructureInt _ _⟩
#align witt_structure_int_exists_unique wittStructureInt_existsUnique

theorem witt_structure_prop (Φ : MvPolynomial idx ℤ) (n) :
    aeval (fun i => map (Int.castRingHom R) (wittStructureInt p Φ i)) (wittPolynomial p ℤ n) =
      aeval (fun i => rename (Prod.mk i) (W n)) Φ := by
  convert congr_arg (map (Int.castRingHom R)) (wittStructureInt_prop p Φ n) using 1 <;>
  -- ⊢ ↑(aeval fun i => ↑(map (Int.castRingHom R)) (wittStructureInt p Φ i)) (W_ ℤ  …
      rw [hom_bind₁] <;>
      -- ⊢ ↑(aeval fun i => ↑(map (Int.castRingHom R)) (wittStructureInt p Φ i)) (W_ ℤ  …
      -- ⊢ ↑(aeval fun i => ↑(rename (Prod.mk i)) (W_ R n)) Φ = ↑(eval₂Hom (RingHom.com …
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    -- ⊢ (fun i => ↑(map (Int.castRingHom R)) (wittStructureInt p Φ i)) = fun i => ↑( …
    -- ⊢ (fun i => ↑(rename (Prod.mk i)) (W_ R n)) = fun i => ↑(map (Int.castRingHom  …
  · rfl
    -- 🎉 no goals
  · simp only [map_rename, map_wittPolynomial]
    -- 🎉 no goals
#align witt_structure_prop witt_structure_prop

theorem wittStructureInt_rename {σ : Type*} (Φ : MvPolynomial idx ℤ) (f : idx → σ) (n : ℕ) :
    wittStructureInt p (rename f Φ) n = rename (Prod.map f id) (wittStructureInt p Φ n) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  -- ⊢ ↑(map (Int.castRingHom ℚ)) (wittStructureInt p (↑(rename f) Φ) n) = ↑(map (I …
  simp only [map_rename, map_wittStructureInt, wittStructureRat, rename_bind₁, rename_rename,
    bind₁_rename]
  rfl
  -- 🎉 no goals
#align witt_structure_int_rename wittStructureInt_rename

@[simp]
theorem constantCoeff_wittStructureRat_zero (Φ : MvPolynomial idx ℚ) :
    constantCoeff (wittStructureRat p Φ 0) = constantCoeff Φ := by
  simp only [wittStructureRat, bind₁, map_aeval, xInTermsOfW_zero, constantCoeff_rename,
    constantCoeff_wittPolynomial, aeval_X, constantCoeff_comp_algebraMap, eval₂Hom_zero'_apply,
    RingHom.id_apply]
#align constant_coeff_witt_structure_rat_zero constantCoeff_wittStructureRat_zero

theorem constantCoeff_wittStructureRat (Φ : MvPolynomial idx ℚ) (h : constantCoeff Φ = 0) (n : ℕ) :
    constantCoeff (wittStructureRat p Φ n) = 0 := by
  simp only [wittStructureRat, eval₂Hom_zero'_apply, h, bind₁, map_aeval, constantCoeff_rename,
    constantCoeff_wittPolynomial, constantCoeff_comp_algebraMap, RingHom.id_apply,
    constantCoeff_xInTermsOfW]
#align constant_coeff_witt_structure_rat constantCoeff_wittStructureRat

@[simp]
theorem constantCoeff_wittStructureInt_zero (Φ : MvPolynomial idx ℤ) :
    constantCoeff (wittStructureInt p Φ 0) = constantCoeff Φ := by
  have inj : Function.Injective (Int.castRingHom ℚ) := by intro m n; exact Int.cast_inj.mp
  -- ⊢ ↑constantCoeff (wittStructureInt p Φ 0) = ↑constantCoeff Φ
  apply inj
  -- ⊢ ↑(Int.castRingHom ℚ) (↑constantCoeff (wittStructureInt p Φ 0)) = ↑(Int.castR …
  rw [← constantCoeff_map, map_wittStructureInt, constantCoeff_wittStructureRat_zero,
    constantCoeff_map]
#align constant_coeff_witt_structure_int_zero constantCoeff_wittStructureInt_zero

theorem constantCoeff_wittStructureInt (Φ : MvPolynomial idx ℤ) (h : constantCoeff Φ = 0) (n : ℕ) :
    constantCoeff (wittStructureInt p Φ n) = 0 := by
  have inj : Function.Injective (Int.castRingHom ℚ) := by intro m n; exact Int.cast_inj.mp
  -- ⊢ ↑constantCoeff (wittStructureInt p Φ n) = 0
  apply inj
  -- ⊢ ↑(Int.castRingHom ℚ) (↑constantCoeff (wittStructureInt p Φ n)) = ↑(Int.castR …
  rw [← constantCoeff_map, map_wittStructureInt, constantCoeff_wittStructureRat, RingHom.map_zero]
  -- ⊢ ↑constantCoeff (↑(map (Int.castRingHom ℚ)) Φ) = 0
  rw [constantCoeff_map, h, RingHom.map_zero]
  -- 🎉 no goals
#align constant_coeff_witt_structure_int constantCoeff_wittStructureInt

variable (R)

-- we could relax the fintype on `idx`, but then we need to cast from finset to set.
-- for our applications `idx` is always finite.
theorem wittStructureRat_vars [Fintype idx] (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    (wittStructureRat p Φ n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) := by
  rw [wittStructureRat]
  -- ⊢ vars (↑(bind₁ fun k => ↑(bind₁ fun i => ↑(rename (Prod.mk i)) (W_ ℚ k)) Φ) ( …
  intro x hx
  -- ⊢ x ∈ Finset.univ ×ˢ Finset.range (n + 1)
  simp only [Finset.mem_product, true_and_iff, Finset.mem_univ, Finset.mem_range]
  -- ⊢ x.snd < n + 1
  obtain ⟨k, hk, hx'⟩ := mem_vars_bind₁ _ _ hx
  -- ⊢ x.snd < n + 1
  obtain ⟨i, -, hx''⟩ := mem_vars_bind₁ _ _ hx'
  -- ⊢ x.snd < n + 1
  obtain ⟨j, hj, rfl⟩ := mem_vars_rename _ _ hx''
  -- ⊢ (i, j).snd < n + 1
  rw [wittPolynomial_vars, Finset.mem_range] at hj
  -- ⊢ (i, j).snd < n + 1
  replace hk := xInTermsOfW_vars_subset p _ hk
  -- ⊢ (i, j).snd < n + 1
  rw [Finset.mem_range] at hk
  -- ⊢ (i, j).snd < n + 1
  exact lt_of_lt_of_le hj hk
  -- 🎉 no goals
#align witt_structure_rat_vars wittStructureRat_vars

-- we could relax the fintype on `idx`, but then we need to cast from finset to set.
-- for our applications `idx` is always finite.
theorem wittStructureInt_vars [Fintype idx] (Φ : MvPolynomial idx ℤ) (n : ℕ) :
    (wittStructureInt p Φ n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) := by
  have : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  -- ⊢ vars (wittStructureInt p Φ n) ⊆ Finset.univ ×ˢ Finset.range (n + 1)
  rw [← vars_map_of_injective _ this, map_wittStructureInt]
  -- ⊢ vars (wittStructureRat p (↑(map (Int.castRingHom ℚ)) Φ) n) ⊆ Finset.univ ×ˢ  …
  apply wittStructureRat_vars
  -- 🎉 no goals
#align witt_structure_int_vars wittStructureInt_vars

end PPrime
