/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.RingTheory.Ideal.LocalRing

#align_import ring_theory.polynomial.dickson from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Dickson polynomials

The (generalised) Dickson polynomials are a family of polynomials indexed by `ℕ × ℕ`,
with coefficients in a commutative ring `R` depending on an element `a∈R`. More precisely, the
they satisfy the recursion `dickson k a (n + 2) = X * (dickson k a n + 1) - a * (dickson k a n)`
with starting values `dickson k a 0 = 3 - k` and `dickson k a 1 = X`. In the literature,
`dickson k a n` is called the `n`-th Dickson polynomial of the `k`-th kind associated to the
parameter `a : R`. They are closely related to the Chebyshev polynomials in the case that `a=1`.
When `a=0` they are just the family of monomials `X ^ n`.

## Main definition

* `Polynomial.dickson`: the generalised Dickson polynomials.

## Main statements

* `Polynomial.dickson_one_one_mul`, the `(m * n)`-th Dickson polynomial of the first kind for
  parameter `1 : R` is the composition of the `m`-th and `n`-th Dickson polynomials of the first
  kind for `1 : R`.
* `Polynomial.dickson_one_one_charP`, for a prime number `p`, the `p`-th Dickson polynomial of the
  first kind associated to parameter `1 : R` is congruent to `X ^ p` modulo `p`.

## References

* [R. Lidl, G. L. Mullen and G. Turnwald, _Dickson polynomials_][MR1237403]

## TODO

* Redefine `dickson` in terms of `LinearRecurrence`.
* Show that `dickson 2 1` is equal to the characteristic polynomial of the adjacency matrix of a
  type A Dynkin diagram.
* Prove that the adjacency matrices of simply laced Dynkin diagrams are precisely the adjacency
  matrices of simple connected graphs which annihilate `dickson 2 1`.
-/


noncomputable section

namespace Polynomial

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (k : ℕ) (a : R)

/-- `dickson` is the `n`-th (generalised) Dickson polynomial of the `k`-th kind associated to the
element `a ∈ R`. -/
noncomputable def dickson : ℕ → R[X]
  | 0 => 3 - k
  | 1 => X
  | n + 2 => X * dickson (n + 1) - C a * dickson n
#align polynomial.dickson Polynomial.dickson

@[simp]
theorem dickson_zero : dickson k a 0 = 3 - k :=
  rfl
#align polynomial.dickson_zero Polynomial.dickson_zero

@[simp]
theorem dickson_one : dickson k a 1 = X :=
  rfl
#align polynomial.dickson_one Polynomial.dickson_one

theorem dickson_two : dickson k a 2 = X ^ 2 - C a * (3 - k : R[X]) := by
  simp only [dickson, sq]
  -- 🎉 no goals
#align polynomial.dickson_two Polynomial.dickson_two

@[simp]
theorem dickson_add_two (n : ℕ) :
    dickson k a (n + 2) = X * dickson k a (n + 1) - C a * dickson k a n := by rw [dickson]
                                                                              -- 🎉 no goals
#align polynomial.dickson_add_two Polynomial.dickson_add_two

theorem dickson_of_two_le {n : ℕ} (h : 2 ≤ n) :
    dickson k a n = X * dickson k a (n - 1) - C a * dickson k a (n - 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  -- ⊢ dickson k a (2 + n) = X * dickson k a (2 + n - 1) - ↑C a * dickson k a (2 +  …
  rw [add_comm]
  -- ⊢ dickson k a (n + 2) = X * dickson k a (n + 2 - 1) - ↑C a * dickson k a (n +  …
  exact dickson_add_two k a n
  -- 🎉 no goals
#align polynomial.dickson_of_two_le Polynomial.dickson_of_two_le

variable {k a}

theorem map_dickson (f : R →+* S) : ∀ n : ℕ, map f (dickson k a n) = dickson k (f a) n
  | 0 => by
    simp_rw [dickson_zero, Polynomial.map_sub, Polynomial.map_nat_cast, Polynomial.map_ofNat]
    -- 🎉 no goals
  | 1 => by simp only [dickson_one, map_X]
            -- 🎉 no goals
  | n + 2 => by
    simp only [dickson_add_two, Polynomial.map_sub, Polynomial.map_mul, map_X, map_C]
    -- ⊢ X * map f (dickson k a (n + 1)) - ↑C (↑f a) * map f (dickson k a n) = X * di …
    rw [map_dickson f n, map_dickson f (n + 1)]
    -- 🎉 no goals
#align polynomial.map_dickson Polynomial.map_dickson

@[simp]
theorem dickson_two_zero : ∀ n : ℕ, dickson 2 (0 : R) n = X ^ n
  | 0 => by
    simp only [dickson_zero, pow_zero]
    -- ⊢ 3 - ↑2 = 1
    norm_num
    -- 🎉 no goals
  | 1 => by simp only [dickson_one, pow_one]
            -- 🎉 no goals
  | n + 2 => by
    simp only [dickson_add_two, C_0, zero_mul, sub_zero]
    -- ⊢ X * dickson 2 0 (n + 1) = X ^ (n + 2)
    rw [dickson_two_zero (n + 1), pow_add X (n + 1) 1, mul_comm, pow_one]
    -- 🎉 no goals
#align polynomial.dickson_two_zero Polynomial.dickson_two_zero

section Dickson

/-!

### A Lambda structure on `ℤ[X]`

Mathlib doesn't currently know what a Lambda ring is.
But once it does, we can endow `ℤ[X]` with a Lambda structure
in terms of the `dickson 1 1` polynomials defined below.
There is exactly one other Lambda structure on `ℤ[X]` in terms of binomial polynomials.

-/


theorem dickson_one_one_eval_add_inv (x y : R) (h : x * y = 1) :
    ∀ n, (dickson 1 (1 : R) n).eval (x + y) = x ^ n + y ^ n
  | 0 => by
    -- Porting note: Original proof was
    -- `simp only [bit0, eval_one, eval_add, pow_zero, dickson_zero]; norm_num`
    suffices eval (x + y) 2 = 2 by convert this <;> norm_num
    -- ⊢ eval (x + y) 2 = 2
    exact eval_nat_cast
    -- 🎉 no goals
  | 1 => by simp only [eval_X, dickson_one, pow_one]
            -- 🎉 no goals
  | n + 2 => by
    simp only [eval_sub, eval_mul, dickson_one_one_eval_add_inv x y h _, eval_X, dickson_add_two,
      C_1, eval_one]
    conv_lhs => simp only [pow_succ, add_mul, mul_add, h, ← mul_assoc, mul_comm y x, one_mul]
    -- ⊢ x * x * x ^ n + x ^ n + (y ^ n + y * y * y ^ n) - (x ^ n + y ^ n) = x ^ (n + …
    ring
    -- 🎉 no goals
#align polynomial.dickson_one_one_eval_add_inv Polynomial.dickson_one_one_eval_add_inv

variable (R)

-- Porting note: Added 2 new theorems for convenience
private theorem two_mul_C_half_eq_one [Invertible (2 : R)] : 2 * C (⅟ 2 : R) = 1 := by
  rw [two_mul, ← C_add, invOf_two_add_invOf_two, C_1]
  -- 🎉 no goals

private theorem C_half_mul_two_eq_one [Invertible (2 : R)] : C (⅟ 2 : R) * 2 = 1 := by
  rw [mul_comm, two_mul_C_half_eq_one]
  -- 🎉 no goals

theorem dickson_one_one_eq_chebyshev_T [Invertible (2 : R)] :
    ∀ n, dickson 1 (1 : R) n = 2 * (Chebyshev.T R n).comp (C (⅟ 2) * X)
  | 0 => by
    simp only [Chebyshev.T_zero, mul_one, one_comp, dickson_zero]
    -- ⊢ 3 - ↑1 = 2
    norm_num
    -- 🎉 no goals
  | 1 => by
    rw [dickson_one, Chebyshev.T_one, X_comp, ← mul_assoc, two_mul_C_half_eq_one, one_mul]
    -- 🎉 no goals
  | n + 2 => by
    rw [dickson_add_two, C_1, Chebyshev.T_add_two, dickson_one_one_eq_chebyshev_T (n + 1),
      dickson_one_one_eq_chebyshev_T n, sub_comp, mul_comp, mul_comp, X_comp, ofNat_comp]
    simp_rw [← mul_assoc, Nat.cast_ofNat, two_mul_C_half_eq_one]
    -- ⊢ X * 2 * comp (Chebyshev.T R (n + 1)) (↑C ⅟2 * X) - 1 * 2 * comp (Chebyshev.T …
    ring
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.dickson_one_one_eq_chebyshev_T Polynomial.dickson_one_one_eq_chebyshev_T

theorem chebyshev_T_eq_dickson_one_one [Invertible (2 : R)] (n : ℕ) :
    Chebyshev.T R n = C (⅟ 2) * (dickson 1 1 n).comp (2 * X) := by
  rw [dickson_one_one_eq_chebyshev_T, mul_comp, ofNat_comp, comp_assoc, mul_comp, C_comp, X_comp]
  -- ⊢ Chebyshev.T R n = ↑C ⅟2 * (↑2 * comp (Chebyshev.T R n) (↑C ⅟2 * (2 * X)))
  simp_rw [← mul_assoc, Nat.cast_ofNat, C_half_mul_two_eq_one, one_mul, comp_X]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev_T_eq_dickson_one_one Polynomial.chebyshev_T_eq_dickson_one_one

/-- The `(m * n)`-th Dickson polynomial of the first kind is the composition of the `m`-th and
`n`-th. -/
theorem dickson_one_one_mul (m n : ℕ) :
    dickson 1 (1 : R) (m * n) = (dickson 1 1 m).comp (dickson 1 1 n) := by
  have h : (1 : R) = Int.castRingHom R 1
  -- ⊢ 1 = ↑(Int.castRingHom R) 1
  simp only [eq_intCast, Int.cast_one]
  -- ⊢ dickson 1 1 (m * n) = comp (dickson 1 1 m) (dickson 1 1 n)
  rw [h]
  -- ⊢ dickson 1 (↑(Int.castRingHom R) 1) (m * n) = comp (dickson 1 (↑(Int.castRing …
  simp only [← map_dickson (Int.castRingHom R), ← map_comp]
  -- ⊢ map (Int.castRingHom R) (dickson 1 1 (m * n)) = map (Int.castRingHom R) (com …
  congr 1
  -- ⊢ dickson 1 1 (m * n) = comp (dickson 1 1 m) (dickson 1 1 n)
  apply map_injective (Int.castRingHom ℚ) Int.cast_injective
  -- ⊢ map (Int.castRingHom ℚ) (dickson 1 1 (m * n)) = map (Int.castRingHom ℚ) (com …
  simp only [map_dickson, map_comp, eq_intCast, Int.cast_one, dickson_one_one_eq_chebyshev_T,
    Chebyshev.T_mul, two_mul, ← add_comp]
  simp only [← two_mul, ← comp_assoc]
  -- ⊢ comp (comp (2 * Chebyshev.T ℚ m) (Chebyshev.T ℚ n)) (↑C ⅟2 * X) = comp (comp …
  apply eval₂_congr rfl rfl
  -- ⊢ comp (2 * Chebyshev.T ℚ m) (Chebyshev.T ℚ n) = comp (comp (2 * Chebyshev.T ℚ …
  rw [comp_assoc]
  -- ⊢ comp (2 * Chebyshev.T ℚ m) (Chebyshev.T ℚ n) = comp (2 * Chebyshev.T ℚ m) (c …
  apply eval₂_congr rfl _ rfl
  -- ⊢ Chebyshev.T ℚ n = comp (↑C ⅟2 * X) (2 * Chebyshev.T ℚ n)
  rw [mul_comp, C_comp, X_comp, ← mul_assoc, C_half_mul_two_eq_one, one_mul]
  -- 🎉 no goals
#align polynomial.dickson_one_one_mul Polynomial.dickson_one_one_mul

theorem dickson_one_one_comp_comm (m n : ℕ) :
    (dickson 1 (1 : R) m).comp (dickson 1 1 n) = (dickson 1 1 n).comp (dickson 1 1 m) := by
  rw [← dickson_one_one_mul, mul_comm, dickson_one_one_mul]
  -- 🎉 no goals
#align polynomial.dickson_one_one_comp_comm Polynomial.dickson_one_one_comp_comm

theorem dickson_one_one_zmod_p (p : ℕ) [Fact p.Prime] : dickson 1 (1 : ZMod p) p = X ^ p := by
  -- Recall that `dickson_one_one_eval_add_inv` characterises `dickson 1 1 p`
  -- as a polynomial that maps `x + x⁻¹` to `x ^ p + (x⁻¹) ^ p`.
  -- Since `X ^ p` also satisfies this property in characteristic `p`,
  -- we can use a variant on `Polynomial.funext` to conclude that these polynomials are equal.
  -- For this argument, we need an arbitrary infinite field of characteristic `p`.
  obtain ⟨K, _, _, H⟩ : ∃ (K : Type) (_ : Field K), ∃ _ : CharP K p, Infinite K := by
    let K := FractionRing (Polynomial (ZMod p))
    let f : ZMod p →+* K := (algebraMap _ (FractionRing _)).comp C
    have : CharP K p := by
      rw [← f.charP_iff_charP]
      infer_instance
    haveI : Infinite K :=
      Infinite.of_injective (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))))
        (IsFractionRing.injective _ _)
    refine' ⟨K, _, _, _⟩ <;> infer_instance
  apply map_injective (ZMod.castHom (dvd_refl p) K) (RingHom.injective _)
  -- ⊢ map (ZMod.castHom (_ : p ∣ p) K) (dickson 1 1 p) = map (ZMod.castHom (_ : p  …
  rw [map_dickson, Polynomial.map_pow, map_X]
  -- ⊢ dickson 1 (↑(ZMod.castHom (_ : p ∣ p) K) 1) p = X ^ p
  apply eq_of_infinite_eval_eq
  -- ⊢ Set.Infinite {x | eval x (dickson 1 (↑(ZMod.castHom (_ : p ∣ p) K) 1) p) = e …
  -- The two polynomials agree on all `x` of the form `x = y + y⁻¹`.
  apply @Set.Infinite.mono _ { x : K | ∃ y, x = y + y⁻¹ ∧ y ≠ 0 }
  -- ⊢ {x | ∃ y, x = y + y⁻¹ ∧ y ≠ 0} ⊆ {x | eval x (dickson 1 (↑(ZMod.castHom (_ : …
  · rintro _ ⟨x, rfl, hx⟩
    -- ⊢ x + x⁻¹ ∈ {x | eval x (dickson 1 (↑(ZMod.castHom (_ : p ∣ p) K) 1) p) = eval …
    simp only [eval_X, eval_pow, Set.mem_setOf_eq, @add_pow_char K _ p,
      dickson_one_one_eval_add_inv _ _ (mul_inv_cancel hx), inv_pow, ZMod.castHom_apply,
      ZMod.cast_one']
  -- Now we need to show that the set of such `x` is infinite.
  -- If the set is finite, then we will show that `K` is also finite.
  · intro h
    -- ⊢ False
    rw [← Set.infinite_univ_iff] at H
    -- ⊢ False
    apply H
    -- ⊢ Set.Finite Set.univ
    -- To each `x` of the form `x = y + y⁻¹`
    -- we `bind` the set of `y` that solve the equation `x = y + y⁻¹`.
    -- For every `x`, that set is finite (since it is governed by a quadratic equation).
    -- For the moment, we claim that all these sets together cover `K`.
    suffices (Set.univ : Set K) =
        { x : K | ∃ y : K, x = y + y⁻¹ ∧ y ≠ 0 } >>= fun x => { y | x = y + y⁻¹ ∨ y = 0 } by
      rw [this]
      clear this
      refine' h.biUnion fun x _ => _
      -- The following quadratic polynomial has as solutions the `y` for which `x = y + y⁻¹`.
      let φ : K[X] := X ^ 2 - C x * X + 1
      have hφ : φ ≠ 0 := by
        intro H
        have : φ.eval 0 = 0 := by rw [H, eval_zero]
        simpa [eval_X, eval_one, eval_pow, eval_sub, sub_zero, eval_add, eval_mul,
          mul_zero, sq, zero_add, one_ne_zero]
      classical
        convert(φ.roots ∪ {0}).toFinset.finite_toSet using 1
        ext1 y
        simp only [Multiset.mem_toFinset, Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_union,
          mem_roots hφ, IsRoot, eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C, eval_one,
          Multiset.mem_singleton]
        by_cases hy : y = 0
        · simp only [hy, eq_self_iff_true, or_true_iff]
        apply or_congr _ Iff.rfl
        rw [← mul_left_inj' hy, eq_comm, ← sub_eq_zero, add_mul, inv_mul_cancel hy]
        apply eq_iff_eq_cancel_right.mpr
        ring
    -- Finally, we prove the claim that our finite union of finite sets covers all of `K`.
    · apply (Set.eq_univ_of_forall _).symm
      -- ⊢ ∀ (x : K),
      intro x
      -- ⊢ x ∈ do
      simp only [exists_prop, Set.mem_iUnion, Set.bind_def, Ne.def, Set.mem_setOf_eq]
      -- ⊢ ∃ i, (∃ y, i = y + y⁻¹ ∧ ¬y = 0) ∧ (i = x + x⁻¹ ∨ x = 0)
      by_cases hx : x = 0
      -- ⊢ ∃ i, (∃ y, i = y + y⁻¹ ∧ ¬y = 0) ∧ (i = x + x⁻¹ ∨ x = 0)
      · simp only [hx, and_true_iff, eq_self_iff_true, inv_zero, or_true_iff]
        -- ⊢ ∃ i y, i = y + y⁻¹ ∧ ¬y = 0
        exact ⟨_, 1, rfl, one_ne_zero⟩
        -- 🎉 no goals
      · simp only [hx, or_false_iff, exists_eq_right]
        -- ⊢ ∃ y, x + x⁻¹ = y + y⁻¹ ∧ ¬y = 0
        exact ⟨_, rfl, hx⟩
        -- 🎉 no goals
#align polynomial.dickson_one_one_zmod_p Polynomial.dickson_one_one_zmod_p

theorem dickson_one_one_charP (p : ℕ) [Fact p.Prime] [CharP R p] : dickson 1 (1 : R) p = X ^ p := by
  have h : (1 : R) = ZMod.castHom (dvd_refl p) R 1
  -- ⊢ 1 = ↑(ZMod.castHom (_ : p ∣ p) R) 1
  simp only [ZMod.castHom_apply, ZMod.cast_one']
  -- ⊢ dickson 1 1 p = X ^ p
  rw [h, ← map_dickson (ZMod.castHom (dvd_refl p) R), dickson_one_one_zmod_p, Polynomial.map_pow,
    map_X]
#align polynomial.dickson_one_one_char_p Polynomial.dickson_one_one_charP

end Dickson

end Polynomial
