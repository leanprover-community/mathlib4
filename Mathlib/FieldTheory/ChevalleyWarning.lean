/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.FieldTheory.Finite.Basic

/-!
# The Chevalley–Warning theorem

This file contains a proof of the Chevalley–Warning theorem.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

## Main results

1. Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
   such that the total degree of `f` is less than `(q-1)` times the cardinality of `σ`.
   Then the evaluation of `f` on all points of `σ → K` (aka `K^σ`) sums to `0`.
   (`sum_eval_eq_zero`)
2. The Chevalley–Warning theorem (`char_dvd_card_solutions_of_sum_lt`).
   Let `f i` be a finite family of multivariate polynomials
   in finitely many variables (`X s`, `s : σ`) such that
   the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
   Then the number of common solutions of the `f i`
   is divisible by the characteristic of `K`.

## Notation

- `K` is a finite field
- `q` is notation for the cardinality of `K`
- `σ` is the indexing type for the variables of a multivariate polynomial ring over `K`

-/


universe u v

section FiniteField

open MvPolynomial

open Function hiding eval

open Finset FiniteField

variable {K σ ι : Type*} [Fintype K] [Field K] [Fintype σ] [DecidableEq σ]

local notation "q" => Fintype.card K

theorem MvPolynomial.sum_eval_eq_zero (f : MvPolynomial σ K)
    (h : f.totalDegree < (q - 1) * Fintype.card σ) : ∑ x, eval x f = 0 := by
  haveI : DecidableEq K := Classical.decEq K
  calc
    ∑ x, eval x f = ∑ x : σ → K, ∑ d ∈ f.support, f.coeff d * ∏ i, x i ^ d i := by
      simp only [eval_eq']
    _ = ∑ d ∈ f.support, ∑ x : σ → K, f.coeff d * ∏ i, x i ^ d i := sum_comm
    _ = 0 := sum_eq_zero ?_
  intro d hd
  obtain ⟨i, hi⟩ : ∃ i, d i < q - 1 := f.exists_degree_lt (q - 1) h hd
  calc
    (∑ x : σ → K, f.coeff d * ∏ i, x i ^ d i) = f.coeff d * ∑ x : σ → K, ∏ i, x i ^ d i :=
      (mul_sum ..).symm
    _ = 0 := (mul_eq_zero.mpr ∘ Or.inr) ?_
  calc
    (∑ x : σ → K, ∏ i, x i ^ d i) =
        ∑ x₀ : { j // j ≠ i } → K, ∑ x : { x : σ → K // x ∘ (↑) = x₀ }, ∏ j, (x : σ → K) j ^ d j :=
      (Fintype.sum_fiberwise _ _).symm
    _ = 0 := Fintype.sum_eq_zero _ ?_
  intro x₀
  let e : K ≃ { x // x ∘ ((↑) : _ → σ) = x₀ } := (Equiv.subtypeEquivCodomain _).symm
  calc
    (∑ x : { x : σ → K // x ∘ (↑) = x₀ }, ∏ j, (x : σ → K) j ^ d j) =
        ∑ a : K, ∏ j : σ, (e a : σ → K) j ^ d j := (e.sum_comp _).symm
    _ = ∑ a : K, (∏ j, x₀ j ^ d j) * a ^ d i := Fintype.sum_congr _ _ ?_
    _ = (∏ j, x₀ j ^ d j) * ∑ a : K, a ^ d i := by rw [mul_sum]
    _ = 0 := by rw [sum_pow_lt_card_sub_one K _ hi, mul_zero]
  intro a
  let e' : { j // j = i } ⊕ { j // j ≠ i } ≃ σ := Equiv.sumCompl _
  letI : Unique { j // j = i } :=
    { default := ⟨i, rfl⟩
      uniq := fun ⟨j, h⟩ => Subtype.val_injective h }
  calc
    (∏ j : σ, (e a : σ → K) j ^ d j) =
        (e a : σ → K) i ^ d i * ∏ j : { j // j ≠ i }, (e a : σ → K) j ^ d j := by
      rw [← e'.prod_comp, Fintype.prod_sum_type, univ_unique, prod_singleton]; rfl
    _ = a ^ d i * ∏ j : { j // j ≠ i }, (e a : σ → K) j ^ d j := by
      rw [Equiv.subtypeEquivCodomain_symm_apply_eq]
    _ = a ^ d i * ∏ j, x₀ j ^ d j := congr_arg _ (Fintype.prod_congr _ _ ?_)
    -- see below
    _ = (∏ j, x₀ j ^ d j) * a ^ d i := mul_comm _ _
  -- the remaining step of the calculation above
  rintro ⟨j, hj⟩
  show (e a : σ → K) j ^ d j = x₀ ⟨j, hj⟩ ^ d j
  rw [Equiv.subtypeEquivCodomain_symm_apply_ne]

variable [DecidableEq K] (p : ℕ) [CharP K p]

/-- The **Chevalley–Warning theorem**, finitary version.
Let `(f i)` be a finite family of multivariate polynomials
in finitely many variables (`X s`, `s : σ`) over a finite field of characteristic `p`.
Assume that the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
Then the number of common solutions of the `f i` is divisible by `p`. -/
theorem char_dvd_card_solutions_of_sum_lt {s : Finset ι} {f : ι → MvPolynomial σ K}
    (h : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ) :
    p ∣ Fintype.card { x : σ → K // ∀ i ∈ s, eval x (f i) = 0 } := by
  have hq : 0 < q - 1 := by rw [← Fintype.card_units, Fintype.card_pos_iff]; exact ⟨1⟩
  let S : Finset (σ → K) := {x | ∀ i ∈ s, eval x (f i) = 0}
  have hS (x : σ → K) : x ∈ S ↔ ∀ i ∈ s, eval x (f i) = 0 := by simp [S]
  /- The polynomial `F = ∏ i ∈ s, (1 - (f i)^(q - 1))` has the nice property
    that it takes the value `1` on elements of `{x : σ → K // ∀ i ∈ s, (f i).eval x = 0}`
    while it is `0` outside that locus.
    Hence the sum of its values is equal to the cardinality of
    `{x : σ → K // ∀ i ∈ s, (f i).eval x = 0}` modulo `p`. -/
  let F : MvPolynomial σ K := ∏ i ∈ s, (1 - f i ^ (q - 1))
  have hF : ∀ x, eval x F = if x ∈ S then 1 else 0 := by
    intro x
    calc
      eval x F = ∏ i ∈ s, eval x (1 - f i ^ (q - 1)) := eval_prod s _ x
      _ = if x ∈ S then 1 else 0 := ?_
    simp only [(eval x).map_sub, (eval x).map_pow, (eval x).map_one]
    split_ifs with hx
    · apply Finset.prod_eq_one
      intro i hi
      rw [hS] at hx
      rw [hx i hi, zero_pow hq.ne', sub_zero]
    · obtain ⟨i, hi, hx⟩ : ∃ i ∈ s, eval x (f i) ≠ 0 := by
        simpa [hS, not_forall, Classical.not_imp] using hx
      apply Finset.prod_eq_zero hi
      rw [pow_card_sub_one_eq_one (eval x (f i)) hx, sub_self]
  -- In particular, we can now show:
  have key : ∑ x, eval x F = Fintype.card { x : σ → K // ∀ i ∈ s, eval x (f i) = 0 } := by
    rw [Fintype.card_of_subtype S hS, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, ←
      Fintype.sum_extend_by_zero S, sum_congr rfl fun x _ => hF x]
  -- With these preparations under our belt, we will approach the main goal.
  show p ∣ Fintype.card { x // ∀ i : ι, i ∈ s → eval x (f i) = 0 }
  rw [← CharP.cast_eq_zero_iff K, ← key]
  show (∑ x, eval x F) = 0
  -- We are now ready to apply the main machine, proven before.
  apply F.sum_eval_eq_zero
  -- It remains to verify the crucial assumption of this machine
  show F.totalDegree < (q - 1) * Fintype.card σ
  calc
    F.totalDegree ≤ ∑ i ∈ s, (1 - f i ^ (q - 1)).totalDegree := totalDegree_finset_prod s _
    _ ≤ ∑ i ∈ s, (q - 1) * (f i).totalDegree := sum_le_sum fun i _ => ?_
    -- see ↓
    _ = (q - 1) * ∑ i ∈ s, (f i).totalDegree := (mul_sum ..).symm
    _ < (q - 1) * Fintype.card σ := by rwa [mul_lt_mul_left hq]
  -- Now we prove the remaining step from the preceding calculation
  show (1 - f i ^ (q - 1)).totalDegree ≤ (q - 1) * (f i).totalDegree
  calc
    (1 - f i ^ (q - 1)).totalDegree ≤
        max (1 : MvPolynomial σ K).totalDegree (f i ^ (q - 1)).totalDegree := totalDegree_sub _ _
    _ ≤ (f i ^ (q - 1)).totalDegree := by simp
    _ ≤ (q - 1) * (f i).totalDegree := totalDegree_pow _ _

/-- The **Chevalley–Warning theorem**, `Fintype` version.
Let `(f i)` be a finite family of multivariate polynomials
in finitely many variables (`X s`, `s : σ`) over a finite field of characteristic `p`.
Assume that the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
Then the number of common solutions of the `f i` is divisible by `p`. -/
theorem char_dvd_card_solutions_of_fintype_sum_lt [Fintype ι] {f : ι → MvPolynomial σ K}
    (h : (∑ i, (f i).totalDegree) < Fintype.card σ) :
    p ∣ Fintype.card { x : σ → K // ∀ i, eval x (f i) = 0 } := by
  simpa using char_dvd_card_solutions_of_sum_lt p h

/-- The **Chevalley–Warning theorem**, unary version.
Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
over a finite field of characteristic `p`.
Assume that the total degree of `f` is less than the cardinality of `σ`.
Then the number of solutions of `f` is divisible by `p`.
See `char_dvd_card_solutions_of_sum_lt` for a version that takes a family of polynomials `f i`. -/
theorem char_dvd_card_solutions {f : MvPolynomial σ K} (h : f.totalDegree < Fintype.card σ) :
    p ∣ Fintype.card { x : σ → K // eval x f = 0 } := by
  let F : Unit → MvPolynomial σ K := fun _ => f
  have : (∑ i : Unit, (F i).totalDegree) < Fintype.card σ := h
  convert char_dvd_card_solutions_of_sum_lt p this
  aesop

/-- The **Chevalley–Warning theorem**, binary version.
Let `f₁`, `f₂` be two multivariate polynomials in finitely many variables (`X s`, `s : σ`) over a
finite field of characteristic `p`.
Assume that the sum of the total degrees of `f₁` and `f₂` is less than the cardinality of `σ`.
Then the number of common solutions of the `f₁` and `f₂` is divisible by `p`. -/
theorem char_dvd_card_solutions_of_add_lt {f₁ f₂ : MvPolynomial σ K}
    (h : f₁.totalDegree + f₂.totalDegree < Fintype.card σ) :
    p ∣ Fintype.card { x : σ → K // eval x f₁ = 0 ∧ eval x f₂ = 0 } := by
  let F : Bool → MvPolynomial σ K := fun b => cond b f₂ f₁
  have : (∑ b : Bool, (F b).totalDegree) < Fintype.card σ := (add_comm _ _).trans_lt h
  simpa only [Bool.forall_bool] using char_dvd_card_solutions_of_fintype_sum_lt p this

end FiniteField
