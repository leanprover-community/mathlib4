/-
Copyright (c) 2020 Johan Commelin, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.RingTheory.WittVector.Basic
import Mathlib.RingTheory.WittVector.IsPoly

/-!

# `init` and `tail`

Given a Witt vector `x`, we are sometimes interested
in its components before and after an index `n`.
This file defines those operations, proves that `init` is polynomial,
and shows how that polynomial interacts with `MvPolynomial.bind₁`.

## Main declarations

* `WittVector.init n x`: the first `n` coefficients of `x`, as a Witt vector. All coefficients at
  indices ≥ `n` are 0.
* `WittVector.tail n x`: the complementary part to `init`. All coefficients at indices < `n` are 0,
  otherwise they are the same as in `x`.
* `WittVector.coeff_add_of_disjoint`: if `x` and `y` are Witt vectors such that for every `n`
  the `n`-th coefficient of `x` or of `y` is `0`, then the coefficients of `x + y`
  are just `x.coeff n + y.coeff n`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]

-/


variable {p : ℕ} (n : ℕ) {R : Type*} [CommRing R]

-- type as `\bbW`
local notation "𝕎" => WittVector p


namespace WittVector

open MvPolynomial

noncomputable section

section

open scoped Classical in
/-- `WittVector.select P x`, for a predicate `P : ℕ → Prop` is the Witt vector
whose `n`-th coefficient is `x.coeff n` if `P n` is true, and `0` otherwise.
-/
def select (P : ℕ → Prop) (x : 𝕎 R) : 𝕎 R :=
  mk p fun n => if P n then x.coeff n else 0

section Select

variable (P : ℕ → Prop)

open scoped Classical in
/-- The polynomial that witnesses that `WittVector.select` is a polynomial function.
`selectPoly n` is `X n` if `P n` holds, and `0` otherwise. -/
def selectPoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  if P n then X n else 0

theorem coeff_select (x : 𝕎 R) (n : ℕ) :
    (select P x).coeff n = aeval x.coeff (selectPoly P n) := by
  dsimp [select, selectPoly]
  split_ifs with hi <;> simp

instance select_isPoly {P : ℕ → Prop} : IsPoly p fun _ _ x => select P x := by
  use selectPoly P
  rintro R _Rcr x
  funext i
  apply coeff_select

variable [hp : Fact p.Prime]

theorem select_add_select_not : ∀ x : 𝕎 R, select P x + select (fun i => ¬P i) x = x := by
  -- Porting note: TC search was insufficient to find this instance, even though all required
  -- instances exist. See zulip: [https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/WittVector.20saga/near/370073526]
  have : IsPoly p fun {R} [CommRing R] x ↦ select P x + select (fun i ↦ ¬P i) x :=
    IsPoly₂.diag (hf := IsPoly₂.comp)
  ghost_calc x
  intro n
  simp only [RingHom.map_add]
  suffices
    (bind₁ (selectPoly P)) (wittPolynomial p ℤ n) +
        (bind₁ (selectPoly fun i => ¬P i)) (wittPolynomial p ℤ n) =
      wittPolynomial p ℤ n by
    apply_fun aeval x.coeff at this
    simpa only [map_add, aeval_bind₁, ← coeff_select]
  simp only [wittPolynomial_eq_sum_C_mul_X_pow, selectPoly, map_sum, map_pow, map_mul,
    bind₁_X_right, bind₁_C_right, ← Finset.sum_add_distrib, ← mul_add]
  apply Finset.sum_congr rfl
  refine fun m _ => mul_eq_mul_left_iff.mpr (Or.inl ?_)
  rw [ite_pow, zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  by_cases Pm : P m
  · rw [if_pos Pm, if_neg <| not_not_intro Pm, zero_pow Fin.pos'.ne', add_zero]
  · rwa [if_neg Pm, if_pos, zero_add]

theorem coeff_add_of_disjoint (x y : 𝕎 R) (h : ∀ n, x.coeff n = 0 ∨ y.coeff n = 0) :
    (x + y).coeff n = x.coeff n + y.coeff n := by
  let P : ℕ → Prop := fun n => y.coeff n = 0
  haveI : DecidablePred P := Classical.decPred P
  set z := mk p fun n => if P n then x.coeff n else y.coeff n
  have hx : select P z = x := by
    ext1 n; rw [select, coeff_mk, coeff_mk]
    split_ifs with hn
    · rfl
    · rw [(h n).resolve_right hn]
  have hy : select (fun i => ¬P i) z = y := by
    ext1 n; rw [select, coeff_mk, coeff_mk]
    split_ifs with hn
    · exact hn.symm
    · rfl
  calc
    (x + y).coeff n = z.coeff n := by rw [← hx, ← hy, select_add_select_not P z]
    _ = x.coeff n + y.coeff n := by
      simp only [z, mk.eq_1]
      split_ifs with y0
      · rw [y0, add_zero]
      · rw [h n |>.resolve_right y0, zero_add]

end Select

variable [Fact p.Prime]

/-- `WittVector.init n x` is the Witt vector of which the first `n` coefficients are those from `x`
and all other coefficients are `0`.
See `WittVector.tail` for the complementary part.
-/
def init (n : ℕ) : 𝕎 R → 𝕎 R :=
  select fun i => i < n

/-- `WittVector.tail n x` is the Witt vector of which the first `n` coefficients are `0`
and all other coefficients are those from `x`.
See `WittVector.init` for the complementary part. -/
def tail (n : ℕ) : 𝕎 R → 𝕎 R :=
  select fun i => n ≤ i

@[simp]
theorem init_add_tail (x : 𝕎 R) (n : ℕ) : init n x + tail n x = x := by
  simp only [init, tail, ← not_lt, select_add_select_not]

end

/--
`init_ring` is an auxiliary tactic that discharges goals factoring `init` over ring operations.
-/
syntax (name := initRing) "init_ring" (" using " term)? : tactic

-- Porting note: this tactic requires that we turn hygiene off (note the free `n`).
-- TODO: make this tactic hygienic.
open Lean Elab Tactic in
elab_rules : tactic
| `(tactic| init_ring $[ using $a:term]?) => withMainContext <| set_option hygiene false in do
  evalTactic <|← `(tactic|(
    rw [WittVector.ext_iff]
    intro i
    simp only [WittVector.init, WittVector.select, WittVector.coeff_mk]
    split_ifs with hi <;> try {rfl}
    ))
  if let some e := a then
    evalTactic <|← `(tactic|(
      simp only [WittVector.add_coeff, WittVector.mul_coeff, WittVector.neg_coeff,
        WittVector.sub_coeff, WittVector.nsmul_coeff, WittVector.zsmul_coeff, WittVector.pow_coeff]
      apply MvPolynomial.eval₂Hom_congr' (RingHom.ext_int _ _) _ rfl
      rintro ⟨b, k⟩ h -
      replace h := $e:term p _ h
      simp only [Finset.mem_range, Finset.mem_product, true_and, Finset.mem_univ] at h
      have hk : k < n := by omega
      fin_cases b <;> simp only [Function.uncurry, Matrix.cons_val_zero, Matrix.head_cons,
        WittVector.coeff_mk, Matrix.cons_val_one, WittVector.mk, Fin.mk_zero, Matrix.cons_val',
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
        hk, if_true]
    ))

@[simp]
theorem init_init (x : 𝕎 R) (n : ℕ) : init n (init n x) = init n x := by
  init_ring

section
variable [Fact p.Prime]

theorem init_add (x y : 𝕎 R) (n : ℕ) : init n (x + y) = init n (init n x + init n y) := by
  init_ring using wittAdd_vars

theorem init_mul (x y : 𝕎 R) (n : ℕ) : init n (x * y) = init n (init n x * init n y) := by
  init_ring using wittMul_vars

theorem init_neg (x : 𝕎 R) (n : ℕ) : init n (-x) = init n (-init n x) := by
  init_ring using wittNeg_vars

theorem init_sub (x y : 𝕎 R) (n : ℕ) : init n (x - y) = init n (init n x - init n y) := by
  init_ring using wittSub_vars

theorem init_nsmul (m : ℕ) (x : 𝕎 R) (n : ℕ) : init n (m • x) = init n (m • init n x) := by
  init_ring using fun p [Fact (Nat.Prime p)] n => wittNSMul_vars p m n

theorem init_zsmul (m : ℤ) (x : 𝕎 R) (n : ℕ) : init n (m • x) = init n (m • init n x) := by
  init_ring using fun p [Fact (Nat.Prime p)] n => wittZSMul_vars p m n

theorem init_pow (m : ℕ) (x : 𝕎 R) (n : ℕ) : init n (x ^ m) = init n (init n x ^ m) := by
  init_ring using fun p [Fact (Nat.Prime p)] n => wittPow_vars p m n

end
section

variable (p)

/-- `WittVector.init n x` is polynomial in the coefficients of `x`. -/
theorem init_isPoly (n : ℕ) : IsPoly p fun _ _ => init n :=
  select_isPoly (P := fun i => i < n)

end

end

end WittVector
