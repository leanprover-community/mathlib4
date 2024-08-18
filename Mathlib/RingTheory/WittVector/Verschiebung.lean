/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.WittVector.Basic
import Mathlib.RingTheory.WittVector.IsPoly

/-!
## The Verschiebung operator

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

open MvPolynomial

variable {p : ℕ} {R S : Type*} [CommRing R] [CommRing S]

local notation "𝕎" => WittVector p -- type as `\bbW`

noncomputable section

/-- `verschiebungFun x` shifts the coefficients of `x` up by one,
by inserting 0 as the 0th coefficient.
`x.coeff i` then becomes `(verchiebungFun x).coeff (i + 1)`.

`verschiebungFun` is the underlying function of the additive monoid hom `WittVector.verschiebung`.
-/
def verschiebungFun (x : 𝕎 R) : 𝕎 R :=
  @mk' p _ fun n => if n = 0 then 0 else x.coeff (n - 1)

theorem verschiebungFun_coeff (x : 𝕎 R) (n : ℕ) :
    (verschiebungFun x).coeff n = if n = 0 then 0 else x.coeff (n - 1) := by
  simp only [verschiebungFun]

theorem verschiebungFun_coeff_zero (x : 𝕎 R) : (verschiebungFun x).coeff 0 = 0 := by
  rw [verschiebungFun_coeff, if_pos rfl]

@[simp]
theorem verschiebungFun_coeff_succ (x : 𝕎 R) (n : ℕ) :
    (verschiebungFun x).coeff n.succ = x.coeff n :=
  rfl

@[ghost_simps]
theorem ghostComponent_zero_verschiebungFun [hp : Fact p.Prime] (x : 𝕎 R) :
    ghostComponent 0 (verschiebungFun x) = 0 := by
  rw [ghostComponent_apply, aeval_wittPolynomial, Finset.range_one, Finset.sum_singleton,
    verschiebungFun_coeff_zero, pow_zero, pow_zero, pow_one, one_mul]

@[ghost_simps]
theorem ghostComponent_verschiebungFun [hp : Fact p.Prime] (x : 𝕎 R) (n : ℕ) :
    ghostComponent (n + 1) (verschiebungFun x) = p * ghostComponent n x := by
  simp only [ghostComponent_apply, aeval_wittPolynomial]
  rw [Finset.sum_range_succ', verschiebungFun_coeff, if_pos rfl,
    zero_pow (pow_ne_zero _ hp.1.ne_zero), mul_zero, add_zero, Finset.mul_sum, Finset.sum_congr rfl]
  rintro i -
  simp only [pow_succ', verschiebungFun_coeff_succ, Nat.succ_sub_succ_eq_sub, mul_assoc]

/-- The 0th Verschiebung polynomial is 0. For `n > 0`, the `n`th Verschiebung polynomial is the
variable `X (n-1)`.
-/
def verschiebungPoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  if n = 0 then 0 else X (n - 1)

@[simp]
theorem verschiebungPoly_zero : verschiebungPoly 0 = 0 :=
  rfl

theorem aeval_verschiebung_poly' (x : 𝕎 R) (n : ℕ) :
    aeval x.coeff (verschiebungPoly n) = (verschiebungFun x).coeff n := by
  cases' n with n
  · simp only [verschiebungPoly, ite_true, map_zero, verschiebungFun_coeff_zero]
  · rw [verschiebungPoly, verschiebungFun_coeff_succ, if_neg n.succ_ne_zero, aeval_X,
      add_tsub_cancel_right]

variable (p)

/-- `WittVector.verschiebung` has polynomial structure given by `WittVector.verschiebungPoly`.
-/
-- Porting note: replaced `@[is_poly]` with `instance`.
instance verschiebungFun_isPoly : IsPoly p fun R _Rcr => @verschiebungFun p R _Rcr := by
  use verschiebungPoly
  simp only [aeval_verschiebung_poly', eq_self_iff_true, forall₃_true_iff]

-- Porting note: we add this example as a verification that Lean 4's instance resolution
-- can handle what in Lean 3 we needed the `@[is_poly]` attribute to help with.
example (p : ℕ) (f : ⦃R : Type _⦄ → [CommRing R] → WittVector p R → WittVector p R) [IsPoly p f] :
    IsPoly p (fun (R : Type*) (I : CommRing R) ↦ verschiebungFun ∘ (@f R I)) :=
  inferInstance

variable {p}
variable [hp : Fact p.Prime]

/--
`verschiebung x` shifts the coefficients of `x` up by one, by inserting 0 as the 0th coefficient.
`x.coeff i` then becomes `(verchiebung x).coeff (i + 1)`.

This is an additive monoid hom with underlying function `verschiebung_fun`.
-/
noncomputable def verschiebung : 𝕎 R →+ 𝕎 R where
  toFun := verschiebungFun
  map_zero' := by
    ext ⟨⟩ <;> rw [verschiebungFun_coeff] <;>
      simp only [if_true, eq_self_iff_true, zero_coeff, ite_self]
  map_add' := by
    dsimp
    ghost_calc _ _
    rintro ⟨⟩ <;> ghost_simp

/-- `WittVector.verschiebung` is a polynomial function. -/
@[is_poly]
theorem verschiebung_isPoly : IsPoly p fun _ _ => verschiebung (p := p) :=
  verschiebungFun_isPoly p

/-- verschiebung is a natural transformation -/
@[simp]
theorem map_verschiebung (f : R →+* S) (x : 𝕎 R) :
    map f (verschiebung x) = verschiebung (map f x) := by
  ext ⟨-, -⟩
  · exact f.map_zero
  · rfl

@[ghost_simps]
theorem ghostComponent_zero_verschiebung (x : 𝕎 R) : ghostComponent 0 (verschiebung x) = 0 :=
  ghostComponent_zero_verschiebungFun _

@[ghost_simps]
theorem ghostComponent_verschiebung (x : 𝕎 R) (n : ℕ) :
    ghostComponent (n + 1) (verschiebung x) = p * ghostComponent n x :=
  ghostComponent_verschiebungFun _ _

@[simp]
theorem verschiebung_coeff_zero (x : 𝕎 R) : (verschiebung x).coeff 0 = 0 :=
  rfl

-- simp_nf complains if this is simp
theorem verschiebung_coeff_add_one (x : 𝕎 R) (n : ℕ) :
    (verschiebung x).coeff (n + 1) = x.coeff n :=
  rfl

@[simp]
theorem verschiebung_coeff_succ (x : 𝕎 R) (n : ℕ) : (verschiebung x).coeff n.succ = x.coeff n :=
  rfl

theorem aeval_verschiebungPoly (x : 𝕎 R) (n : ℕ) :
    aeval x.coeff (verschiebungPoly n) = (verschiebung x).coeff n :=
  aeval_verschiebung_poly' x n

@[simp]
theorem bind₁_verschiebungPoly_wittPolynomial (n : ℕ) :
    bind₁ verschiebungPoly (wittPolynomial p ℤ n) =
      if n = 0 then 0 else p * wittPolynomial p ℤ (n - 1) := by
  apply MvPolynomial.funext
  intro x
  split_ifs with hn
  · simp only [hn, wittPolynomial_zero, bind₁_X_right, verschiebungPoly_zero, map_zero, ite_true]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [Nat.succ_eq_add_one, add_tsub_cancel_right]
    simp only [add_eq_zero, and_false, ite_false, map_mul]
    rw [map_natCast, hom_bind₁]
    calc
      _ = ghostComponent (n + 1) (verschiebung <| mk p x) := by
       apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
       funext k
       simp only [← aeval_verschiebungPoly]
       exact eval₂Hom_congr (RingHom.ext_int _ _) rfl rfl
      _ = _ := by rw [ghostComponent_verschiebung]; rfl

end

end WittVector
