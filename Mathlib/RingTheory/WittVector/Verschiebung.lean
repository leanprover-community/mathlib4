/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.WittVector.Basic
import Mathlib.RingTheory.WittVector.IsPoly

#align_import ring_theory.witt_vector.verschiebung from "leanprover-community/mathlib"@"32b08ef840dd25ca2e47e035c5da03ce16d2dc3c"

/-!
## The Verschiebung operator

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

open MvPolynomial

variable {p : ℕ} {R S : Type*} [hp : Fact p.Prime] [CommRing R] [CommRing S]

local notation "𝕎" => WittVector p -- type as `\bbW`

noncomputable section

/-- `verschiebungFun x` shifts the coefficients of `x` up by one,
by inserting 0 as the 0th coefficient.
`x.coeff i` then becomes `(verchiebungFun x).coeff (i + 1)`.

`verschiebungFun` is the underlying function of the additive monoid hom `WittVector.verschiebung`.
-/
def verschiebungFun (x : 𝕎 R) : 𝕎 R :=
  @mk' p _ fun n => if n = 0 then 0 else x.coeff (n - 1)
#align witt_vector.verschiebung_fun WittVector.verschiebungFun

theorem verschiebungFun_coeff (x : 𝕎 R) (n : ℕ) :
    (verschiebungFun x).coeff n = if n = 0 then 0 else x.coeff (n - 1) := by
  simp only [verschiebungFun, ge_iff_le]
  -- 🎉 no goals
#align witt_vector.verschiebung_fun_coeff WittVector.verschiebungFun_coeff

theorem verschiebungFun_coeff_zero (x : 𝕎 R) : (verschiebungFun x).coeff 0 = 0 := by
  rw [verschiebungFun_coeff, if_pos rfl]
  -- 🎉 no goals
#align witt_vector.verschiebung_fun_coeff_zero WittVector.verschiebungFun_coeff_zero

@[simp]
theorem verschiebungFun_coeff_succ (x : 𝕎 R) (n : ℕ) :
    (verschiebungFun x).coeff n.succ = x.coeff n :=
  rfl
#align witt_vector.verschiebung_fun_coeff_succ WittVector.verschiebungFun_coeff_succ

@[ghost_simps]
theorem ghostComponent_zero_verschiebungFun (x : 𝕎 R) :
  ghostComponent 0 (verschiebungFun x) = 0 := by
  rw [ghostComponent_apply, aeval_wittPolynomial, Finset.range_one, Finset.sum_singleton,
    verschiebungFun_coeff_zero, pow_zero, pow_zero, pow_one, one_mul]
#align witt_vector.ghost_component_zero_verschiebung_fun WittVector.ghostComponent_zero_verschiebungFun

@[ghost_simps]
theorem ghostComponent_verschiebungFun (x : 𝕎 R) (n : ℕ) :
    ghostComponent (n + 1) (verschiebungFun x) = p * ghostComponent n x := by
  simp only [ghostComponent_apply, aeval_wittPolynomial]
  -- ⊢ (Finset.sum (Finset.range (n + 1 + 1)) fun i => ↑p ^ i * coeff (verschiebung …
  rw [Finset.sum_range_succ', verschiebungFun_coeff, if_pos rfl, zero_pow (pow_pos hp.1.pos _),
    mul_zero, add_zero, Finset.mul_sum, Finset.sum_congr rfl]
  rintro i -
  -- ⊢ ↑p ^ (i + 1) * coeff (verschiebungFun x) (i + 1) ^ p ^ (n + 1 - (i + 1)) = ↑ …
  simp only [pow_succ, mul_assoc, verschiebungFun_coeff, if_neg (Nat.succ_ne_zero i),
    Nat.succ_sub_succ, tsub_zero]
#align witt_vector.ghost_component_verschiebung_fun WittVector.ghostComponent_verschiebungFun

/-- The 0th Verschiebung polynomial is 0. For `n > 0`, the `n`th Verschiebung polynomial is the
variable `X (n-1)`.
-/
def verschiebungPoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  if n = 0 then 0 else X (n - 1)
#align witt_vector.verschiebung_poly WittVector.verschiebungPoly

@[simp]
theorem verschiebungPoly_zero : verschiebungPoly 0 = 0 :=
  rfl
#align witt_vector.verschiebung_poly_zero WittVector.verschiebungPoly_zero

theorem aeval_verschiebung_poly' (x : 𝕎 R) (n : ℕ) :
    aeval x.coeff (verschiebungPoly n) = (verschiebungFun x).coeff n := by
  cases' n with n
  -- ⊢ ↑(aeval x.coeff) (verschiebungPoly Nat.zero) = coeff (verschiebungFun x) Nat …
  · simp only [verschiebungPoly, Nat.zero_eq, ge_iff_le, tsub_eq_zero_of_le, ite_true, map_zero,
    verschiebungFun_coeff_zero]
  · rw [verschiebungPoly, verschiebungFun_coeff_succ, if_neg n.succ_ne_zero, aeval_X,
      Nat.succ_eq_add_one, add_tsub_cancel_right]
#align witt_vector.aeval_verschiebung_poly' WittVector.aeval_verschiebung_poly'

variable (p)

/-- `WittVector.verschiebung` has polynomial structure given by `WittVector.verschiebungPoly`.
-/
-- Porting note: replaced `@[is_poly]` with `instance`.
instance verschiebungFun_isPoly : IsPoly p fun R _Rcr => @verschiebungFun p R _Rcr := by
  use verschiebungPoly
  -- ⊢ ∀ ⦃R : Type ?u.111750⦄ [inst : CommRing R] (x : 𝕎 R), (verschiebungFun x).co …
  simp only [aeval_verschiebung_poly', eq_self_iff_true, forall₃_true_iff]
  -- 🎉 no goals
#align witt_vector.verschiebung_fun_is_poly WittVector.verschiebungFun_isPoly

-- Porting note: we add this example as a verification that Lean 4's instance resolution
-- can handle what in Lean 3 we needed the `@[is_poly]` attribute to help with.
example (p : ℕ) (f : ⦃R : Type _⦄ → [CommRing R] → WittVector p R → WittVector p R) [IsPoly p f] :
    IsPoly p (λ (R : Type*) (I : CommRing R) => verschiebungFun ∘ (@f R I)) :=
  inferInstance

variable {p}

/--
`verschiebung x` shifts the coefficients of `x` up by one, by inserting 0 as the 0th coefficient.
`x.coeff i` then becomes `(verchiebung x).coeff (i + 1)`.

This is an additive monoid hom with underlying function `verschiebung_fun`.
-/
noncomputable def verschiebung : 𝕎 R →+ 𝕎 R where
  toFun := verschiebungFun
  map_zero' := by
    ext ⟨⟩ <;> rw [verschiebungFun_coeff] <;>
    -- ⊢ coeff (verschiebungFun 0) Nat.zero = coeff 0 Nat.zero
               -- ⊢ (if Nat.zero = 0 then 0 else coeff 0 (Nat.zero - 1)) = coeff 0 Nat.zero
               -- ⊢ (if Nat.succ n✝ = 0 then 0 else coeff 0 (Nat.succ n✝ - 1)) = coeff 0 (Nat.su …
      simp only [if_true, eq_self_iff_true, zero_coeff, ite_self]
      -- 🎉 no goals
      -- 🎉 no goals
  map_add' := by
    dsimp
    -- ⊢ ∀ (x y : 𝕎 R), verschiebungFun (x + y) = verschiebungFun x + verschiebungFun y
    ghost_calc _ _
    -- ⊢ ∀ (n : ℕ), ↑(ghostComponent n) (verschiebungFun (x✝ + y✝)) = ↑(ghostComponen …
    rintro ⟨⟩ <;> -- Uses the dumb induction principle, hence adding `Nat.zero_eq` to ghost_simps.
    -- ⊢ ↑(ghostComponent Nat.zero) (verschiebungFun (x✝ + y✝)) = ↑(ghostComponent Na …
      ghost_simp
      -- 🎉 no goals
      -- 🎉 no goals
#align witt_vector.verschiebung WittVector.verschiebung

/-- `WittVector.verschiebung` is a polynomial function. -/
@[is_poly]
theorem verschiebung_isPoly : IsPoly p fun R _Rcr => @verschiebung p R hp _Rcr :=
  verschiebungFun_isPoly p
#align witt_vector.verschiebung_is_poly WittVector.verschiebung_isPoly

/-- verschiebung is a natural transformation -/
@[simp]
theorem map_verschiebung (f : R →+* S) (x : 𝕎 R) :
    map f (verschiebung x) = verschiebung (map f x) := by ext ⟨-, -⟩; exact f.map_zero; rfl
                                                          -- ⊢ coeff (↑(map f) (↑verschiebung x)) Nat.zero = coeff (↑verschiebung (↑(map f) …
                                                                      -- ⊢ coeff (↑(map f) (↑verschiebung x)) (Nat.succ n✝) = coeff (↑verschiebung (↑(m …
                                                                                        -- 🎉 no goals
#align witt_vector.map_verschiebung WittVector.map_verschiebung

@[ghost_simps]
theorem ghostComponent_zero_verschiebung (x : 𝕎 R) : ghostComponent 0 (verschiebung x) = 0 :=
  ghostComponent_zero_verschiebungFun _
#align witt_vector.ghost_component_zero_verschiebung WittVector.ghostComponent_zero_verschiebung

@[ghost_simps]
theorem ghostComponent_verschiebung (x : 𝕎 R) (n : ℕ) :
    ghostComponent (n + 1) (verschiebung x) = p * ghostComponent n x :=
  ghostComponent_verschiebungFun _ _
#align witt_vector.ghost_component_verschiebung WittVector.ghostComponent_verschiebung

@[simp]
theorem verschiebung_coeff_zero (x : 𝕎 R) : (verschiebung x).coeff 0 = 0 :=
  rfl
#align witt_vector.verschiebung_coeff_zero WittVector.verschiebung_coeff_zero

-- simp_nf complains if this is simp
theorem verschiebung_coeff_add_one (x : 𝕎 R) (n : ℕ) :
    (verschiebung x).coeff (n + 1) = x.coeff n :=
  rfl
#align witt_vector.verschiebung_coeff_add_one WittVector.verschiebung_coeff_add_one

@[simp]
theorem verschiebung_coeff_succ (x : 𝕎 R) (n : ℕ) : (verschiebung x).coeff n.succ = x.coeff n :=
  rfl
#align witt_vector.verschiebung_coeff_succ WittVector.verschiebung_coeff_succ

theorem aeval_verschiebungPoly (x : 𝕎 R) (n : ℕ) :
    aeval x.coeff (verschiebungPoly n) = (verschiebung x).coeff n :=
  aeval_verschiebung_poly' x n
#align witt_vector.aeval_verschiebung_poly WittVector.aeval_verschiebungPoly

@[simp]
theorem bind₁_verschiebungPoly_wittPolynomial (n : ℕ) :
    bind₁ verschiebungPoly (wittPolynomial p ℤ n) =
      if n = 0 then 0 else p * wittPolynomial p ℤ (n - 1) := by
  apply MvPolynomial.funext
  -- ⊢ ∀ (x : ℕ → ℤ), ↑(MvPolynomial.eval x) (↑(bind₁ verschiebungPoly) (wittPolyno …
  intro x
  -- ⊢ ↑(MvPolynomial.eval x) (↑(bind₁ verschiebungPoly) (wittPolynomial p ℤ n)) =  …
  split_ifs with hn
  -- ⊢ ↑(MvPolynomial.eval x) (↑(bind₁ verschiebungPoly) (wittPolynomial p ℤ n)) =  …
  · simp only [hn, wittPolynomial_zero, bind₁_X_right, verschiebungPoly_zero, map_zero, ite_true]
    -- 🎉 no goals
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    -- ⊢ ↑(MvPolynomial.eval x) (↑(bind₁ verschiebungPoly) (wittPolynomial p ℤ (Nat.s …
    rw [Nat.succ_eq_add_one, add_tsub_cancel_right]
    -- ⊢ ↑(MvPolynomial.eval x) (↑(bind₁ verschiebungPoly) (wittPolynomial p ℤ (n + 1 …
    simp only [add_eq_zero, and_false, ite_false, map_mul]
    -- ⊢ ↑(MvPolynomial.eval x) (↑(bind₁ verschiebungPoly) (wittPolynomial p ℤ (n + 1 …
    rw [map_natCast, hom_bind₁]
    -- ⊢ ↑(eval₂Hom (RingHom.comp (MvPolynomial.eval x) C) fun i => ↑(MvPolynomial.ev …
    calc
      _ = ghostComponent (n + 1) (verschiebung <| mk p x) := by
       apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
       simp only [← aeval_verschiebungPoly, coeff_mk]
       funext k
       exact eval₂Hom_congr (RingHom.ext_int _ _) rfl rfl
      _ = _ := by rw [ghostComponent_verschiebung]; rfl
#align witt_vector.bind₁_verschiebung_poly_witt_polynomial WittVector.bind₁_verschiebungPoly_wittPolynomial

end

end WittVector
