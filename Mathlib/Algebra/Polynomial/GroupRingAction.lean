/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.GroupRingAction.Basic
import Mathlib.Algebra.Hom.GroupAction
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Data.Polynomial.Monic
import Mathlib.GroupTheory.GroupAction.Quotient

#align_import algebra.polynomial.group_ring_action from "leanprover-community/mathlib"@"afad8e438d03f9d89da2914aa06cb4964ba87a18"

/-!
# Group action on rings applied to polynomials

This file contains instances and definitions relating `MulSemiringAction` to `Polynomial`.
-/


variable (M : Type*) [Monoid M]

open Polynomial

namespace Polynomial

variable (R : Type*) [Semiring R]

variable {M}

-- porting note: changed `(· • ·) m` to `HSMul.hSMul m`
theorem smul_eq_map [MulSemiringAction M R] (m : M) :
    HSMul.hSMul m = map (MulSemiringAction.toRingHom M R m) := by
  suffices DistribMulAction.toAddMonoidHom R[X] m =
      (mapRingHom (MulSemiringAction.toRingHom M R m)).toAddMonoidHom by
    ext1 r
    exact FunLike.congr_fun this r
  ext n r : 2
  -- ⊢ ↑(AddMonoidHom.comp (DistribMulAction.toAddMonoidHom R[X] m) (LinearMap.toAd …
  change m • monomial n r = map (MulSemiringAction.toRingHom M R m) (monomial n r)
  -- ⊢ m • ↑(monomial n) r = map (MulSemiringAction.toRingHom M R m) (↑(monomial n) …
  rw [Polynomial.map_monomial, Polynomial.smul_monomial, MulSemiringAction.toRingHom_apply]
  -- 🎉 no goals
#align polynomial.smul_eq_map Polynomial.smul_eq_map

variable (M)

noncomputable instance [MulSemiringAction M R] : MulSemiringAction M R[X] :=
  { Polynomial.distribMulAction with
    smul := (· • ·)
    smul_one := fun m ↦
      smul_eq_map R m ▸ Polynomial.map_one (MulSemiringAction.toRingHom M R m)
    smul_mul := fun m _ _ ↦
      smul_eq_map R m ▸ Polynomial.map_mul (MulSemiringAction.toRingHom M R m) }

variable {M R}

variable [MulSemiringAction M R]

@[simp]
theorem smul_X (m : M) : (m • X : R[X]) = X :=
  (smul_eq_map R m).symm ▸ map_X _
set_option linter.uppercaseLean3 false in
#align polynomial.smul_X Polynomial.smul_X

variable (S : Type*) [CommSemiring S] [MulSemiringAction M S]

theorem smul_eval_smul (m : M) (f : S[X]) (x : S) : (m • f).eval (m • x) = m • f.eval x :=
  Polynomial.induction_on f (fun r ↦ by rw [smul_C, eval_C, eval_C])
                                        -- 🎉 no goals
    (fun f g ihf ihg ↦ by rw [smul_add, eval_add, ihf, ihg, eval_add, smul_add]) fun n r _ ↦ by
                          -- 🎉 no goals
    rw [smul_mul', smul_pow', smul_C, smul_X, eval_mul, eval_C, eval_pow, eval_X, eval_mul, eval_C,
      eval_pow, eval_X, smul_mul', smul_pow']
#align polynomial.smul_eval_smul Polynomial.smul_eval_smul

variable (G : Type*) [Group G]

theorem eval_smul' [MulSemiringAction G S] (g : G) (f : S[X]) (x : S) :
    f.eval (g • x) = g • (g⁻¹ • f).eval x := by
  rw [← smul_eval_smul, smul_inv_smul]
  -- 🎉 no goals
#align polynomial.eval_smul' Polynomial.eval_smul'

theorem smul_eval [MulSemiringAction G S] (g : G) (f : S[X]) (x : S) :
    (g • f).eval x = g • f.eval (g⁻¹ • x) := by
  rw [← smul_eval_smul, smul_inv_smul]
  -- 🎉 no goals
#align polynomial.smul_eval Polynomial.smul_eval

end Polynomial

section CommRing
set_option linter.uppercaseLean3 false  -- porting note: `prod_X_*`

variable (G : Type*) [Group G] [Fintype G]

variable (R : Type*) [CommRing R] [MulSemiringAction G R]

open MulAction

open Classical

/-- the product of `(X - g • x)` over distinct `g • x`. -/
noncomputable def prodXSubSmul (x : R) : R[X] :=
  (Finset.univ : Finset (G ⧸ MulAction.stabilizer G x)).prod fun g ↦
    Polynomial.X - Polynomial.C (ofQuotientStabilizer G x g)
#align prod_X_sub_smul prodXSubSmul

theorem prodXSubSmul.monic (x : R) : (prodXSubSmul G R x).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ ↦ Polynomial.monic_X_sub_C _
#align prod_X_sub_smul.monic prodXSubSmul.monic

theorem prodXSubSmul.eval (x : R) : (prodXSubSmul G R x).eval x = 0 :=
  (map_prod ((Polynomial.aeval x).toRingHom.toMonoidHom : R[X] →* R) _ _).trans <|
    Finset.prod_eq_zero (Finset.mem_univ <| QuotientGroup.mk 1) <| by simp
                                                                      -- 🎉 no goals
#align prod_X_sub_smul.eval prodXSubSmul.eval

theorem prodXSubSmul.smul (x : R) (g : G) : g • prodXSubSmul G R x = prodXSubSmul G R x :=
  Finset.smul_prod.trans <|
    Fintype.prod_bijective _ (MulAction.bijective g) _ _ fun g' ↦ by
      rw [ofQuotientStabilizer_smul, smul_sub, Polynomial.smul_X, Polynomial.smul_C]
      -- 🎉 no goals
#align prod_X_sub_smul.smul prodXSubSmul.smul

theorem prodXSubSmul.coeff (x : R) (g : G) (n : ℕ) :
    g • (prodXSubSmul G R x).coeff n = (prodXSubSmul G R x).coeff n := by
  rw [← Polynomial.coeff_smul, prodXSubSmul.smul]
  -- 🎉 no goals
#align prod_X_sub_smul.coeff prodXSubSmul.coeff

end CommRing

namespace MulSemiringActionHom

variable {M}

variable {P : Type*} [CommSemiring P] [MulSemiringAction M P]

variable {Q : Type*} [CommSemiring Q] [MulSemiringAction M Q]

open Polynomial

/-- An equivariant map induces an equivariant map on polynomials. -/
protected noncomputable def polynomial (g : P →+*[M] Q) : P[X] →+*[M] Q[X] where
  toFun := map g
  map_smul' m p :=
    Polynomial.induction_on p
      (fun b ↦ by rw [smul_C, map_C, coe_fn_coe, g.map_smul, map_C, coe_fn_coe, smul_C])
                  -- 🎉 no goals
      (fun p q ihp ihq ↦ by
        rw [smul_add, Polynomial.map_add, ihp, ihq, Polynomial.map_add, smul_add])
        -- 🎉 no goals
      fun n b _ ↦ by
      rw [smul_mul', smul_C, smul_pow', smul_X, Polynomial.map_mul, map_C, Polynomial.map_pow,
        map_X, coe_fn_coe, g.map_smul, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
        smul_mul', smul_C, smul_pow', smul_X, coe_fn_coe]
  -- porting note: added `.toRingHom`
  map_zero' := Polynomial.map_zero g.toRingHom
  map_add' p q := Polynomial.map_add g.toRingHom
  map_one' := Polynomial.map_one g.toRingHom
  map_mul' p q := Polynomial.map_mul g.toRingHom
#align mul_semiring_action_hom.polynomial MulSemiringActionHom.polynomial

@[simp]
theorem coe_polynomial (g : P →+*[M] Q) : (g.polynomial : P[X] → Q[X]) = map g := rfl
#align mul_semiring_action_hom.coe_polynomial MulSemiringActionHom.coe_polynomial

end MulSemiringActionHom
