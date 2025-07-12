/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Group action on rings applied to polynomials

This file contains instances and definitions relating `MulSemiringAction` to `Polynomial`.
-/


variable (M : Type*) [Monoid M]

open Polynomial

namespace Polynomial

variable (R : Type*) [Semiring R]

variable {M} in
-- In this statement, we use `HSMul.hSMul m` as LHS instead of `(m • ·)`
-- to avoid a spurious lambda-expression that complicates rewriting with this lemma.
theorem smul_eq_map [MulSemiringAction M R] (m : M) :
    HSMul.hSMul m = map (MulSemiringAction.toRingHom M R m) := by
  ext
  simp

noncomputable instance [MulSemiringAction M R] : MulSemiringAction M R[X] :=
  { Polynomial.distribMulAction with
    smul_one := fun m ↦
      smul_eq_map R m ▸ Polynomial.map_one (MulSemiringAction.toRingHom M R m)
    smul_mul := fun m _ _ ↦
      smul_eq_map R m ▸ Polynomial.map_mul (MulSemiringAction.toRingHom M R m) }

variable {M R}
variable [MulSemiringAction M R]

@[simp]
theorem smul_X (m : M) : (m • X : R[X]) = X :=
  (smul_eq_map R m).symm ▸ map_X _

variable (S : Type*) [CommSemiring S] [MulSemiringAction M S]

theorem smul_eval_smul (m : M) (f : S[X]) (x : S) : (m • f).eval (m • x) = m • f.eval x :=
  Polynomial.induction_on f (fun r ↦ by rw [smul_C, eval_C, eval_C])
    (fun f g ihf ihg ↦ by rw [smul_add, eval_add, ihf, ihg, eval_add, smul_add]) fun n r _ ↦ by
    rw [smul_mul', smul_pow', smul_C, smul_X, eval_mul, eval_C, eval_pow, eval_X, eval_mul, eval_C,
      eval_pow, eval_X, smul_mul', smul_pow']

variable (G : Type*) [Group G]

theorem eval_smul' [MulSemiringAction G S] (g : G) (f : S[X]) (x : S) :
    f.eval (g • x) = g • (g⁻¹ • f).eval x := by
  rw [← smul_eval_smul, smul_inv_smul]

theorem smul_eval [MulSemiringAction G S] (g : G) (f : S[X]) (x : S) :
    (g • f).eval x = g • f.eval (g⁻¹ • x) := by
  rw [← smul_eval_smul, smul_inv_smul]

end Polynomial

section CommRing

variable (G : Type*) [Group G] [Fintype G]
variable (R : Type*) [CommRing R] [MulSemiringAction G R]

open MulAction

/-- the product of `(X - g • x)` over distinct `g • x`. -/
noncomputable def prodXSubSMul (x : R) : R[X] :=
  letI := Classical.decEq R
  (Finset.univ : Finset (G ⧸ MulAction.stabilizer G x)).prod fun g ↦
    Polynomial.X - Polynomial.C (ofQuotientStabilizer G x g)

theorem prodXSubSMul.monic (x : R) : (prodXSubSMul G R x).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ ↦ Polynomial.monic_X_sub_C _

theorem prodXSubSMul.eval (x : R) : (prodXSubSMul G R x).eval x = 0 :=
  letI := Classical.decEq R
  (map_prod ((Polynomial.aeval x).toRingHom.toMonoidHom : R[X] →* R) _ _).trans <|
    Finset.prod_eq_zero (Finset.mem_univ <| QuotientGroup.mk 1) <| by simp

theorem prodXSubSMul.smul (x : R) (g : G) : g • prodXSubSMul G R x = prodXSubSMul G R x :=
  letI := Classical.decEq R
  Finset.smul_prod'.trans <|
    Fintype.prod_bijective _ (MulAction.bijective g) _ _ fun g' ↦ by
      rw [ofQuotientStabilizer_smul, smul_sub, Polynomial.smul_X, Polynomial.smul_C]

theorem prodXSubSMul.coeff (x : R) (g : G) (n : ℕ) :
    g • (prodXSubSMul G R x).coeff n = (prodXSubSMul G R x).coeff n := by
  rw [← Polynomial.coeff_smul, prodXSubSMul.smul]

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
      (fun b ↦ by rw [MonoidHom.id_apply, smul_C, map_C, coe_fn_coe, g.map_smul, map_C,
          coe_fn_coe, smul_C])
      (fun p q ihp ihq ↦ by
        rw [smul_add, Polynomial.map_add, ihp, ihq, Polynomial.map_add, smul_add])
      fun n b _ ↦ by rw [MonoidHom.id_apply, smul_mul', smul_C, smul_pow', smul_X,
        Polynomial.map_mul, map_C, Polynomial.map_pow,
        map_X, coe_fn_coe, g.map_smul, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
        smul_mul', smul_C, smul_pow', smul_X, coe_fn_coe]
  map_zero' := Polynomial.map_zero (g : P →+* Q)
  map_add' _ _ := Polynomial.map_add (g : P →+* Q)
  map_one' := Polynomial.map_one (g : P →+* Q)
  map_mul' _ _ := Polynomial.map_mul (g : P →+* Q)

@[simp]
theorem coe_polynomial (g : P →+*[M] Q) : (g.polynomial : P[X] → Q[X]) = map g := rfl

end MulSemiringActionHom
