/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

module

public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Matrices are isomorphic with linear maps between Lp spaces

This file provides a `WithLp` version of `Matrix.toLin'`.
-/

@[expose] public section

open Matrix ENNReal

variable {m n o R : Type*}

namespace Matrix
variable [Fintype n] [DecidableEq n] [CommRing R] (p q r : ℝ≥0∞)

open WithLp (toLp ofLp)

/-- `Matrix.toLin'` adapted for `PiLp R _`. -/
def toLpLin : Matrix m n R ≃ₗ[R] WithLp p (n → R) →ₗ[R] WithLp q (m → R) :=
  toLin' ≪≫ₗ
    (WithLp.linearEquiv _ R (n → R)).symm.arrowCongr
      (WithLp.linearEquiv _ R (m → R)).symm

@[simp]
lemma toLpLin_toLp (A : Matrix m n R) (x : n → R) :
    toLpLin p q A (toLp _ x) = toLp _ (Matrix.toLin' A x) := rfl

@[simp]
theorem ofLp_toLpLin (A : Matrix m n R) (x : WithLp p (n → R)) :
    ofLp (toLpLin p q A x) = Matrix.toLin' A (ofLp x) :=
  rfl

theorem toLpLin_apply (M : Matrix m n R) (v : WithLp p (n → R)) :
    toLpLin p q M v = toLp _ (M *ᵥ ofLp v) := rfl

theorem toLpLin_eq_toLin [Finite m] :
    toLpLin p q = Matrix.toLin (PiLp.basisFun p R n) (PiLp.basisFun q R m) :=
  rfl

@[simp]
theorem toLpLin_one : toLpLin p p (1 : Matrix n n R) = LinearMap.id := by ext; simp

/-- Note that applying this theorem needs an explicit choice of `q`. -/
theorem toLpLin_mul [Fintype o] [DecidableEq o] (A : Matrix m n R) (B : Matrix n o R) :
    toLpLin p r (A * B) = toLpLin q r A ∘ₗ toLpLin p q B := by
  ext; simp

/-- A copy of `toLpLin_mul` that works for `simp`, for the common case where the domain and codomain
have the same norm. -/
@[simp]
theorem toLpLin_mul_same [Fintype o] [DecidableEq o] (A : Matrix m n R) (B : Matrix n o R) :
    toLpLin p p (A * B) = toLpLin p p A ∘ₗ toLpLin p p B :=
  toLpLin_mul _ _ _ _ _

@[simp]
theorem toLpLin_symm_id : (toLpLin p p).symm .id = (1 : Matrix n n R) :=
  toLpLin p p |>.injective <| by simp

/-- Note that applying this theorem needs an explicit choice of `q`. -/
theorem toLpLin_symm_comp [Fintype o] [DecidableEq o]
    (A : WithLp q (n → R) →ₗ[R] WithLp r (m → R)) (B : WithLp p (o → R) →ₗ[R] WithLp q (n → R)) :
    (toLpLin p r).symm (A ∘ₗ B) = (toLpLin q r).symm A * (toLpLin p q).symm B :=
  toLpLin p r |>.injective <| by simp [toLpLin_mul (q := q)]

/-- `Matrix.toLinAlgEquiv'` adapted for `PiLp R _`. -/
@[simps!]
def toLpLinAlgEquiv : Matrix n n R ≃ₐ[R] Module.End R (WithLp p (n → R)) :=
  .ofLinearEquiv (toLpLin p p) (toLpLin_one p) (toLpLin_mul p p p)

@[simp]
theorem toLpLin_pow (A : Matrix n n R) (k : ℕ) : toLpLin p p (A ^ k) = toLpLin p p A ^ k :=
  map_pow (toLpLinAlgEquiv p) A k

@[simp]
theorem toLpLin_symm_pow (A : Module.End R (WithLp p (n → R))) (k : ℕ) :
    (toLpLin p p).symm (A ^ k) = (toLpLin p p).symm A ^ k :=
  map_pow (toLpLinAlgEquiv p).symm A k

end Matrix
