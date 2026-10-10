/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The ring of symmetric functions `Λ_ℚ`, presented by power sums

`SymmFun R` is the ring of symmetric functions in countably many variables.
When `R` is a `ℚ`-algebra, it can be presented freely
by its power-sum generators `p 1, p 2, p 3, ...`.
This use of rational coefficients allows avoidance of more
complicated Newton identities if we were to use elementary symmetric functions
and `R` as integers instead.

`Mathlib.RingTheory.MvPolynomial.Symmetric` provides the finite-variable symmetric polynomials
`MvPolynomial.psum`, but for the purpose of the universal lambda ring structure here, we need this
instead.
-/

/-- The ring of symmetric functions in countably many variables
presented freely by its power sums.
`SymmFun R := MvPolynomial ℕ R`, where the generator `X n` stands for the power sum `p (n + 1)`.
This presentation *is* `Λ_R` only once `ℚ ⊆ R`, so the
hypothesis is carried on the type itself rather than left implicit. -/
@[nolint unusedArguments]
public abbrev SymmFun (R : Type*) [CommRing R] [Algebra ℚ R] :=
  MvPolynomial ℕ R

namespace SymmFun

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- `p_n` inside `SymmFun R` for `n ≥ 1`. -/
@[expose] public noncomputable def p (n : ℕ) (_hn : 0 < n) :
  SymmFun R := MvPolynomial.X (n - 1)

/-- The power sum inside `SymmFun R` are
the `X_{n-1}` variables of the `MvPolynomial` -/
public theorem p_def (n : ℕ) (hn : 0 < n) :
  p n hn = (MvPolynomial.X (n - 1) : SymmFun R) := rfl

/-- Evaluate a symmetric function at
`X = x_1 + ... + x_m` which turns
the abstract `p_n` into the concrete `p_n(x_1, ..., x_m)`. -/
public noncomputable def realize (m : ℕ) :
  SymmFun R →ₐ[R] MvPolynomial (Fin m) R :=
  MvPolynomial.aeval fun n => MvPolynomial.psum (Fin m) R (n + 1)

/-- Evaluating `p_n` at `X = x_1 + ... x_m`
gives the concrete `p_n(x_1, ..., x_m)`. -/
@[simp]
public theorem realize_p (m n : ℕ) (hn : 0 < n) :
    realize m (p n hn) = MvPolynomial.psum (Fin m) R n := by
  rw [p_def]
  change MvPolynomial.aeval (fun k => MvPolynomial.psum (Fin m) R (k + 1))
      (MvPolynomial.X (n - 1) : SymmFun R) = MvPolynomial.psum (Fin m) R n
  rw [MvPolynomial.aeval_X, Nat.sub_add_cancel hn]

open scoped TensorProduct

/-!
## Hopf algebra structure

The Hopf algebra structure on `SymmFun R`
is the one where `p_n`'s are primitive
and `ε p_n = 0`. This is what makes the choice
of rationals being present such an advantage.
It is much easier to get this structure and
many applications will often have `ℚ`-algebras anyway.
-/

/-- The comultiplication making every power sum primitive
`Δ(p n) = p n ⊗ 1 + 1 ⊗ p n`. -/
public noncomputable def comul : SymmFun R →ₐ[R] SymmFun R ⊗[R] SymmFun R :=
  MvPolynomial.aeval fun n => (MvPolynomial.X n : SymmFun R) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] MvPolynomial.X n

/-- The counit killing every power sum: `ε (p n) = 0`. -/
public noncomputable def counit : SymmFun R →ₐ[R] R :=
  MvPolynomial.aeval fun _ => (0 : R)

/-- Helper for constructing the `Bialgebra` instance below -/
theorem comul_apply_X (n : ℕ) :
    comul (R := R) (MvPolynomial.X n : SymmFun R) =
      (MvPolynomial.X n : SymmFun R) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] (MvPolynomial.X n : SymmFun R) :=
  MvPolynomial.aeval_X _ _

/-- Helper for constructing the `Bialgebra` instance below -/
theorem counit_apply_X (n : ℕ) : counit (R := R) (MvPolynomial.X n : SymmFun R) = 0 :=
  MvPolynomial.aeval_X _ _

/-- The counit and comultiplication above combine consistently to form a bialgebra -/
public noncomputable instance : Bialgebra R (SymmFun R) :=
  .ofAlgHom comul counit
    (by
      ext1 n
      simp [comul_apply_X, Algebra.TensorProduct.one_def, TensorProduct.add_tmul,
        TensorProduct.tmul_add]
      abel)
    (by ext1 n; simp [comul_apply_X, counit_apply_X])
    (by ext1 n; simp [comul_apply_X, counit_apply_X])

/-- `Δ (p_n) = p_n ⊗ 1 + 1 ⊗ p_n` -/
@[simp]
public theorem comul_X (n : ℕ) :
    Coalgebra.comul (R := R) (MvPolynomial.X n : SymmFun R) =
      (MvPolynomial.X n : SymmFun R) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] (MvPolynomial.X n : SymmFun R) :=
  comul_apply_X n

/-- `ε (p n) = 0`. -/
@[simp]
theorem counit_X (n : ℕ) : Coalgebra.counit (R := R) (MvPolynomial.X n : SymmFun R) = 0 :=
  counit_apply_X n

/-- `Δ (p_n) = p_n ⊗ 1 + 1 ⊗ p_n` -/
@[simp]
public theorem comul_p (n : ℕ) (hn : 0 < n) :
    Coalgebra.comul (R := R) (p n hn : SymmFun R)
      = (p n hn : SymmFun R) ⊗ₜ[R] (1 : SymmFun R) + 1 ⊗ₜ[R] (p n hn : SymmFun R) := by
  rw [p_def]; exact comul_X (n - 1)

/-- `ε (p n) = 0`. -/
@[simp]
public theorem counit_p (n : ℕ) (hn : 0 < n) :
  Coalgebra.counit (R := R) (p n hn : SymmFun R) = 0 := by
  rw [p_def]; exact counit_X (n - 1)

/-- The antipode, negating every power sum:
`S(p n) = -p n` -/
public noncomputable def antipode : SymmFun R →ₐ[R] SymmFun R :=
  MvPolynomial.aeval fun n => -(MvPolynomial.X n : SymmFun R)

/- The antipode on just `p_n` does satisfy `S(p_n) = -p_n` -/
@[simp]
theorem antipode_X (n : ℕ) :
    antipode (R := R) (MvPolynomial.X n : SymmFun R) = -(MvPolynomial.X n : SymmFun R) :=
  MvPolynomial.aeval_X _ _

/-- The bialgebra and antipode consistently combine to make `Λ_R` into a Hopf algebra. -/
public noncomputable instance : HopfAlgebra R (SymmFun R) :=
  .ofAlgHom antipode
    (by
      ext1 n
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, comul_X, map_add]
      erw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
      simp [antipode_X, counit_X])
    (by
      ext1 n
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, comul_X, map_add]
      erw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
      simp [antipode_X, counit_X])

/-- `S (p_n) = -p_n`. -/
@[simp]
public theorem antipode_p (n : ℕ) (hn : 0 < n) :
    HopfAlgebra.antipode (R := R) (p n hn : SymmFun R) = -(p n hn : SymmFun R) := by
  rw [p_def]; exact antipode_X (n - 1)

end SymmFun
