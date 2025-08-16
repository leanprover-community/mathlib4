import Mathlib.Tactic.Ring.NamePolyVars

set_option trace.name_poly_vars true

axiom Polynomial : Type → Type
axiom Polynomial.C {R : Type} : R → Polynomial R
axiom Polynomial.X {R : Type} : Polynomial R

#register_poly_vars "[" X "]" Polynomial Polynomial.C Polynomial.X

variable (R : Type)

axiom MvPolynomial : Type → Type → Type
axiom MvPolynomial.C {σ R : Type} : R → MvPolynomial σ R
axiom MvPolynomial.X {σ R : Type} (i : σ) : MvPolynomial σ R

#register_poly_vars "[" X, ... "]" MvPolynomial MvPolynomial.C MvPolynomial.X

#name_poly_vars R[a,b][C]

noncomputable example : Vector (R[a,b][C]) 3 :=
  have : Polynomial (MvPolynomial (Fin 2) R) = R[a,b][C] := rfl
  have : Polynomial.C (MvPolynomial.X 0) = a := rfl
  have : Polynomial.C (MvPolynomial.X 1) = b := rfl
  have : Polynomial.X = C := rfl
  #v[a, b, C]
