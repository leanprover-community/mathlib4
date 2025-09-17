-- import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.Ring.NamePolyVars

-- set_option trace.name_poly_vars true
-- set_option pp.rawOnError true

axiom Polynomial : Type → Type
axiom Polynomial.C {R : Type} : R → Polynomial R
axiom Polynomial.X {R : Type} : Polynomial R

register_poly_vars "[" "]" Polynomial Polynomial.C Polynomial.X

axiom MvPolynomial : Type → Type → Type
axiom MvPolynomial.C {σ R : Type} : R → MvPolynomial σ R
axiom MvPolynomial.X {σ R : Type} (i : σ) : MvPolynomial σ R

register_poly_vars (mv := true) "[" "]" MvPolynomial MvPolynomial.C MvPolynomial.X

section Test1

name_poly_vars _[a,b][C]

variable (R : Type)

noncomputable example : Vector R[a,b][C] 3 :=
  have : Polynomial (MvPolynomial (Fin 2) R) = R[a,b][C] := by with_reducible rfl
  have : (Polynomial.C (MvPolynomial.X 0) : R[a,b][C]) = a := rfl
  have : (Polynomial.C (MvPolynomial.X 1) : R[a,b][C]) = b := rfl
  have : (Polynomial.X : R[a,b][C]) = C := rfl
  have : _[a,b][C] = R[a,b][C] := rfl
  #v[a, b, C]

noncomputable example : Vector (Fin 37)[a,b][C] 3 :=
  have : Polynomial (MvPolynomial (Fin 2) (Fin 37)) = (Fin 37)[a,b][C] := rfl
  have : (Polynomial.C (MvPolynomial.X 0) : (Fin 37)[a,b][C]) = a := rfl
  have : (Polynomial.C (MvPolynomial.X 1) : (Fin 37)[a,b][C]) = b := rfl
  have : (Polynomial.X : (Fin 37)[a,b][C]) = C := rfl
  have : _[a,b][C] = (Fin 37)[a,b][C] := rfl
  #v[a, b, C]

def «a,b» : Nat := 37

end Test1

section Test2

variable (R : Type)

name_poly_vars R[a,b][C]

noncomputable example : Vector R[a,b][C] 3 :=
  have : Polynomial (MvPolynomial (Fin 2) R) = R[a,b][C] := rfl
  have : Polynomial.C (MvPolynomial.X 0) = a := rfl
  have : Polynomial.C (MvPolynomial.X 1) = b := rfl
  have : Polynomial.X = C := rfl
  #v[a, b, C]

name_poly_vars R[t,]

/-- info: MvPolynomial.X 0 : MvPolynomial (Fin 1) R -/
#guard_msgs in
#check t

end Test2

section Test3

axiom AddMonoidAlgebra : Type → Type → Type

syntax:max (priority := high) term noWs "[" term "]" : term

macro_rules | `($k[$g]) => `(AddMonoidAlgebra $k $g)

variable (R M : Type)

name_poly_vars R[t]

/-- info: AddMonoidAlgebra R M : Type -/
#guard_msgs in
#check R[M]

/-- info: Polynomial R : Type -/
#guard_msgs in
#check R[t]

end Test3
