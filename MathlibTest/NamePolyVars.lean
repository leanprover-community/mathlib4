-- import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.Ring.NamePolyVars

-- set_option trace.name_poly_vars true
-- set_option pp.rawOnError true

@[class] axiom Semiring : Type → Type

axiom Polynomial (R : Type) [Semiring R] : Type
axiom Polynomial.C {R : Type} [Semiring R] : R → Polynomial R
axiom Polynomial.X {R : Type} [Semiring R] : Polynomial R

register_poly_vars "[" "]" Polynomial Polynomial.C Polynomial.X

axiom MvPolynomial (σ R : Type) [Semiring R] : Type
axiom MvPolynomial.C {σ R : Type} [Semiring R] : R → MvPolynomial σ R
axiom MvPolynomial.X {σ R : Type} [Semiring R] (i : σ) : MvPolynomial σ R

register_poly_vars (mv := true) "[" "]" MvPolynomial MvPolynomial.C MvPolynomial.X

@[instance] axiom Polynomial.semiring (R : Type) [Semiring R] : Semiring (Polynomial R)
@[instance] axiom MvPolynomial.semiring (σ R : Type) [Semiring R] : Semiring (MvPolynomial σ R)
@[instance] axiom Fin.semiring37 : Semiring (Fin 37)

section Test1

name_poly_vars _[a,b][C]

variable (R : Type) [Semiring R]

/-- info: R[a,b][C] : Type -/
#guard_msgs in
#check R[a,b][C]

noncomputable example : Vector R[a,b][C] 3 :=
  have : Polynomial (MvPolynomial (Fin 2) R) = R[a,b][C] := by with_reducible rfl
  have : (Polynomial.C (MvPolynomial.X 0) : R[a,b][C]) = a := rfl
  have : (Polynomial.C (MvPolynomial.X 1) : R[a,b][C]) = b := rfl
  have : (Polynomial.X : R[a,b][C]) = C := rfl
  #v[a, b, C]

noncomputable example : Vector (Fin 37)[a,b][C] 3 :=
  have : Polynomial (MvPolynomial (Fin 2) (Fin 37)) = (Fin 37)[a,b][C] := rfl
  have : (Polynomial.C (MvPolynomial.X 0) : (Fin 37)[a,b][C]) = a := rfl
  have : (Polynomial.C (MvPolynomial.X 1) : (Fin 37)[a,b][C]) = b := rfl
  have : (Polynomial.X : (Fin 37)[a,b][C]) = C := rfl
  #v[a, b, C]

def «a,b» : Nat := 37

name_poly_vars _[t][u]

/-- info: R[t][u] : Type -/
#guard_msgs in
#check R[t][u]

name_poly_vars _[q]

/-- info: R[q] : Type -/
#guard_msgs in
#check R[q]

name_poly_vars _[x,y]

/-- info: R[x,y] : Type -/
#guard_msgs in
#check R[x,y]

end Test1

section Test2

variable (R S : Type) [Semiring R] [Semiring S]

name_poly_vars R[a,b][C]

noncomputable example : Vector R[a,b][C] 3 :=
  have : Polynomial (MvPolynomial (Fin 2) R) = R[a,b][C] := rfl
  have : Polynomial.C (MvPolynomial.X 0) = a := rfl
  have : Polynomial.C (MvPolynomial.X 1) = b := rfl
  have : Polynomial.X = C := rfl
  #v[a, b, C]

name_poly_vars R[t,]

/-- info: R[t,] : Type -/
#guard_msgs in
#check R[t,]

/-- info: MvPolynomial.X 0 : R[t,] -/
#guard_msgs in
#check t

name_poly_vars R[x,y,z]

/-- info: R[x,y,z] : Type -/
#guard_msgs in
#check MvPolynomial (Fin 3) R

/-- info: MvPolynomial (Fin 3) S : Type -/
#guard_msgs in
#check MvPolynomial (Fin 3) S

end Test2

section Test3

axiom AddMonoidAlgebra : Type → Type → Type

syntax:max (priority := high) term noWs "[" term "]" : term

macro_rules | `($k[$g]) => `(AddMonoidAlgebra $k $g)

variable (R M : Type) [Semiring R]

name_poly_vars R[t]

/-- info: AddMonoidAlgebra R M : Type -/
#guard_msgs in
#check R[M]

/-- info: R[t] : Type -/
#guard_msgs in
#check R[t]

end Test3

section Test4

name_poly_vars (Fin 37)[x,y,z][C]

/-- info: (Fin 37)[x,y,z][C] : Type -/
#guard_msgs in
#check (Fin 37)[x,y,z][C]

end Test4
