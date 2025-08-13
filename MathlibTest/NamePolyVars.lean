import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring.NamePolyVars

variable (R : Type) [CommRing R]

name_poly_vars R[X,Y,Z]
name_poly_vars Int[q]
name_poly_vars R[S][T][U]
name_poly_vars (ZMod 37)[d,e]

noncomputable example : Vector (MvPolynomial (Fin 3) R) 3 :=
  have : X = MvPolynomial.X 0 := rfl
  have : Y = MvPolynomial.X 1 := rfl
  have : Z = MvPolynomial.X 2 := rfl
  #v[X, Y, Z]

noncomputable example : Polynomial ℤ :=
  have : q = Polynomial.X := rfl
  q

noncomputable example : Vector (Polynomial (Polynomial (Polynomial R))) 3 :=
  have : S = Polynomial.C (Polynomial.C Polynomial.X) := rfl
  have : T = Polynomial.C Polynomial.X := rfl
  have : U = Polynomial.X := rfl
  #v[S, T, U]

noncomputable example : Vector (MvPolynomial (Fin 2) (ZMod 37)) 2 :=
  have : d = MvPolynomial.X 0 := rfl
  have : e = MvPolynomial.X 1 := rfl
  #v[d, e]
