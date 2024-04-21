import Mathlib

open Matrix Polynomial

universe u v w

def SimpleReedSolomonCode {F : Type} [Field F] (n m : ℕ) (a : Fin n → F) (message : Fin m → F) : Fin n → F :=
  fun i => List.sum ((List.finRange m).map fun j => message j * (a i) ^ (j : ℕ))

/--
https://gfeng2001.github.io/assets/pdfs/cs70/BWGuide.pdf

Let E be the error polynomial of degree at most e of the form E(x) = (x-e1)(x-e2)...(x-ee).

n = m + 2e

for all i in Fin m+2e,
  Q.eval (a i) = E.eval(a i) * F.eval (a i)
  E.eval(a i) * F.eval (a i) - Q.eval (a i) = 0


Let AB_mat be the matrix of dimension n x e
  where the i-th row jth col
  is b_i * a_i ^j




a_n

Then the received polynomial is the sum of the message polynomial and the error polynomial.

-/


noncomputable def BerlekampWelchDecoding {F : Type} [Field F] (m e : ℕ)
    (a : Fin (m + e + e) -> F) (received : Fin (m + e + e) → F) (i_ : Fin m) : F :=
  let n := m + e + e
  let AB_mat : Matrix (Fin n) (Fin e) F := fun i j => (received i) * (a i) ^ (j : ℕ)
  let A_mat : Matrix (Fin n) (Fin (m + e)) F := fun i j => (a i) ^ (j : ℕ)
  let full_mat : Matrix (Fin n) (Fin (m + e + e)) F :=
    fun i j => ((-A_mat).fromColumns AB_mat) i (finSumFinEquiv.symm j)
  let AB_vec : Fin n → F := fun i => received i * (a i) ^ (e)
  let qe_vec : Fin n → F := (full_mat)⁻¹ *ᵥ -AB_vec
  let q_vec : Fin (m+e) → F := fun i => qe_vec (finSumFinEquiv (Sum.inl i))
  let e_vec : Fin (e) → F := fun i => qe_vec (finSumFinEquiv (Sum.inr i))
  let e_poly : Polynomial F := X ^ e + List.sum ((List.finRange e).map (fun i => C (e_vec i) * X ^ (i : ℕ)))
  let q_poly : Polynomial F := List.sum ((List.finRange (m+e)).map (fun i => C (q_vec i) * X ^ (i : ℕ)))
  let f_poly : Polynomial F := q_poly.modByMonic e_poly;
  f_poly.coeff i_

def sparseVector {F : Type} [Field F] [DecidableEq F] {n : ℕ} (e : ℕ) (v : Fin n → F) : Prop :=
    ((List.finRange n).filter (fun i => v i ≠ 0)).length ≤ e

theorem BerlekampWelchDecodingCorrect {F : Type} [Field F] [DecidableEq F] (m e : ℕ)
    (a : Fin (m + e + e) -> F) (message : Fin m → F) (error : Fin (m + e + e) → F)
    (low_error : sparseVector (F := F) e error) :
    BerlekampWelchDecoding m e a (SimpleReedSolomonCode (m + e + e) m a message + error)
      = message := by
  unfold BerlekampWelchDecoding SimpleReedSolomonCode
  lift_lets
  extract_lets n AB_mat A_mat full_mat AB_vec qe_vec q_vec e_vec e_poly q_poly f_poly
  ext i_
  -- TODO critical question: Is it always the case that full_mat is invertible?
  -- If so, how to prove it?
  -- If not, what is the semantic situation that leads to it not being inveritble
  -- subquestion is it related to the possibility of the error vector being even sparser than the algorithm requires?

  -- have : full_mat *ᵥ qe_vec = -AB_vec := by
  --   apply?

  have e_poly_is_errors : e_poly = List.prod (X - ) := by
    apply?




end Polynomial
