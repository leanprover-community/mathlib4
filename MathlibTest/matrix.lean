/-
manually ported from
https://github.com/leanprover-community/mathlib/blob/4f4a1c875d0baa92ab5d92f3fb1bb258ad9f3e5b/test/matrix.lean
-/
import Mathlib.Data.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Qq

set_option linter.style.commandStart false

open Qq

variable {α β : Type} [Semiring α] [Ring β]

namespace Matrix

/-! Test that the dimensions are inferred correctly, even for empty matrices -/
section dimensions

-- set_option pp.universes true
-- set_option pp.all true

section elaborators
open Lean Meta Elab Command

/-- `dims% e` elaborates `e` as a Matrix and returns its dimensions as a `Nat × Nat`. -/
elab "dims% " e:term : term => do
  let elem_t ← mkFreshTypeMVar
  let m ← mkFreshExprMVar (mkConst ``Nat)
  let n ← mkFreshExprMVar (mkConst ``Nat)
  let matrix_t := mkAppN (← mkConstWithFreshMVarLevels ``Matrix)
                    #[mkApp (mkConst ``Fin) m, mkApp (mkConst ``Fin) n, elem_t]
  let _ ← Term.elabTermEnsuringType e (some matrix_t)
  let m ← instantiateMVars m
  let n ← instantiateMVars n
  mkAppM ``Prod.mk #[m, n]

end elaborators

-- we test equality of expressions here to ensure that we have `2` and not `1.succ` in the type
#guard_expr dims% !![]        =ₛ (0, 0)
#guard_expr dims% !![;]       =ₛ (1, 0)
#guard_expr dims% !![;;]      =ₛ (2, 0)
#guard_expr dims% !![,]       =ₛ (0, 1)
#guard_expr dims% !![,,]      =ₛ (0, 2)
#guard_expr dims% !![1]       =ₛ (1, 1)
#guard_expr dims% !![1,]      =ₛ (1, 1)
#guard_expr dims% !![1;]      =ₛ (1, 1)
#guard_expr dims% !![1,2;3,4] =ₛ (2, 2)

end dimensions

section safety
open Lean Meta Elab Command

def mkMatrix (rows : Array (Array Term)) : Term := Unhygienic.run `(!![$[$[$rows],*];*])

def mkColumnVector (elems : Array Term) : Term := Unhygienic.run `(!![$[$elems];*])

-- Check that the `!![$[$[$rows],*];*]` case can deal with empty arrays even though it uses sepBy1
run_elab do
  let e ← Term.elabTerm (mkMatrix #[]) q(Matrix (Fin 0) (Fin 0) Nat)
  Term.synthesizeSyntheticMVarsUsingDefault
  let e ← instantiateMVars e
  guard <| e == q(!![] : Matrix (Fin 0) (Fin 0) Nat)

run_elab do
  let e ← Term.elabTerm (mkColumnVector #[]) q(Matrix (Fin 0) (Fin 0) Nat)
  Term.synthesizeSyntheticMVarsUsingDefault
  let e ← instantiateMVars e
  guard <| e == q(!![] : Matrix (Fin 0) (Fin 0) Nat)

end safety

#guard !![1;2]       = of ![![1], ![2]]
#guard !![1,3]       = of ![![1,3]]
#guard !![1,2;3,4]   = of ![![1,2], ![3,4]]
#guard !![1,2;3,4;]  = of ![![1,2], ![3,4]]
#guard !![1,2,;3,4,] = of ![![1,2], ![3,4]]

section to_expr

open Lean Meta

/-- info: !![1 + 1, 1 + 2; 2 + 1, 2 + 2] : Matrix (Fin 2) (Fin 2) ℕ -/
#guard_msgs in
#check by_elab return Matrix.mkLiteralQ !![q(1 + 1), q(1 + 2); q(2 + 1), q(2 + 2)]

run_elab do
  let x := !![1, 2; 3, 4]
  guard (← withReducible <| isDefEq (toExpr x) q(!![1, 2; 3, 4]))

end to_expr

section delaborators

/-- info: !![0, 1, 2; 3, 4, 5] : Matrix (Fin 2) (Fin 3) ℕ -/
#guard_msgs in #check (!![0, 1, 2; 3, 4, 5] : Matrix (Fin 2) (Fin 3) ℕ)

/-- info: !![0, 1, 2; 3, 4, 5] 1 1 : ℕ -/
#guard_msgs in #check (!![0, 1, 2; 3, 4, 5] : Matrix (Fin 2) (Fin 3) ℕ) 1 1

/-- info: !![,,,] : Matrix (Fin 0) (Fin 3) ℕ -/
#guard_msgs in #check (!![,,,] : Matrix (Fin 0) (Fin 3) ℕ)

/-- info: !![;;;] : Matrix (Fin 3) (Fin 0) ℕ -/
#guard_msgs in #check (!![;;;] : Matrix (Fin 3) (Fin 0) ℕ)

/-- info: !![] : Matrix (Fin 0) (Fin 0) ℕ -/
#guard_msgs in #check (!![] : Matrix (Fin 0) (Fin 0) ℕ)

end delaborators

example {a a' b b' c c' d d' : α} :
  !![a, b; c, d] + !![a', b'; c', d'] = !![a + a', b + b'; c + c', d + d'] := by
  simp

example {a a' b b' c c' d d' : β} :
  !![a, b; c, d] - !![a', b'; c', d'] = !![a - a', b - b'; c - c', d - d'] := by
  simp

example {a a' b b' c c' d d' : α} :
  !![a, b; c, d] * !![a', b'; c', d'] =
    !![a * a' + b * c', a * b' + b * d'; c * a' + d * c', c * b' + d * d'] := by
  simp

example {a b c d x y : α} :
  !![a, b; c, d] *ᵥ ![x, y] = ![a * x + b * y, c * x + d * y] := by
  simp

/-!
TODO: the below lemmas rely on simp lemmas assuming the indexing numerals are assembled from
`bit0` and `bit1`, so no longer work in Lean 4
-/
/-
example {a b c d : α} : submatrix !![a, b; c, d] ![1, 0] ![0] = !![c; a] := by
  ext; simp
-/
example {α : Type _} [CommRing α] {a b c d : α} :
    Matrix.det !![a, b; c, d] = a * d - b * c := by
  simp? [Matrix.det_succ_row_zero, Fin.sum_univ_succ] says
    simp only [det_succ_row_zero, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, of_apply,
      cons_val', cons_val_fin_one, cons_val_zero, det_unique, Fin.default_eq_zero, submatrix_apply,
      Fin.succ_zero_eq_one, cons_val_one, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul,
      Fin.zero_succAbove, Finset.univ_unique, Fin.val_succ, Fin.val_eq_zero, zero_add, pow_one,
      cons_val_succ, neg_mul, ne_eq, Fin.succ_ne_zero, not_false_eq_true,
      Fin.succAbove_ne_zero_zero, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_singleton,
      one_smul]
  ring

example {α : Type _} [CommRing α] {a b c d e f g h i : α} :
    Matrix.det !![a, b, c; d, e, f; g, h, i] =
      a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g := by
  simp? [Matrix.det_succ_row_zero, Fin.sum_univ_succ] says
    simp only [det_succ_row_zero, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, of_apply,
      cons_val', cons_val_fin_one, cons_val_zero, submatrix_apply, Fin.succ_zero_eq_one,
      cons_val_one, submatrix_submatrix, det_unique, Fin.default_eq_zero, Function.comp_apply,
      Fin.succ_one_eq_two, cons_val, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul,
      Fin.zero_succAbove, Finset.univ_unique, Fin.val_succ, Fin.val_eq_zero, zero_add, pow_one,
      neg_mul, ne_eq, Fin.succ_ne_zero, not_false_eq_true, Fin.succAbove_ne_zero_zero,
      Finset.sum_neg_distrib, Finset.sum_singleton, cons_val_succ, Fin.succ_succAbove_one, even_two,
      Even.neg_pow, one_pow, Finset.sum_const, Finset.card_singleton, one_smul]
  ring

example {R : Type*} [Semiring R] {a b c d : R} :
    !![a, b] * (transpose !![c, d]) = !![a * c + b * d] := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.vecHead, Matrix.vecTail]

/- Check that matrix notation works with `row` and `col` -/
example : Matrix.replicateRow _ ![1, 1] = !![1, 1] := by
  ext i j
  simp

example : Matrix.replicateCol _ ![1, 1] = !![1; 1] := by
  ext i j
  fin_cases i <;> simp

example (ι : Type*) [Inhabited ι] : Matrix.replicateRow ι (fun (_ : Fin 3) => 0) = 0 := by
  simp_all
  rfl

example (ι : Type*) [Inhabited ι] : Matrix.replicateCol ι (fun (_ : Fin 3) => 0) = 0 := by
  simp_all
  rfl

end Matrix
