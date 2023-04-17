/-
manually ported from
https://github.com/leanprover-community/mathlib/blob/4f4a1c875d0baa92ab5d92f3fb1bb258ad9f3e5b/test/matrix.lean
-/
import Mathlib.Data.Matrix.Notation
-- import linear_algebra.Matrix.determinant
import Mathlib.GroupTheory.Perm.Fin
-- import Mathlib.Tactic.NormSwap
import Qq

open Qq

-- todo: uncomment above imports when they are ported

variables {α β : Type} [Semiring α] [Ring β]

namespace Matrix

open Matrix

/-! Test that the dimensions are inferred correctly, even for empty matrices -/
section dimensions

-- set_option pp.universes true
-- set_option pp.all true

section elaborators
open Lean Meta Elab Command

/-- `dims% e` elaborates `e` as a Matrix and returns its dimensions as a `Nat × Nat`. -/
elab "dims% " e:term : term => do
  let elem_t ← mkFreshExprMVar (mkSort levelOne)
  let m ← mkFreshExprMVar (mkConst ``Nat)
  let n ← mkFreshExprMVar (mkConst ``Nat)
  let matrix_t := mkAppN (mkConst ``Matrix [levelZero, levelZero, levelZero])
                    #[mkApp (mkConst ``Fin) m, mkApp (mkConst ``Fin) n, elem_t]
  let _ ← Term.elabTermEnsuringType e (some matrix_t)
  let m ← instantiateMVars m
  let n ← instantiateMVars n
  mkAppM ``Prod.mk #[m, n]

/-- `#guard e1 is e2` elaborates `e1` and `e2` and checks they are `BEq`. -/
elab "#guard " e1:term " is " e2:term : command => liftTermElabM do
  let ty ← mkFreshExprMVar none
  let e1 ← Term.elabTerm e1 ty
  let e2 ← Term.elabTermEnsuringType e2 ty
  Elab.Term.synthesizeSyntheticMVarsUsingDefault
  let e1 ← instantiateMVars e1
  let e2 ← instantiateMVars e2
  if e1.hasMVar then
    throwError "expression{indentExpr e1}\nhas metavariables"
  if e2.hasMVar then
    throwError "expression{indentExpr e2}\nhas metavariables"
  unless e1 == e2 do
    throwError "expression{indentExpr e1}\nis not identically{indentExpr e2}"

/-- `#guard e` elaborates `e` as a boolean and checks that it evaluates to `true`. -/
elab "#guard " e:term : command => liftTermElabM do
  let e ← Term.elabTermEnsuringType e (mkConst ``Bool)
  Elab.Term.synthesizeSyntheticMVarsUsingDefault
  let e ← instantiateMVars e
  if e.hasMVar then
    throwError "expression{indentExpr e}\nhas metavariables"
  let v ← unsafe (evalExpr Bool (mkConst ``Bool) e)
  unless v do
    throwError "expression{indentExpr e}\ndid not evaluate to `true`"

end elaborators

-- we test equality of expressions here to ensure that we have `2` and not `1.succ` in the type
#guard dims% !![]        is (0, 0)
#guard dims% !![;]       is (1, 0)
#guard dims% !![;;]      is (2, 0)
#guard dims% !![,]       is (0, 1)
#guard dims% !![,,]      is (0, 2)
#guard dims% !![1]       is (1, 1)
#guard dims% !![1,]      is (1, 1)
#guard dims% !![1;]      is (1, 1)
#guard dims% !![1,2;3,4] is (2, 2)

end dimensions

#guard !![1;2]       = of ![![1], ![2]]
#guard !![1,3]       = of ![![1,3]]
#guard !![1,2;3,4]   = of ![![1,2], ![3,4]]
#guard !![1,2;3,4;]  = of ![![1,2], ![3,4]]
#guard !![1,2,;3,4,] = of ![![1,2], ![3,4]]

example {a a' b b' c c' d d' : α} :
  !![a, b; c, d] + !![a', b'; c', d'] = !![a + a', b + b'; c + c', d + d'] :=
by simp

example {a a' b b' c c' d d' : β} :
  !![a, b; c, d] - !![a', b'; c', d'] = !![a - a', b - b'; c - c', d - d'] :=
by simp

example {a a' b b' c c' d d' : α} :
  !![a, b; c, d] ⬝ !![a', b'; c', d'] =
    !![a * a' + b * c', a * b' + b * d'; c * a' + d * c', c * b' + d * d'] :=
by simp

example {a b c d x y : α} :
  mulVec !![a, b; c, d] ![x, y] = ![a * x + b * y, c * x + d * y] :=
by simp

/-!
TODO: the below lemmas rely on simp lemmas assuming the indexing numerals are assembled from
`bit0` and `bit1`, so no longer work in Lean 4
-/
/-
example {a b c d : α} : submatrix !![a, b; c, d] ![1, 0] ![0] = !![c; a] :=
by ext; simp

example {a b c : α} : ![a, b, c] 0 = a := by simp
example {a b c : α} : ![a, b, c] 1 = b := by simp
example {a b c : α} : ![a, b, c] 2 = c := by simp

example {a b c d : α} : ![a, b, c, d] 0 = a := by simp
example {a b c d : α} : ![a, b, c, d] 1 = b := by simp
example {a b c d : α} : ![a, b, c, d] 2 = c := by simp
example {a b c d : α} : ![a, b, c, d] 3 = d := by simp
example {a b c d : α} : ![a, b, c, d] 42 = c := by simp

example {a b c d e : α} : ![a, b, c, d, e] 0 = a := by simp
example {a b c d e : α} : ![a, b, c, d, e] 1 = b := by simp
example {a b c d e : α} : ![a, b, c, d, e] 2 = c := by simp
example {a b c d e : α} : ![a, b, c, d, e] 3 = d := by simp
example {a b c d e : α} : ![a, b, c, d, e] 4 = e := by simp
example {a b c d e : α} : ![a, b, c, d, e] 5 = a := by simp
example {a b c d e : α} : ![a, b, c, d, e] 6 = b := by simp
example {a b c d e : α} : ![a, b, c, d, e] 7 = c := by simp
example {a b c d e : α} : ![a, b, c, d, e] 8 = d := by simp
example {a b c d e : α} : ![a, b, c, d, e] 9 = e := by simp
example {a b c d e : α} : ![a, b, c, d, e] 123 = d := by simp
example {a b c d e : α} : ![a, b, c, d, e] 123456789 = e := by simp

example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 5 = f := by simp
example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 7 = h := by simp
example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 37 = f := by simp
example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 99 = d := by simp
-/

-- TODO: uncomment snd update `try this` when porting `Matrix.det`
/-
example {α : Type _} [CommRing α] {a b c d : α} :
    Matrix.det !![a, b; c, d] = a * d - b * c := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  /-
  Try this: simp only [det_succ_row_zero, Fin.sum_univ_succ, neg_mul, mul_one,
  Fin.default_eq_zero, Fin.coe_zero, one_mul, cons_val_one, Fin.coe_succ, univ_unique,
  submatrix_apply, pow_one, Fin.zero_succ_above, Fin.succ_succ_above_zero,  finset.sum_singleton,
  cons_val_zero, cons_val_succ, det_fin_zero, pow_zero]
  -/
  ring

example {α : Type _} [CommRing α] {a b c d e f g h i : α} :
    Matrix.det !![a, b, c; d, e, f; g, h, i] =
      a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  /-
  Try this: simp only [det_succ_row_zero, Fin.sum_univ_succ, neg_mul, cons_append,
  mul_one, Fin.default_eq_zero, Fin.coe_zero, cons_vec_bit0_eq_alt0, one_mul, cons_val_one,
  cons_vec_alt0, Fin.succ_succ_above_one, Fin.coe_succ, univ_unique, submatrix_apply, pow_one,
  Fin.zero_succ_above, Fin.succ_zero_eq_one, Fin.succ_succ_above_zero, nat.neg_one_sq,
  finset.sum_singleton, cons_val_zero, cons_val_succ, det_fin_zero, head_cons, pow_zero]
   -/
  ring
-/
end Matrix
