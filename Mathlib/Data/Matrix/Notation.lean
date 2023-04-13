/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Eric Wieser

! This file was ported from Lean 3 source module data.matrix.notation
! leanprover-community/mathlib commit 3e068ece210655b7b9a9477c3aff38a492400aa1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basic
import Mathbin.Data.Fin.VecNotation
import Mathbin.Tactic.FinCases
import Mathbin.Algebra.BigOperators.Fin

/-!
# Matrix and vector notation

This file includes `simp` lemmas for applying operations in `data.matrix.basic` to values built out
of the matrix notation `![a, b] = vec_cons a (vec_cons b vec_empty)` defined in
`data.fin.vec_notation`.

This also provides the new notation `!![a, b; c, d] = matrix.of ![![a, b], ![c, d]]`.
This notation also works for empty matrices; `!![,,,] : matrix (fin 0) (fin 3)` and
`!![;;;] : matrix (fin 3) (fin 0)`.

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vec_cons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notations

This file provide notation `!![a, b; c, d]` for matrices, which corresponds to
`matrix.of ![![a, b], ![c, d]]`.
A parser for `a, b; c, d`-style strings is provided as `matrix.entry_parser`, while
`matrix.notation` provides the hook for the `!!` notation.
Note that in lean 3 the pretty-printer will not show `!!` notation, instead showing the version
with `of ![![...]]`.

## Examples

Examples of usage can be found in the `test/matrix.lean` file.
-/


namespace Matrix

universe u

variable {α : Type u} {o n m : ℕ} {m' n' o' : Type _}

open Matrix

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `reflect_name #[] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `reflect_name #[] -/
/-- Matrices can be reflected whenever their entries can. We insert an `@id (matrix m' n' α)` to
prevent immediate decay to a function. -/
unsafe instance matrix.reflect [reflected_univ.{u}] [reflected_univ.{u_1}] [reflected_univ.{u_2}]
    [reflected _ α] [reflected _ m'] [reflected _ n'] [h : has_reflect (m' → n' → α)] :
    has_reflect (Matrix m' n' α) := fun m =>
  (by
          trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `reflect_name #[]" :
          reflected _ @id.{max u_1 u_2 u + 1}).subst₂
      ((by
            trace
              "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `reflect_name #[]" :
            reflected _ @Matrix.{u_1, u_2, u}).subst₃
        q(_) q(_) q(_)) <|
    by
    dsimp only [Matrix]
    exact h m
#align matrix.matrix.reflect matrix.matrix.reflect

section Parser

open Lean

open Lean.Parser

open Interactive

open Interactive.Types

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Parse the entries of a matrix -/
unsafe def entry_parser {α : Type} (p : parser α) : parser (Σm n, Fin m → Fin n → α) := do
  let-- a list of lists if the matrix has at least one row, or the number of columns if the matrix has
  -- zero rows.
  p :
    parser (Sum (List (List α)) ℕ) :=-- empty rows
        Sum.inl <$>
        ((pure [] <* tk ";").repeat_at_least 1 <|>
          (sep_by_trailing (tk ";") <| sep_by_trailing (tk ",") p)) <|>
      Sum.inr <$> List.length <$> many (tk ",")
  let which
    ←-- empty columns
      p
  match which with
    | Sum.inl l => do
      let h::tl ← pure l
      let n := h
      let l : List (Vector α n) ←
        l fun row =>
            if h : row = n then pure (⟨row, h⟩ : Vector α n)
            else interaction_monad.fail "Rows must be of equal length"
      pure ⟨l, n, fun i j => (l _ i).get? j⟩
    | Sum.inr n => pure ⟨0, n, finZeroElim⟩
#align matrix.entry_parser matrix.entry_parser

-- Lean can't find this instance without some help. We only need it available in `Type 0`, and it is
-- a massive amount of effort to make it universe-polymorphic.
@[instance]
unsafe def sigma_sigma_fin_matrix_has_reflect {α : Type} [has_reflect α] [reflected _ α] :
    has_reflect (Σm n : ℕ, Fin m → Fin n → α) :=
  @sigma.reflect.{0, 0} _ _ ℕ (fun m => Σn, Fin m → Fin n → α) _ _ _ fun i =>
    @sigma.reflect.{0, 0} _ _ ℕ _ _ _ _ fun j => inferInstance
#align matrix.sigma_sigma_fin_matrix_has_reflect matrix.sigma_sigma_fin_matrix_has_reflect

/-- `!![a, b; c, d]` notation for matrices indexed by `fin m` and `fin n`. See the module docstring
for details. -/
@[user_notation]
unsafe def notation (_ : parse <| tk "!![")
    (val : parse (entry_parser (parser.pexpr 1) <* tk "]")) : parser pexpr := do
  let ⟨m, n, entries⟩ := val
  let entry_vals := pi_fin.to_pexpr (pi_fin.to_pexpr ∘ entries)
  pure (``(@Matrix.of (Fin $(q(m))) (Fin $(q(n))) _).app entry_vals)
#align matrix.notation matrix.notation

end Parser

variable (a b : ℕ)

/-- Use `![...]` notation for displaying a `fin`-indexed matrix, for example:

```
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]
```
-/
instance [Repr α] : Repr (Matrix (Fin m) (Fin n) α)
    where repr f :=
    "!![" ++
        (String.intercalate "; " <|
          (List.finRange m).map fun i =>
            String.intercalate ", " <| (List.finRange n).map fun j => repr (f i j)) ++
      "]"

@[simp]
theorem cons_val' (v : n' → α) (B : Fin m → n' → α) (i j) :
    vecCons v B i j = vecCons (v j) (fun i => B i j) i := by refine' Fin.cases _ _ i <;> simp
#align matrix.cons_val' Matrix.cons_val'

@[simp]
theorem head_val' (B : Fin m.succ → n' → α) (j : n') : (vecHead fun i => B i j) = vecHead B j :=
  rfl
#align matrix.head_val' Matrix.head_val'

@[simp]
theorem tail_val' (B : Fin m.succ → n' → α) (j : n') :
    (vecTail fun i => B i j) = fun i => vecTail B i j :=
  by
  ext
  simp [vec_tail]
#align matrix.tail_val' Matrix.tail_val'

section DotProduct

variable [AddCommMonoid α] [Mul α]

@[simp]
theorem dotProduct_empty (v w : Fin 0 → α) : dotProduct v w = 0 :=
  Finset.sum_empty
#align matrix.dot_product_empty Matrix.dotProduct_empty

@[simp]
theorem cons_dotProduct (x : α) (v : Fin n → α) (w : Fin n.succ → α) :
    dotProduct (vecCons x v) w = x * vecHead w + dotProduct v (vecTail w) := by
  simp [dot_product, Fin.sum_univ_succ, vec_head, vec_tail]
#align matrix.cons_dot_product Matrix.cons_dotProduct

@[simp]
theorem dotProduct_cons (v : Fin n.succ → α) (x : α) (w : Fin n → α) :
    dotProduct v (vecCons x w) = vecHead v * x + dotProduct (vecTail v) w := by
  simp [dot_product, Fin.sum_univ_succ, vec_head, vec_tail]
#align matrix.dot_product_cons Matrix.dotProduct_cons

@[simp]
theorem cons_dotProduct_cons (x : α) (v : Fin n → α) (y : α) (w : Fin n → α) :
    dotProduct (vecCons x v) (vecCons y w) = x * y + dotProduct v w := by simp
#align matrix.cons_dot_product_cons Matrix.cons_dotProduct_cons

end DotProduct

section ColRow

@[simp]
theorem col_empty (v : Fin 0 → α) : col v = vecEmpty :=
  empty_eq _
#align matrix.col_empty Matrix.col_empty

@[simp]
theorem col_cons (x : α) (u : Fin m → α) : col (vecCons x u) = vecCons (fun _ => x) (col u) :=
  by
  ext (i j)
  refine' Fin.cases _ _ i <;> simp [vec_head, vec_tail]
#align matrix.col_cons Matrix.col_cons

@[simp]
theorem row_empty : row (vecEmpty : Fin 0 → α) = fun _ => vecEmpty :=
  by
  ext
  rfl
#align matrix.row_empty Matrix.row_empty

@[simp]
theorem row_cons (x : α) (u : Fin m → α) : row (vecCons x u) = fun _ => vecCons x u :=
  by
  ext
  rfl
#align matrix.row_cons Matrix.row_cons

end ColRow

section Transpose

@[simp]
theorem transpose_empty_rows (A : Matrix m' (Fin 0) α) : Aᵀ = of ![] :=
  empty_eq _
#align matrix.transpose_empty_rows Matrix.transpose_empty_rows

@[simp]
theorem transpose_empty_cols (A : Matrix (Fin 0) m' α) : Aᵀ = of fun i => ![] :=
  funext fun i => empty_eq _
#align matrix.transpose_empty_cols Matrix.transpose_empty_cols

@[simp]
theorem cons_transpose (v : n' → α) (A : Matrix (Fin m) n' α) :
    (of (vecCons v A))ᵀ = of fun i => vecCons (v i) (Aᵀ i) :=
  by
  ext (i j)
  refine' Fin.cases _ _ j <;> simp
#align matrix.cons_transpose Matrix.cons_transpose

@[simp]
theorem head_transpose (A : Matrix m' (Fin n.succ) α) :
    vecHead (of.symm Aᵀ) = vecHead ∘ of.symm A :=
  rfl
#align matrix.head_transpose Matrix.head_transpose

@[simp]
theorem tail_transpose (A : Matrix m' (Fin n.succ) α) : vecTail (of.symm Aᵀ) = (vecTail ∘ A)ᵀ :=
  by
  ext (i j)
  rfl
#align matrix.tail_transpose Matrix.tail_transpose

end Transpose

section Mul

variable [Semiring α]

@[simp]
theorem empty_mul [Fintype n'] (A : Matrix (Fin 0) n' α) (B : Matrix n' o' α) : A ⬝ B = of ![] :=
  empty_eq _
#align matrix.empty_mul Matrix.empty_mul

@[simp]
theorem empty_mul_empty (A : Matrix m' (Fin 0) α) (B : Matrix (Fin 0) o' α) : A ⬝ B = 0 :=
  rfl
#align matrix.empty_mul_empty Matrix.empty_mul_empty

@[simp]
theorem mul_empty [Fintype n'] (A : Matrix m' n' α) (B : Matrix n' (Fin 0) α) :
    A ⬝ B = of fun _ => ![] :=
  funext fun _ => empty_eq _
#align matrix.mul_empty Matrix.mul_empty

theorem mul_val_succ [Fintype n'] (A : Matrix (Fin m.succ) n' α) (B : Matrix n' o' α) (i : Fin m)
    (j : o') : (A ⬝ B) i.succ j = (of (vecTail (of.symm A)) ⬝ B) i j :=
  rfl
#align matrix.mul_val_succ Matrix.mul_val_succ

@[simp]
theorem cons_mul [Fintype n'] (v : n' → α) (A : Fin m → n' → α) (B : Matrix n' o' α) :
    of (vecCons v A) ⬝ B = of (vecCons (vecMul v B) (of.symm (of A ⬝ B))) :=
  by
  ext (i j)
  refine' Fin.cases _ _ i
  · rfl
  simp [mul_val_succ]
#align matrix.cons_mul Matrix.cons_mul

end Mul

section VecMul

variable [Semiring α]

@[simp]
theorem empty_vecMul (v : Fin 0 → α) (B : Matrix (Fin 0) o' α) : vecMul v B = 0 :=
  rfl
#align matrix.empty_vec_mul Matrix.empty_vecMul

@[simp]
theorem vecMul_empty [Fintype n'] (v : n' → α) (B : Matrix n' (Fin 0) α) : vecMul v B = ![] :=
  empty_eq _
#align matrix.vec_mul_empty Matrix.vecMul_empty

@[simp]
theorem cons_vecMul (x : α) (v : Fin n → α) (B : Fin n.succ → o' → α) :
    vecMul (vecCons x v) (of B) = x • vecHead B + vecMul v (of <| vecTail B) :=
  by
  ext i
  simp [vec_mul]
#align matrix.cons_vec_mul Matrix.cons_vecMul

@[simp]
theorem vecMul_cons (v : Fin n.succ → α) (w : o' → α) (B : Fin n → o' → α) :
    vecMul v (of <| vecCons w B) = vecHead v • w + vecMul (vecTail v) (of B) :=
  by
  ext i
  simp [vec_mul]
#align matrix.vec_mul_cons Matrix.vecMul_cons

@[simp]
theorem cons_vecMul_cons (x : α) (v : Fin n → α) (w : o' → α) (B : Fin n → o' → α) :
    vecMul (vecCons x v) (of <| vecCons w B) = x • w + vecMul v (of B) := by simp
#align matrix.cons_vec_mul_cons Matrix.cons_vecMul_cons

end VecMul

section MulVec

variable [Semiring α]

@[simp]
theorem empty_mulVec [Fintype n'] (A : Matrix (Fin 0) n' α) (v : n' → α) : mulVec A v = ![] :=
  empty_eq _
#align matrix.empty_mul_vec Matrix.empty_mulVec

@[simp]
theorem mulVec_empty (A : Matrix m' (Fin 0) α) (v : Fin 0 → α) : mulVec A v = 0 :=
  rfl
#align matrix.mul_vec_empty Matrix.mulVec_empty

@[simp]
theorem cons_mulVec [Fintype n'] (v : n' → α) (A : Fin m → n' → α) (w : n' → α) :
    mulVec (of <| vecCons v A) w = vecCons (dotProduct v w) (mulVec (of A) w) :=
  by
  ext i
  refine' Fin.cases _ _ i <;> simp [mul_vec]
#align matrix.cons_mul_vec Matrix.cons_mulVec

@[simp]
theorem mulVec_cons {α} [CommSemiring α] (A : m' → Fin n.succ → α) (x : α) (v : Fin n → α) :
    mulVec (of A) (vecCons x v) = x • vecHead ∘ A + mulVec (of (vecTail ∘ A)) v :=
  by
  ext i
  simp [mul_vec, mul_comm]
#align matrix.mul_vec_cons Matrix.mulVec_cons

end MulVec

section VecMulVec

variable [Semiring α]

@[simp]
theorem empty_vecMulVec (v : Fin 0 → α) (w : n' → α) : vecMulVec v w = ![] :=
  empty_eq _
#align matrix.empty_vec_mul_vec Matrix.empty_vecMulVec

@[simp]
theorem vecMulVec_empty (v : m' → α) (w : Fin 0 → α) : vecMulVec v w = fun _ => ![] :=
  funext fun i => empty_eq _
#align matrix.vec_mul_vec_empty Matrix.vecMulVec_empty

@[simp]
theorem cons_vecMulVec (x : α) (v : Fin m → α) (w : n' → α) :
    vecMulVec (vecCons x v) w = vecCons (x • w) (vecMulVec v w) :=
  by
  ext i
  refine' Fin.cases _ _ i <;> simp [vec_mul_vec]
#align matrix.cons_vec_mul_vec Matrix.cons_vecMulVec

@[simp]
theorem vecMulVec_cons (v : m' → α) (x : α) (w : Fin n → α) :
    vecMulVec v (vecCons x w) = fun i => v i • vecCons x w :=
  by
  ext (i j)
  rw [vec_mul_vec_apply, Pi.smul_apply, smul_eq_mul]
#align matrix.vec_mul_vec_cons Matrix.vecMulVec_cons

end VecMulVec

section Smul

variable [Semiring α]

@[simp]
theorem smul_mat_empty {m' : Type _} (x : α) (A : Fin 0 → m' → α) : x • A = ![] :=
  empty_eq _
#align matrix.smul_mat_empty Matrix.smul_mat_empty

@[simp]
theorem smul_mat_cons (x : α) (v : n' → α) (A : Fin m → n' → α) :
    x • vecCons v A = vecCons (x • v) (x • A) :=
  by
  ext i
  refine' Fin.cases _ _ i <;> simp
#align matrix.smul_mat_cons Matrix.smul_mat_cons

end Smul

section Submatrix

@[simp]
theorem submatrix_empty (A : Matrix m' n' α) (row : Fin 0 → m') (col : o' → n') :
    submatrix A row col = ![] :=
  empty_eq _
#align matrix.submatrix_empty Matrix.submatrix_empty

@[simp]
theorem submatrix_cons_row (A : Matrix m' n' α) (i : m') (row : Fin m → m') (col : o' → n') :
    submatrix A (vecCons i row) col = vecCons (fun j => A i (col j)) (submatrix A row col) :=
  by
  ext (i j)
  refine' Fin.cases _ _ i <;> simp [submatrix]
#align matrix.submatrix_cons_row Matrix.submatrix_cons_row

end Submatrix

section Vec2AndVec3

section One

variable [Zero α] [One α]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation -/
theorem one_fin_two :
    (1 : Matrix (Fin 2) (Fin 2) α) =
      «expr!![ »
        "./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation" :=
  by
  ext (i j)
  fin_cases i <;> fin_cases j <;> rfl
#align matrix.one_fin_two Matrix.one_fin_two

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation -/
theorem one_fin_three :
    (1 : Matrix (Fin 3) (Fin 3) α) =
      «expr!![ »
        "./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation" :=
  by
  ext (i j)
  fin_cases i <;> fin_cases j <;> rfl
#align matrix.one_fin_three Matrix.one_fin_three

end One

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation -/
theorem eta_fin_two (A : Matrix (Fin 2) (Fin 2) α) :
    A =
      «expr!![ »
        "./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation" :=
  by
  ext (i j)
  fin_cases i <;> fin_cases j <;> rfl
#align matrix.eta_fin_two Matrix.eta_fin_two

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation -/
theorem eta_fin_three (A : Matrix (Fin 3) (Fin 3) α) :
    A =
      «expr!![ »
        "./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation" :=
  by
  ext (i j)
  fin_cases i <;> fin_cases j <;> rfl
#align matrix.eta_fin_three Matrix.eta_fin_three

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation -/
theorem mul_fin_two [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    «expr!![ »
          "./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation" ⬝
        «expr!![ »
          "./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation" =
      «expr!![ »
        "./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation" :=
  by
  ext (i j)
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul, dot_product, Fin.sum_univ_succ]
#align matrix.mul_fin_two Matrix.mul_fin_two

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation -/
theorem mul_fin_three [AddCommMonoid α] [Mul α]
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : α) :
    «expr!![ »
          "./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation" ⬝
        «expr!![ »
          "./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation" =
      «expr!![ »
        "./././Mathport/Syntax/Translate/Expr.lean:387:14: unsupported user notation matrix.notation" :=
  by
  ext (i j)
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul, dot_product, Fin.sum_univ_succ, ← add_assoc]
#align matrix.mul_fin_three Matrix.mul_fin_three

theorem vec2_eq {a₀ a₁ b₀ b₁ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) : ![a₀, a₁] = ![b₀, b₁] := by
  subst_vars
#align matrix.vec2_eq Matrix.vec2_eq

theorem vec3_eq {a₀ a₁ a₂ b₀ b₁ b₂ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) :
    ![a₀, a₁, a₂] = ![b₀, b₁, b₂] := by subst_vars
#align matrix.vec3_eq Matrix.vec3_eq

theorem vec2_add [Add α] (a₀ a₁ b₀ b₁ : α) : ![a₀, a₁] + ![b₀, b₁] = ![a₀ + b₀, a₁ + b₁] := by
  rw [cons_add_cons, cons_add_cons, empty_add_empty]
#align matrix.vec2_add Matrix.vec2_add

theorem vec3_add [Add α] (a₀ a₁ a₂ b₀ b₁ b₂ : α) :
    ![a₀, a₁, a₂] + ![b₀, b₁, b₂] = ![a₀ + b₀, a₁ + b₁, a₂ + b₂] := by
  rw [cons_add_cons, cons_add_cons, cons_add_cons, empty_add_empty]
#align matrix.vec3_add Matrix.vec3_add

theorem smul_vec2 {R : Type _} [SMul R α] (x : R) (a₀ a₁ : α) : x • ![a₀, a₁] = ![x • a₀, x • a₁] :=
  by rw [smul_cons, smul_cons, smul_empty]
#align matrix.smul_vec2 Matrix.smul_vec2

theorem smul_vec3 {R : Type _} [SMul R α] (x : R) (a₀ a₁ a₂ : α) :
    x • ![a₀, a₁, a₂] = ![x • a₀, x • a₁, x • a₂] := by
  rw [smul_cons, smul_cons, smul_cons, smul_empty]
#align matrix.smul_vec3 Matrix.smul_vec3

variable [AddCommMonoid α] [Mul α]

theorem vec2_dot_product' {a₀ a₁ b₀ b₁ : α} : ![a₀, a₁] ⬝ᵥ ![b₀, b₁] = a₀ * b₀ + a₁ * b₁ := by
  rw [cons_dot_product_cons, cons_dot_product_cons, dot_product_empty, add_zero]
#align matrix.vec2_dot_product' Matrix.vec2_dot_product'

@[simp]
theorem vec2_dotProduct (v w : Fin 2 → α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 :=
  vec2_dot_product'
#align matrix.vec2_dot_product Matrix.vec2_dotProduct

theorem vec3_dot_product' {a₀ a₁ a₂ b₀ b₁ b₂ : α} :
    ![a₀, a₁, a₂] ⬝ᵥ ![b₀, b₁, b₂] = a₀ * b₀ + a₁ * b₁ + a₂ * b₂ := by
  rw [cons_dot_product_cons, cons_dot_product_cons, cons_dot_product_cons, dot_product_empty,
    add_zero, add_assoc]
#align matrix.vec3_dot_product' Matrix.vec3_dot_product'

@[simp]
theorem vec3_dotProduct (v w : Fin 3 → α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 :=
  vec3_dot_product'
#align matrix.vec3_dot_product Matrix.vec3_dotProduct

end Vec2AndVec3

end Matrix

