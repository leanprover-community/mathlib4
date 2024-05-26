/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Eric Wieser
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.RowCol
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

#align_import data.matrix.notation from "leanprover-community/mathlib"@"a99f85220eaf38f14f94e04699943e185a5e1d1a"

/-!
# Matrix and vector notation

This file includes `simp` lemmas for applying operations in `Data.Matrix.Basic` to values built out
of the matrix notation `![a, b] = vecCons a (vecCons b vecEmpty)` defined in
`Data.Fin.VecNotation`.

This also provides the new notation `!![a, b; c, d] = Matrix.of ![![a, b], ![c, d]]`.
This notation also works for empty matrices; `!![,,,] : Matrix (Fin 0) (Fin 3)` and
`!![;;;] : Matrix (Fin 3) (Fin 0)`.

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vecCons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notations

This file provide notation `!![a, b; c, d]` for matrices, which corresponds to
`Matrix.of ![![a, b], ![c, d]]`.
TODO: until we implement a `Lean.PrettyPrinter.Unexpander` for `Matrix.of`, the pretty-printer will
not show `!!` notation, instead showing the version with `of ![![...]]`.

## Examples

Examples of usage can be found in the `test/matrix.lean` file.
-/

namespace Matrix

universe u uₘ uₙ uₒ

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

open Matrix

section toExpr
open Lean
open Qq

/-- Matrices can be reflected whenever their entries can. We insert a `Matrix.of` to
prevent immediate decay to a function. -/
protected instance toExpr [ToLevel.{u}] [ToLevel.{uₘ}] [ToLevel.{uₙ}]
    [Lean.ToExpr α] [Lean.ToExpr m'] [Lean.ToExpr n'] [Lean.ToExpr (m' → n' → α)] :
    Lean.ToExpr (Matrix m' n' α) :=
  have eα : Q(Type $(toLevel.{u})) := toTypeExpr α
  have em' : Q(Type $(toLevel.{uₘ})) := toTypeExpr m'
  have en' : Q(Type $(toLevel.{uₙ})) := toTypeExpr n'
  { toTypeExpr :=
    q(Matrix $eα $em' $en')
    toExpr := fun M =>
      have eM : Q($em' → $en' → $eα) := toExpr (show m' → n' → α from M)
      q(Matrix.of $eM) }
#align matrix.matrix.reflect Matrix.toExpr

end toExpr

section Parser
open Lean Elab Term Macro TSyntax

/-- Notation for m×n matrices, aka `Matrix (Fin m) (Fin n) α`.

For instance:
* `!![a, b, c; d, e, f]` is the matrix with two rows and three columns, of type
  `Matrix (Fin 2) (Fin 3) α`
* `!![a, b, c]` is a row vector of type `Matrix (Fin 1) (Fin 3) α` (see also `Matrix.row`).
* `!![a; b; c]` is a column vector of type `Matrix (Fin 3) (Fin 1) α` (see also `Matrix.col`).

This notation implements some special cases:

* `![,,]`, with `n` `,`s, is a term of type `Matrix (Fin 0) (Fin n) α`
* `![;;]`, with `m` `;`s, is a term of type `Matrix (Fin m) (Fin 0) α`
* `![]` is the 0×0 matrix

Note that vector notation is provided elsewhere (by `Matrix.vecNotation`) as `![a, b, c]`.
Under the hood, `!![a, b, c; d, e, f]` is syntax for `Matrix.of ![![a, b, c], ![d, e, f]]`.
-/
syntax (name := matrixNotation)
  "!![" ppRealGroup(sepBy1(ppGroup(term,+,?), ";", "; ", allowTrailingSep)) "]" : term

@[inherit_doc matrixNotation]
syntax (name := matrixNotationRx0) "!![" ";"* "]" : term
@[inherit_doc matrixNotation]
syntax (name := matrixNotation0xC) "!![" ","+ "]" : term

macro_rules
  | `(!![$[$[$rows],*];*]) => do
    let m := rows.size
    let n := if h : 0 < m then rows[0].size else 0
    let rowVecs ← rows.mapM fun row : Array Term => do
      unless row.size = n do
        Macro.throwErrorAt (mkNullNode row) s!"\
          Rows must be of equal length; this row has {row.size} items, \
          the previous rows have {n}"
      `(![$row,*])
    `(@Matrix.of (Fin $(quote m)) (Fin $(quote n)) _ ![$rowVecs,*])
  | `(!![$[;%$semicolons]*]) => do
    let emptyVec ← `(![])
    let emptyVecs := semicolons.map (fun _ => emptyVec)
    `(@Matrix.of (Fin $(quote semicolons.size)) (Fin 0) _ ![$emptyVecs,*])
  | `(!![$[,%$commas]*]) => `(@Matrix.of (Fin 0) (Fin $(quote commas.size)) _ ![])

end Parser

variable (a b : ℕ)

/-- Use `![...]` notation for displaying a `Fin`-indexed matrix, for example:

```
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]
```
-/
instance repr [Repr α] : Repr (Matrix (Fin m) (Fin n) α) where
  reprPrec f _p :=
    (Std.Format.bracket "!![" · "]") <|
      (Std.Format.joinSep · (";" ++ Std.Format.line)) <|
        (List.finRange m).map fun i =>
          Std.Format.fill <|  -- wrap line in a single place rather than all at once
            (Std.Format.joinSep · ("," ++ Std.Format.line)) <|
            (List.finRange n).map fun j => _root_.repr (f i j)
#align matrix.has_repr Matrix.repr

@[simp]
theorem cons_val' (v : n' → α) (B : Fin m → n' → α) (i j) :
    vecCons v B i j = vecCons (v j) (fun i => B i j) i := by refine Fin.cases ?_ ?_ i <;> simp
#align matrix.cons_val' Matrix.cons_val'

@[simp, nolint simpNF] -- Porting note: LHS does not simplify.
theorem head_val' (B : Fin m.succ → n' → α) (j : n') : (vecHead fun i => B i j) = vecHead B j :=
  rfl
#align matrix.head_val' Matrix.head_val'

@[simp, nolint simpNF] -- Porting note: LHS does not simplify.
theorem tail_val' (B : Fin m.succ → n' → α) (j : n') :
    (vecTail fun i => B i j) = fun i => vecTail B i j := rfl
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
  simp [dotProduct, Fin.sum_univ_succ, vecHead, vecTail]
#align matrix.cons_dot_product Matrix.cons_dotProduct

@[simp]
theorem dotProduct_cons (v : Fin n.succ → α) (x : α) (w : Fin n → α) :
    dotProduct v (vecCons x w) = vecHead v * x + dotProduct (vecTail v) w := by
  simp [dotProduct, Fin.sum_univ_succ, vecHead, vecTail]
#align matrix.dot_product_cons Matrix.dotProduct_cons

-- @[simp] -- Porting note (#10618): simp can prove this
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
theorem col_cons (x : α) (u : Fin m → α) :
    col (vecCons x u) = of (vecCons (fun _ => x) (col u)) := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> simp [vecHead, vecTail]
#align matrix.col_cons Matrix.col_cons

@[simp]
theorem row_empty : row (vecEmpty : Fin 0 → α) = of fun _ => vecEmpty := rfl
#align matrix.row_empty Matrix.row_empty

@[simp]
theorem row_cons (x : α) (u : Fin m → α) : row (vecCons x u) = of fun _ => vecCons x u := rfl
#align matrix.row_cons Matrix.row_cons

end ColRow

section Transpose

@[simp]
theorem transpose_empty_rows (A : Matrix m' (Fin 0) α) : Aᵀ = of ![] :=
  empty_eq _
#align matrix.transpose_empty_rows Matrix.transpose_empty_rows

@[simp]
theorem transpose_empty_cols (A : Matrix (Fin 0) m' α) : Aᵀ = of fun _ => ![] :=
  funext fun _ => empty_eq _
#align matrix.transpose_empty_cols Matrix.transpose_empty_cols

@[simp]
theorem cons_transpose (v : n' → α) (A : Matrix (Fin m) n' α) :
    (of (vecCons v A))ᵀ = of fun i => vecCons (v i) (Aᵀ i) := by
  ext i j
  refine Fin.cases ?_ ?_ j <;> simp
#align matrix.cons_transpose Matrix.cons_transpose

@[simp]
theorem head_transpose (A : Matrix m' (Fin n.succ) α) :
    vecHead (of.symm Aᵀ) = vecHead ∘ of.symm A :=
  rfl
#align matrix.head_transpose Matrix.head_transpose

@[simp]
theorem tail_transpose (A : Matrix m' (Fin n.succ) α) : vecTail (of.symm Aᵀ) = (vecTail ∘ A)ᵀ := by
  ext i j
  rfl
#align matrix.tail_transpose Matrix.tail_transpose

end Transpose

section Mul

variable [NonUnitalNonAssocSemiring α]

@[simp]
theorem empty_mul [Fintype n'] (A : Matrix (Fin 0) n' α) (B : Matrix n' o' α) : A * B = of ![] :=
  empty_eq _
#align matrix.empty_mul Matrix.empty_mul

@[simp]
theorem empty_mul_empty (A : Matrix m' (Fin 0) α) (B : Matrix (Fin 0) o' α) : A * B = 0 :=
  rfl
#align matrix.empty_mul_empty Matrix.empty_mul_empty

@[simp]
theorem mul_empty [Fintype n'] (A : Matrix m' n' α) (B : Matrix n' (Fin 0) α) :
    A * B = of fun _ => ![] :=
  funext fun _ => empty_eq _
#align matrix.mul_empty Matrix.mul_empty

theorem mul_val_succ [Fintype n'] (A : Matrix (Fin m.succ) n' α) (B : Matrix n' o' α) (i : Fin m)
    (j : o') : (A * B) i.succ j = (of (vecTail (of.symm A)) * B) i j :=
  rfl
#align matrix.mul_val_succ Matrix.mul_val_succ

@[simp]
theorem cons_mul [Fintype n'] (v : n' → α) (A : Fin m → n' → α) (B : Matrix n' o' α) :
    of (vecCons v A) * B = of (vecCons (v ᵥ* B) (of.symm (of A * B))) := by
  ext i j
  refine Fin.cases ?_ ?_ i
  · rfl
  simp [mul_val_succ]
#align matrix.cons_mul Matrix.cons_mul

end Mul

section VecMul

variable [NonUnitalNonAssocSemiring α]

@[simp]
theorem empty_vecMul (v : Fin 0 → α) (B : Matrix (Fin 0) o' α) : v ᵥ* B = 0 :=
  rfl
#align matrix.empty_vec_mul Matrix.empty_vecMul

@[simp]
theorem vecMul_empty [Fintype n'] (v : n' → α) (B : Matrix n' (Fin 0) α) : v ᵥ* B = ![] :=
  empty_eq _
#align matrix.vec_mul_empty Matrix.vecMul_empty

@[simp]
theorem cons_vecMul (x : α) (v : Fin n → α) (B : Fin n.succ → o' → α) :
    vecCons x v ᵥ* of B = x • vecHead B + v ᵥ* of (vecTail B) := by
  ext i
  simp [vecMul]
#align matrix.cons_vec_mul Matrix.cons_vecMul

@[simp]
theorem vecMul_cons (v : Fin n.succ → α) (w : o' → α) (B : Fin n → o' → α) :
    v ᵥ* of (vecCons w B) = vecHead v • w + vecTail v ᵥ* of B := by
  ext i
  simp [vecMul]
#align matrix.vec_mul_cons Matrix.vecMul_cons

-- @[simp] -- Porting note (#10618): simp can prove this
theorem cons_vecMul_cons (x : α) (v : Fin n → α) (w : o' → α) (B : Fin n → o' → α) :
    vecCons x v ᵥ* of (vecCons w B) = x • w + v ᵥ* of B := by simp
#align matrix.cons_vec_mul_cons Matrix.cons_vecMul_cons

end VecMul

section MulVec

variable [NonUnitalNonAssocSemiring α]

@[simp]
theorem empty_mulVec [Fintype n'] (A : Matrix (Fin 0) n' α) (v : n' → α) : A *ᵥ v = ![] :=
  empty_eq _
#align matrix.empty_mul_vec Matrix.empty_mulVec

@[simp]
theorem mulVec_empty (A : Matrix m' (Fin 0) α) (v : Fin 0 → α) : A *ᵥ v = 0 :=
  rfl
#align matrix.mul_vec_empty Matrix.mulVec_empty

@[simp]
theorem cons_mulVec [Fintype n'] (v : n' → α) (A : Fin m → n' → α) (w : n' → α) :
    (of <| vecCons v A) *ᵥ w = vecCons (dotProduct v w) (of A *ᵥ w) := by
  ext i
  refine Fin.cases ?_ ?_ i <;> simp [mulVec]
#align matrix.cons_mul_vec Matrix.cons_mulVec

@[simp]
theorem mulVec_cons {α} [CommSemiring α] (A : m' → Fin n.succ → α) (x : α) (v : Fin n → α) :
    (of A) *ᵥ (vecCons x v) = x • vecHead ∘ A + (of (vecTail ∘ A)) *ᵥ v := by
  ext i
  simp [mulVec, mul_comm]
#align matrix.mul_vec_cons Matrix.mulVec_cons

end MulVec

section VecMulVec

variable [NonUnitalNonAssocSemiring α]

@[simp]
theorem empty_vecMulVec (v : Fin 0 → α) (w : n' → α) : vecMulVec v w = ![] :=
  empty_eq _
#align matrix.empty_vec_mul_vec Matrix.empty_vecMulVec

@[simp]
theorem vecMulVec_empty (v : m' → α) (w : Fin 0 → α) : vecMulVec v w = of fun _ => ![] :=
  funext fun _ => empty_eq _
#align matrix.vec_mul_vec_empty Matrix.vecMulVec_empty

@[simp]
theorem cons_vecMulVec (x : α) (v : Fin m → α) (w : n' → α) :
    vecMulVec (vecCons x v) w = vecCons (x • w) (vecMulVec v w) := by
  ext i
  refine Fin.cases ?_ ?_ i <;> simp [vecMulVec]
#align matrix.cons_vec_mul_vec Matrix.cons_vecMulVec

@[simp]
theorem vecMulVec_cons (v : m' → α) (x : α) (w : Fin n → α) :
    vecMulVec v (vecCons x w) = of fun i => v i • vecCons x w := rfl
#align matrix.vec_mul_vec_cons Matrix.vecMulVec_cons

end VecMulVec

section SMul

variable [NonUnitalNonAssocSemiring α]

-- @[simp] -- Porting note (#10618): simp can prove this
theorem smul_mat_empty {m' : Type*} (x : α) (A : Fin 0 → m' → α) : x • A = ![] :=
  empty_eq _
#align matrix.smul_mat_empty Matrix.smul_mat_empty

-- @[simp] -- Porting note (#10618): simp can prove this
theorem smul_mat_cons (x : α) (v : n' → α) (A : Fin m → n' → α) :
    x • vecCons v A = vecCons (x • v) (x • A) := by
  ext i
  refine Fin.cases ?_ ?_ i <;> simp
#align matrix.smul_mat_cons Matrix.smul_mat_cons

end SMul

section Submatrix

@[simp]
theorem submatrix_empty (A : Matrix m' n' α) (row : Fin 0 → m') (col : o' → n') :
    submatrix A row col = ![] :=
  empty_eq _
#align matrix.submatrix_empty Matrix.submatrix_empty

@[simp]
theorem submatrix_cons_row (A : Matrix m' n' α) (i : m') (row : Fin m → m') (col : o' → n') :
    submatrix A (vecCons i row) col = vecCons (fun j => A i (col j)) (submatrix A row col) := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> simp [submatrix]
#align matrix.submatrix_cons_row Matrix.submatrix_cons_row

/-- Updating a row then removing it is the same as removing it. -/
@[simp]
theorem submatrix_updateRow_succAbove (A : Matrix (Fin m.succ) n' α) (v : n' → α) (f : o' → n')
    (i : Fin m.succ) : (A.updateRow i v).submatrix i.succAbove f = A.submatrix i.succAbove f :=
  ext fun r s => (congr_fun (updateRow_ne (Fin.succAbove_ne i r) : _ = A _) (f s) : _)
#align matrix.submatrix_update_row_succ_above Matrix.submatrix_updateRow_succAbove

/-- Updating a column then removing it is the same as removing it. -/
@[simp]
theorem submatrix_updateColumn_succAbove (A : Matrix m' (Fin n.succ) α) (v : m' → α) (f : o' → m')
    (i : Fin n.succ) : (A.updateColumn i v).submatrix f i.succAbove = A.submatrix f i.succAbove :=
  ext fun _r s => updateColumn_ne (Fin.succAbove_ne i s)
#align matrix.submatrix_update_column_succ_above Matrix.submatrix_updateColumn_succAbove

end Submatrix

section Vec2AndVec3

section One

variable [Zero α] [One α]

theorem one_fin_two : (1 : Matrix (Fin 2) (Fin 2) α) = !![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
#align matrix.one_fin_two Matrix.one_fin_two

theorem one_fin_three : (1 : Matrix (Fin 3) (Fin 3) α) = !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
#align matrix.one_fin_three Matrix.one_fin_three

end One

section AddMonoidWithOne
variable [AddMonoidWithOne α]

theorem natCast_fin_two (n : ℕ) : (n : Matrix (Fin 2) (Fin 2) α) = !![↑n, 0; 0, ↑n] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem natCast_fin_three (n : ℕ) :
    (n : Matrix (Fin 3) (Fin 3) α) = !![↑n, 0, 0; 0, ↑n, 0; 0, 0, ↑n] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

-- See note [no_index around OfNat.ofNat]
theorem ofNat_fin_two (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : Matrix (Fin 2) (Fin 2) α) =
      !![OfNat.ofNat n, 0; 0, OfNat.ofNat n] :=
  natCast_fin_two _

-- See note [no_index around OfNat.ofNat]
theorem ofNat_fin_three (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : Matrix (Fin 3) (Fin 3) α) =
      !![OfNat.ofNat n, 0, 0; 0, OfNat.ofNat n, 0; 0, 0, OfNat.ofNat n] :=
  natCast_fin_three _

end AddMonoidWithOne

theorem eta_fin_two (A : Matrix (Fin 2) (Fin 2) α) : A = !![A 0 0, A 0 1; A 1 0, A 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
#align matrix.eta_fin_two Matrix.eta_fin_two

theorem eta_fin_three (A : Matrix (Fin 3) (Fin 3) α) :
    A = !![A 0 0, A 0 1, A 0 2;
           A 1 0, A 1 1, A 1 2;
           A 2 0, A 2 1, A 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
#align matrix.eta_fin_three Matrix.eta_fin_three

theorem mul_fin_two [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    !![a₁₁, a₁₂;
       a₂₁, a₂₂] * !![b₁₁, b₁₂;
                      b₂₁, b₂₂] = !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
                                     a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]
#align matrix.mul_fin_two Matrix.mul_fin_two

theorem mul_fin_three [AddCommMonoid α] [Mul α]
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : α) :
    !![a₁₁, a₁₂, a₁₃;
       a₂₁, a₂₂, a₂₃;
       a₃₁, a₃₂, a₃₃] * !![b₁₁, b₁₂, b₁₃;
                           b₂₁, b₂₂, b₂₃;
                           b₃₁, b₃₂, b₃₃] =
    !![a₁₁*b₁₁ + a₁₂*b₂₁ + a₁₃*b₃₁, a₁₁*b₁₂ + a₁₂*b₂₂ + a₁₃*b₃₂, a₁₁*b₁₃ + a₁₂*b₂₃ + a₁₃*b₃₃;
       a₂₁*b₁₁ + a₂₂*b₂₁ + a₂₃*b₃₁, a₂₁*b₁₂ + a₂₂*b₂₂ + a₂₃*b₃₂, a₂₁*b₁₃ + a₂₂*b₂₃ + a₂₃*b₃₃;
       a₃₁*b₁₁ + a₃₂*b₂₁ + a₃₃*b₃₁, a₃₁*b₁₂ + a₃₂*b₂₂ + a₃₃*b₃₂, a₃₁*b₁₃ + a₃₂*b₂₃ + a₃₃*b₃₃] := by
  ext i j
  fin_cases i <;> fin_cases j
    <;> simp [Matrix.mul_apply, dotProduct, Fin.sum_univ_succ, ← add_assoc]
#align matrix.mul_fin_three Matrix.mul_fin_three

theorem vec2_eq {a₀ a₁ b₀ b₁ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) : ![a₀, a₁] = ![b₀, b₁] := by
  subst_vars
  rfl
#align matrix.vec2_eq Matrix.vec2_eq

theorem vec3_eq {a₀ a₁ a₂ b₀ b₁ b₂ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) :
    ![a₀, a₁, a₂] = ![b₀, b₁, b₂] := by
  subst_vars
  rfl
#align matrix.vec3_eq Matrix.vec3_eq

theorem vec2_add [Add α] (a₀ a₁ b₀ b₁ : α) : ![a₀, a₁] + ![b₀, b₁] = ![a₀ + b₀, a₁ + b₁] := by
  rw [cons_add_cons, cons_add_cons, empty_add_empty]
#align matrix.vec2_add Matrix.vec2_add

theorem vec3_add [Add α] (a₀ a₁ a₂ b₀ b₁ b₂ : α) :
    ![a₀, a₁, a₂] + ![b₀, b₁, b₂] = ![a₀ + b₀, a₁ + b₁, a₂ + b₂] := by
  rw [cons_add_cons, cons_add_cons, cons_add_cons, empty_add_empty]
#align matrix.vec3_add Matrix.vec3_add

theorem smul_vec2 {R : Type*} [SMul R α] (x : R) (a₀ a₁ : α) :
    x • ![a₀, a₁] = ![x • a₀, x • a₁] := by rw [smul_cons, smul_cons, smul_empty]
#align matrix.smul_vec2 Matrix.smul_vec2

theorem smul_vec3 {R : Type*} [SMul R α] (x : R) (a₀ a₁ a₂ : α) :
    x • ![a₀, a₁, a₂] = ![x • a₀, x • a₁, x • a₂] := by
  rw [smul_cons, smul_cons, smul_cons, smul_empty]
#align matrix.smul_vec3 Matrix.smul_vec3

variable [AddCommMonoid α] [Mul α]

theorem vec2_dotProduct' {a₀ a₁ b₀ b₁ : α} : ![a₀, a₁] ⬝ᵥ ![b₀, b₁] = a₀ * b₀ + a₁ * b₁ := by
  rw [cons_dotProduct_cons, cons_dotProduct_cons, dotProduct_empty, add_zero]
#align matrix.vec2_dot_product' Matrix.vec2_dotProduct'

@[simp]
theorem vec2_dotProduct (v w : Fin 2 → α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 :=
  vec2_dotProduct'
#align matrix.vec2_dot_product Matrix.vec2_dotProduct

theorem vec3_dotProduct' {a₀ a₁ a₂ b₀ b₁ b₂ : α} :
    ![a₀, a₁, a₂] ⬝ᵥ ![b₀, b₁, b₂] = a₀ * b₀ + a₁ * b₁ + a₂ * b₂ := by
  rw [cons_dotProduct_cons, cons_dotProduct_cons, cons_dotProduct_cons, dotProduct_empty,
    add_zero, add_assoc]
#align matrix.vec3_dot_product' Matrix.vec3_dotProduct'

@[simp]
theorem vec3_dotProduct (v w : Fin 3 → α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 :=
  vec3_dotProduct'
#align matrix.vec3_dot_product Matrix.vec3_dotProduct

end Vec2AndVec3

end Matrix
