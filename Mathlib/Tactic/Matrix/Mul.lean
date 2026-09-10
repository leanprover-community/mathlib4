/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Matrix.OfLists  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Matrix.Parsing
public import Mathlib.Tactic.NormNum.Basic  -- shake: keep (`+`/`*` extensions run by `norm_matmul`)

/-!
# Products of matrix literals

`proveMul` proves `A * B = C` for matrix literals `A` and `B`, with `C` the literal whose entries
are the sums of products of the entries, and returns `C` with the proof for other tactics to
consume in `MetaM`; `normalizeEntries` rewrites the entries of a literal by a given normalizer,
and `norm_matmul` is the simproc composing the two with `norm_num`.

## Implementation notes

The simproc simplifies the factors before matching them, so that a product of products is
evaluated inside-out.

Note that the simp lemmas unfolding `vecCons` compete with this simproc due to how `!![]` is
currently elaborated, so the simproc be used by `simp only` or with `↓` to run as a
pre-procedure.
-/

public meta section

open Lean Meta Qq

initialize registerTraceClass `Tactic.norm_matmul

namespace Mathlib.Tactic.Matrix

section

-- the classes are parameters so that every quotation references the one instance term the
-- caller synthesised, rather than rebuilding a projection path in every cell
variable {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (aα : Q(Add $α)) (mα : Q(Mul $α))

/-- A dot product of two lists of entries, `ListMatrix.dotProduct n l₁ l₂ = result`, with its
proof. -/
structure DotProductEq where
  /-- The number of terms. -/
  n : Q(ℕ)
  /-- The first list. -/
  l₁ : Q(List $α)
  /-- The second list. -/
  l₂ : Q(List $α)
  /-- The right-hand side. -/
  result : Q($α)
  /-- The proof. -/
  proof : Q(ListMatrix.dotProduct $n $l₁ $l₂ = $result)

/-- The unfolding of the dot product of the entries `as` and `bs` to the fold
`a₀ * b₀ + (a₁ * b₁ + (… + 0))`, by the equations of `ListMatrix.dotProduct`; its `n` is the
successor tower `((0 + 1) + 1) + …` the equations build, one `+ 1` per term rather than a
numeral. -/
def mkDotProductChain : List Q($α) → List Q($α) → DotProductEq zα aα mα
  | a :: as, b :: bs =>
    let ⟨n, l₁, l₂, fold, h⟩ := mkDotProductChain as bs
    ⟨q($n + 1), q($a :: $l₁), q($b :: $l₂), q($a * $b + $fold),
      q(ListMatrix.dotProduct_succ_cons_cons $a $b $h)⟩
  | _, _ => ⟨q(0), q([]), q([]), q(0), q(ListMatrix.dotProduct_zero [] [])⟩

/-- The dot product of the `m` entries `as` and `bs`, `ListMatrix.dotProduct m l₁ l₂ = fold`, with
`m` a numeral and `fold` the sum of the products. -/
def proveDotProduct (m : ℕ) (as bs : List Q($α)) : DotProductEq zα aα mα :=
  let ⟨_, l₁, l₂, fold, h⟩ := mkDotProductChain zα aα mα as bs
  have mQ : Q(ℕ) := q($m)
  -- restate the chain's successor tower as the numeral `m`: Qq cannot check the two equal, the
  -- kernel does by literal arithmetic
  ⟨mQ, l₁, l₂, fold, mkExpectedPropHint h q(ListMatrix.dotProduct $mQ $l₁ $l₂ = $fold)⟩

end

/-- Construct a proof term that `[a₀, …] = [b₀, …]` in `List α` from proofs of `aᵢ = bᵢ`.
`MVarId.congrN` also works, but is much slower to elaborate. -/
def mkListCongr {u : Level} {α : Q(Type u)} :
    List ((a : Q($α)) × (b : Q($α)) × Q($a = $b)) →
      (l₁ : Q(List $α)) × (l₂ : Q(List $α)) × Q($l₁ = $l₂)
  | [] => ⟨q([]), q([]), q(rfl)⟩
  | ⟨a, b, h⟩ :: es =>
    let ⟨l₁, l₂, hl⟩ := mkListCongr es
    ⟨q($a :: $l₁), q($b :: $l₂), q(congrArg₂ List.cons $h $hl)⟩

/-- Rewrite `e`, the product of the matrix literals with rows `A` and `B` over `α`, to the
literal whose entries are the sums of products of the entries. -/
def proveMul {u : Level} (l m n : ℕ) (α : Q(Type u)) (e : Q(Matrix (Fin $l) (Fin $n) $α))
    (A B : Array (Array Q($α))) : MetaM Simp.Result := do
  -- synthesise the instances for the rewrite lemmas and are not actually used for evaluation here.
  let zα ← synthInstanceQ q(Zero $α)
  let aα ← synthInstanceQ q(Add $α)
  let mα ← synthInstanceQ q(Mul $α)
  let _acm ← synthInstanceQ q(AddCommMonoid $α)
  let Bt : Array (Array Q($α)) :=
    Array.ofFn (n := n) fun j => Array.ofFn (n := m) fun i => (B[i]!)[j]!
  let rowsA := A.map Array.toList
  let colsB := Bt.map Array.toList
  -- assemble the dotproduct matrix from A and Bᵗ
  let mulEntryEqs := Array.ofFn (n := l) fun i => Array.ofFn (n := n) fun j =>
    proveDotProduct zα aα mα m rowsA[i]! colsB[j]!
  let entries := mulEntryEqs.map (·.map (·.result))
  let ⟨_, _, hMulEntries⟩ := mkListCongr (α := q(List $α)) <| mulEntryEqs.toList.map fun row =>
    mkListCongr <| row.toList.map fun d =>
      ⟨q(ListMatrix.dotProduct $(d.n) $(d.l₁) $(d.l₂)), d.result, d.proof⟩
  have listA : Q(List (List $α)) := ← mkListLit q(List $α) (← A.toList.mapM (mkListLit α ·.toList))
  have listB : Q(List (List $α)) := ← mkListLit q(List $α) (← B.toList.mapM (mkListLit α ·.toList))
  let C := Matrix.mkLiteralQ (α := α) (m := l) (n := n) (.of fun i j => (entries[i]!)[j]!)
  let hMul := q((ofLists_mul $l $m $n $listA $listB).symm)
  let hC := q(congrArg (ofLists (α := $α) $l $n) $hMulEntries)
  let pf ← mkEqTrans hMul hC
  -- `pf` is stated on `ofLists` forms; the hint to `e = C` holds because `ofLists` on
  -- a row-list literal unfolds to exactly the `Matrix.of`/`vecCons` term of the `!![…]`
  -- literal, so the kernel settles it by reduction
  return { expr := C, proof? := some (mkExpectedPropHint pf q($e = $C)) }

/-- Construct the literals `![a₀, …]` and `![b₀, …]` in `Fin n → α` with a proof of their equality
from proofs of `aᵢ = bᵢ`, in the shape `PiFin.mkLiteralQ` builds them. -/
def mkVecCongr {u : Level} {α : Q(Type u)} {n : ℕ}
    (elems : Fin n → (a : Q($α)) × (b : Q($α)) × Q($a = $b)) :
    (v : Q(Fin $n → $α)) × (w : Q(Fin $n → $α)) × Q($v = $w) :=
  loop 0 ⟨q(Matrix.vecEmpty), q(Matrix.vecEmpty), q(rfl)⟩
where
  /-- Extend the literals of the last `i` entries by the entry before them. -/
  loop (i : ℕ) (rest : (v : Q(Fin $i → $α)) × (w : Q(Fin $i → $α)) × Q($v = $w)) :
      (v : Q(Fin $n → $α)) × (w : Q(Fin $n → $α)) × Q($v = $w) :=
    if h : i < n then
      let ⟨a, b, hab⟩ := elems (Fin.rev ⟨i, h⟩)
      let ⟨v, w, hvw⟩ := rest
      loop (i + 1) ⟨q(Matrix.vecCons $a $v), q(Matrix.vecCons $b $w),
        q(congrArg₂ Matrix.vecCons $hab $hvw)⟩
    else
      rest
  termination_by n - i

/-- Construct the literals `!![a₀₀, …]` and `!![b₀₀, …]` with a proof of their equality from
proofs of `aᵢⱼ = bᵢⱼ`, in the shape `Matrix.mkLiteralQ` builds them. -/
def mkMatrixCongr {u : Level} {α : Q(Type u)} {m n : ℕ}
    (elems : Fin m → Fin n → (a : Q($α)) × (b : Q($α)) × Q($a = $b)) :
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) × (B : Q(Matrix (Fin $m) (Fin $n) $α)) × Q($A = $B) :=
  let ⟨v, w, h⟩ := mkVecCongr (α := q(Fin $n → $α)) fun i => mkVecCongr (elems i)
  ⟨q(Matrix.of $v), q(Matrix.of $w), q(congrArg (fun f => Matrix.of f) $h)⟩

/-- Rewrite the entries of the matrix literal `C` by `normalizer`. -/
def normalizeEntries (normalizer : Expr → MetaM Simp.Result) (C : Expr) : MetaM Simp.Result := do
  let some (m, n, R, entries) ← matchMatrixLit? C
    | throwError "not a closed matrix literal{indentExpr C}"
  let u ← getDecLevel R
  have α : Q(Type u) := R
  let eqs ← entries.mapM (·.mapM fun a => do
    have a : Q($α) := a
    let r ← normalizer a
    have b : Q($α) := r.expr
    have h : Q($a = $b) := ← r.getProof
    return (⟨a, b, h⟩ : (a : Q($α)) × (b : Q($α)) × Q($a = $b)))
  -- the left literal is `C` as `Matrix.mkLiteralQ` builds it
  let ⟨_, C', h⟩ := mkMatrixCongr (m := m) (n := n) fun i j => (eqs[i]!)[j]!
  return { expr := C', proof? := some h }

/-- Core of the `norm_matmul` simproc: the factors are simplified first, and the entries of the
product literal are computed by `norm_num`. -/
def normMatMulCore : Simp.Simproc := fun e => do
  let_expr HMul.hMul _ _ _ _ A B := e | return .continue
  let rA ← Simp.simp A
  let rB ← Simp.simp B
  let some (l, m, R, rowsA) ← matchMatrixLit? rA.expr
    | trace[Tactic.norm_matmul] "not a closed matrix literal{indentExpr rA.expr}"
      return .continue
  let some (_, n, _, rowsB) ← matchMatrixLit? rB.expr
    | trace[Tactic.norm_matmul] "not a closed matrix literal{indentExpr rB.expr}"
      return .continue
  let rAB ← Simp.mkCongr (← Simp.mkCongr { expr := e.appFn!.appFn! } rA) rB
  let u ← getDecLevel R
  have α : Q(Type u) := R
  have AB : Q(Matrix (Fin $l) (Fin $n) $α) := rAB.expr
  let r ← proveMul l m n α AB rowsA rowsB
  let s ← normalizeEntries Mathlib.Meta.NormNum.eval r.expr
  return .done (← rAB.mkEqTrans (← r.mkEqTrans s))

end Mathlib.Tactic.Matrix

open Mathlib.Tactic.Matrix

/-- The `norm_matmul` simproc rewrites a product of matrix literals with non-symbolic entries
to the literal of the product, with the entries computed by `norm_num`. Terms that it cannot
evaluate are skipped, and can be viewed by using `set_option trace.Tactic.norm_matmul true`. -/
simproc_decl norm_matmul ((_ * _ : Matrix (Fin _) (Fin _) _)) := fun e => do
  try normMatMulCore e
  catch ex =>
    trace[Tactic.norm_matmul] "{ex.toMessageData}"
    return .continue
