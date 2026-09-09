/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Matrix.OfLists  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Matrix.Parsing
public import Mathlib.Tactic.NormNum.Core

/-!
# Products of matrix literals

`proveMul` proves `A * B = C` for matrix literals `A` and `B`, with the entries of `C` normalized
by a given `EntryNormalizer`, and returns it as a `Simp.Result` that other tactics consume in
`MetaM`; `norm_matmul` is the simproc wrapping it, currently using `norm_num` as the normalizer.

## Main definitions

* `EntryNormalizer`
* `proveDotProduct`
* `proveMul`
* `normMatMulCore`
* `norm_matmul`

## Implementation notes

The simproc simplifies the factors before matching them, so that a product of products is
evaluated inside-out.

Note that the simp lemmas unfolding `vecCons` compete with this simproc due to how `!![]` is
currently elaborated, so this tactic should be used by `simp only` or with `↓` to run as a
pre-procedure.
-/

public meta section

open Lean Meta Qq

initialize registerTraceClass `Tactic.norm_matmul

namespace Mathlib.Tactic.Matrix

/-- An entry normalizer rewrites an expression about a single entry to a normal form. -/
abbrev EntryNormalizer := Expr → MetaM Simp.Result

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

/-- Prove `ListMatrix.dotProduct m l₁ l₂ = v` for the `m` entries `as` and `bs`, with `v` their
dot product normalized by `normalizer`. -/
def proveDotProduct (normalizer : EntryNormalizer) (m : ℕ) (as bs : List Q($α)) :
    MetaM (DotProductEq zα aα mα) := do
  let ⟨_, l₁, l₂, fold, h⟩ := mkDotProductChain zα aα mα as bs
  have mQ : Q(ℕ) := q($m)
  -- restate the chain's successor tower as the numeral `m`: Qq cannot check the two equal, the
  -- kernel does by literal arithmetic
  have hDot : Q(ListMatrix.dotProduct $mQ $l₁ $l₂ = $fold) :=
    ← mkExpectedTypeHint h q(ListMatrix.dotProduct $mQ $l₁ $l₂ = $fold)
  -- normalize the rhs
  let r ← normalizer fold
  have v : Q($α) := r.expr
  have hFold : Q($fold = $v) := ← r.getProof
  return ⟨mQ, l₁, l₂, v, q(($hDot).trans $hFold)⟩

end

/-- Prove `[a₀, …] = [b₀, …]` in `List α` from proofs of `aᵢ = bᵢ` by manually applying `congr`.
`MVarId.congrN` also works, but takes around 40x heartbeats to elaborate. -/
def mkListCongr {u : Level} {α : Q(Type u)} :
    List ((a : Q($α)) × (b : Q($α)) × Q($a = $b)) →
      (l₁ : Q(List $α)) × (l₂ : Q(List $α)) × Q($l₁ = $l₂)
  | [] => ⟨q([]), q([]), q(rfl)⟩
  | ⟨a, b, h⟩ :: es =>
    let ⟨l₁, l₂, hl⟩ := mkListCongr es
    ⟨q($a :: $l₁), q($b :: $l₂), q(congr (congrArg List.cons $h) $hl)⟩

/-- Prove `e = C`, where `e` is the product of the matrix literals with rows `rowsA` and
`rowsB` over `α`, and `C` is the literal of the product with entries normalized by
`normalizer`. -/
def proveMul {u : Level} (normalizer : EntryNormalizer) (e : Expr) (l m n : ℕ) (α : Q(Type u))
    (rowsA rowsB : Array (Array Expr)) : MetaM Simp.Result := do
  let zα ← synthInstanceQ q(Zero $α)
  let aα ← synthInstanceQ q(Add $α)
  let mα ← synthInstanceQ q(Mul $α)
  let _acm ← synthInstanceQ q(AddCommMonoid $α)
  let cols : Array (Array Expr) :=
    Array.ofFn (n := n) fun j => Array.ofFn (n := m) fun i => (rowsB[i]!)[j]!
  let cells ← Array.ofFnM (n := l) fun i => Array.ofFnM (n := n) fun j =>
    proveDotProduct zα aα mα normalizer m rowsA[i]!.toList cols[j]!.toList
  let entries := cells.map (·.map (·.result))
  let ⟨_, _, hAll⟩ := mkListCongr (α := q(List $α)) <| cells.toList.map fun row =>
    mkListCongr <| row.toList.map fun d =>
      ⟨q(ListMatrix.dotProduct $(d.n) $(d.l₁) $(d.l₂)), d.result, d.proof⟩
  let mkLists (rows : Array (Array Expr)) : MetaM Q(List (List $α)) := do
    mkListLit q(List $α) (← rows.toList.mapM (mkListLit α ·.toList))
  have A : Q(List (List $α)) := ← mkLists rowsA
  have B : Q(List (List $α)) := ← mkLists rowsB
  have C : Q(Matrix (Fin $l) (Fin $n) $α) :=
    Matrix.mkLiteralQ (α := α) (m := l) (n := n) (.of fun i j => (entries[i]!)[j]!)
  let hMul := q((ofLists_mul $l $m $n $A $B).symm)
  let hC := q(congrArg (ofLists (α := $α) $l $n) $hAll)
  let pf ← mkEqTrans hMul hC
  -- `pf` is stated on `ofLists` forms; the hint to `e = C` holds because `ofLists` on
  -- a row-list literal unfolds to exactly the `Matrix.of`/`vecCons` term of the `!![…]`
  -- literal, so the kernel settles it by reduction
  return { expr := C, proof? := some (← mkExpectedTypeHint pf (← mkEq e C)) }

/-- Core of the `norm_matmul` simproc with the given entry normalizer; the factors are
simplified first. -/
def normMatMulCore (normalizer : EntryNormalizer) : Simp.Simproc := fun e => do
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
  return .done (← rAB.mkEqTrans (← proveMul (u := u) normalizer rAB.expr l m n R rowsA rowsB))

end Mathlib.Tactic.Matrix

open Mathlib.Tactic.Matrix

/-- The `norm_matmul` simproc rewrites a product of matrix literals with non-symbolic entries
to the literal of the product, with the entries computed by `norm_num`. Use it as
`simp only [norm_matmul]`; alongside the default simp set it must run as a pre-procedure,
`simp [↓ norm_matmul]`, ahead of the simp lemmas on `vecCons` rows. `norm_num` ignores simprocs
given as arguments. Terms that it cannot evaluate are skipped, and can be viewed by using
`set_option trace.Tactic.norm_matmul true`. -/
simproc_decl norm_matmul ((_ * _ : Matrix (Fin _) (Fin _) _)) := fun e => do
  try normMatMulCore (Mathlib.Meta.NormNum.eval ·) e
  catch ex =>
    trace[Tactic.norm_matmul] "{ex.toMessageData}"
    return .continue
