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

`proveMul` proves `A * B = C` for matrix literals `A` and `B`, with the entries of `C` normalized
by a given `EntryNormalizer`, and returns `C` with the proof for other tactics to consume in
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
currently elaborated, so the simproc be used by `simp only` or with `↓` to run as a
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
    mkExpectedPropHint h q(ListMatrix.dotProduct $mQ $l₁ $l₂ = $fold)
  let r ← normalizer fold
  have v : Q($α) := r.expr
  have hFold : Q($fold = $v) := ← r.getProof
  return ⟨mQ, l₁, l₂, v, q(($hDot).trans $hFold)⟩

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

/-- Prove `e = C`, where `e` is the product of the matrix literals with rows `A` and `B` over
`α`, and `C` is the literal of the product with entries normalized by `normalizer`. -/
def proveMul {u : Level} (normalizer : EntryNormalizer) (l m n : ℕ) (α : Q(Type u))
    (e : Q(Matrix (Fin $l) (Fin $n) $α)) (A B : Array (Array Q($α))) :
    MetaM ((C : Q(Matrix (Fin $l) (Fin $n) $α)) × Q($e = $C)) := do
  let zα ← synthInstanceQ q(Zero $α)
  let aα ← synthInstanceQ q(Add $α)
  let mα ← synthInstanceQ q(Mul $α)
  let _acm ← synthInstanceQ q(AddCommMonoid $α)
  let Bt : Array (Array Q($α)) :=
    Array.ofFn (n := n) fun j => Array.ofFn (n := m) fun i => (B[i]!)[j]!
  let rowsA := A.map (·.toList)
  let colsB := Bt.map (·.toList)
  -- assemble the dotproduct matrix from A and Bᵗ
  let mulEntryEqs ← Array.ofFnM (n := l) fun i => Array.ofFnM (n := n) fun j =>
    proveDotProduct zα aα mα normalizer m rowsA[i]! colsB[j]!
  let mulEntries := mulEntryEqs.map (·.map (·.result))
  let ⟨_, _, hMulEntries⟩ := mkListCongr (α := q(List $α)) <| mulEntryEqs.toList.map fun row =>
    mkListCongr <| row.toList.map fun d =>
      ⟨q(ListMatrix.dotProduct $(d.n) $(d.l₁) $(d.l₂)), d.result, d.proof⟩
  have listA : Q(List (List $α)) := ← mkListLit q(List $α) (← A.toList.mapM (mkListLit α ·.toList))
  have listB : Q(List (List $α)) := ← mkListLit q(List $α) (← B.toList.mapM (mkListLit α ·.toList))
  let C := Matrix.mkLiteralQ (α := α) (m := l) (n := n) (.of fun i j => (mulEntries[i]!)[j]!)
  let hMul := q((ofLists_mul $l $m $n $listA $listB).symm)
  let hC := q(congrArg (ofLists (α := $α) $l $n) $hMulEntries)
  let pf ← mkEqTrans hMul hC
  -- `pf` is stated on `ofLists` forms; the hint to `e = C` holds because `ofLists` on
  -- a row-list literal unfolds to exactly the `Matrix.of`/`vecCons` term of the `!![…]`
  -- literal, so the kernel settles it by reduction
  have h : Q($e = $C) := mkExpectedPropHint pf q($e = $C)
  return ⟨C, h⟩

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
  have α : Q(Type u) := R
  have AB : Q(Matrix (Fin $l) (Fin $n) $α) := rAB.expr
  let ⟨C, h⟩ ← proveMul normalizer l m n α AB rowsA rowsB
  return .done (← rAB.mkEqTrans { expr := C, proof? := some h })

end Mathlib.Tactic.Matrix

open Mathlib.Tactic.Matrix

/-- The `norm_matmul` simproc rewrites a product of matrix literals with non-symbolic entries
to the literal of the product, with the entries computed by `norm_num`. Terms that it cannot
evaluate are skipped, and can be viewed by using `set_option trace.Tactic.norm_matmul true`. -/
simproc_decl norm_matmul ((_ * _ : Matrix (Fin _) (Fin _) _)) := fun e => do
  try normMatMulCore (Mathlib.Meta.NormNum.eval ·) e
  catch ex =>
    trace[Tactic.norm_matmul] "{ex.toMessageData}"
    return .continue
