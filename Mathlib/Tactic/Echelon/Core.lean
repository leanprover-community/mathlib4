/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Init

/-!
# Parameterized computation core for the Bareiss elimination

A computable model of a ring packages the representation the untrusted producer computes
with: a value type `V`, its arithmetic (`RingOps V`), and the encoding between entry
syntax and values. `mkProducer` assembles a `Producer` from a model's parts, and the
tactic selects a model through the `bareiss_ext` extension registry.

## Main definitions

- `RingOps`: the arithmetic of a model's value type.
- `bareissDecomp`: fraction-free Gaussian elimination over a model's values.
- `mkProducer`: assemble a producer from a model's parts.
- `bareiss_ext`: the attribute registering a `BareissExt` computation model.

## Implementation notes

The elimination in `bareissDecomp` maintains the invariant `L * A_σ = W`, where
`A_σ := A.submatrix σ id` is the input with its rows in the arrangement `σ` accumulated
so far and `W` is the working matrix. When the pivot search swaps the rows at positions
`r < p`, the invariant must be restored against the new `A_σ' = S * A_σ`, where `S` is
the permutation matrix of the transposition `τ = (r, p)`:

  `S * W = S * L * (S⁻¹ * S) * A_σ = (S * L * S⁻¹) * A_σ'`

so `L` is conjugated by the matrix of `τ`, as in LU factorisation with partial pivoting.

## References

* [Bareiss, *Sylvester's identity and multistep integer-preserving Gaussian
  elimination*][bareiss1968]
-/

public meta section

open Lean Meta

namespace Mathlib.Tactic.Echelon

/-- Arithmetic of a model's value type. -/
structure RingOps (V : Type) where
  /-- The zero value. -/
  zero : V
  /-- The one value. -/
  one : V
  /-- Multiplication. -/
  mul : V → V → V
  /-- Subtraction. -/
  sub : V → V → V
  /-- Exact division: total on the quotients of the elimination -/
  divExact : V → V → V
  /-- The pivot zero test. -/
  isZero : V → Bool

/-- Decomposition data with entries in `V`: the values of the elimination, or the
ring expressions constructed (`V := Expr`). -/
structure BareissData (V : Type) where
  /-- The lower-triangular transform. -/
  L : Array (Array V)
  /-- The echelon form, the final working matrix `L * A_σ` of the elimination. -/
  U : Array (Array V)
  /-- The row swaps, in order. Stores the swaps instead of row re-indexing, since in
  common cases swaps are infrequent and therefore produce a smaller term to be checked
  by the kernel. The row permutation `σ` is later constructed by their product. -/
  swaps : Array (Nat × Nat)
  /-- The pivot columns. The `k`-th entry is the column of the pivot in row `k` of the
  final echelon form. -/
  pivot : Array Nat

/-- Map over the entries of the transform. -/
def BareissData.mapM {V W : Type} (f : V → MetaM W) (d : BareissData V) :
    MetaM (BareissData W) :=
  return { L := ← d.L.mapM (·.mapM f), U := ← d.U.mapM (·.mapM f),
           swaps := d.swaps, pivot := d.pivot }

/-- The row arrangement of the swaps: the entry at position `i` is the original row index
that the swaps move to position `i`, that is, `σ i`. -/
def BareissData.rowOrder {V : Type} (d : BareissData V) : Array Nat :=
  d.swaps.foldl (fun ord (a, b) => ord.swapIfInBounds a b) (Array.range d.L.size)

/-- A producer: run the elimination on the entries of a matrix literal, returning
the decomposition constructed. -/
@[expose] def Producer := Array (Array Expr) → MetaM (BareissData Expr)

/-- Core algorithm of fraction-free Gaussian elimination, with the arithmetic supplied
by the model.

A single sweep accumulates the transform `L` alongside the working matrix `W`, maintaining
`L * (A.submatrix σ id) = W` for the row arrangement `σ` so far. The divisions are exact
by Sylvester's identity, although the data-only computation does not prove that. -/
def bareissDecomp {V : Type} (ops : RingOps V) (A : Array (Array V)) :
    MetaM (BareissData V) := do
  let rows := A.size
  let cols := (A.getD 0 #[]).size
  let getEntry (M : Array (Array V)) (i j : Nat) : V := (M.getD i #[]).getD j ops.zero
  let eliminate (pivot coef prev : V) (row pivotRow : Array V) : Array V :=
    Array.zipWith (fun a b => ops.divExact (ops.sub (ops.mul pivot a) (ops.mul coef b)) prev)
      row pivotRow
  let mut W := A
  let mut L : Array (Array V) :=
    Array.ofFn (n := rows) fun i =>
      Array.ofFn (n := rows) fun j => if i == j then ops.one else ops.zero
  let mut swaps : Array (Nat × Nat) := #[]
  let mut pivotCols : Array Nat := #[]
  let mut r : Nat := 0
  -- the exact divisor of the elimination step
  let mut prevPivot : V := ops.one
  /- TODO: if we're handling larger matrices (beyond 10⁴ entries), add a checkSystem call
  per column to honor user interruption. At current realistic sizes this computation is
  almost instant. -/
  for c in 0...cols do
    if r == rows then break
    -- find the first row at or below `r` with a nonzero entry in column `c`
    let mut p? : Option Nat := none
    for q in r...rows do
      if !ops.isZero (getEntry W q c) then
        p? := some q
        break
    if let some p := p? then
      if p ≠ r then
        W := W.swapIfInBounds r p
        -- row swap
        L := L.swapIfInBounds r p
        -- column swap. This affects only rows `r` and `p`, since every other
        -- row vanishes at both columns
        L := (L.modify r (·.swapIfInBounds r p)).modify p (·.swapIfInBounds r p)
        swaps := swaps.push (r, p)
      pivotCols := pivotCols.push c
      let pivot := getEntry W r c
      let wRow := W.getD r #[]
      let lRow := L.getD r #[]
      for i in r<...rows do
        let coef := getEntry W i c
        W := W.set! i (eliminate pivot coef prevPivot (W.getD i #[]) wRow)
        L := L.set! i (eliminate pivot coef prevPivot (L.getD i #[]) lRow)
      prevPivot := pivot
      r := r + 1
  return { L, U := W, swaps, pivot := pivotCols }

/-- Assemble a producer from a computation model's parts.
`ops` describes the ring operation structure;
`prepare` reifies the entries into the values the elimination runs on, plus a
function restoring the resulting decomposition to one of the original matrix;
`mkEntry` constructs the value back in the ring. -/
def mkProducer {V : Type} (ops : RingOps V)
    (prepare : Array (Array Expr) →
      MetaM (Array (Array V) × (BareissData V → BareissData V)))
    (mkEntry : V → MetaM Expr) : Producer := fun entries => do
  let (values, restore) ← prepare entries
  let d ← bareissDecomp ops values
  (restore d).mapM mkEntry

/-- An extension of the Bareiss ring computation model. -/
structure BareissExt where
  /-- The computation model for the ring type `R`, or `none` if the extension does not
  handle `R`. -/
  producer? (R : Expr) : MetaM (Option Producer)

/-- Read a `bareiss_ext` extension from a declaration of the right type. -/
def mkBareissExt (n : Name) : ImportM BareissExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck BareissExt opts ``BareissExt n

/-- Environment extension for the `bareiss_ext` computation models.
Uses a simple array to store the name-extension pairs for now. -/
initialize bareissExt : ScopedEnvExtension Name (Name × BareissExt) (Array (Name × BareissExt)) ←
  registerScopedEnvExtension {
    mkInitial := pure #[]
    ofOLeanEntry := fun _ n => return (n, ← mkBareissExt n)
    toOLeanEntry := (·.1)
    addEntry := fun s e => s.push e
  }

initialize registerBuiltinAttribute {
  name := `bareiss_ext
  descr := "adds a computation model to the Bareiss elimination"
  applicationTime := .afterCompilation
  add := fun declName _ kind => do
    ensureAttrDeclIsMeta `bareiss_ext declName kind
    let env ← getEnv
    unless (env.getModuleIdxFor? declName).isNone do
      throwError "invalid attribute 'bareiss_ext', declaration is in an imported module"
    -- this ignores in-progress definitions
    if (IR.getSorryDep env declName).isSome then return
    bareissExt.add (declName, ← mkBareissExt declName) kind
    recordExtraRevUseOfCurrentModule
}

end Mathlib.Tactic.Echelon
