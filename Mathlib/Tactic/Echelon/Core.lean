/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Init

/-!
# Parameterized computation core for the Bareiss elimination

`bareissDecomp` computes the transform `L`, the echelon form `U`, the row swaps and the pivot
columns of an echelon decomposition by fraction-free elimination on a carrier of values.

As an optimisation, rows are scaled to clear their denominators (when applicable) before the
elimination with the scales folded back into `L` afterwards.

A computation model supplies the carrier, its arithmetic operations (`RingOps`) and the
encoding between entry syntax and values, and the tactic selects a model through the `bareiss_ext`
extension registry.

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

/-- Arithmetic of a model's carrier. -/
structure RingOps (V : Type) where
  /-- The zero value. -/
  zero : V
  /-- The one value. -/
  one : V
  /-- Multiplication. -/
  mul : V → V → V
  /-- Subtraction. -/
  sub : V → V → V
  /-- Exact division. -/
  divExact : V → V → V
  /-- The pivot zero test. -/
  isZero : V → Bool

/-- The arithmetic of `V` on its literals. `decode` reads a literal into a value and `encode`
writes a value as a literal. A literal `decode` rejects is read as 0. The literals
reaching them are the ones `encode` wrote. -/
def RingOps.lift {V : Type} (ops : RingOps V) (decode : Expr → Option V) (encode : V → Expr) :
    RingOps Expr :=
  let read (e : Expr) : V := (decode e).getD ops.zero
  { zero := encode ops.zero
    one := encode ops.one
    mul x y := encode (ops.mul (read x) (read y))
    sub x y := encode (ops.sub (read x) (read y))
    divExact x y := encode (ops.divExact (read x) (read y))
    isZero x := ops.isZero (read x) }

/-- Decomposition data with entries in `V`, the carrier of the elimination or `Expr` once the
entries are encoded. -/
structure BareissData (V : Type) where
  /-- The lower-triangular transform. -/
  L : Array (Array V)
  /-- The echelon form, the final working matrix `L * A_σ` of the elimination. -/
  U : Array (Array V)
  /-- The row swaps, in order. Swaps are infrequent in common cases, so their product is a
  smaller term for the kernel than a row permutation. -/
  swaps : Array (Nat × Nat)
  /-- The pivot columns. The `k`-th entry is the column of the pivot in row `k` of the
  final echelon form. -/
  pivot : Array Nat

/-- Map over the entries of the transform. -/
def BareissData.mapM {V W : Type} (f : V → MetaM W) (d : BareissData V) :
    MetaM (BareissData W) :=
  return { L := ← d.L.mapM fun row => row.mapM f
           U := ← d.U.mapM fun row => row.mapM f
           swaps := d.swaps
           pivot := d.pivot }

/-- The row arrangement `σ` of the swaps. The entry at position `i` is the original index of
the row the swaps move to position `i`. -/
def BareissData.rowOrder {V : Type} (d : BareissData V) : Array Nat :=
  d.swaps.foldl (fun ord (a, b) => ord.swapIfInBounds a b) (Array.range d.L.size)

/-- An entry certifier proves a proposition about a single entry, throwing on a proposition
it cannot prove. -/
@[expose] def EntryCertifier := Expr → MetaM Expr

/-- Core algorithm of fraction-free Gaussian elimination. -/
def bareissDecomp {V : Type} (ops : RingOps V) (A : Array (Array V)) :
    MetaM (BareissData V) := do
  let rows := A.size
  let cols := (A.getD 0 #[]).size
  let getEntry (M : Array (Array V)) (i j : Nat) : V := (M.getD i #[]).getD j ops.zero
  let eliminate (pivot coef prev : V) (row pivotRow : Array V) : Array V :=
    row.zipWith (bs := pivotRow) fun a b =>
      ops.divExact (ops.sub (ops.mul pivot a) (ops.mul coef b)) prev
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

/-- The carriers a model computes on, the integers or expressions of the ring.
The most direct method is for a model to name this as a parameter in `Type`, but that
puts the model in a higher universe level, and the registry can only store `Type 0` elements. -/
inductive Carrier
  | int
  | expr

/-- The type of the values of a carrier. -/
abbrev Carrier.type : Carrier → Type
  | .int => Int
  | .expr => Expr

/-- A computation model of a ring on the carrier `V`. -/
structure Model (V : Type) where
  /-- The arithmetic of the carrier. -/
  ops : RingOps V
  /-- An entry as a value with an optional denominator (used for the scaling optimisation).
  `(n, some d)` denotes `n / d` for a nonzero `d`, and `(n, none)` denotes `n`. -/
  evalEntry : Expr → MetaM (V × Option V)
  /-- A common multiple for eliminating the denominators (`ops.mul` by default). A
  carrier type with a cheap lcm function could supply it as an optimisation to keep the
  scaled entries small. -/
  commonMultiple : V → V → V := ops.mul
  /-- The expression of the ring denoting a value. -/
  mkEntry : V → MetaM Expr
  /-- The entry certifier, or `none` to close the entry propositions by `decide`. -/
  entryCertifier? : Option EntryCertifier := none

/-- Clear the denominators of the rows before the decomposition algorithm. -/
def scaleRows {V : Type} (ops : RingOps V) (commonMultiple : V → V → V)
    (rows : Array (Array (V × Option V))) : Array (Array V) × Array (Option V) :=
  let scales := rows.map fun row =>
    row.foldl (init := none) fun scale? entry => Option.merge commonMultiple scale? entry.2
  let scaled := rows.zipWith (bs := scales) fun row scale? =>
    match scale? with
    | none => row.map Prod.fst
    | some scale => row.map fun entry =>
      match entry.2 with
      | none => ops.mul entry.1 scale
      | some den => ops.mul entry.1 (ops.divExact scale den)
  (scaled, scales)

/-- Fold the row scales into the transform after the decomposition algorithm. Column `j` of
`L` is multiplied by the scale of the row that ends up in position `j` after permutation. -/
def restoreScaling {V : Type} (ops : RingOps V) (scales : Array (Option V))
    (d : BareissData V) : BareissData V :=
  if scales.all Option.isNone then d
  else
    let colScale := d.rowOrder.map fun i => scales.getD i none
    { d with L := d.L.map fun row => row.zipWith (bs := colScale) fun a scale? =>
        match scale? with
        | none => a
        | some scale => ops.mul a scale }

/-- An extension of the Bareiss ring computation model. -/
structure BareissExt where
  /-- The model for the element type `R` and its carrier, or `none` if the extension does not
  handle `R`. -/
  model? (R : Expr) : MetaM (Option ((c : Carrier) × Model c.type))

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
