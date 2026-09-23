/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Init

/-!
# Parameterized computation core for the Bareiss elimination

A computable model of a ring packages the representation the untrusted elimination computes
with: a carrier, its arithmetic (`RingOps`), and the encoding between entry syntax and
values. The tactic selects a model through the `bareiss_ext` extension registry.

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

/-- The carriers a model computes on, the integers or expressions of the ring.
The most direct way is for a model to name this as a parameter in `Type`, but that
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
  /-- A common multiple for eliminating the denominators. The default (mul) is always available. A
  carrier type with a cheap lcm function could supply it as an optimisation to keep the
  scaled entries small. -/
  commonMultiple : V → V → V := ops.mul
  /-- The expression of the ring denoting a value. -/
  mkEntry : V → MetaM Expr

/-- Decode decomposition data into expressions of the ring. -/
def Model.toExprData {V : Type} (m : Model V) (d : BareissData V) : MetaM (BareissData Expr) :=
  d.mapM m.mkEntry

/-- Clear the denominators of the rows before the decomposition algorithm. -/
def scaleRows {V : Type} (ops : RingOps V) (commonMultiple : V → V → V)
    (rows : Array (Array (V × Option V))) : Array (Array V) × Array (Option V) :=
  let scale (row : Array (V × Option V)) : Option V :=
    row.foldl (init := none) fun s nd =>
      match s, nd.2 with
      | none, d => d
      | some s, none => some s
      | some s, some d => some (commonMultiple s d)
  let scales := rows.map scale
  let scaled := rows.zipWith (bs := scales) fun row s =>
    match s with
    | none => row.map fun nd => nd.1
    | some s => row.map fun nd =>
      match nd.2 with
      | none => ops.mul nd.1 s
      | some d => ops.mul nd.1 (ops.divExact s d)
  (scaled, scales)

/-- Fold the row scales into the transform after the decomposition algorithm. Column `j` of
`L` is multiplied by the scale of the row that ends up in position `j` after permutation. -/
def restoreScaling {V : Type} (ops : RingOps V) (scales : Array (Option V))
    (d : BareissData V) : BareissData V :=
  if scales.all fun s => s.isNone then d
  else
    let colScale := d.rowOrder.map fun i => scales.getD i none
    { d with L := d.L.map fun row => row.mapIdx fun j a =>
        match colScale.getD j none with
        | none => a
        | some s => ops.mul a s }

/-- An extension of the Bareiss ring computation model. -/
structure BareissExt where
  /-- The model for the ring type `R`, with its carrier, or `none` if the extension does not
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
