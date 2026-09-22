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
with: a carrier, its arithmetic (`RingOps`), and the encoding between entry syntax and
values. `Model.run` runs the elimination of a model, and the tactic selects a model through
the `bareiss_ext` extension registry.

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

/-- The arithmetic of `V` on its literals: `decode` reads a literal into a value and `encode`
writes a value as a literal. -/
def RingOps.lift {V : Type} (ops : RingOps V) (decode : Expr → V) (encode : V → Expr) :
    RingOps Expr where
  zero := encode ops.zero
  one := encode ops.one
  mul x y := encode (ops.mul (decode x) (decode y))
  sub x y := encode (ops.sub (decode x) (decode y))
  divExact x y := encode (ops.divExact (decode x) (decode y))
  isZero x := ops.isZero (decode x)

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

/-- The carriers an elimination runs on. -/
inductive Carrier
  /-- Integers: the values are integer numerals of the ring. -/
  | int
  /-- Expressions: the values are literals of the ring, in a form the model chooses. -/
  | expr

/-- The type of the values of a carrier. -/
abbrev Carrier.type : Carrier → Type
  | .int => Int
  | .expr => Expr

/-- A computation model of a ring: the carrier the elimination runs on, its arithmetic, the
encoding of the entries of a matrix literal into values, and the decoding of a value into an
expression of the ring. -/
structure Model where
  /-- The carrier of the elimination. -/
  carrier : Carrier
  /-- The arithmetic of the carrier. -/
  ops : RingOps carrier.type
  /-- The values the elimination runs on, together with the restoration of the resulting
  decomposition to one of the original matrix. -/
  prepare : Array (Array Expr) →
    MetaM (Array (Array carrier.type) × (BareissData carrier.type → BareissData carrier.type))
  /-- The expression of the ring denoting a value. -/
  mkEntry : carrier.type → MetaM Expr

/-- One run of the elimination: the model and its decomposition data. -/
structure Run where
  /-- The model that ran. -/
  model : Model
  /-- The decomposition data, restored to the original matrix. -/
  data : BareissData model.carrier.type

/-- Run the elimination of the model on the entries of a matrix literal. -/
def Model.run (m : Model) (entries : Array (Array Expr)) : MetaM Run := do
  let (values, restore) ← m.prepare entries
  let d ← bareissDecomp m.ops values
  return { model := m, data := restore d }

/-- The decomposition data decoded into expressions of the ring. -/
def Run.toExprData (r : Run) : MetaM (BareissData Expr) :=
  r.data.mapM r.model.mkEntry

/-- Apply a function generic in the carrier to the run's arithmetic, decoding and data. -/
def Run.elim {β : Type} (r : Run)
    (k : {V : Type} → RingOps V → (V → MetaM Expr) → BareissData V → β) : β :=
  match r with
  | ⟨⟨.int, ops, _, mkEntry⟩, d⟩ => k ops mkEntry d
  | ⟨⟨.expr, ops, _, mkEntry⟩, d⟩ => k ops mkEntry d

/-- An extension of the Bareiss ring computation model. -/
structure BareissExt where
  /-- The computation model for the ring type `R`, or `none` if the extension does not
  handle `R`. -/
  model? (R : Expr) : MetaM (Option Model)

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
