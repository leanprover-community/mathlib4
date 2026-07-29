/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Bareiss.Defs

public meta import Mathlib.Util.Qq

meta import Mathlib.LinearAlgebra.Matrix.Notation

import Mathlib.Tactic.NormNum.Basic

/-!
# Computation engine for the Bareiss decomposition tactic

Given a matrix literal `M` over a commutative domain, the entry point
`mkBareissDecomposition` elaborates a certificate `⟨L, σ, pivot, …⟩ :
Bareiss.Decomposition M`, with the four certificate conditions checked by the kernel via
`decide`.

The production is data-only: no proofs are constructed, and the ring is consulted only to
decide whether a value vanishes (`isZeroInR`).

## Main definitions

- `mkBareissDecomposition`: produce and elaborate the decomposition of a matrix literal.
- `bareissDecomp`: fraction-free Gaussian elimination on integer values.
- `BareissData`: the raw decomposition data.
-/

public meta section

open Lean Meta Elab Qq

namespace Mathlib.Tactic.Echelon

/-- Build the matrix literal `!![…]` with the given rows of entries. -/
def mkMatrixLit {u : Level} (R : Q(Type u)) (rows : Array (Array Expr)) : Expr :=
  Matrix.mkLiteralQ (α := R) (m := rows.size) (n := (rows.getD 0 #[]).size)
    (.of fun i j => show Q($R) from (rows[i.1]!)[j.1]!)

/- TODO: once `!![…]` elaborates to `Matrix.ofArray`, the following parsers need a
corresponding adaptation. -/
/-- Parse a `![a, b, …]` vector literal into its entries. -/
partial def parseVec? (e : Expr) : Option (Array Expr) :=
  go #[] e
where
  go (acc : Array Expr) (e : Expr) : Option (Array Expr) :=
    match_expr e.cleanupAnnotations with
    | Matrix.vecEmpty _ => some acc
    | Matrix.vecCons _ _ head tail => go (acc.push head) tail
    | _ => none

/-- Parse a `!![…]` matrix literal into its rows of entry expressions. -/
def parseMatrix? (M : Expr) : Option (Array (Array Expr)) :=
  match_expr M.cleanupAnnotations with
  | DFunLike.coe _ _ _ _ f v =>
    match_expr f.cleanupAnnotations with
    | Matrix.of _ _ _ => (parseVec? v).bind (·.mapM parseVec?)
    | _ => none
  | _ => none

/-- Match a closed `Fin`-indexed matrix literal: its dimensions, element type, and rows of
entries. Commits into computation if this succeeds. -/
def matchMatrixLit? (M : Expr) : MetaM (Option (Nat × Nat × Expr × Array (Array Expr))) := do
  let some entries := parseMatrix? M | return none
  let_expr Matrix finM finN R := ← inferType M | return none
  let_expr Fin mE := finM.cleanupAnnotations | return none
  let_expr Fin nE := finN.cleanupAnnotations | return none
  -- the counts appear as `OfNat` numerals or as raw literals; `Expr.nat?` matches only the
  -- former
  let some m := mE.nat?.orElse fun _ => mE.rawNatLit? | return none
  let some n := nE.nat?.orElse fun _ => nE.rawNatLit? | return none
  unless entries.size == m && entries.all (·.size == n) do return none
  return some (m, n, R, entries)

/-- Build the pivot literal `![↑c₀, …, ⊤, …] : Fin m → WithTop (Fin n)`, sending the
first rows to their pivot columns and the remaining rows to `⊤`. -/
def mkPivotLit (m n : Nat) (pivots : Array Nat) : MetaM Expr := do
  let entries : Array Q(WithTop (Fin $n)) ← (Array.range m).mapM fun i => do
    if hi : i < pivots.size then
      let c ← mkNumeral q(Fin $n) pivots[i]
      have c : Q(Fin $n) := c
      return q(WithTop.some $c)
    else
      return q((⊤ : WithTop (Fin $n)))
  return PiFin.mkLiteralQ (α := q(WithTop (Fin $n))) (n := m) fun i => entries[i.1]!

/-- Build the permutation `σ = swap a₀ b₀ * swap a₁ b₁ * ⋯` from the recorded swaps. -/
def mkPerm (m : Nat) (swaps : Array (Nat × Nat)) : MetaM Expr := do
  have mE : Q(ℕ) := mkNatLit m
  let mut acc : Q(Equiv.Perm (Fin $mE)) := q(Equiv.refl (Fin $mE))
  for (a, b) in swaps do
    let aE ← mkNumeral q(Fin $mE) a
    let bE ← mkNumeral q(Fin $mE) b
    have aE : Q(Fin $mE) := aE
    have bE : Q(Fin $mE) := bE
    acc := q($acc * Equiv.swap $aE $bE)
  return acc

/-- Build the numeral of an integer in `R`: `mkNumeral` on the absolute value, negated if
`i` is negative. -/
def mkIntNumeral {u : Level} (R : Q(Type u)) (i : Int) : MetaM Q($R) := do
  let n ← mkNumeral R i.natAbs
  have n : Q($R) := n
  if i < 0 then
    let _instNeg ← synthInstanceQ q(Neg $R)
    return q(-$n)
  else
    return n

/-- Read the rational value of a numeral. `a / b` is read as a fraction only when division
in the ring is field division. -/
def rat? (isDivRing : Bool) (e : Expr) : Option Rat :=
  let (sign, e) : Int × Expr :=
    match_expr e.cleanupAnnotations with
    | Neg.neg _ _ a => (-1, a)
    | _ => (1, e)
  match_expr e.cleanupAnnotations with
  | HDiv.hDiv _ _ _ _ a b =>
    if isDivRing then
      match a.cleanupAnnotations.int?, b.cleanupAnnotations.nat? with
      | some n, some d => some (mkRat (sign * n) d)
      | _, _ => none
    else
      none
  | _ => e.cleanupAnnotations.int?.map fun n => mkRat (sign * n) 1

/-- Read a matrix entry's rational value: off its numeral syntax when possible, else off the
`norm_num` normal form of the entry. The evaluation is data-only — the certificate is stated
about the original entries, so no proof is kept. -/
def entryRat (isDivRing : Bool) (e : Expr) : MetaM Rat := do
  -- shortcut if the entry is already a value literal
  match rat? isDivRing e with
  | some v => return v
  | none =>
    -- fallback: try to evaluate the expression
    let ctx ← Simp.mkContext (congrTheorems := ← getSimpCongrTheorems)
    let r ← Meta.NormNum.deriveSimp ctx (useSimp := false) e
    let some v := rat? isDivRing r.expr
      | throwError "the entry does not evaluate to a numeral{indentExpr e}"
    return v

/-- Whether the integer value `v` is zero in `R`, by reducing the `Decidable` instance of
`(v : R) = 0` in the kernel. The engine also checks the final certificate. -/
def isZeroInR {u : Level} (R : Q(Type u)) (v : Int) : MetaM Bool := do
  -- shortcircuit
  if v == 0 then return true
  let _instCast ← synthInstanceQ q(IntCast $R)
  let _instZero ← synthInstanceQ q(Zero $R)
  have vE : Q(Int) := toExpr v
  let eq : Q(Prop) := q((Int.cast $vE : $R) = 0)
  let some inst ← synthInstance? q(Decidable $eq)
    | throwError "equality with zero in the element type is not decidable{indentExpr R}"
  if let .ok r := Kernel.whnf (← getEnv) (← getLCtx) inst then
    if r.isAppOf ``Decidable.isTrue then return true
    if r.isAppOf ``Decidable.isFalse then return false
  throwError "equality in the element type does not reduce in the kernel{indentExpr R}"

/-- Raw data of a Bareiss decomposition on integer valuess. -/
structure BareissData where
  /-- The lower-triangular transform. -/
  L : Array (Array Int)
  /-- The row transpositions in the order performed: the pair `(r, p)` exchanges the rows
  at positions `r < p` of the current arrangement when the pivot of step `r` is found at
  position `p`. The row permutation `σ` is later constructed by their product. -/
  swaps : Array (Nat × Nat)
  /-- The pivot columns. The `k`-th entry is the column of the pivot
  in row `k` of the final echelon form. -/
  pivot : Array Nat

/-- `get A i j` is the `(i, j)`-th entry of the matrix `A`, or `0` when out of bounds. -/
protected def get {α : Type*} [Zero α] (A : Array (Array α)) (i j : Nat) : α :=
  (A.getD i #[]).getD j 0

/- Pivot swap mechanism
Let `M_σ := M.submatrix σ id` be the original matrix with its rows in the arrangement `σ`
accumulated so far.

When the pivot search swaps the rows at positions `r < p`, the invariant `L * M_σ = W` must be
restored against the new `M_σ' = S * M_σ`, where `S` is the permutation matrix of the
transposition `σ`:

  `S * W = S * L * (S⁻¹ * S) * M_σ = (S * L * S⁻¹) * M_σ'`

so `L` needs to be conjugated by the matrix corresponding to `σ = (r, p)`.

This is similar to LU factorisation with partial pivoting. -/

/-- Core algorithm of Fraction-free Gaussian elimination.

A separate `isZero` function handles testing for zero in the original ring `R`.

A single sweep accumulates the transform `L` alongside the working matrix `W`. The main
invariant is `L * (M.submatrix σ id) = W` for the row arrangement `σ` so far: eliminations
update both simultaneously, and a row interchange conjugates `L` by the swap.
The divisions are exact by Sylvester's identity. -/
def bareissDecomp (isZero : Int → MetaM Bool) (M : Array (Array Int)) :
    MetaM BareissData := do
  let m := M.size
  let n := (M.getD 0 #[]).size
  -- the main row elimination function
  let eliminate : Int → Int → Int → Array Int → Array Int → Array Int :=
    fun piv f prev rowI rowR =>
      rowI.mapIdx fun j a => (piv * a - f * rowR.getD j 0) / prev
  let mut W := M
  let mut L : Array (Array Int) :=
    (Array.range m).map fun i => (Array.range m).map fun j => if i == j then 1 else 0
  let mut swaps : Array (Nat × Nat) := #[]
  let mut pivots : Array Nat := #[]
  let mut r : Nat := 0
  let mut prev : Int := 1
  for c in [0:n] do
    if r == m then break
    let mut p : Nat := m
    for q in [r:m] do
      if !(← isZero (Echelon.get W q c)) then
        p := q
        break
    if p < m then
      if p ≠ r then
        W := W.swapIfInBounds r p
        -- the interchange conjugates the transform, `L ← S * L * S⁻¹`.
        -- row swap
        L := L.swapIfInBounds r p
        -- column swap. This affects only rows `r` and `p`, since every other
        -- row vanishes at both columns
        L := (L.modify r (·.swapIfInBounds r p)).modify p (·.swapIfInBounds r p)
        swaps := swaps.push (r, p)
      pivots := pivots.push c
      let piv := Echelon.get W r c
      let rowR := W.getD r #[]
      let lRow := L.getD r #[]
      for i in [r+1:m] do
        let f := Echelon.get W i c
        W := W.set! i (eliminate piv f prev (W.getD i #[]) rowR)
        L := L.set! i (eliminate piv f prev (L.getD i #[]) lRow)
      prev := piv
      r := r + 1
  return { L, swaps, pivot := pivots }

/-- Produce and elaborate a `Bareiss.Decomposition` of the matrix literal `M`, given its
matched dimensions, element type, and entries (from `matchMatrixLit?`): parse the entries'
values, scale fractional rows integral, eliminate, fold the scaling back into `L`, and
elaborate the certificate with the kernel checking its four conditions. Failures here are
refusals of a committed attempt, and throw. -/
def mkBareissDecomposition (M : Expr) (m n : Nat) (R : Expr)
    (entries : Array (Array Expr)) : TermElabM Expr := do
  let u ← getDecLevel R
  have R : Q(Type u) := R
  let isDivRing := (← synthInstance? q(DivisionRing $R)).isSome
  let ratRows ← entries.mapM fun row => row.mapM fun e => entryRat isDivRing e
  -- scale each row integral by its denominator lcm; the scaling is folded into `L` below
  let scales : Array Nat := ratRows.map fun row => row.foldl (fun l v => Nat.lcm l v.den) 1
  let values : Array (Array Int) :=
    (ratRows.zip scales).map fun (row, s) => row.map fun v => (mkRat s 1 * v).num
  -- verification runs in the kernel: probe one zero test so that element types without
  -- kernel-decidable equality refuse early with a clean error (drop the probe once a
  -- non-kernel verification route exists)
  try
    discard <| isZeroInR R 1
  catch e =>
    throwError "cannot verify the rank certificate: {e.toMessageData}"
  -- in a `CharZero` ring the integer values decide their own zero tests, so expensive
  -- kernel tests for zero can be avoided.
  -- `CharZero` has an `[AddMonoidWithOne R]` prerequisite that only runtime synthesis
  -- against the concrete `R` can provide, so this probe stays `mkAppM`-based.
  let charZero := (← synthInstance? (← mkAppM ``CharZero #[R])).isSome
  let d ← bareissDecomp (if charZero then fun v => pure (v == 0) else isZeroInR R) values
  -- `L * (D·M).submatrix σ id = E` gives `(L·D_σ) * (M.submatrix σ id) = E`: scale column
  -- `j` of `L` by the factor of the row that ends up in position `j`
  let order := d.swaps.foldl (fun ord (a, b) => ord.swapIfInBounds a b) (Array.range m)
  let scaledL := d.L.map fun row =>
    row.mapIdx fun j a => a * (scales.getD (order.getD j 0) 1 : Int)
  -- constructing the main Bareiss certificate from internal raw data
  let L := mkMatrixLit R (← scaledL.mapM fun row => row.mapM fun v => mkIntNumeral R v)
  let σ ← mkPerm m d.swaps
  let pivotE ← mkPivotLit m n d.pivot
  let rankE := mkNatLit d.pivot.size
  let stx ← `((⟨$(← Term.exprToSyntax L), $(← Term.exprToSyntax σ),
                $(← Term.exprToSyntax pivotE), $(← Term.exprToSyntax rankE),
                -- switch to an efficient decision of matrix mult once implemented
                by decide +kernel, by decide +kernel, by decide +kernel,
                by decide +kernel⟩ :
              Bareiss.Decomposition $(← Term.exprToSyntax M)))
  let e ← Term.elabTermEnsuringType stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

end Mathlib.Tactic.Echelon

end
