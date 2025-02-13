/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import Mathlib.Tactic.Linarith.Parsing
import Mathlib.Util.Qq

/-!
# Deriving a proof of false

`linarith` uses an untrusted oracle to produce a certificate of unsatisfiability.
It needs to do some proof reconstruction work to turn this into a proof term.
This file implements the reconstruction.

## Main declarations

The public facing declaration in this file is `proveFalseByLinarith`.
-/

open Lean Elab Tactic Meta Mathlib

namespace Qq

variable {u : Level}

/-- Typesafe conversion of `n : ℕ` to `Q($α)`. -/
def ofNatQ (α : Q(Type $u)) (_ : Q(Semiring $α)) (n : ℕ) : Q($α) :=
  match n with
  | 0 => q(0 : $α)
  | 1 => q(1 : $α)
  | k+2 =>
    have lit : Q(ℕ) := mkRawNatLit n
    have k : Q(ℕ) := mkRawNatLit k
    haveI : $lit =Q $k + 2 := ⟨⟩
    q(OfNat.ofNat $lit)

end Qq

namespace Linarith

open Ineq
open Qq

/-! ### Auxiliary functions for assembling proofs -/

/-- A typesafe version of `mulExpr`. -/
def mulExpr' {u : Level} (n : ℕ) {α : Q(Type $u)} (inst : Q(Semiring $α)) (e : Q($α)) : Q($α) :=
  if n = 1 then e else
    let n := ofNatQ α inst n
    q($n * $e)

/--
`mulExpr n e` creates an `Expr` representing `n*e`.
When elaborated, the coefficient will be a native numeral of the same type as `e`.
-/
def mulExpr (n : ℕ) (e : Expr) : MetaM Expr := do
  let ⟨_, α, e⟩ ← inferTypeQ' e
  let inst : Q(Semiring $α) ← synthInstanceQ q(Semiring $α)
  return mulExpr' n inst e

/-- A type-safe analogue of `addExprs`. -/
def addExprs' {u : Level} {α : Q(Type $u)} (_inst : Q(AddMonoid $α)) : List Q($α) → Q($α)
  | []   => q(0)
  | h::t => go h t
    where
    /-- Inner loop for `addExprs'`. -/
    go (p : Q($α)) : List Q($α) → Q($α)
    | [] => p
    | [q] => q($p + $q)
    | q::t => go q($p + $q) t

/-- `addExprs L` creates an `Expr` representing the sum of the elements of `L`, associated left. -/
def addExprs : List Expr → MetaM Expr
  | [] => return q(0) -- This may not be of the intended type; use with caution.
  | L@(h::_) => do
    let ⟨_, α, _⟩ ← inferTypeQ' h
    let inst : Q(AddMonoid $α) ← synthInstanceQ q(AddMonoid $α)
    -- This is not type safe; we just assume all the `Expr`s in the tail have the same type:
    return addExprs' inst L

/--
If our goal is to add together two inequalities `t1 R1 0` and `t2 R2 0`,
`addIneq R1 R2` produces the strength of the inequality in the sum `R`,
along with the name of a lemma to apply in order to conclude `t1 + t2 R 0`.
-/
def addIneq : Ineq → Ineq → (Name × Ineq)
  | eq, eq => (``Linarith.eq_of_eq_of_eq, eq)
  | eq, le => (``Linarith.le_of_eq_of_le, le)
  | eq, lt => (``Linarith.lt_of_eq_of_lt, lt)
  | le, eq => (``Linarith.le_of_le_of_eq, le)
  | le, le => (``Linarith.add_nonpos, le)
  | le, lt => (``Linarith.add_lt_of_le_of_neg, lt)
  | lt, eq => (``Linarith.lt_of_lt_of_eq, lt)
  | lt, le => (``Linarith.add_lt_of_neg_of_le, lt)
  | lt, lt => (``Linarith.add_neg, lt)

/--
`mkLTZeroProof coeffs pfs` takes a list of proofs of the form `tᵢ Rᵢ 0`,
paired with coefficients `cᵢ`.
It produces a proof that `∑cᵢ * tᵢ R 0`, where `R` is as strong as possible.
-/
def mkLTZeroProof : List (Expr × ℕ) → MetaM Expr
  | [] => throwError "no linear hypotheses found"
  | [(h, c)] => do
      let (_, t) ← mkSingleCompZeroOf c h
      return t
  | ((h, c)::t) => do
      let (iq, h') ← mkSingleCompZeroOf c h
      let (_, t) ← t.foldlM (fun pr ce ↦ step pr.1 pr.2 ce.1 ce.2) (iq, h')
      return t
  where
    /--
    `step c pf npf coeff` assumes that `pf` is a proof of `t1 R1 0` and `npf` is a proof
    of `t2 R2 0`. It uses `mkSingleCompZeroOf` to prove `t1 + coeff*t2 R 0`, and returns `R`
    along with this proof.
    -/
    step (c : Ineq) (pf npf : Expr) (coeff : ℕ) : MetaM (Ineq × Expr) := do
      let (iq, h') ← mkSingleCompZeroOf coeff npf
      let (nm, niq) := addIneq c iq
      return (niq, ← mkAppM nm #[pf, h'])

/-- If `prf` is a proof of `t R s`, `leftOfIneqProof prf` returns `t`. -/
def leftOfIneqProof (prf : Expr) : MetaM Expr := do
  let (_, _, t, _) ← (← inferType prf).ineq?
  return t

/-- If `prf` is a proof of `t R s`, `typeOfIneqProof prf` returns the type of `t`. -/
def typeOfIneqProof (prf : Expr) : MetaM Expr := do
  let (_, ty, _) ← (← inferType prf).ineq?
  return ty

/--
`mkNegOneLtZeroProof tp` returns a proof of `-1 < 0`,
where the numerals are natively of type `tp`.
-/
def mkNegOneLtZeroProof (tp : Expr) : MetaM Expr := do
  -- TODO: pass in `v` rather than partially reproducing the contents of `inferType'`.
  let .sort u ← whnf (← inferType tp) | throwError "not a type{indentExpr tp}"
  let some v := (← instantiateLevelMVars u).dec | throwError "not a Type{indentExpr tp}"
  have α : Q(Type v) := tp
  letI := ← synthInstanceQ q(StrictOrderedRing $α)
  return q(neg_neg_of_pos <| Linarith.zero_lt_one (α := $α))

/--
`addNegEqProofs l` inspects the list of proofs `l` for proofs of the form `t = 0`. For each such
proof, it adds a proof of `-t = 0` to the list.
-/
def addNegEqProofs : List Expr → MetaM (List Expr)
  | [] => return []
  | (h::tl) => do
    let (iq, t) ← parseCompAndExpr (← inferType h)
    match iq with
    | Ineq.eq => do
      let nep := mkAppN (← mkAppM `Iff.mpr #[← mkAppOptM ``neg_eq_zero #[none, none, t]]) #[h]
      let tl ← addNegEqProofs tl
      return h::nep::tl
    | _ => return h :: (← addNegEqProofs tl)

/-! #### The main method -/

/--
`proveFalseByLinarith` is the main workhorse of `linarith`.
Given a list `l` of proofs of `tᵢ Rᵢ 0`,
it tries to derive a contradiction from `l` and use this to produce a proof of `False`.

`oracle : CertificateOracle` is used to search for a certificate of unsatisfiability.

The returned certificate is a map `m` from hypothesis indices to natural number coefficients.
If our set of hypotheses has the form `{tᵢ Rᵢ 0}`,
then the elimination process should have guaranteed that
1.\ `∑ (m i)*tᵢ = 0`,
with at least one `i` such that `m i > 0` and `Rᵢ` is `<`.

We have also that
2.\ `∑ (m i)*tᵢ < 0`,
since for each `i`, `(m i)*tᵢ ≤ 0` and at least one is strictly negative.
So we conclude a contradiction `0 < 0`.

It remains to produce proofs of (1) and (2). (1) is verified by calling the provided `discharger`
tactic, which is typically `ring`. We prove (2) by folding over the set of hypotheses.

`transparency : TransparencyMode` controls the transparency level with which atoms are identified.
-/
def proveFalseByLinarith (transparency : TransparencyMode) (oracle : CertificateOracle)
    (discharger : TacticM Unit) : MVarId → List Expr → MetaM Q(False)
  | _, [] => throwError "no args to linarith"
  | g, l@(h::_) => do
      Lean.Core.checkSystem decl_name%.toString
      -- for the elimination to work properly, we must add a proof of `-1 < 0` to the list,
      -- along with negated equality proofs.
      let l' ← detailTrace "addNegEqProofs" <| addNegEqProofs l
      let inputs ← detailTrace "mkNegOneLtZeroProof" <|
        return (← mkNegOneLtZeroProof (← typeOfIneqProof h))::l'.reverse
      trace[linarith.detail] "inputs:{indentD <| toMessageData (← inputs.mapM inferType)}"
      let (comps, max_var) ← detailTrace "linearFormsAndMaxVar" <|
        linearFormsAndMaxVar transparency inputs
      trace[linarith.detail] "comps:{indentD <| toMessageData comps}"
      -- perform the elimination and fail if no contradiction is found.
      let certificate : Std.HashMap Nat Nat ←
        withTraceNode `linarith (return m!"{exceptEmoji ·} Invoking oracle") do
          let certificate ←
            try
              oracle.produceCertificate comps max_var
            catch e =>
              trace[linarith] e.toMessageData
              throwError "linarith failed to find a contradiction"
          trace[linarith] "found a contradiction: {certificate.toList}"
          return certificate
      let (sm, zip) ←
        withTraceNode `linarith (return m!"{exceptEmoji ·} Building final expression") do
          let enum_inputs := inputs.zipIdx
          -- construct a list pairing nonzero coeffs with the proof of their corresponding
          -- comparison
          let zip := enum_inputs.filterMap fun ⟨e, n⟩ => (certificate[n]?).map (e, ·)
          let mls ← zip.mapM fun ⟨e, n⟩ => do mulExpr n (← leftOfIneqProof e)
          -- `sm` is the sum of input terms, scaled to cancel out all variables.
          let sm ← addExprs mls
          -- let sm ← instantiateMVars sm
          trace[linarith] "{indentD sm}\nshould be both 0 and negative"
          return (sm, zip)
      let ⟨u, α, smq⟩ ← inferTypeQ' sm
      have : Q(StrictOrderedCommRing $α) := ← synthInstanceQ q(StrictOrderedCommRing $α)
      let sm_eq_zero : Q($smq = 0) := ← detailTrace "proveEqZeroUsing" <|
        synthesizeUsing' q($smq = 0) discharger
      let sm_lt_zero: Q($smq < 0) := ← detailTrace "mkLTZeroProof" <| mkLTZeroProof zip
      -- this is a contradiction.
      return q(($sm_eq_zero).not_lt $sm_lt_zero)
where
  /-- Log `f` under `linarith.detail`, with exception emojis and the provided name. -/
  detailTrace {α} (s : String) (f : MetaM α) : MetaM α :=
    withTraceNode `linarith.detail (return m!"{exceptEmoji ·} {s}") f

end Linarith
