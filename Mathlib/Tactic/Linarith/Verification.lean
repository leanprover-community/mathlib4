/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

-- import Mathlib.Tactic.Linarith.Oracle.FourierMotzkin
import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm
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

set_option autoImplicit true

open Lean Elab Tactic Meta

namespace Qq

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
def mulExpr' (n : ℕ) {α : Q(Type $u)} (inst : Q(Semiring $α)) (e : Q($α)) : Q($α) :=
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
def addExprs' {α : Q(Type $u)} (_inst : Q(AddMonoid $α)) : List Q($α) → Q($α)
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
  | le, le => (``add_nonpos, le)
  | le, lt => (``add_lt_of_le_of_neg, lt)
  | lt, eq => (``Linarith.lt_of_lt_of_eq, lt)
  | lt, le => (``add_lt_of_neg_of_le, lt)
  | lt, lt => (``Left.add_neg, lt)

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
  let (t, _) ← getRelSides (← inferType prf)
  return t

/-- If `prf` is a proof of `t R s`, `typeOfIneqProof prf` returns the type of `t`. -/
def typeOfIneqProof (prf : Expr) : MetaM Expr := do
  inferType (← leftOfIneqProof prf)

/--
`mkNegOneLtZeroProof tp` returns a proof of `-1 < 0`,
where the numerals are natively of type `tp`.
-/
def mkNegOneLtZeroProof (tp : Expr) : MetaM Expr := do
  let zero_lt_one ← mkAppOptM ``zero_lt_one #[tp, none, none, none, none, none]
  mkAppM `neg_neg_of_pos #[zero_lt_one]

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

/--
`proveEqZeroUsing tac e` tries to use `tac` to construct a proof of `e = 0`.
-/
def proveEqZeroUsing (tac : TacticM Unit) (e : Expr) : MetaM Expr := do
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let _h : Q(Zero $α) ← synthInstanceQ q(Zero $α)
  synthesizeUsing' q($e = 0) tac

/-! #### The main method -/

/--
`proveFalseByLinarith` is the main workhorse of `linarith`.
Given a list `l` of proofs of `tᵢ Rᵢ 0`,
it tries to derive a contradiction from `l` and use this to produce a proof of `False`.

An oracle is used to search for a certificate of unsatisfiability.
In the current implementation, this is the Fourier Motzkin elimination routine in
`Elimination.lean`, but other oracles could easily be swapped in.

The returned certificate is a map `m` from hypothesis indices to natural number coefficients.
If our set of hypotheses has the form `{tᵢ Rᵢ 0}`,
then the elimination process should have guaranteed that
1.\ `∑ (m i)*tᵢ = 0`,
with at least one `i` such that `m i > 0` and `Rᵢ` is `<`.

We have also that
2.\ `∑ (m i)*tᵢ < 0`,
since for each `i`, `(m i)*tᵢ ≤ 0` and at least one is strictly negative.
So we conclude a contradiction `0 < 0`.

It remains to produce proofs of (1) and (2). (1) is verified by calling the `discharger` tactic
of the `LinarithConfig` object, which is typically `ring`. We prove (2) by folding over the
set of hypotheses.
-/
def proveFalseByLinarith (cfg : LinarithConfig) : MVarId → List Expr → MetaM Expr
  | _, [] => throwError "no args to linarith"
  | g, l@(h::_) => do
      trace[linarith.detail] "Beginning work in `proveFalseByLinarith`."
      -- for the elimination to work properly, we must add a proof of `-1 < 0` to the list,
      -- along with negated equality proofs.
      let l' ← addNegEqProofs l
      trace[linarith.detail] "... finished `addNegEqProofs`."
      let inputs := (← mkNegOneLtZeroProof (← typeOfIneqProof h))::l'.reverse
      trace[linarith.detail] "... finished `mkNegOneLtZeroProof`."
      trace[linarith.detail] (← inputs.mapM inferType)
      let (comps, max_var) ← linearFormsAndMaxVar cfg.transparency inputs
      trace[linarith.detail] "... finished `linearFormsAndMaxVar`."
      trace[linarith.detail] "{comps}"
      let oracle := cfg.oracle.getD (.simplexAlgorithm)
      -- perform the elimination and fail if no contradiction is found.
      let certificate : Batteries.HashMap Nat Nat ← try
        oracle.produceCertificate comps max_var
      catch e =>
        trace[linarith] e.toMessageData
        throwError "linarith failed to find a contradiction"
      trace[linarith] "linarith has found a contradiction: {certificate.toList}"
      let enum_inputs := inputs.enum
      -- construct a list pairing nonzero coeffs with the proof of their corresponding comparison
      let zip := enum_inputs.filterMap fun ⟨n, e⟩ => (certificate.find? n).map (e, ·)
      let mls ← zip.mapM fun ⟨e, n⟩ => do mulExpr n (← leftOfIneqProof e)
      -- `sm` is the sum of input terms, scaled to cancel out all variables.
      let sm ← addExprs mls
      -- let sm ← instantiateMVars sm
      trace[linarith] "The expression\n  {sm}\nshould be both 0 and negative"
      -- we prove that `sm = 0`, typically with `ring`.
      let sm_eq_zero ← proveEqZeroUsing cfg.discharger sm
      -- we also prove that `sm < 0`
      let sm_lt_zero ← mkLTZeroProof zip
      -- this is a contradiction.
      let pftp ← inferType sm_lt_zero
      let ⟨_, nep, _⟩ ← g.rewrite pftp sm_eq_zero
      let pf' ← mkAppM ``Eq.mp #[nep, sm_lt_zero]
      mkAppM ``Linarith.lt_irrefl #[pf']

end Linarith
