/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public meta import Mathlib.Tactic.SOS.Reify
public meta import SOS.Engine
public meta import SOS.Quote
public import Mathlib.Tactic.SOS.Verifier
public meta import Mathlib.Tactic.SOS.Lift
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.Config
public meta import Lean.Meta.Tactic.TryThis
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# The `sos` tactic

Elaboration for `sos`, `sos?`, and `sos_witness`.
-/

public meta section

namespace SOS

open Lean Elab Tactic Meta

/-- Elaborator for `(config := …)` clauses on `sos`/`sos?`. -/
declare_config_elab elabConfig Config

/-! ### Common Expr fragments -/

/-- `Lean.Expr` for `ℝ`, used throughout the elaborator. -/
private def realTy : Expr := Lean.mkConst ``Real

/-- `Lean.Expr` for `ℚ`, used throughout the elaborator. -/
private def ratTy : Expr := Lean.mkConst ``Rat

/-- `Lean.Expr` for `CMvPolynomial n ℚ`. -/
private def cmvType (n : Nat) : MetaM Expr :=
  Meta.mkAppOptM ``CPoly.CMvPolynomial
    #[some (Lean.mkNatLit n), some ratTy, none]

/-! ### Bridge equality: `evalReal x p = origExpr` -/

/-- Run a Lean tactic on a fresh metavariable of the given type and
return the resulting proof, throwing if the tactic leaves open goals. -/
private def proveByTactic (type : Expr) (tac : Syntax) : TacticM Expr := do
  let mv ← mkFreshExprSyntheticOpaqueMVar type
  let goalsBefore ← Tactic.getGoals
  Tactic.setGoals [mv.mvarId!]
  try
    Tactic.evalTactic tac
    let remaining ← Tactic.getGoals
    unless remaining.isEmpty do
      throwError "SOS.proveByTactic: tactic left open goals"
  finally
    Tactic.setGoals goalsBefore
  instantiateMVars mv

/-- Build `SOS.Poly.evalReal x p` as an `Expr`. -/
private def evalRealExpr (n : Nat) (xE : Expr) (p : SOS.Poly n) : MetaM Expr := do
  let pE := Lean.toExpr p
  mkAppOptM ``SOS.Poly.evalReal #[some (Lean.mkNatLit n), some xE, some pE]

/-- Build `(p : SOS.Poly n).toCMv` as an `Expr`. -/
private def toCMvExpr (n : Nat) (p : SOS.Poly n) : MetaM Expr := do
  let pE := Lean.toExpr p
  mkAppOptM ``SOS.Poly.toCMv #[some (Lean.mkNatLit n), some pE]

/-- Build `CMvPolynomial.aeval x p.toCMv` as an `Expr`. -/
private def aevalExpr (n : Nat) (xE : Expr) (p : SOS.Poly n) : MetaM Expr := do
  let pCMv ← toCMvExpr n p
  mkAppOptM ``CPoly.CMvPolynomial.aeval #[some (Lean.mkNatLit n),
    some xE, some pCMv]

/-! ### Atomic-bridge helpers

These build the `Fin n → ℝ` valuation expression `![atom₀, …,
atomₙ₋₁]` from an atom array, and prove the bridge equation
`pTyped.evalReal φ = origExpr` where `pTyped := raw.cast n h` and `φ
:= ![…]`. The bridge proof reduces `φ ⟨k, _⟩` to `atom_k` via
`Matrix.cons_val_*` simp lemmas. -/

/-- Build `Expr` of type `Fin n → ℝ`, where `n = atoms.size`,
defined by the vector literal `![atoms[0], …, atoms[n-1]]`
(right-associated `Matrix.vecCons` chain ending in
`Matrix.vecEmpty`). -/
private def buildFinValExpr (atoms : Array Expr) : MetaM Expr := do
  let n := atoms.size
  -- Tail: `Matrix.vecEmpty : Fin 0 → ℝ`.
  let mut acc : Expr ←
    mkAppOptM ``Matrix.vecEmpty #[some realTy]
  -- Right-to-left: the leftmost atom is the outermost cons. After
  -- pushing `k` atoms, `acc : Fin k → ℝ`. The next push prepends
  -- `atoms[n-1-k]`.
  for k in [:n] do
    let i := n - 1 - k
    let m := Lean.mkNatLit k  -- current length of `acc`
    acc ← mkAppOptM ``Matrix.vecCons
      #[some realTy, some m, some atoms[i]!, some acc]
  return acc

/-- Meta-compute the typed `SOS.Poly n` from a `SOS.Poly.Raw` whose
`maxAtomBound ≤ n`. The boundedness is decided at meta-time. Returns
`none` if the bound check fails. -/
private def castRawToPoly (raw : SOS.Poly.Raw) (n : Nat) :
    Option (SOS.Poly n) :=
  if h : raw.maxAtomBound ≤ n then some (raw.cast n h) else none

/-- Prove `SOS.Poly.evalReal φ p = origExpr` where `φ` is the
`![atoms[0], …]` vector. The proof uses `SOS.Poly.evalReal` plus
`Matrix.cons_val_*` to reduce `φ ⟨k, _⟩` for each literal `k`. -/
private def buildAtomicBridgeEq (n : Nat) (φE : Expr) (p : SOS.Poly n)
    (origExpr : Expr) : TacticM Expr := do
  let lhs ← evalRealExpr n φE p
  let eqType ← mkEq lhs origExpr
  let tac ← `(tactic|
    (simp only [SOS.Poly.evalReal, Matrix.cons_val_zero,
       Matrix.cons_val_succ, Matrix.cons_val_zero',
       Matrix.cons_val_succ', Fin.isValue]
     all_goals (push_cast; ring)))
  proveByTactic eqType tac

/-! ### Closed-positivity proof builder -/

/-- Build the `List (CMvPolynomial n ℚ)` expression
`[g₁.toCMv, …, gₘ.toCMv]`. -/
private def gsCMvListExpr (n : Nat) (gs : List (SOS.Poly n)) : MetaM Expr := do
  let cmvTy ← cmvType n
  let mut acc ← mkAppOptM ``List.nil #[some cmvTy]
  for g in gs.reverse do
    let gCMv ← toCMvExpr n g
    acc ← mkAppOptM ``List.cons #[some cmvTy, some gCMv, some acc]
  return acc

/-- Build a proof of `∀ g ∈ gsList, P g` from per-element proofs `hP i :
P gs[i].toCMv`, given the predicate `P` as a one-argument lambda. -/
private def buildForallMemProofGen (n : Nat) (gs : List (SOS.Poly n))
    (hAevalProofs : List Expr) (predicate : Expr) : MetaM Expr := do
  let cmvTy ← cmvType n
  let mut accList ← mkAppOptM ``List.nil #[some cmvTy]
  let mut accProof ← mkAppOptM ``List.forall_mem_nil #[some cmvTy, some predicate]
  for (g, hP) in (gs.zip hAevalProofs).reverse do
    let gCMv ← toCMvExpr n g
    let newList ← mkAppOptM ``List.cons #[some cmvTy, some gCMv, some accList]
    let pair ← mkAppM ``And.intro #[hP, accProof]
    let iff ← mkAppOptM ``List.forall_mem_cons
      #[some cmvTy, some predicate, some gCMv, some accList]
    accProof ← mkAppM ``Iff.mpr #[iff, pair]
    accList := newList
  return accProof

/-- Build a proof of `∀ g ∈ gsList, 0 ≤ CMvPolynomial.aeval x g`, given
per-hypothesis proofs `hAevalProofs i : 0 ≤ aeval x gs[i].toCMv`. -/
private def buildForallMemProof (n : Nat) (xE : Expr) (gs : List (SOS.Poly n))
    (hAevalProofs : List Expr) : MetaM Expr := do
  let cmvTy ← cmvType n
  let predicate ← withLocalDeclD `g cmvTy fun gFV => do
    let body ← mkAppM ``LE.le
      #[(← mkAppOptM ``OfNat.ofNat
          #[some realTy, some (Lean.mkNatLit 0), none]),
        (← mkAppOptM ``CPoly.CMvPolynomial.aeval
          #[some (Lean.mkNatLit n), some xE, some gFV])]
    mkLambdaFVars #[gFV] body
  buildForallMemProofGen n gs hAevalProofs predicate

/-- Build a proof of `∀ g ∈ gsList, 0 < CMvPolynomial.aeval x g`, given
per-hypothesis proofs `hP i : 0 < aeval x gs[i].toCMv`. Strict-positivity
companion to `buildForallMemProof`, consumed by the strict-product
Positivstellensatz close path. -/
private def buildForallMemStrictProof (n : Nat) (xE : Expr) (gs : List (SOS.Poly n))
    (hAevalProofs : List Expr) : MetaM Expr := do
  let cmvTy ← cmvType n
  let predicate ← withLocalDeclD `g cmvTy fun gFV => do
    let body ← mkAppM ``LT.lt
      #[(← mkAppOptM ``OfNat.ofNat
          #[some realTy, some (Lean.mkNatLit 0), none]),
        (← mkAppOptM ``CPoly.CMvPolynomial.aeval
          #[some (Lean.mkNatLit n), some xE, some gFV])]
    mkLambdaFVars #[gFV] body
  buildForallMemProofGen n gs hAevalProofs predicate

/-- Build a proof of `∀ p ∈ psList, CMvPolynomial.aeval x p = 0`, given
per-hypothesis proofs `hP i : aeval x ps[i].toCMv = 0`. -/
private def buildForallMemEqZeroProof (n : Nat) (xE : Expr)
    (ps : List (SOS.Poly n)) (hAevalProofs : List Expr) : MetaM Expr := do
  let cmvTy ← cmvType n
  let predicate ← withLocalDeclD `q cmvTy fun gFV => do
    let lhs ← mkAppOptM ``CPoly.CMvPolynomial.aeval
      #[some (Lean.mkNatLit n), some xE, some gFV]
    let zero ← mkAppOptM ``OfNat.ofNat
      #[some realTy, some (Lean.mkNatLit 0), none]
    let body ← mkEq lhs zero
    mkLambdaFVars #[gFV] body
  buildForallMemProofGen n ps hAevalProofs predicate

/-- Discharge the `cert.checks goal gs = true` side condition by
`decide +kernel`. Kernel reduction handles `Std.ExtTreeMap` lookups
and rational arithmetic at the witness denominators the search
actually emits. -/
private def buildDecideTrue (type : Expr) : TacticM Expr := do
  let tac ← `(tactic| (decide +kernel))
  proveByTactic type tac

/-! ### Per-hypothesis bridged proofs

Builds `0 ≤ aeval φ g_i.toCMv` for inequality constraints and
`aeval φ p_j.toCMv = 0` for equality constraints, dispatching on
`ConstraintKind`. -/

/-- Bundle of bridged proofs partitioned by constraint kind.

`strictPosProofs` / `strictPosPolys` record the *strict* (`0 < g`)
inequality hypotheses, with their lifted `0 < aeval φ g.toCMv` proofs.
The same hypotheses also appear (downgraded to `0 ≤ aeval φ g.toCMv`)
in `ineqProofs` / `ineqPolys`, so the cone-side bridge is unchanged;
the strict-product Positivstellensatz path consumes these extra
strict-positivity facts. -/
private structure BridgedConstraints (n : Nat) where
  ineqProofs : List Expr
  ineqPolys  : List (SOS.Poly n)
  eqProofs   : List Expr
  eqPolys    : List (SOS.Poly n)
  strictPosProofs : List Expr := []
  strictPosPolys  : List (SOS.Poly n) := []

/-- Build per-hypothesis bridged proofs from the ParsedGoal's
constraints, partitioning into inequality and equality halves. -/
private def buildHypothesisAevalProofsA (n : Nat) (φE : Expr)
    (constraints : Array SOS.Reify.ConstraintInfo) :
    TacticM (BridgedConstraints n) := do
  let nE := Lean.mkNatLit n
  let mut accIneq : Array Expr := #[]
  let mut polysIneq : Array (SOS.Poly n) := #[]
  let mut accEq : Array Expr := #[]
  let mut polysEq : Array (SOS.Poly n) := #[]
  let mut accStrict : Array Expr := #[]
  let mut polysStrict : Array (SOS.Poly n) := #[]
  for c in constraints do
    let some gTree := castRawToPoly c.raw n |
      throwError "sos: constraint poly's maxAtomBound exceeds n = {n}"
    let hRaw := Lean.mkFVar c.fvar
    let gE := Lean.toExpr gTree
    match c.kind with
    | .nonneg =>
      -- For general `a ≤ b` hypotheses, `c.orig = b − a` and the raw
      -- FVar has type `a ≤ b`; `sub_nonneg_of_le` lifts it to the
      -- canonical `0 ≤ b − a` shape `aeval_nonneg_of_orig` expects.
      let hExpr ← if c.useSubBridge then mkAppM ``sub_nonneg_of_le #[hRaw]
                  else pure hRaw
      let eqProof ← buildAtomicBridgeEq n φE gTree c.orig
      let aProof ← mkAppOptM ``SOS.aeval_nonneg_of_orig
        #[some nE, some φE, some gE, some c.orig,
          some eqProof, some hExpr]
      accIneq := accIneq.push aProof
      polysIneq := polysIneq.push gTree
    | .nonpos =>
      let negOrig ← mkAppM ``Neg.neg #[c.orig]
      let eqProof ← buildAtomicBridgeEq n φE gTree negOrig
      let aProof ← mkAppOptM ``SOS.aeval_nonneg_of_orig_neg
        #[some nE, some φE, some gE, some c.orig,
          some eqProof, some hRaw]
      accIneq := accIneq.push aProof
      polysIneq := polysIneq.push gTree
    | .pos =>
      -- For general `a < b` hypotheses, `c.orig = b − a` and the raw
      -- FVar has type `a < b`; `sub_pos_of_lt` lifts it to `0 < b − a`
      -- before downgrading to `0 ≤ b − a` via `le_of_lt`.
      let hExpr ← if c.useSubBridge then mkAppM ``sub_pos_of_lt #[hRaw]
                  else pure hRaw
      let hLeExpr ← mkAppM ``le_of_lt #[hExpr]
      let eqProof ← buildAtomicBridgeEq n φE gTree c.orig
      let aProof ← mkAppOptM ``SOS.aeval_nonneg_of_orig
        #[some nE, some φE, some gE, some c.orig,
          some eqProof, some hLeExpr]
      accIneq := accIneq.push aProof
      polysIneq := polysIneq.push gTree
      -- Also build the strict-positive bridge `0 < aeval φ g.toCMv`
      -- consumed by the strict-product Positivstellensatz path.
      let aPosProof ← mkAppOptM ``SOS.aeval_pos_of_orig
        #[some nE, some φE, some gE, some c.orig,
          some eqProof, some hExpr]
      accStrict := accStrict.push aPosProof
      polysStrict := polysStrict.push gTree
    | .eq =>
      -- `c.orig` is the difference `a − b`; `c.fvar : a = b`.
      -- Bridge: `evalReal x p = a − b`. Combined with
      -- `sub_eq_zero_of_eq h : a − b = 0` we get `aeval x p.toCMv = 0`
      -- via `aeval_eq_zero_of_orig`.
      let eqProof ← buildAtomicBridgeEq n φE gTree c.orig
      let hSubZero ← mkAppM ``sub_eq_zero_of_eq #[hRaw]
      let aProof ← mkAppOptM ``SOS.aeval_eq_zero_of_orig
        #[some nE, some φE, some gE, some c.orig,
          some eqProof, some hSubZero]
      accEq := accEq.push aProof
      polysEq := polysEq.push gTree
  return { ineqProofs := accIneq.toList, ineqPolys := polysIneq.toList,
           eqProofs := accEq.toList, eqPolys := polysEq.toList,
           strictPosProofs := accStrict.toList,
           strictPosPolys := polysStrict.toList }

/-- Closed and strict goals carry a conclusion polynomial plus the
original user expression it must bridge back to. -/
private structure ParsedConclusionData (n : Nat) where
  tree : SOS.Poly n
  cmv  : Expr
  orig : Expr
  /-- See `SOS.Reify.ParsedConcl.useSubBridge`. -/
  useSubBridge : Bool

/-- Extract and cast the conclusion polynomial for closed/strict modes. -/
private def parsedConclusionData (tag : String)
    (parsed : SOS.Reify.ParsedGoal) (n : Nat) :
    TacticM (ParsedConclusionData n) := do
  let some concl := parsed.concl |
    throwError "{tag}: missing concl"
  let some pTree := castRawToPoly concl.raw n |
    throwError "{tag}: conclusion poly's maxAtomBound exceeds n = {n}"
  let pCMv ← toCMvExpr n pTree
  return { tree := pTree, cmv := pCMv, orig := concl.orig,
           useSubBridge := concl.useSubBridge }

/-- The shape-specific data the unified close needs: which `Goal`
constructor to invoke, which soundness lemma, and (for closed/strict)
how to bridge the resulting `0 ≤ aeval …` / `0 < aeval …` proof back
to the user's original `0 ≤ origExpr` / `0 < origExpr` goal.
Infeasibility's conclusion is `False`, so it skips the bridge. -/
private inductive CloseMode where
  | closed
  | strict (εE : Expr) (hεE : Expr)
  | infeasible

/-- Build a `decide +kernel`-checked proof of
`cert.checks goal gs ps = true`. -/
private def buildCheckProof (certE goalE gsListE psListE : Expr) :
    TacticM Expr := do
  let checksE ← mkAppM ``SOS.Certificate.checks
    #[certE, goalE, gsListE, psListE]
  let trueE ← mkAppOptM ``Bool.true #[]
  buildDecideTrue (← mkEq checksE trueE)

/-- Unified close: builds `decide +kernel`-checked soundness application
for the closed / strict / infeasible certificate and assigns the main
goal. Mode-specific differences are tabulated in `CloseMode`. -/
private def closeSos (parsed : SOS.Reify.ParsedGoal) (certE : Expr)
    (mode : CloseMode) : TacticM Unit := Tactic.withMainContext do
  let n := parsed.atoms.size
  let nE := Lean.mkNatLit n
  let mv ← Tactic.getMainGoal
  let φE ← buildFinValExpr parsed.atoms
  let bridged ← buildHypothesisAevalProofsA n φE parsed.constraints
  let gsListE ← gsCMvListExpr n bridged.ineqPolys
  let psListE ← gsCMvListExpr n bridged.eqPolys
  let hgsProof ← buildForallMemProof n φE bridged.ineqPolys bridged.ineqProofs
  let hpsProof ← buildForallMemEqZeroProof n φE bridged.eqPolys bridged.eqProofs
  let final ← match mode with
    | .closed =>
      let p ← parsedConclusionData "sos" parsed n
      let goalE ← mkAppOptM ``SOS.Goal.closed #[some nE, some p.cmv]
      let decProof ← buildCheckProof certE goalE gsListE psListE
      let hTarget ← mkAppM ``SOS.sos_sound
        #[p.cmv, gsListE, psListE, certE, decProof, φE, hgsProof, hpsProof]
      let eqProof_p ← buildAtomicBridgeEq n φE p.tree p.orig
      let pE := Lean.toExpr p.tree
      let hNonneg ← mkAppOptM ``SOS.nonneg_orig_of_aeval
        #[some nE, some φE, some pE, some p.orig, some eqProof_p, some hTarget]
      -- For `a ≤ b` (sub-bridge) goals, `p.orig = b − a`, so the
      -- recovered fact is `0 ≤ b − a`; wrap with `le_of_sub_nonneg`
      -- to get the user-form `a ≤ b`.
      if p.useSubBridge then
        mkAppM ``le_of_sub_nonneg #[hNonneg]
      else
        pure hNonneg
    | .strict εE hεE =>
      let p ← parsedConclusionData "sos" parsed n
      let goalE ← mkAppOptM ``SOS.Goal.strict
        #[some nE, some p.cmv, some εE, some hεE]
      let decProof ← buildCheckProof certE goalE gsListE psListE
      let hTarget ← mkAppM ``SOS.sos_strict_sound
        #[p.cmv, εE, hεE, gsListE, psListE, certE, decProof, φE,
          hgsProof, hpsProof]
      let eqProof_p ← buildAtomicBridgeEq n φE p.tree p.orig
      let pE := Lean.toExpr p.tree
      let hPos ← mkAppOptM ``SOS.pos_orig_of_aeval
        #[some nE, some φE, some pE, some p.orig, some eqProof_p, some hTarget]
      if p.useSubBridge then
        mkAppM ``lt_of_sub_pos #[hPos]
      else
        pure hPos
    | .infeasible =>
      let goalE ← mkAppOptM ``SOS.Goal.infeasible #[some nE]
      let decProof ← buildCheckProof certE goalE gsListE psListE
      mkAppM ``SOS.sos_infeasible_sound
        #[gsListE, psListE, certE, decProof, φE, hgsProof, hpsProof]
  mv.assign final
  Tactic.replaceMainGoal []

/-- Strict-product Positivstellensatz close: discharges `0 < p` via
`sos_strict_product_sound`, where the certificate verifies the closed
identity `−(∏ strictGs)^exponent = σ_cert((gs ++ [−p]), ps)`. Strict
hypotheses are read from the parsed constraints (kind = `.pos`); they
contribute *both* a downgraded `0 ≤ g` proof to the cone bridge *and* a
strict-positive `0 < g` proof to the structural witness. -/
private def closeSosStrictProduct (parsed : SOS.Reify.ParsedGoal)
    (certE : Expr) (exponent : Nat) :
    TacticM Unit := Tactic.withMainContext do
  let n := parsed.atoms.size
  let nE := Lean.mkNatLit n
  let mv ← Tactic.getMainGoal
  let φE ← buildFinValExpr parsed.atoms
  let bridged ← buildHypothesisAevalProofsA n φE parsed.constraints
  let gsListE ← gsCMvListExpr n bridged.ineqPolys
  let psListE ← gsCMvListExpr n bridged.eqPolys
  let strictGsListE ← gsCMvListExpr n bridged.strictPosPolys
  let hgsProof ← buildForallMemProof n φE bridged.ineqPolys bridged.ineqProofs
  let hpsProof ← buildForallMemEqZeroProof n φE bridged.eqPolys bridged.eqProofs
  let hStrictProof ← buildForallMemStrictProof n φE
    bridged.strictPosPolys bridged.strictPosProofs
  let p ← parsedConclusionData "sos" parsed n
  -- Augmented inequality list `gs ++ [-p]`. The certificate's σ
  -- subsets index into this list (with `-p` at the last position).
  let cmvTy ← cmvType n
  let negPE ← mkAppM ``Neg.neg #[p.cmv]
  let nilE ← mkAppOptM ``List.nil #[some cmvTy]
  let singletonE ← mkAppOptM ``List.cons #[some cmvTy, some negPE, some nilE]
  let augGsListE ← mkAppM ``HAppend.hAppend #[gsListE, singletonE]
  -- Target polynomial: `−(strictProductPoly strictGs)^exponent`.
  let strictProdE ← mkAppOptM ``SOS.strictProductPoly #[some nE, some strictGsListE]
  let expE := Lean.mkNatLit exponent
  let powE ← mkAppM ``HPow.hPow #[strictProdE, expE]
  let negPowE ← mkAppM ``Neg.neg #[powE]
  let goalE ← mkAppOptM ``SOS.Goal.closed #[some nE, some negPowE]
  let decProof ← buildCheckProof certE goalE augGsListE psListE
  let hTarget ← mkAppM ``SOS.sos_strict_product_sound
    #[p.cmv, strictGsListE, expE, gsListE, psListE, certE, decProof, φE,
      hgsProof, hpsProof, hStrictProof]
  let eqProof_p ← buildAtomicBridgeEq n φE p.tree p.orig
  let pE := Lean.toExpr p.tree
  let hPos ← mkAppOptM ``SOS.pos_orig_of_aeval
    #[some nE, some φE, some pE, some p.orig, some eqProof_p, some hTarget]
  let final ←
    if p.useSubBridge then mkAppM ``lt_of_sub_pos #[hPos]
    else pure hPos
  mv.assign final
  Tactic.replaceMainGoal []

/-- Close a refutation goal using a checked closed SOS certificate. -/
private def closeSosClosedRefutation (parsed : SOS.Reify.ParsedGoal)
    (certE : Expr) :
    TacticM Unit := Tactic.withMainContext do
  let n := parsed.atoms.size
  let nE := Lean.mkNatLit n
  let mv ← Tactic.getMainGoal
  let φE ← buildFinValExpr parsed.atoms
  let bridged ← buildHypothesisAevalProofsA n φE parsed.constraints
  let gsListE ← gsCMvListExpr n bridged.ineqPolys
  let psListE ← gsCMvListExpr n bridged.eqPolys
  let hgsProof ← buildForallMemProof n φE bridged.ineqPolys bridged.ineqProofs
  let hpsProof ← buildForallMemEqZeroProof n φE bridged.eqPolys bridged.eqProofs
  let p ← parsedConclusionData "sos" parsed n
  let cmvTy ← cmvType n
  let negPE ← mkAppM ``Neg.neg #[p.cmv]
  let nilE ← mkAppOptM ``List.nil #[some cmvTy]
  let singletonE ← mkAppOptM ``List.cons #[some cmvTy, some negPE, some nilE]
  let augGsListE ← mkAppM ``HAppend.hAppend #[gsListE, singletonE]
  -- `strictGs = []`, `exponent = 1`; target `−(strictProductPoly [])^1 = −1`.
  let strictGsListE := nilE
  let hStrictProof ← buildForallMemStrictProof n φE [] []
  let expE := Lean.mkNatLit 1
  let strictProdE ← mkAppOptM ``SOS.strictProductPoly #[some nE, some strictGsListE]
  let powE ← mkAppM ``HPow.hPow #[strictProdE, expE]
  let negPowE ← mkAppM ``Neg.neg #[powE]
  let goalE ← mkAppOptM ``SOS.Goal.closed #[some nE, some negPowE]
  let decProof ← buildCheckProof certE goalE augGsListE psListE
  let hTarget ← mkAppM ``SOS.sos_strict_product_sound
    #[p.cmv, strictGsListE, expE, gsListE, psListE, certE, decProof, φE,
      hgsProof, hpsProof, hStrictProof]
  let eqProof_p ← buildAtomicBridgeEq n φE p.tree p.orig
  let pE := Lean.toExpr p.tree
  let hPos ← mkAppOptM ``SOS.pos_orig_of_aeval
    #[some nE, some φE, some pE, some p.orig, some eqProof_p, some hTarget]
  let hNonneg ← mkAppM ``le_of_lt #[hPos]
  let final ←
    if p.useSubBridge then mkAppM ``le_of_sub_nonneg #[hNonneg]
    else pure hNonneg
  mv.assign final
  Tactic.replaceMainGoal []

/-- Positivstellensatz `i`-th power refutation close: discharges `0 ≤ p` via
`sos_nonneg_refutation_sound`, where the certificate verifies the closed
identity `−(−p)^exponent = σ_cert((gs ++ [−p]), ps)`. Unlike
`closeSosClosedRefutation` (the `i = 0` case, which routes through the strict
`0 < p`), this yields the non-strict `0 ≤ p` directly — the form required for
non-negative polynomials with a real zero, such as Motzkin's. -/
private def closeSosNonnegRefutation (parsed : SOS.Reify.ParsedGoal)
    (certE : Expr) (exponent : Nat) :
    TacticM Unit := Tactic.withMainContext do
  let n := parsed.atoms.size
  let nE := Lean.mkNatLit n
  let mv ← Tactic.getMainGoal
  let φE ← buildFinValExpr parsed.atoms
  let bridged ← buildHypothesisAevalProofsA n φE parsed.constraints
  let gsListE ← gsCMvListExpr n bridged.ineqPolys
  let psListE ← gsCMvListExpr n bridged.eqPolys
  let hgsProof ← buildForallMemProof n φE bridged.ineqPolys bridged.ineqProofs
  let hpsProof ← buildForallMemEqZeroProof n φE bridged.eqPolys bridged.eqProofs
  let p ← parsedConclusionData "sos" parsed n
  let cmvTy ← cmvType n
  let negPE ← mkAppM ``Neg.neg #[p.cmv]
  let nilE ← mkAppOptM ``List.nil #[some cmvTy]
  let singletonE ← mkAppOptM ``List.cons #[some cmvTy, some negPE, some nilE]
  let augGsListE ← mkAppM ``HAppend.hAppend #[gsListE, singletonE]
  -- Target polynomial: `−(−p)^exponent`.
  let expE := Lean.mkNatLit exponent
  let powE ← mkAppM ``HPow.hPow #[negPE, expE]
  let negPowE ← mkAppM ``Neg.neg #[powE]
  let goalE ← mkAppOptM ``SOS.Goal.closed #[some nE, some negPowE]
  let decProof ← buildCheckProof certE goalE augGsListE psListE
  let hTarget ← mkAppM ``SOS.sos_nonneg_refutation_sound
    #[p.cmv, expE, gsListE, psListE, certE, decProof, φE, hgsProof, hpsProof]
  let eqProof_p ← buildAtomicBridgeEq n φE p.tree p.orig
  let pE := Lean.toExpr p.tree
  let hNonneg ← mkAppOptM ``SOS.nonneg_orig_of_aeval
    #[some nE, some φE, some pE, some p.orig, some eqProof_p, some hTarget]
  let final ←
    if p.useSubBridge then mkAppM ``le_of_sub_nonneg #[hNonneg]
    else pure hNonneg
  mv.assign final
  Tactic.replaceMainGoal []

/-! ### Tactic surface -/

/-- `sos` proves supported polynomial goals by finding and checking a sum-of-squares
certificate. -/
syntax (name := sosTactic) "sos" Lean.Parser.Tactic.optConfig : tactic
/-- `sos?` proves a supported polynomial goal and suggests an explicit `sos_witness`. -/
syntax (name := sosTryTactic) "sos?" Lean.Parser.Tactic.optConfig : tactic
/-- `pure_sos` proves an unconstrained polynomial nonnegativity goal with a
sum-of-squares certificate. -/
syntax (name := pureSosTactic) "pure_sos" Lean.Parser.Tactic.optConfig : tactic
/-- `sos_witness cert` checks the explicit sum-of-squares certificate `cert`.
For a strict-positivity goal, supply its positive rational margin as `with ε := eps`. -/
syntax (name := sosWitnessTactic)
  "sos_witness " term ("with" "ε" ":=" term)? : tactic
/-- `sos_witness cert with exponent := n` checks a closed refutation certificate
whose strict-product exponent is `n`. -/
syntax (name := sosWitnessExpTactic)
  "sos_witness " term "with" "exponent" ":=" num : tactic

/-- Cast each constraint's `Raw` to the typed `Poly n`. Returns
`(inequality polys, equality polys)`, partitioned by `ConstraintKind`. -/
private def castConstraints (constraints : Array SOS.Reify.ConstraintInfo)
    (n : Nat) : TacticM (List (SOS.Poly n) × List (SOS.Poly n)) := do
  let mut accIneq : Array (SOS.Poly n) := #[]
  let mut accEq : Array (SOS.Poly n) := #[]
  for c in constraints do
    let some gT := castRawToPoly c.raw n |
      throwError "sos: constraint poly's maxAtomBound > n = {n}"
    match c.kind with
    | .nonneg | .nonpos | .pos => accIneq := accIneq.push gT
    | .eq => accEq := accEq.push gT
  return (accIneq.toList, accEq.toList)

/-- Build the `LT.lt 0 ε` proof needed by `closeSos (.strict εE hεE)`,
given the `ε` returned by the search. -/
private def buildStrictHεProof (εE : Expr) : TacticM Expr := do
  let hεType ← mkAppM ``LT.lt #[(← mkAppOptM ``OfNat.ofNat
    #[some ratTy, some (Lean.mkNatLit 0), none]), εE]
  let hεE ← buildDecideTrue (← mkEq
    (← mkAppOptM ``Decidable.decide #[some hεType, none])
    (Lean.mkConst ``Bool.true))
  mkAppM ``of_decide_eq_true #[hεE]

/-! ### `sos?` suggestions -/

/-- Emit the `Try this:` suggestion for a found certificate. When `ε?`
is `some r`, append `with ε := <r>` so the suggestion compiles for
strict-positivity goals.

We pass the suggestion as a raw `SuggestionText.string` rather than
roundtripping through `Parser.runParserCategory`; the latter re-pretty-
prints the parsed syntax tree and squashes whitespace around the
`with ε := …` clause. -/
private def emitSosSuggestion (tk : Syntax) (certText : String)
    (ε? : Option ℚ) : TacticM Unit := do
  let suffix := match ε? with
    | none => ""
    | some r => s!" with ε := {formatRat r}"
  let suggestion : String := s!"sos_witness {certText}{suffix}"
  let sugg : Lean.Meta.Tactic.TryThis.Suggestion :=
    { suggestion := .string suggestion }
  Lean.Meta.Tactic.TryThis.addSuggestion tk sugg

/-- The shared body of `sos` and `sos?`. Runs search for the parsed
goal, optionally emits a `Try this:` suggestion at `suggest?`, and
closes the goal with the resulting certificate. The error-message
prefix (`"sos"` vs `"sos?"`) is taken from `tag`. -/
private def runSosTactic (parsed : SOS.Reify.ParsedGoal) (cfg : Config)
    (suggest? : Option Syntax) (tag : String) : TacticM Unit := do
  let n := parsed.atoms.size
  let (gPolys, pPolys) ← castConstraints parsed.constraints n
  let gsCMv := gPolys.map SOS.Poly.toCMv
  let psCMv := pPolys.map SOS.Poly.toCMv
  let withFoundCert (cert : SOS.Certificate n) (mode : CloseMode)
      (ε? : Option ℚ) : TacticM Unit := do
    let decompiled := cert.decompile
    if let some tk := suggest? then
      emitSosSuggestion tk decompiled.format ε?
    let certE ← decompiled.toExpr
    closeSos parsed certE mode
  let strictIdxs : List Nat := Id.run do
    let mut idxs : Array Nat := #[]
    let mut ineqIdx : Nat := 0
    for c in parsed.constraints do
      match c.kind with
      | .pos =>
        idxs := idxs.push ineqIdx
        ineqIdx := ineqIdx + 1
      | .nonneg | .nonpos =>
        ineqIdx := ineqIdx + 1
      | .eq => pure ()
    return idxs.toList
  let problem : SOS.Engine.Problem n ← match parsed.shape with
    | .closed =>
      let p ← parsedConclusionData s!"{tag} (closed)" parsed n
      pure (.closed p.tree.toCMv gsCMv psCMv)
    | .strict =>
      let p ← parsedConclusionData s!"{tag} (strict)" parsed n
      pure (.strict p.tree.toCMv gsCMv strictIdxs psCMv)
    | .infeasible =>
      pure (.infeasible gsCMv psCMv)
  let some result ← (SOS.Engine.solve cfg problem : IO _) |
    let route := match parsed.shape with
      | .closed => "a certificate"
      | .strict => "a strict-positivity certificate"
      | .infeasible => "an infeasibility certificate"
    throwError "{tag}: search failed to find {route}"
  unless result.check problem do
    throwError "{tag}: internal error: search returned an invalid certificate"
  match result with
  | .closed cert =>
    withFoundCert cert .closed none
  | .infeasible cert =>
    withFoundCert cert .infeasible none
  | .strict epsilon _ cert =>
    let εE := Lean.toExpr epsilon
    let hεProof ← buildStrictHεProof εE
    withFoundCert cert (.strict εE hεProof) (some epsilon)
  | .closedRefutation cert =>
    let certE ← cert.decompile.toExpr
    closeSosClosedRefutation parsed certE
  | .nonnegRefutation power cert =>
    let certE ← cert.decompile.toExpr
    closeSosNonnegRefutation parsed certE power
  | .strictProduct _ power cert =>
    let decompiled := cert.decompile
    if let some tk := suggest? then
      let certText := decompiled.format
      let suggestion :=
        s!"sos_witness {certText} with exponent := {power}"
      let sugg : Lean.Meta.Tactic.TryThis.Suggestion :=
        { suggestion := .string suggestion }
      Lean.Meta.Tactic.TryThis.addSuggestion tk sugg
    let certE ← decompiled.toExpr
    closeSosStrictProduct parsed certE power

/-- Detect whether the *original* goal (before any lift / refute step)
has a ℕ/ℤ ≤/</= conclusion at its head after stripping leading binders.
This is the syntactic precondition for the negate-and-refute fallback. -/
private partial def isDiscreteIneqGoal : TacticM Bool := withMainContext do
  let mv ← getMainGoal
  let isDiscreteDomain (α : Expr) : MetaM Bool := do
    let α ← whnfR α
    return α.isConstOf ``Nat || α.isConstOf ``Int
  let rec go (e : Expr) : MetaM Bool := do
    let e ← whnfR e
    match e with
    | .forallE _ _ body _ => go body
    | _ =>
      match_expr e with
      | LE.le α _ _ _ =>
        isDiscreteDomain α
      | LT.lt α _ _ _ =>
        isDiscreteDomain α
      | Eq α _ _ =>
        isDiscreteDomain α
      | _ => return false
  go (← mv.getType >>= instantiateMVars)

/-- Drive parse + search on every open goal. Used by both the direct
and refute arms of `runSosWithLift`. -/
private def parseAndSearchAll (cfg : Config) (suggest? : Option Syntax)
    (tag : String) : TacticM Unit := do
  let goals ← getGoals
  for g in goals do
    if ← g.isAssigned then continue
    setGoals [g]
    let some parsed ← SOS.Reify.parseGoalAtomic |
      throwError "{tag}: goal not in supported fragment"
    runSosTactic parsed cfg suggest? tag
  setGoals []

/-- Parse and close all current goals as explicit `PURE_SOS` goals.
Unlike `sos`, this tactic surface is deliberately unconstrained: any
recognised constraint hypothesis is an error, and only closed
non-negativity goals are accepted. -/
private def parseAndPureSearchAll (cfg : Config) : TacticM Unit := do
  let goals ← getGoals
  for g in goals do
    if ← g.isAssigned then continue
    setGoals [g]
    let some parsed ← SOS.Reify.parseGoalAtomic |
      throwError "pure_sos: goal not in supported fragment"
    unless parsed.shape matches .closed do
      throwError "pure_sos: expected an unconstrained non-negativity goal"
    unless parsed.constraints.isEmpty do
      throwError "pure_sos: constraint hypotheses are not allowed"
    runSosTactic parsed cfg none "pure_sos"
  setGoals []

/-- Run the lift pre-pass, then the SOS pipeline. The pre-pass may
produce multiple subgoals (e.g. from an `Eq` conclusion split via
`le_antisymm`), or close some subgoals outright (e.g. `n < n+1` over
ℕ becomes `n+1 ≤ n+1` and the rewrite step closes it reflexively).
Each surviving subgoal is parsed and closed independently.

For ℕ/ℤ ≤/</= goals where the direct path fails (no Putinar certificate
over ℝ — e.g. `n ≤ n*n`, which is false at `n = 0.5`), we restore the
pre-lift state and retry on the negate-and-refute branch (Harrison's
`INT_SOS` trick), which routes through the existing `.infeasible` SOS
arm. See `SOS.Lift.refuteToReal`. -/
private def runSosWithLift (cfg : Config) (suggest? : Option Syntax)
    (tag : String) : TacticM Unit := do
  let canRefute ← isDiscreteIneqGoal
  if canRefute then
    -- Try the direct path first; on any failure, restore and retry on
    -- the refute branch. This mirrors the dense-fallback pattern in
    -- `runSearch`: the direct path is cheaper for goals that *are*
    -- Putinar-certifiable; the refute branch only earns its keep on
    -- discreteness-dependent goals.
    let st ← saveState
    try
      SOS.Lift.liftToReal
      parseAndSearchAll cfg suggest? tag
    catch direct =>
      -- Trace the direct-path failure under `sos.lift` for debuggability:
      -- the catch is intentionally broad (any failure shape — search
      -- miss, reify rejection, lift error — falls through to refute), so
      -- a stray bug in the direct arm would otherwise be hidden by a
      -- successful refute. If refute also fails, its exception
      -- propagates and the user sees the second-stage error.
      trace[sos.lift] "direct path failed; trying refute: {direct.toMessageData}"
      st.restore
      SOS.Lift.refuteToReal
      parseAndSearchAll cfg suggest? tag
  else
    SOS.Lift.liftToReal
    parseAndSearchAll cfg suggest? tag

/-! ### Boolean-combination splitter

Harrison's frontend reduces a conclusion of the form `p ∧ q` or
`p ∨ q` (possibly nested) to a finite set of refutation subproblems
before handing each off to the SOS pipeline. We do the same:

* `p ∧ q` — split via `And.intro` and recurse on both subgoals.
* `p ∨ q` — try the left disjunct (via `Or.inl`) and recurse on the
  resulting subgoal; on any failure, restore the pre-split state and
  try the right disjunct.

Leading universal / hypothesis binders are introduced before the
match so e.g. `∀ x : ℝ, 0 ≤ x^2 ∧ 0 ≤ x^4` is recognised. Nesting is
capped at 3 levels — search cost grows multiplicatively in the
conjunctive case and as a try/restore tree in the disjunctive case,
so the cap protects users from runaway elaboration. The cap is
enforced by a single preflight scan of the conclusion's Boolean tree,
so it is a global property of the goal rather than a per-path bound
(a `(too-deep) ∨ easy` goal is rejected even though the easy disjunct
would otherwise succeed). Flatten the goal manually if you really
need more depth.

Disjunctive *hypotheses* are out of scope. -/

/-- Maximum nested-Boolean depth handled by the splitter. -/
private def maxBoolDepth : Nat := 3

/-- Count the maximum nesting depth of `And` / `Or` in `e`, descending
under `whnfR`. Leaves (anything that isn't an `And`/`Or` after
reduction) contribute depth `0`; each `And`/`Or` node adds `1`. -/
private partial def boolDepthOf (e : Expr) : MetaM Nat := do
  let e ← whnfR e
  match_expr e with
  | And p q => return 1 + max (← boolDepthOf p) (← boolDepthOf q)
  | Or  p q => return 1 + max (← boolDepthOf p) (← boolDepthOf q)
  | _ => return 0

/-- Split an `And p q` goal into its two children via the meta API,
avoiding any tail-goal contamination that a generic `apply` /
`refine` would expose to `getGoals`. -/
private def splitAndGoal (mv : MVarId) : MetaM (MVarId × MVarId) := mv.withContext do
  let goal ← mv.getType >>= instantiateMVars
  match_expr (← whnfR goal) with
  | And p q =>
    let pMV ← mkFreshExprSyntheticOpaqueMVar p
    let qMV ← mkFreshExprSyntheticOpaqueMVar q
    mv.assign (← mkAppM ``And.intro #[pMV, qMV])
    return (pMV.mvarId!, qMV.mvarId!)
  | _ => throwError "splitAndGoal: goal is not an `And`"

/-- Apply `Or.inl` (`side = false`) or `Or.inr` (`side = true`) to an
`Or p q` goal, returning the single resulting subgoal. -/
private def splitOrGoal (mv : MVarId) (side : Bool) : MetaM MVarId := mv.withContext do
  let goal ← mv.getType >>= instantiateMVars
  match_expr (← whnfR goal) with
  | Or p q =>
    if side then
      let qMV ← mkFreshExprSyntheticOpaqueMVar q
      mv.assign (← mkAppOptM ``Or.inr #[some p, some q, some qMV])
      return qMV.mvarId!
    else
      let pMV ← mkFreshExprSyntheticOpaqueMVar p
      mv.assign (← mkAppOptM ``Or.inl #[some p, some q, some pMV])
      return pMV.mvarId!
  | _ => throwError "splitOrGoal: goal is not an `Or`"

/-- Splitter for Boolean combinations in the conclusion. Intros leading
universal / hypothesis binders, then dispatches on `And` / `Or` /
anything-else. Falls through to `runSosWithLift` at the leaves. The
depth cap is enforced upstream by `runSosBool`. -/
private partial def runSosBoolAux (cfg : Config) (suggest? : Option Syntax)
    (tag : String) : TacticM Unit := withMainContext do
  SOS.Lift.introLeadingBinders
  let mv ← getMainGoal
  let goal ← mv.getType >>= instantiateMVars
  match_expr (← whnfR goal) with
  | And _ _ =>
    let (lMV, rMV) ← splitAndGoal mv
    setGoals [lMV]
    runSosBoolAux cfg suggest? tag
    let lLeftovers ← getGoals
    setGoals [rMV]
    runSosBoolAux cfg suggest? tag
    let rLeftovers ← getGoals
    setGoals (lLeftovers ++ rLeftovers)
  | Or _ _ =>
    let st ← saveState
    try
      let lMV ← splitOrGoal mv (side := false)
      setGoals [lMV]
      runSosBoolAux cfg suggest? tag
    catch leftEx =>
      trace[sos.lift] "Or.inl failed; trying Or.inr: {leftEx.toMessageData}"
      st.restore
      let mv ← getMainGoal
      let rMV ← splitOrGoal mv (side := true)
      setGoals [rMV]
      runSosBoolAux cfg suggest? tag
  | _ =>
    runSosWithLift cfg suggest? tag

/-- Entry point. Intros leading binders so the depth scan sees the
conclusion under any `∀`, checks the Boolean-nesting cap once
globally, and then dispatches via `runSosBoolAux`. -/
private def runSosBool (cfg : Config) (suggest? : Option Syntax)
    (tag : String) : TacticM Unit := withMainContext do
  SOS.Lift.introLeadingBinders
  let mv ← getMainGoal
  let goal ← mv.getType >>= instantiateMVars
  let d ← boolDepthOf goal
  if d > maxBoolDepth then
    throwError "{tag}: boolean nesting in conclusion exceeds depth \
      {maxBoolDepth} (found {d}); flatten the goal or split manually"
  runSosBoolAux cfg suggest? tag

/-- Entry point for `pure_sos`: introduce leading binders, run the same
real-lift pre-pass as `sos`, then require each parsed goal to have no
constraints before closing it. -/
private def runPureSos (cfg : Config) : TacticM Unit := withMainContext do
  SOS.Lift.introLeadingBinders
  SOS.Lift.liftToReal
  parseAndPureSearchAll cfg

elab_rules : tactic
  | `(tactic| sos $cfg:optConfig) => do
    let cfg ← elabConfig cfg
    runSosBool cfg none "sos"

elab_rules : tactic
  | `(tactic| pure_sos $cfg:optConfig) => do
    let cfg ← elabConfig cfg
    runPureSos cfg

elab_rules : tactic
  | `(tactic| sos?%$tk $cfg:optConfig) => do
    let cfg ← elabConfig cfg
    runSosBool cfg (some tk) "sos?"

/-- Shared body of `sos_witness` (with and without the `with ε := …`
suffix). Elaborates the certificate, dispatches on the parsed goal
shape, and routes through `closeSos`. -/
private def runSosWitness (cert : Term)
    (epsTerm? : Option Term) : TacticM Unit := do
  let some parsed ← SOS.Reify.parseGoalAtomic |
    throwError "sos_witness: goal not in supported fragment"
  let n := parsed.atoms.size
  let certTy ← mkAppOptM ``SOS.Certificate #[some (Lean.mkNatLit n)]
  let certE ← Term.elabTermEnsuringType cert certTy
  Term.synthesizeSyntheticMVarsNoPostponing
  let certE ← instantiateMVars certE
  match parsed.shape, epsTerm? with
  | .closed, none => closeSos parsed certE .closed
  | .infeasible, none => closeSos parsed certE .infeasible
  | .strict, some εT =>
    let εE ← Term.elabTermEnsuringType εT ratTy
    Term.synthesizeSyntheticMVarsNoPostponing
    let εE ← instantiateMVars εE
    let hεProof ← buildStrictHεProof εE
    closeSos parsed certE (.strict εE hεProof)
  | .strict, none =>
    throwError "sos_witness: strict-positivity goal requires `with ε := <rat>`"
  | _, some _ =>
    throwError "sos_witness: `with ε := …` is only valid on strict-positivity goals"

/-- Shared body of `sos_witness <cert> with exponent := <n>`, the
witness form for strict-product Positivstellensatz certificates
(issue #46). Elaborates the certificate against the parsed goal,
verifies the parsed shape is `.strict`, and dispatches to
`closeSosStrictProduct`. -/
private def runSosWitnessStrictProduct (cert : Term) (expN : Nat) :
    TacticM Unit := do
  let some parsed ← SOS.Reify.parseGoalAtomic |
    throwError "sos_witness: goal not in supported fragment"
  unless parsed.shape matches .strict do
    throwError
      "sos_witness: `with exponent := <nat>` is only valid on strict-positivity goals"
  let n := parsed.atoms.size
  let certTy ← mkAppOptM ``SOS.Certificate #[some (Lean.mkNatLit n)]
  let certE ← Term.elabTermEnsuringType cert certTy
  Term.synthesizeSyntheticMVarsNoPostponing
  let certE ← instantiateMVars certE
  closeSosStrictProduct parsed certE expN

elab_rules : tactic
  | `(tactic| sos_witness $cert:term) => runSosWitness cert none
  | `(tactic| sos_witness $cert:term with ε := $eps:term) =>
      runSosWitness cert (some eps)
  | `(tactic| sos_witness $cert:term with exponent := $expN:num) =>
      runSosWitnessStrictProduct cert expN.getNat

end SOS
