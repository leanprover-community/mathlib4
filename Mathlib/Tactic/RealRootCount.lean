/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Polynomial.Sturm.Certificate
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.RealRootCount.Parse
public meta import Mathlib.Tactic.RealRootCount.Parse
public meta import HexRealRoots.Chain
public meta import HexPoly.Euclid.DivGcd

/-!
# Certified real root counts

`by real_root_count` proves a goal `Fintype.card (p.rootSet ℝ) = n`.
The term form `real_root_count (p : ℚ[X])` proves `Fintype.card (p.rootSet ℝ) = n` for a closed,
squarefree polynomial of positive degree with integer coefficients. Hex proposes
a signed remainder chain; `ring`, `compute_degree`, and `norm_num` check its
identities, nonvanishing, and signs. No correctness assumption about the generator
or its polynomial representation enters the proof.
-/

public meta section

namespace Mathlib.Tactic.RealRootCount

open Lean Meta Elab Term

private def intTerm (z : Int) : TermElabM (TSyntax `term) := do
  let n := Syntax.mkNumLit (toString z.natAbs)
  if z < 0 then `(-$n) else `($n)

private def polyTerm (cs : Array Int) : TermElabM (TSyntax `term) := do
  let mut sum : Option (TSyntax `term) := none
  for i in [:cs.size] do
    if cs[i]! != 0 then
      let c ← intTerm cs[i]!
      let k := Syntax.mkNumLit (toString i)
      let monomial ← if i == 0 then `(($c : Polynomial ℝ))
        else `(($c : Polynomial ℝ) * Polynomial.X ^ $k)
      sum ← match sum with
        | none => pure (some monomial)
        | some t => some <$> `($t + $monomial)
  return sum.getD (← `((0 : Polynomial ℝ)))

/-- Coefficients of `C left * p = quotient * q - C right * r`. -/
private structure RemainderIdentity where
  left : Int
  quotient : Array Int
  right : Int

/-- Divide over `ℚ`, then clear denominators to obtain an integer identity.
The generated proof checks both the identity and positivity of the two factors. -/
private def remainderIdentity (p q r : Array Int) : RemainderIdentity := Id.run do
  let toRat := Hex.DensePoly.ofCoeffs ∘ Array.map (fun (c : Int) => (c : Rat))
  let (quotient, remainder) := Hex.DensePoly.divMod (toRat p) (toRat q)
  let right := -remainder.coeff (r.size - 1) / (r.back! : Rat)
  let left := quotient.coeffs.foldl (fun n c => n.lcm c.den) right.den
  return ⟨left, quotient.coeffs.map (fun c => (c * (left : Rat)).num),
    (right * (left : Rat)).num⟩

private def variations (xs : Array Int) : Nat := Id.run do
  let mut last := 0
  let mut n := 0
  for x in xs do
    if x != 0 then
      if last * x < 0 then n := n + 1
      last := x
  return n

private def emit (pStx : TSyntax `term) (p : Hex.ZPoly)
    (unfolds : Array (TSyntax ``Parser.Tactic.simpLemma)) : TermElabM (TSyntax `term) := do
  let _ : Inhabited Hex.ZPoly := ⟨Hex.DensePoly.C 0⟩
  if p.isZero then
    throwError "real_root_count: expected a nonzero polynomial"
  if p.size == 1 then
    throwError "real_root_count: expected a polynomial of positive degree"
  let polys := Hex.ZPoly.sturmChain p
  if polys.size < 2 || polys.back!.size != 1 then
    throwError "real_root_count: expected a squarefree polynomial"
  -- The generator removes positive content from its first entry. Use the original
  -- polynomial here, so the final transport only checks coefficient arithmetic.
  let cs := (polys.set! 0 p).map (·.coeffs)
  let ps ← cs.mapM polyTerm
  let mut facts : Array (TSyntax `tactic) := #[]
  let mut nonzeros : Array (TSyntax `term) := #[]
  -- Record degree, leading coefficient, and nonvanishing once per entry.
  for i in [:ps.size] do
    let t := ps[i]!
    let d := Syntax.mkNumLit (toString (cs[i]!.size - 1))
    let c ← intTerm cs[i]!.back!
    let hd := mkIdent (← mkFreshUserName `degree)
    let hc := mkIdent (← mkFreshUserName `coeff)
    let hl := mkIdent (← mkFreshUserName `leadingCoeff)
    let hn := mkIdent (← mkFreshUserName `nonzero)
    facts := facts.push (← `(tactic| have $hd : ($t).natDegree = $d := by compute_degree!))
    facts := facts.push (← `(tactic| have $hc : ($t).coeff $d = $c := by compute_degree!))
    facts := facts.push (← `(tactic| have $hl : ($t).leadingCoeff = $c := by
      rw [Polynomial.leadingCoeff, $hd:term]; exact $hc))
    facts := facts.push (← `(tactic| have $hn : $t ≠ 0 := by
      apply Polynomial.leadingCoeff_ne_zero.mp
      rw [$hl:term]
      norm_num))
    nonzeros := nonzeros.push (← `($hn))
  let m := ps.size
  let c ← intTerm cs.back!.back!
  let mut cert ← `(show Sturm.RemainderChain [$(ps[m - 2]!), $(ps[m - 1]!)] from by
    convert Sturm.RemainderChain.pair $(nonzeros[m - 2]!)
      (show ($c : ℝ) ≠ 0 by norm_num) using 1 <;> norm_num)
  for k in [:m - 2] do
    let i := m - 3 - k
    let identity := remainderIdentity cs[i]! cs[i + 1]! cs[i + 2]!
    let a ← intTerm identity.left
    let b ← intTerm identity.right
    let d ← polyTerm identity.quotient
    cert ← `(Sturm.RemainderChain.cons (d := $d) $cert $(nonzeros[i]!)
      (show (0 : ℝ) < $a by norm_num) (show (0 : ℝ) < $b by norm_num)
      (by norm_num [map_ofNat] <;> ring))
  let a ← intTerm ((p.coeff (p.size - 1) * (p.size - 1 : Nat)) / cs[1]!.back!)
  let pos := variations (cs.map Array.back!)
  let neg := variations (cs.map fun c => c.back! * (-1) ^ (c.size - 1))
  let n := Syntax.mkNumLit (toString (neg - pos))
  `(by
    $facts:tactic*
    exact Sturm.RemainderChain.card_rootSet (f := $pStx) (n := $n) $cert
      (show (0 : ℝ) < $a by norm_num)
      (by simp [Polynomial.derivative_add, Polynomial.derivative_mul,
        Polynomial.derivative_pow, map_ofNat] <;> ring)
      (by norm_num [map_ofNat, $unfolds,*] <;> ring)
      (by simp only [Sturm.sturmVarNegInf, Sturm.sturmVarPosInf,
            List.map_cons, List.map_nil, *]
          norm_num [Sturm.signVariations, Sturm.countSignChanges]))

/-- Compute and certify the number of distinct real roots of a closed squarefree
integer-coefficient polynomial over `ℚ` of positive degree. -/
elab "real_root_count " pStx:term : term <= expectedType? => withRef pStx do
  let pTy ← elabType (← `(Polynomial ℚ))
  let e ← elabTermEnsuringType pStx pTy
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasFVar || e.hasExprMVar then
    throwError "real_root_count: expected a closed polynomial"
  let names ← IO.mkRef (#[] : Array Name)
  let p ← Mathlib.Tactic.RealRootCount.Parse.parsePoly "real_root_count" true 16 e
    (fun n => names.modify (fun ns => if ns.contains n then ns else ns.push n))
  let unfolds ← (← names.get).mapM fun n => `(Parser.Tactic.simpLemma| $(mkIdent n):term)
  elabTermEnsuringType (← emit pStx p unfolds) expectedType?

/-- Prove a goal `Fintype.card (p.rootSet ℝ) = n` by a checked Sturm chain.
The polynomial must be closed, squarefree, of positive degree, and have integer coefficients. -/
elab "real_root_count" : tactic => do
  let goal ← Tactic.getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (_, lhs, _) := target.eq? |
    throwError "real_root_count: expected a goal `Fintype.card (p.rootSet ℝ) = n`"
  unless lhs.isAppOf ``Fintype.card do
    throwError "real_root_count: expected a goal `Fintype.card (p.rootSet ℝ) = n`"
  let some roots := lhs.getAppArgs[0]!.find? (·.isAppOf ``Polynomial.rootSet) |
    throwError "real_root_count: expected a goal `Fintype.card (p.rootSet ℝ) = n`"
  let p ← PrettyPrinter.delab roots.getAppArgs[2]!
  let proof ← elabTermEnsuringType (← `(real_root_count $p)) (some target)
  goal.assign proof
  Tactic.replaceMainGoal []

end Mathlib.Tactic.RealRootCount
