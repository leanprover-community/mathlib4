/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Analysis.Polynomial.Sturm.Certificate
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Polynomial.Hex
public meta import Mathlib.Tactic.Polynomial.Hex
public meta import HexRealRoots.Chain

/-!
# Certified real root counts

`real_root_count (p : ℚ[X])` proves `Fintype.card (p.rootSet ℝ) = n` for a closed,
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
  let mut t ← `((0 : Polynomial ℝ))
  for i in [:cs.size] do
    if cs[i]! != 0 then
      let c ← intTerm cs[i]!
      let k := Syntax.mkNumLit (toString i)
      t ← `($t + $c * Polynomial.X ^ $k)
  return t

private def coeffs (p : Hex.ZPoly) : Array Int :=
  (List.range p.size).toArray.map p.coeff

-- Untrusted rational long division, followed by clearing denominators.
private def division (p q r : Array Int) : Int × Array Int × Int := Id.run do
  let mut rem := p.map (fun (c : Int) => (c : Rat))
  let mut quo : Array Rat := Array.replicate p.size 0
  for k in [:p.size] do
    let i := p.size - 1 - k
    if i + 1 ≥ q.size then
      let c := rem[i]! / (q.back! : Rat)
      let j := i + 1 - q.size
      quo := quo.set! j c
      for t in [:q.size] do
        rem := rem.set! (j + t) (rem[j + t]! - c * (q[t]! : Rat))
  let b := -rem[r.size - 1]! / (r.back! : Rat)
  let a := quo.foldl (fun n c => n.lcm c.den) b.den
  return (a, quo.map (fun c => (c * (a : Rat)).num), (b * (a : Rat)).num)

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
  if p.size < 2 then
    throwError "real_root_count: expected a squarefree polynomial of positive degree"
  let polys :=  (Hex.ZPoly.sturmChain p).set! 0 p
  if polys.size < 2 || polys.back!.size != 1 then
    throwError "real_root_count: expected a squarefree polynomial of positive degree"
  let cs := Array.map coeffs polys
  let ps ← cs.mapM polyTerm
  let mut facts : Array (TSyntax `tactic) := #[]
  let mut nonzeros : Array (TSyntax `term) := #[]
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
      intro hz; rw [hz, Polynomial.coeff_zero] at $hc:ident; norm_num at $hc:ident))
    nonzeros := nonzeros.push (← `($hn))
  let m := ps.size
  let c ← intTerm cs.back!.back!
  let mut cert ← `(show Sturm.RemainderChain [$(ps[m-2]!), $(ps[m-1]!)] from by
    convert Sturm.RemainderChain.pair $(nonzeros[m-2]!)
      (show ($c : ℝ) ≠ 0 by norm_num) using 1 <;> norm_num)
  for k in [:m-2] do
    let i := m - 3 - k
    let (a, d, b) := division cs[i]! cs[i+1]! cs[i+2]!
    let a ← intTerm a
    let b ← intTerm b
    let d ← polyTerm d
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
elab "real_root_count " pStx:term : term <= expectedType? => do
  let pTy ← elabType (← `(Polynomial ℚ))
  let e ← elabTermEnsuringType pStx pTy
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasFVar || e.hasExprMVar then
    throwError "real_root_count: expected a closed polynomial"
  let names ← IO.mkRef (#[] : Array Name)
  let p ← Mathlib.Tactic.Polynomial.Hex.parsePoly "real_root_count" true 16 e
    (fun n => names.modify (fun ns => if ns.contains n then ns else ns.push n))
  let unfolds ← (← names.get).mapM fun n => `(Parser.Tactic.simpLemma| $(mkIdent n):term)
  elabTerm (← emit pStx p unfolds) expectedType?

end Mathlib.Tactic.RealRootCount
