module

public import Mathlib.Tactic.IntervalArithmetic.Certificate

set_option linter.style.header false

public meta section

namespace IntervalArithmetic

open Lean Expr Meta Elab Command Tactic

syntax (name := interval) "interval " ident num : tactic

def mkIntervalHyps (decl : IntervalArithmeticDecl) (α β φ n : Expr) :
    MetaM (FVarIdMap (Expr × Expr)) := do
  let lctx ← getLCtx
  let mut rs : Array FVarId := #[]
  let mut hs : FVarIdMap (Array (Expr × Expr)) := {}
  for ldecl in lctx do
    let t ← instantiateMVars ldecl.type
    if ← isDefEq t β then
      let rId := ldecl.fvarId
      rs := rs.push rId
    else if let some ⟨rId, x, hrx⟩ ← ldecl.toExpr.ineqToIntervalHyp? decl n then
      --log m!"Hello? var : {mkFVar rId}, interval : {x}, proof: {hrx}"
      if hs.contains rId then
        hs := hs.modify rId (Array.push · (x, hrx))
      else
        hs := hs.insert rId #[(x, hrx)]
    else if let some ⟨r, x, φ'⟩ := memIntervaltoSet? t then
      if let some rId := r.fvarId? then
        if ! x.hasFVar ∧ (← withNewMCtxDepth <| isDefEq φ φ') then
          if hs.contains rId then
            hs := hs.modify rId (Array.push · (x, ldecl.toExpr))
          else
            hs := hs.insert rId #[(x, ldecl.toExpr)]
  let mut hyps : FVarIdMap (Expr × Expr) := {}
  for rId in rs do
    let mut x ← mkAppM ``Interval.univ #[α]
    let mut h ← mkAppM ``Interval.mem_toSet_univ #[φ, mkFVar rId]
    if hc : hs.contains rId then
      for (y, hry) in hs.get rId hc do
        x := ← mkAppM ``Interval.inter #[x, y]
        h := ← mkAppM ``Interval.inter_inclusion #[h, hry]
    hyps := hyps.insert rId (x, h)
  return hyps

-- maybe taken in a select array of interval hypotheses
def interIntervalHyps (α β φ : Expr) : MetaM (FVarIdMap (Expr × Expr)) := do
  let lctx ← getLCtx
  let mut rs : Array FVarId := #[]
  let mut hs : FVarIdMap (Array (Expr × Expr)) := {}
  for ldecl in lctx do
    let t ← instantiateMVars ldecl.type
    if ← isDefEq t β then
      let rId := ldecl.fvarId
      rs := rs.push rId
    else if let some ⟨r, x, φ'⟩ := memIntervaltoSet? t then
      if let some rId := r.fvarId? then
        if ! x.hasFVar ∧ (← withNewMCtxDepth <| isDefEq φ φ') then
          if hs.contains rId then
            hs := hs.modify rId (Array.push · (x, ldecl.toExpr))
          else
            hs := hs.insert rId #[(x, ldecl.toExpr)]
  let mut hyps : FVarIdMap (Expr × Expr) := {}
  for rId in rs do
    let mut x ← mkAppM ``Interval.univ #[α]
    let mut h ← mkAppM ``Interval.mem_toSet_univ #[φ, mkFVar rId]
    if hc : hs.contains rId then
      for (y, hry) in hs.get rId hc do
        x := ← mkAppM ``Interval.inter #[x, y]
        h := ← mkAppM ``Interval.inter_inclusion #[h, hry]
    hyps := hyps.insert rId (x, h)
  return hyps

elab_rules : tactic
  | `(tactic| interval $decl:ident $n:num) => withMainContext do
    let some decl ← getIntervalArithmeticDecl? decl.getId
      | throwError m!"Unknown interval arithmetic declaration `{decl}`"
    let α ← mkConstWithFreshMVarLevels decl.intervalType
    let β ← mkConstWithFreshMVarLevels decl.setType
    let φ ← mkConstWithFreshMVarLevels decl.embedding
    let hφ ← mkConstWithFreshMVarLevels decl.strictMono
    let n := mkNatLit n.getNat
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let some ⟨ineq, _, e₁, e₂⟩ := IntervalArithmetic.ineq? t
      | throwError m!"The goal is not an inequality (≤ or <)"
    let hyps ← mkIntervalHyps decl α β φ n
    -- e₁ process:
    let cert₁ ← e₁.toIntervalArithmeticCertificate decl
    let mut xs := #[]
    let mut hrxs := #[]
    for rId in cert₁.fvars do
      let ⟨x, hrx⟩ := hyps.get! rId
      xs := xs.push x
      hrxs := hrxs.push hrx
    -- e₂ process:
    let x ← instantiateMVars <| mkAppN cert₁.comp (#[n] ++ xs)
    let hrx ← instantiateMVars <| mkAppN cert₁.proof (#[n] ++ xs ++ hrxs)
    let cert₂ ← e₂.toIntervalArithmeticCertificate decl
    let mut ys := #[]
    let mut hrys := #[]
    for sId in cert₂.fvars do
      let ⟨y, hsy⟩ := hyps.get! sId
      ys := ys.push y
      hrys := hrys.push hsy
    let y ← instantiateMVars <| mkAppN cert₂.comp (#[n] ++ ys)
    let hsy ← instantiateMVars <| mkAppN cert₂.proof (#[n] ++ ys ++ hrys)
    -- build proof
    match ineq with
      | .le => do
        let x_le_y ← mkAppM ``Interval.le #[x, y]
        let hxy ← mkDecideProof x_le_y
        let g_proof ← mkAppM ``Interval.le_of_le #[hφ, hrx, hsy, hxy]
        g.assign g_proof
        replaceMainGoal []
      | .lt => do
        let x_lt_y ← mkAppM ``Interval.lt #[x, y]
        let hxy ← mkDecideProof x_lt_y
        let g_proof ← mkAppM ``Interval.lt_of_lt #[hφ, hrx, hsy, hxy]
        g.assign g_proof
        replaceMainGoal []

end IntervalArithmetic
