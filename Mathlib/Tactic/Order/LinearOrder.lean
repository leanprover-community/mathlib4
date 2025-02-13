import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Basic
import Qq

namespace Mathlib.Tactic.Order

open Lean Qq Elab Meta Tactic

inductive AtomicRel
| eq | ne | le | nle | lt | nlt
deriving Inhabited

structure AtomicFact where
  lhs : Nat
  rhs : Nat
  rel : AtomicRel
  proof : Expr
deriving Inhabited

abbrev Graph := Array (Array AtomicFact)

instance : ToString AtomicFact where
  toString := fun fa => match fa.rel with
  | .eq => s!"{fa.lhs} = {fa.rhs}"
  | .ne => s!"{fa.lhs} ≠ {fa.rhs}"
  | .le => s!"{fa.lhs} ≤ {fa.rhs}"
  | .lt => s!"{fa.lhs} < {fa.rhs}"
  | .nle => s!"¬ {fa.lhs} ≤ {fa.rhs}"
  | .nlt => s!"¬ {fa.lhs} < {fa.rhs}"

/-- Returns a map from a type to TODO. -/
def collectAtoms (g : MVarId) :
    MetaM <| Std.HashMap Expr <| Std.HashMap Nat Expr × Array AtomicFact := g.withContext do
  let ctx ← getLCtx
  let res : (Std.HashMap Expr <| Std.HashMap Expr Nat × Array AtomicFact) ←
  ctx.foldlM (init := Std.HashMap.empty) fun res ldecl => do
    let ⟨0, type, expr⟩ := ← inferTypeQ ldecl.toExpr | return res
    match type with
    | ~q(@Eq $α $x $y) =>
      return update res α x y .eq expr
    | ~q(@LE.le $α $inst $x $y) =>
      return update res α x y .le expr
    | ~q(@LT.lt $α $inst $x $y) =>
      return update res α x y .lt expr
    | ~q(@Ne $α $x $y) =>
      return update res α x y .ne expr
    | ~q(Not $p) =>
      match p with
      | ~q(@LE.le $α $inst $x $y) =>
        return update res α x y .nle expr
      | ~q(@LT.lt $α $inst $x $y) =>
        return update res α x y .nlt expr
    | _ => return res
  return res.map fun _ (atomToIdx, facts) =>
    let idxToAtom : Std.HashMap Nat Expr := atomToIdx.fold (init := .empty) fun acc key value =>
      acc.insert value key
    (idxToAtom, facts)
where update (res : Std.HashMap Expr <| Std.HashMap Expr Nat × Array AtomicFact) (type x y : Expr)
    (rel : AtomicRel) (expr : Expr) : Std.HashMap Expr <| Std.HashMap Expr Nat × Array AtomicFact :=
  let res := res.insertIfNew type (Std.HashMap.empty, #[])
  res.modify type fun (atomToIdx, facts) =>
    let atomToIdx := atomToIdx.insertIfNew x atomToIdx.size
    let atomToIdx := atomToIdx.insertIfNew y atomToIdx.size
    let facts := facts.push <| ⟨atomToIdx.get! x, atomToIdx.get! y, rel, expr⟩
    (atomToIdx, facts)

private lemma le_of_eq_symm {α : Type} [Preorder α] {x y : α} (h : x = y) : y ≤ x :=
  le_of_eq (Eq.symm h)

private lemma not_lt_of_not_le {α : Type} [Preorder α] {x y : α} (h : ¬(x ≤ y)) : ¬(x < y) := by
  intro h'
  exact h h'.le

private lemma le_of_not_lf_le {α : Type} [PartialOrder α] {x y : α} (h1 : ¬(x < y)) (h2 : x ≤ y) :
    y ≤ x := by
  rw [not_lt_iff_not_le_or_ge] at h1
  rcases h1 with (h1 | h1)
  · exact False.elim (h1 h2)
  · assumption

-- Note: Here `Preorder` is enough. The only problem is that `x = y` is not equivalent
-- to `x ≤ y ∧ y ≤ x`, it's just implication.
def preprocessFactsPartial (g : MVarId) (facts : Array AtomicFact) :
    MetaM <| Array AtomicFact := g.withContext do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact.rel with
    | .lt =>
      res := res.push ⟨fact.lhs, fact.rhs, .ne, ← mkAppM ``LT.lt.ne #[fact.proof]⟩
      res := res.push ⟨fact.lhs, fact.rhs, .le, ← mkAppM ``LT.lt.le #[fact.proof]⟩
    | .nle =>
      res := res.push ⟨fact.lhs, fact.rhs, .ne, ← mkAppM ``ne_of_not_le #[fact.proof]⟩
      res := res.push ⟨fact.lhs, fact.rhs, .nlt, ← mkAppM ``not_lt_of_not_le #[fact.proof]⟩
    | .eq =>
      res := res.push ⟨fact.lhs, fact.rhs, .le, ← mkAppM ``le_of_eq #[fact.proof]⟩
      res := res.push ⟨fact.rhs, fact.lhs, .le, ← mkAppM ``le_of_eq_symm #[fact.proof]⟩
    | _ =>
      res := res.push fact
  return res

/-- Replace `x < y`, `¬ (x ≤ y)`, `¬ (x < y)` and `x = y` with equivalent facts involving only
`≤` and `≠` in linear order. -/
def preprocessFactsLinear (g : MVarId) (facts : Array AtomicFact) :
    MetaM <| Array AtomicFact := g.withContext do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact.rel with
    | .lt =>
      res := res.push ⟨fact.lhs, fact.rhs, .ne, ← mkAppM ``LT.lt.ne #[fact.proof]⟩
      res := res.push ⟨fact.lhs, fact.rhs, .le, ← mkAppM ``LT.lt.le #[fact.proof]⟩
    | .nle =>
      res := res.push ⟨fact.lhs, fact.rhs, .ne, ← mkAppM ``ne_of_not_le #[fact.proof]⟩
      res := res.push ⟨fact.rhs, fact.lhs, .le, ← mkAppM ``le_of_not_ge #[fact.proof]⟩
    | .nlt =>
      res := res.push ⟨fact.rhs, fact.lhs, .le, ← mkAppM ``le_of_not_lt #[fact.proof]⟩
    | .eq =>
      res := res.push ⟨fact.lhs, fact.rhs, .le, ← mkAppM ``le_of_eq #[fact.proof]⟩
      res := res.push ⟨fact.rhs, fact.lhs, .le, ← mkAppM ``le_of_eq_symm #[fact.proof]⟩
    | _ =>
      res := res.push fact
  return res

def constructLeGraph (nVertexes : Nat) (facts : Array AtomicFact) :
    Graph := Id.run do
  let mut res : Graph := Array.mkArray nVertexes #[]
  for fact in facts do
    match fact.rel with
    | .le =>
      res := res.modify fact.lhs fun edges => edges.push fact
    | _ => continue
  return res

def inverseGraph (g : Graph) : Graph := Id.run do
  let mut res := Array.mkArray g.size #[]
  for v in [:g.size] do
    for edge in g[v]! do
      res := res.modify edge.rhs fun edges => edges.push ⟨edge.rhs, edge.lhs, edge.rel, edge.proof⟩
  return res

structure DFSState where
  visited : Array Bool

structure FindToutDFSState extends DFSState where
  tout : Array Nat
  time : Nat

partial def findToutDFS (g : Graph) (v : Nat) : StateM FindToutDFSState Unit := do
  modify fun s => {s with visited := s.visited.set! v true}
  for edge in g[v]! do
    let u := edge.rhs
    if !(← get).visited[u]! then
      findToutDFS g u
  modify fun s => {s with tout := s.tout.set! v s.time}
  modify fun s => {s with time := s.time + 1}

def findToutImp (g : Graph) : StateM FindToutDFSState Unit := do
  for v in [:g.size] do
    if !(← get).visited[v]! then
      findToutDFS g v

def findTout (g : Graph) : Array Nat :=
  let s : FindToutDFSState := {
    visited := mkArray g.size false
    tout := mkArray g.size 0
    time := 0
  }
  (findToutImp g).run s |>.snd.tout

def toutToOrder (tout : Array Nat) : Array Nat := Id.run do
  let nVertexes := tout.size
  let mut res := mkArray nVertexes 0
  for v in [:nVertexes] do
    res := res.set! (nVertexes - tout[v]! - 1) v
  return res

structure CondenseDFSState extends DFSState where
  condensation : Array Nat

partial def condenseDFS (g : Graph) (c : Nat) (v : Nat) : StateM CondenseDFSState Unit := do
  modify fun s => {s with visited := s.visited.set! v true, condensation := s.condensation.set! v c}
  for edge in g[v]! do
    let u := edge.rhs
    if !(← get).visited[u]! then
      condenseDFS g c u

def condenseImp (g : Graph) (order : Array Nat) : StateM CondenseDFSState Unit := do
  for v in order do
    if !(← get).visited[v]! then
      condenseDFS g v v

def condense (graph graphInv : Graph) : Array Nat :=
  let tout := findTout graph
  let order := toutToOrder tout
  let s : CondenseDFSState := {
    visited := mkArray graph.size false
    condensation := mkArray graph.size graph.size
  }
  (condenseImp graphInv order).run s |>.snd.condensation

def findContradictoryNe (condensation : Array Nat) (facts : Array AtomicFact) : Option AtomicFact :=
  facts.find? fun fact =>
    match fact.rel with
    | .ne => condensation[fact.lhs]! == condensation[fact.rhs]!
    | _ => false

partial def buildTransitiveLeProofDFS (g : Graph) (v t : Nat) (tExpr : Expr) :
    StateT DFSState MetaM (Option Expr) := do
  modify fun s => {s with visited := s.visited.set! v true}
  if v == t then
    return ← mkAppM ``le_refl #[tExpr]
  for edge in g[v]! do
    let u := edge.rhs
    if !(← get).visited[u]! then
      match ← buildTransitiveLeProofDFS g u t tExpr with
      | .some pf => return .some <| ← mkAppM ``le_trans #[edge.proof, pf]
      | .none => continue
  return .none

def buildTransitiveLeProof (g : Graph) (s t : Nat) (tExpr : Expr) : MetaM (Option Expr) := do
  let state : DFSState := ⟨mkArray g.size false⟩
  (buildTransitiveLeProofDFS g s t tExpr).run' state

def updateGraphWithNlt (g : Graph) (idxToAtom : Std.HashMap Nat Expr) (facts : Array AtomicFact) :
    MetaM Graph := do
  let nltFacts := facts.filter fun fact => match fact.rel with | .nlt => true | _ => false
  let mut used : Array Bool := mkArray nltFacts.size false
  let mut res := g
  while true do
    let mut changed : Bool := false
    for i in [:nltFacts.size] do
      if used[i]! then
        continue
      let fact := nltFacts[i]!
      let .some pf ← buildTransitiveLeProof g fact.lhs fact.rhs (idxToAtom.get! fact.rhs) | continue
      changed := true
      used := used.set! i true
      let newFact : AtomicFact := ⟨fact.rhs, fact.lhs, .le,
        ← mkAppM ``le_of_not_lf_le #[fact.proof, pf]⟩
      res := res.modify fact.rhs fun edges => edges.push newFact
    if !changed then
      break
  return res

inductive OrderType
| lin | part | pre

def findBestInstance (type : Expr) : MetaM <| Option OrderType := do
  if (← synthInstance? (← mkAppM ``LinearOrder #[type])).isSome then
    return .some .lin
  if (← synthInstance? (← mkAppM ``PartialOrder #[type])).isSome then
    return .some .part
  if (← synthInstance? (← mkAppM ``Preorder #[type])).isSome then
    return .some .pre
  return .none

elab "order" : tactic => focus do
  let g ← getMainGoal
  let .some g ← g.falseOrByContra | return
  setGoals [g]
  let TypeToAtoms ← collectAtoms g
  g.withContext do
  for (type, (idxToAtom, facts)) in TypeToAtoms do
    let .some orderType ← findBestInstance type | continue
    let facts : Array AtomicFact ← match orderType with
    | .lin => preprocessFactsLinear g facts
    | .part => preprocessFactsPartial g facts
    | .pre => throwError "Preorders are not implemented"
    let mut graph := constructLeGraph idxToAtom.size facts
    if let .part := orderType then
      graph ← updateGraphWithNlt graph idxToAtom facts
    let graphInv := inverseGraph graph
    let condensation := condense graph graphInv
    let .some contNe := findContradictoryNe condensation facts | throwError "No contradiction found"
    let .some pf1 ← buildTransitiveLeProof graph contNe.lhs contNe.rhs
      (idxToAtom.get! contNe.rhs) | throwError "bug"
    let .some pf2 ← buildTransitiveLeProof graph contNe.rhs contNe.lhs
      (idxToAtom.get! contNe.lhs) | throwError "bug"
    let pf3 ← mkAppM ``le_antisymm #[pf1, pf2]
    g.assign <| mkApp contNe.proof pf3
    return
  throwError "No contradiction found"

end Mathlib.Tactic.Order
