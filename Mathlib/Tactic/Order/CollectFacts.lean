import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Lattice
import Qq

namespace Mathlib.Tactic.Order

open Lean Qq Elab Meta Tactic

/-- A structure for storing facts about variables. -/
inductive AtomicFact
| eq (lhs : Nat) (rhs : Nat) (proof : Expr)
| ne (lhs : Nat) (rhs : Nat) (proof : Expr)
| le (lhs : Nat) (rhs : Nat) (proof : Expr)
| nle (lhs : Nat) (rhs : Nat) (proof : Expr)
| lt (lhs : Nat) (rhs : Nat) (proof : Expr)
| nlt (lhs : Nat) (rhs : Nat) (proof : Expr)
| isTop (idx : Nat)
| isBot (idx : Nat)
| isInf (lhs : Nat) (rhs : Nat) (res : Nat)
| isSup (lhs : Nat) (rhs : Nat) (res : Nat)
deriving Inhabited, BEq

-- For debugging purposes.
instance : ToString AtomicFact where
  toString fa := match fa with
  | .eq lhs rhs _ => s!"{lhs} = {rhs}"
  | .ne lhs rhs _ => s!"{lhs} ≠ {rhs}"
  | .le lhs rhs _ => s!"{lhs} ≤ {rhs}"
  | .nle lhs rhs _ => s!"¬ {lhs} ≤ {rhs}"
  | .lt lhs rhs _ => s!"{lhs} < {rhs}"
  | .nlt lhs rhs _ => s!"¬ {lhs} < {rhs}"
  | .isTop idx => s!"{idx} = ⊤"
  | .isBot idx => s!"{idx} = ⊥"
  | .isInf lhs rhs res => s!"{lhs} ⊓ {rhs} = {res}"
  | .isSup lhs rhs res => s!"{lhs} ⊔ {rhs} = {res}"

abbrev CollectFactsState := Std.HashMap Expr <| Std.HashMap Expr Nat × Array AtomicFact
abbrev CollectFactsM := StateT CollectFactsState MetaM

def isTop {u : Level} (type : Q(Type u)) (x : Q($type)) : MetaM Bool := do
  try
    let leInst ← synthInstanceQ (q(LE $type))
    let inst ← synthInstanceQ (q(OrderTop $type))
    let top := q((@OrderTop.toTop $type $leInst $inst).top)
    return ← isDefEq x top
  catch _ =>
    return false

def isBot {u : Level} (type : Q(Type u)) (x : Q($type)) : MetaM Bool := do
  try
    let leInst ← synthInstanceQ (q(LE $type))
    let inst ← synthInstanceQ (q(OrderBot $type))
    let bot := q((@OrderBot.toBot $type $leInst $inst).bot)
    return ← isDefEq x bot
  catch _ =>
    return false

def getSupArgs? {u : Level} (type : Q(Type u)) (x : Q($type)) :
    MetaM <| Option (Q($type) × Q($type)) := do
  try
    let inst ← synthInstanceQ q(SemilatticeSup $type)
    let a ← mkFreshExprMVarQ type
    let b ← mkFreshExprMVarQ type
    let sup := q(@SemilatticeSup.sup $type $inst $a $b)
    if ← isDefEq x sup then
      return .some (← instantiateMVars a, ← instantiateMVars b)
    else
      return .none
  catch _ =>
    return .none

def getInfArgs? {u : Level} (type : Q(Type u)) (x : Q($type)) :
    MetaM <| Option (Q($type) × Q($type)) := do
  try
    let inst ← synthInstanceQ q(SemilatticeInf $type)
    let a ← mkFreshExprMVarQ type
    let b ← mkFreshExprMVarQ type
    let inf := q(@SemilatticeInf.inf $type $inst $a $b)
    if ← isDefEq x inf then
      return .some (← instantiateMVars a, ← instantiateMVars b)
    else
      return .none
  catch _ =>
    return .none

partial def addAtom {u : Level} (type : Q(Type u)) (x : Q($type)) : CollectFactsM Nat := do
  modify fun res => res.insertIfNew type (Std.HashMap.empty, #[])
  modify fun res => res.modify type fun (atomToIdx, facts) =>
    let atomToIdx := atomToIdx.insertIfNew x atomToIdx.size
    (atomToIdx, facts)
  let idx := (← get).get! type |>.fst.get! x
  if idx + 1 == ((← get).get! type).fst.size then -- if new atom
    if ← isTop type x then
      modify fun res => res.modify type fun (atomToIdx, facts) =>
        (atomToIdx, facts.push <| .isTop idx)
    if ← isBot type x then
      modify fun res => res.modify type fun (atomToIdx, facts) =>
        (atomToIdx, facts.push <| .isBot idx)
    if let .some (a, b) := ← getSupArgs? type x then
      let aIdx ← addAtom type a
      let bIdx ← addAtom type b
      modify fun res => res.modify type fun (atomToIdx, facts) =>
        (atomToIdx, facts.push <| .isSup aIdx bIdx idx)
    if let .some (a, b) := ← getInfArgs? type x then
      let aIdx ← addAtom type a
      let bIdx ← addAtom type b
      modify fun res => res.modify type fun (atomToIdx, facts) =>
        (atomToIdx, facts.push <| .isInf aIdx bIdx idx)
  return idx

def addFact (type : Expr) (fact : AtomicFact) : CollectFactsM Unit :=
  modify fun res => res.modify type fun (atomToIdx, facts) =>
    (atomToIdx, facts.push fact)

-- TODO: Split conjunctions.
def collectFactsImp (g : MVarId) : CollectFactsM Unit := g.withContext do
  let ctx ← getLCtx
  for ldecl in ctx do
    if ldecl.isImplementationDetail then
      continue
    let ⟨0, type, expr⟩ := ← inferTypeQ ldecl.toExpr | continue
    match type with
    | ~q(@Eq ($α : Type _) $x $y) =>
      if (← synthInstance? (q(Preorder $α))).isSome then
        let xIdx := ← addAtom α x
        let yIdx := ← addAtom α y
        addFact α <| .eq xIdx yIdx expr
    | ~q(@LE.le $α $inst $x $y) =>
      let xIdx := ← addAtom α x
      let yIdx := ← addAtom α y
      addFact α <| .le xIdx yIdx expr
    | ~q(@LT.lt $α $inst $x $y) =>
      let xIdx := ← addAtom α x
      let yIdx := ← addAtom α y
      addFact α <| .lt xIdx yIdx expr
    | ~q(@Ne ($α : Type _) $x $y) =>
      if (← synthInstance? (q(Preorder $α))).isSome then
        let xIdx := ← addAtom α x
        let yIdx := ← addAtom α y
        addFact α <| .ne xIdx yIdx expr
    | ~q(Not $p) =>
      match p with
      | ~q(@LE.le $α $inst $x $y) =>
        let xIdx := ← addAtom α x
        let yIdx := ← addAtom α y
        addFact α <| .nle xIdx yIdx expr
      | ~q(@LT.lt $α $inst $x $y) =>
        let xIdx := ← addAtom α x
        let yIdx := ← addAtom α y
        addFact α <| .nlt xIdx yIdx expr

/-- Collects facts from the local context. For each occurring type `α`, the returned map contains
a pair `(idxToAtom, facts)`, where the map `idxToAtom` converts indices to found
atomic expressions of type `α`, and `facts` contains all collected `AtomicFact`s about them. -/
def collectFacts (g : MVarId) :
    MetaM <| Std.HashMap Expr <| Std.HashMap Nat Expr × Array AtomicFact := g.withContext do
  let res := (← (collectFactsImp g).run Std.HashMap.empty).snd
  return res.map fun _ (atomToIdx, facts) =>
    let idxToAtom : Std.HashMap Nat Expr := atomToIdx.fold (init := .empty) fun acc key value =>
      acc.insert value key
    (idxToAtom, facts)

end Mathlib.Tactic.Order
