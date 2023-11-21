import Mathlib.Lean.Expr.Basic
import Mathlib.Logic.Equiv.Basic
import Qq

namespace Lean.Expr

open Lean Meta

inductive ProdTree where
  | type (tp : Expr) (l : Level)
  | prod (fst snd : ProdTree) (lfst lsnd : Level)

def ProdTree.getType : ProdTree → Expr
  | type tp _ => tp
  | prod fst snd u v => mkAppN (.const ``Prod [u,v]) #[fst.getType, snd.getType]


def ProdTree.size : ProdTree → Nat
  | type _ _ => 1
  | prod fst snd _ _ => fst.size + snd.size

def mkProdTree (e : Expr) : MetaM ProdTree :=
  match e with
    | .app (.app (.const ``Prod [u,v]) X) Y => do
        return .prod (← X.mkProdTree) (← Y.mkProdTree) u v
    | X => do
      let .sort (.succ u) ← inferType X | throwError "Type expected."
      return .type X u

def ProdTree.unpack (t : Expr) : ProdTree → MetaM (List Expr)
  | type _ _ => return [t]
  | prod fst snd u v => do
      let fst' ← fst.unpack <| mkAppN (.const ``Prod.fst [u,v]) #[fst.getType, snd.getType, t]
      let snd' ← snd.unpack <| mkAppN (.const ``Prod.snd [u,v]) #[fst.getType, snd.getType, t]
      return fst' ++ snd'

def ProdTree.pack (ts : List Expr) : ProdTree → MetaM Expr
  | type tp _ => do
    match ts with
      | [] => throwError "empty list"
      | [a] =>
        if ← isDefEq tp (← inferType a) then return a
        else throwError "Types are different"
      | _ => throwError "Wrong size"
  | prod fst snd u v => do
    let fstSize := fst.size
    let sndSize := snd.size
    unless ts.length == fstSize + sndSize do throwError "Wrong size"
    let tsfst := ts.toArray[:fstSize] |>.toArray.toList
    let tssnd := ts.toArray[fstSize:] |>.toArray.toList
    let mk : Expr := mkAppN (.const ``Prod.mk [u,v]) #[fst.getType, snd.getType]
    return .app (.app mk (← fst.pack tsfst)) (← snd.pack tssnd)

def mkFun (a b : Expr) : MetaM Expr := do
  let pa ← a.mkProdTree
  let pb ← b.mkProdTree
  return .lam `t a (← pb.pack <| (← pa.unpack <| .bvar 0)) .default

def mkEquiv (a b : Expr) : MetaM Expr := do
  let .sort (u) ← inferType a | throwError "Type expected."
  let .sort (v) ← inferType b | throwError "Type expected."
  return mkAppN (.const ``Equiv.mk [u,v])
    #[a, b, ← mkFun a b, ← mkFun b a, .app (.const ``rfl [u]) a, .app (.const ``rfl [v]) b]

elab "associate(" a:term "," b:term ")" : term => do
  let a ← Elab.Term.elabTerm a none
  let b ← Elab.Term.elabTerm b none
  mkEquiv a b

example {α β γ δ : Type*} (a : α) (b : β) (g : γ) (d : δ) :
  associate((α × β) × (γ × δ), α × (β × γ) × δ) ((a,b),(g,d)) = (a,(b,g),d) := rfl

end Lean.Expr
