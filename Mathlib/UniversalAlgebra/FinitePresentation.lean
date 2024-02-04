import Std.Data.List.Basic
import Mathlib.UniversalAlgebra.LawvereTheory

structure RFLP where
  name : String
  sortNames : List String
  opNames : List (String × List (Fin sortNames.length) × Fin sortNames.length)

namespace RFLP

variable (R : RFLP)

def numSorts := R.sortNames.length

abbrev Srt := Fin R.numSorts

def ops (L : List (Fin R.numSorts)) (X : R.Srt) :
    List String :=
  R.opNames.filterMap fun (nm,l,x) =>
    if L = l ∧ X = x then some nm else none

def numOps (L : List R.Srt) (X : R.Srt) :=
  R.ops L X |>.length

abbrev Op (L : List R.Srt) (X : R.Srt) : Type :=
  Fin (R.numOps L X)

abbrev Word (A B : List R.Srt) := _root_.LawvereWord R.Op A B

end RFLP

structure FiniteLawverePresentation extends RFLP where
  relNames : List (String × (A B : List toRFLP.Srt) × toRFLP.Word A B × toRFLP.Word A B)

syntax sortName := ident
syntax sortDescr := sortName ";"
syntax opName := ident
syntax opDescr := opName ":" sepBy(sortName,",") " → " sortName

declare_syntax_cat prod_word
syntax sortName : prod_word
syntax "⊥" : prod_word
syntax prod_word "×" prod_word : prod_word
syntax "[ProdWord|" prod_word "]" : term

declare_syntax_cat lawvere_word
syntax "[of" opName "]" : lawvere_word
syntax "[id" prod_word "]" : lawvere_word
syntax "[comp" lawvere_word "," lawvere_word "]" : lawvere_word
syntax "[fst" prod_word "," prod_word "]" : lawvere_word
syntax "[snd" prod_word "," prod_word "]" : lawvere_word
syntax "[lift" lawvere_word "," lawvere_word "]" : lawvere_word
syntax "[toNil" prod_word "]" : lawvere_word

syntax relName := ident
syntax relDescr := relName ":" lawvere_word "=" lawvere_word

syntax (name := flpStx) "[RFLP|"
  "NAME:" ident
  ("SORTS:" sepBy(sortName,","))?
  ("OPS:" sepBy(opDescr,","))?
"]" : term

open Qq Lean Elab Term

def elabSortName (nm : TSyntax `sortName) : TermElabM String :=
  match nm with
  | `(sortName|$s:ident) => return s.getId.toString
  | _ => throwUnsupportedSyntax

def elabOpName (nm : TSyntax `opName) : TermElabM String :=
  match nm with
  | `(opName|$s:ident) => return s.getId.toString
  | _ => throwUnsupportedSyntax

def elabRelName (nm : TSyntax `relName) : TermElabM String :=
  match nm with
  | `(relName|$s:ident) => return s.getId.toString
  | _ => throwUnsupportedSyntax

def elabOpDescr (descr : TSyntax `opDescr) : TermElabM (String × List String × String) :=
  match descr with
  | `(opDescr|$nm : $nms,* → $out) => do
    let nm ← elabOpName nm
    let nms ← nms.getElems.mapM elabSortName
    let out ← elabSortName out
    return (nm, nms.toList, out)
  | _ => throwUnsupportedSyntax

def elabRelDescrAux (descr : TSyntax `relDescr) :
    TermElabM (String × TSyntax `lawvere_word × TSyntax `lawvere_word) :=
  match descr with
  | `(relDescr|$nm : $lhs = $rhs) => return (← elabRelName nm, lhs, rhs)
  | _ => throwUnsupportedSyntax

def RFLP.elabSort (rflp : RFLP) : TermElabM Expr := do
  return .app (.const ``Fin []) (toExpr <| rflp.sortNames.length)

def RFLP.elabOp (rflp : RFLP) : TermElabM Expr :=
  Meta.withLocalDecls
    #[(`L, .default, fun _ => return .app (.const ``List [0]) <| ← rflp.elabSort),
      (`X, .default, fun _ => rflp.elabSort)] fun xs => do
      return .app (.const ``Fin []) _

def elabWord (rfpl : RFLP) (word : TSyntax `lawvere_word) : TermElabM Expr :=
  match word with
  | `(lawvere_word|[of $opname:opName]) => do
    let opname ← elabOpName opname
    return mkAppN (.const ``LawvereWord.of [0,0]) _
  | _ => throwUnsupportedSyntax

@[term_elab flpStx]
def elabFlp : TermElab := fun stx tp =>
  match stx with
  | `([RFLP| NAME: $nm:ident $[SORTS: $sorts,*]? $[OPS: $ops,*]?]) => do
    let nm := nm.getId.toString
    let sorts ← match sorts with
      | some sorts => sorts.getElems.toList.mapM elabSortName
      | none => pure []
    let ops ← match ops with
      | some ops => ops.getElems.toList.mapM elabOpDescr
      | none => pure []
    unless sorts.Nodup do throwError "Sorts must have unique names."
    unless ops.map (fun (nm,_) => nm) |>.Nodup do throwError "Operations must have unique names."
    for (d,nms,out) in ops do
      unless out ∈ sorts do throwError m!"{out} appears in {d} and is not a valid sort name."
      for nm in nms do
        unless nm ∈ sorts do throwError "{nm} appears in {d} is not a valid sort name"
    let actualOps : List (String × List (Fin sorts.length) × Fin sorts.length) :=
      match sorts.length with
      | 0 => []
      | _+1 => ops.map fun (opnm, ins, out) =>
        (opnm, ins.map fun s => sorts.indexOf s, sorts.indexOf out)
    --let rflp : RFLP := .mk nm sorts actualOps
    return mkApp3 (.const ``RFLP.mk []) (toExpr nm) (toExpr sorts) (toExpr actualOps)
    --return toExpr rflp
  | _ => throwUnsupportedSyntax

#check [RFLP|
  NAME:
    Module
  SORTS:
    A, B, C, M, R
  OPS:
   add : M, M → M,
   mul : R, M, R, M → R
]
