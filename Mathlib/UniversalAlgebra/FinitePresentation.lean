import Mathlib.UniversalAlgebra.LawvereTheory

structure RawFiniteLawverePresentation where
  name : String
  sortNames : Array String
  opNames : Array (String × Array String × String)

structure FiniteLawverePresentation extends RawFiniteLawverePresentation where

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
syntax opName : lawvere_word
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

def elabOpDescr (descr : TSyntax `opDescr) : TermElabM (String × Array String × String) :=
  match descr with
  | `(opDescr|$nm : $nms,* → $out) => do
    let nm ← elabOpName nm
    let nms ← nms.getElems.mapM elabSortName
    let out ← elabSortName out
    return (nm, nms, out)
  | _ => throwUnsupportedSyntax

def elabRelDescr (descr : TSyntax `relDescr) :
    TermElabM (String × TSyntax `lawvere_word × TSyntax `lawvere_word) :=
  match descr with
  | `(relDescr|$nm : $lhs = $rhs) => return (← elabRelName nm, lhs, rhs)
  | _ => throwUnsupportedSyntax

@[term_elab flpStx]
def elabFlp : TermElab := fun stx tp =>
  match stx with
  | `([RFLP| NAME: $nm:ident $[SORTS: $sorts,*]? $[OPS: $ops,*]?]) => do
    let nm := nm.getId.toString
    let sorts ← match sorts with
      | some sorts => sorts.getElems.mapM elabSortName
      | none => pure #[]
    let ops ← match ops with
      | some ops => ops.getElems.mapM elabOpDescr
      | none => pure #[]
    for (d,nms,out) in ops do
      unless out ∈ sorts do throwError m!"{out} appears in {d} and is not a valid sort name."
      for nm in nms do
        unless nm ∈ sorts do throwError "{nm} appears in {d} is not a valid sort name"
    logInfo m!"{nm}"
    logInfo m!"{sorts}"
    logInfo m!"{ops}"
    --return q(RawFiniteLawverePresentation.mk $nm $sorts $ops)
    return q(0)
  | _ => throwUnsupportedSyntax

#check [RFLP|
  NAME:
    Module
  SORTS:
    R, M
  OPS:
    add : M, M → M,
    smul : R, M → M,
    neg : M → M
]
