/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import Lean

/-!

Formatter hacks to pretty-print theorems more nicely like this:
```
theorem foo : False ∧ False := by 
  constructor
  · simp 
    trivial
    
  · split 
    assumption
```

-/

namespace Mathlib.FormattingHacks
open Lean Parser Command PrettyPrinter Formatter Meta

/--
`replacing defn a => b` returns the value of the definition `defn`,
after replacing references to the constant `a` by `b`.
-/
local syntax "replacing " ident manyIndent(ident " => " ident ";"?): term
elab_rules : term | `(replacing $defn:ident $[$as => $bs]*) => do
  let const ← getConstInfo (← resolveGlobalConstNoOverload defn)
  let some value ← const.value? | throwError "not a definition: {const.name}"
  let mut map : Std.HashMap Name Name := {}
  for a in as, b in bs do
    map := map.insert (← resolveGlobalConstNoOverload a) (← resolveGlobalConstNoOverload b)
  value.replace fun
    | Expr.const n lvls .. => map.find? n |>.map (mkConst · lvls)
    | e => none

/- Version of termParser which does not indent&group by/do/fun -/
def termParser.formatter' (prio : Nat := 0) : Formatter := do
  match (← Syntax.MonadTraverser.getCur).getKind with
  | ``Term.do => Term.do.formatter
  | ``Term.byTactic => Term.byTactic.formatter
  | ``Term.fun => Term.fun.formatter
  | _ => termParser.formatter

def declValSimple.formatter' : Formatter :=
  withAntiquot.formatter (Parser.mkAntiquot.formatter "declValSimple" (some `Lean.Parser.Command.declValSimple) true)
    (leadingNode.formatter `Lean.Parser.Command.declValSimple 1024
      (andthen.formatter (push Format.line *> symbol.formatter " :=") -- no hard break!
        (andthen.formatter (termParser.formatter' 0) (optional.formatter Term.whereDecls.formatter))))

set_option pp.rawOnError true
def declVal.formatter' : Formatter :=
  replacing declVal.formatter
    declValSimple.formatter => declValSimple.formatter'

def def.formatter' : Formatter :=
  replacing def.formatter declVal.formatter => declVal.formatter'

def theorem.formatter' : Formatter :=
  replacing theorem.formatter declVal.formatter => declVal.formatter'

@[formatter Lean.Parser.Command.declaration]
def declaration.formatter' : Formatter :=
  replacing declaration.formatter
    def.formatter => def.formatter'
    theorem.formatter => theorem.formatter'

def Tactic.tacticSeq1Indented.formatter' : Formatter :=
  withAntiquot.formatter
    (Parser.mkAntiquot.formatter "tacticSeq1Indented" (some ``Tactic.tacticSeq1Indented) true)
    (leadingNode.formatter `Lean.Parser.Tactic.tacticSeq1Indented 1024
      (many1Indent.formatter <|
        push "\n" *>
        (group.formatter
          (andthen.formatter (pure ())
            (andthen.formatter (tacticParser.formatter 0) (optional.formatter (symbol.formatter ";")))))))

def Tactic.tacticSeq.formatter' : Formatter :=
  replacing Tactic.tacticSeq.formatter
    Tactic.tacticSeq1Indented.formatter => Tactic.tacticSeq1Indented.formatter'

@[formatter Lean.Parser.Tactic.«tactic·._»]
def tacticCDotFormatter : Formatter := do
  leadingNode.formatter ``Tactic.«tactic·._» 1022
    (andthen.formatter (orelse.formatter (symbol.formatter "· ") (symbol.formatter ". "))
      <| if Std.Format.getIndent (← getOptions) == 2 then Tactic.tacticSeq.formatter' else Tactic.tacticSeq.formatter)

/-
#eval show Elab.TermElabM _ from do
  PrettyPrinter.ppTerm <|<-
  `(theorem foo : False ∧ False := by
    constructor
    · simp
      trivial
    · split
      assumption)
-/
