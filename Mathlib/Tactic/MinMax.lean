/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Mathlib.Order.Notation
/-!
#  `toTop` a command to convert from `Bot` to `Top`

If `thm` is a theorem about `WithBot`, then `toTop thm` tries to add to the
environment the analogous result about `WithTop`.
-/

open Lean Elab Command

namespace Mathlib.ToNatDegree

partial
def replAS (stx : Syntax) : CommandElabM Syntax :=
  stx.replaceM fun s => do
    match s with
      | `(term| antisymm $ha $hb) => return some (← `($(mkIdent `antisymm) $hb $ha))
      | `(term| le_trans $ha $hb) => return some (← `($(mkIdent `le_trans) $hb $ha))
      | `(term| lt_trans $ha $hb) => return some (← `($(mkIdent `lt_trans) $hb $ha))
      | `(term| $ha ⊔ $hb) =>
        let ha' := ⟨← replAS ha⟩
        let hb' := ⟨← replAS hb⟩
        return some (← `(term| $ha' ⊓ $hb'))
      | `(term| $ha ∪ $hb) =>
        let ha' := ⟨← replAS ha⟩
        let hb' := ⟨← replAS hb⟩
        return some (← `(term| $ha' ∩ $hb'))
      | `(term| $ha ∩ $hb) =>
        let ha' := ⟨← replAS ha⟩
        let hb' := ⟨← replAS hb⟩
        return some (← `(term| $ha' ∪ $hb'))
      | _ =>  /-dbg_trace "not";-/ return none


#eval "abcDeF".toList.groupBy fun a b => a.isUpper || (a.isLower && b.isLower)

def splitUpper (s : String) : List String :=
  s.toList.groupBy (fun a b => a.isUpper || (a.isLower && b.isLower)) |>.map (⟨·⟩)


#eval do
  let res := "SemilatticeSup"
  IO.println (splitUpper res == ["Semilattice", "Sup"])

def wordReplacements : String → String
  | "max" => "min"
  | "Sup" => "Inf"
  | "sup" => "inf"
  | "Bot" => "Top"
  | "bot" => "top"
  | "bot'" => "top'"
  | "unbot" => "untop"
  | "unbot'" => "untop'"
  | "comp" => "lift"
  | "lift" => "comp"
  | "union" => "inter"
  | "inter" => "union"
  | e => e

abbrev lelt : HashSet String := { "le", "lt" }
abbrev leftRight : HashSet String := { "left", "right", "sup", "inf", "inter", "union" }


def swapWords : List String → List String
  | le::left::ls =>
    if (lelt.contains le) && (leftRight.contains left)
    then left::le::(swapWords ls)
    else if (lelt.contains left) && (leftRight.contains le)
    then left::le::(swapWords ls)
    else le::swapWords (left :: ls)
  | e => e
--  | "sup_le" => "le_inf"
--  | "sup_lt" => "lt_inf"
--  | "union_le" => "le_union"

#eval do
  let res := ["le", "inf"]
  let res := ["inf", "le"]
  IO.println (swapWords res) -- == ["Semilattice", "Sup"])

#eval do
  let res := "NNRealHHi"
  IO.println (splitUpper res)
  IO.println (splitUpper res == ["NNReal", "HHi"])

/-- converts a name involving `WithBot` to a name involving `WithTop`. -/
def nameToTop : Name → Name
  | .str a b =>
      let words := b.splitOn "_"
      let words : List (List String) := words.map fun w => (splitUpper w).map wordReplacements
      let words := swapWords (words.map fun ws => (ws.foldl (· ++ ·) ""))
      let w_s := "_".intercalate words
      .str (nameToTop a) w_s
  | _ => default

/-- converts a statement involving `WithBot` to a name involving `WithTop`. -/
def toTop (stx : Syntax) : CommandElabM Syntax :=
  stx.replaceM fun s => do
    match s.getId with
      | .anonymous => return none
      | v => return some (mkIdent (nameToTop v))

/-- converts `WithBot _` to `ℕ∞` and `⊥` to `⊤`.
Useful when converting a `degree` with values in `WithBot ℕ` to a `trailingDegree` with values
in `ℕ∞`. -/
def MaxToMin (stx : Syntax) : CommandElabM Syntax :=
  stx.replaceM fun s => do
    match s with
--      | .node _ ``Lean.Parser.Term.app #[.ident _ _ `WithBot _, _] =>
--        return some (← `(ℕ∞))
      | .node _ ``Lean.Parser.Term.app #[.ident _ _ na _, .node _ _ #[hb]] =>
        match na with
          | .str ha "antisymm" => return some (← `($(mkIdent `antisymm) $(mkIdent ha) $(⟨hb⟩)))
          | .str ha "trans_le" => return some (← `($(mkIdent `lt_of_le_of_lt) $(⟨hb⟩) $(mkIdent ha)))
          | _ => return none
--      | .node _ `«term⊔» #[.atom _ "⊔"] => return some (← `(⊓))
      | .node _ `«term⊥» #[.atom _ "⊥"] => return some (← `((⊤ : $(mkIdent `WithTop) _)))
      | .atom _ s =>
        if s.contains '⊥' then return some (mkAtom (s.replace "⊥" "⊤")) else return none
      | .node _ `«term_≤_» #[a, _, b] => return some (← `($(⟨b⟩) ≤ $(⟨a⟩)))
      | .node _ `«term_<_» #[a, _, b] => return some (← `($(⟨b⟩) < $(⟨a⟩)))
      | .node _ ``Lean.Parser.Command.docComment #[init, .atom _ docs] =>
--        let newDocs := " ".intercalate <| (docs.splitOn " ").map wordReplacements
        let pieces := (docs.splitOn " ").map fun s => s.splitOn "`"
        let modPieces := pieces.map fun p1 : List String => p1.map wordReplacements
        let newDocs := (" ".intercalate (modPieces.map "`".intercalate))
--        let newDocs := " ".intercalate <| (docs.splitOn " ").map wordReplacements
--        let newDocs := "`".intercalate <| (newDocs.splitOn "`").map wordReplacements
        let newDocs :=
          if newDocs == docs
          then "[recycled by `toMin`] " ++ docs
          else "[autogenerated by `toMin`] " ++ newDocs
        let nd := mkNode ``Lean.Parser.Command.docComment #[init, mkAtom newDocs]
        return some nd
      | _ => return none

-- |-node Lean.Parser.Command.docComment, none
-- |   |-atom original: ⟨⟩⟨ ⟩-- '/--'
-- |   |-atom original: ⟨⟩⟨\n⟩-- 'hi -/'



/--
If `thm` is a theorem about `WithBot`, then `toTop thm` tries to add to the
environment the analogous result about `WithTop`.
-/
elab "toTop " tk:"?"? cmd:command : command => do
  let newCmd ← replAS <| ← MaxToMin <| ← toTop cmd
  if tk.isSome then logInfo m!"-- adding\n{newCmd}"
  elabCommand cmd
  let currNS ← getCurrNamespace

  withScope (fun s => { s with currNamespace := nameToTop currNS } ) <| elabCommand newCmd

--  let newNS := mkIdent (nameToTop currNS)
--  let currNS := mkIdent currNS
--  elabCommand (← `(end $currNS namespace $newNS))
--  --withScope (fun s => { s with currNamespace := nameToTop currNS } ) <|
--  elabCommand newCmd
--  elabCommand (← `(end $newNS namespace $currNS))


macro "toTop? " cmd:command : command => return (← `(toTop ? $cmd))
