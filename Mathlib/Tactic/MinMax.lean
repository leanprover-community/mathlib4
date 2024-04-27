/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Mathlib.Order.Notation
/-!
#  `toTD` a command to convert from `degree` to `trailingDegree`

If `thm` is a theorem about `max`, then `toMin thm` tries to add to the
environment the analogous result about `min`.
-/

open Lean Elab Command

namespace Mathlib.ToNatDegree

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
--      | .node _ `«term⊥» #[.atom _ "⊥"] => return some (← `(⊤))
      | .node _ `«term_≤_» #[a, _, b] => return some (← `($(⟨b⟩) ≤ $(⟨a⟩)))
      | .node _ `«term_<_» #[a, _, b] => return some (← `($(⟨b⟩) < $(⟨a⟩)))
      | _ => return none

-- |-node Lean.Parser.Term.app, none
-- |   |-ident original: ⟨⟩⟨ ⟩-- (ha.antisymm,ha.antisymm)
-- |   |-node null, none
-- |   |   |-ident original: ⟨⟩⟨\n\n⟩-- (hb,hb)


partial
def replAS (stx : Syntax) : CommandElabM Syntax :=
  stx.replaceM fun s => do
    match s with
      | `(term| antisymm $ha $hb) => /-dbg_trace "fd";-/  return some (← `($(mkIdent `antisymm) $hb $ha))
      | `(term| le_trans $ha $hb) => /-dbg_trace "fd";-/  return some (← `($(mkIdent `le_trans) $hb $ha))
      | `(term| lt_trans $ha $hb) => /-dbg_trace "fd";-/  return some (← `($(mkIdent `lt_trans) $hb $ha))
      | `(term| $ha ⊔ $hb) =>
        let ha' := ⟨← replAS ha.raw⟩
        let hb' := ⟨← replAS hb.raw⟩
        return some (← `(term| $ha' ⊓ $hb'))
      | _ =>  /-dbg_trace "not";-/ return none


--|-node «term_≤_», none


/-- converts a name involving `max` to a name involving `min`. -/
def nameToMin : Name → Name
  | .str a b =>
      let b := b.replace "max" "min"
--      let b := b.replace "bot" "top"
--      let b := b.replace "WithBot" "WithTop"
      let b := b.replace "Sup" "Inf"
      let b := b.replace "le_left" "left_le"
      let b := b.replace "le_right" "right_le"
      let b := b.replace "lt_left" "left_lt"
      let b := b.replace "lt_right" "right_lt"
      let b := b.replace "le_sup" "inf_le"
      let b := b.replace "lt_sup" "inf_lt"
      let b := b.replace "sup_le" "le_inf"
      let b := b.replace "sup_lt" "lt_inf"
      let b := b.replace "sup" "inf"
      let b := b.replace "Sup" "Inf"
--      let b := b.replace "sup_mono" "inf_mono"
--      let b := b.replace "min_eq_sup_coe" "min_eq_inf_coe"
      .str (nameToMin a) b
  | _ => default

/-- converts a statement involving `degree` to a name involving `trailingDegree`. -/
def toMin (stx : Syntax) : CommandElabM Syntax :=
  stx.replaceM fun s => do
    match s.getId with
      | .anonymous => return none
      | v => return some (mkIdent (nameToMin v))

/--
If `thm` is a theorem about `max`, then `toMin thm` tries to add to the
environment the analogous result about `min`.
-/
elab "toMin " tk:"?"? cmd:command : command => do
  let newCmd ← replAS <| ← MaxToMin <| ← toMin cmd
  if tk.isSome then logInfo m!"adding {indentD newCmd}"
  elabCommand cmd
  elabCommand newCmd

macro "toMin? " cmd:command : command => return (← `(toMin ? $cmd))
