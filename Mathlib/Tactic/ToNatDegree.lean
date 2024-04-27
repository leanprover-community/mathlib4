/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Mathlib.Data.ENat.Basic

/-!
#  `toTD` a command to convert from `degree` to `trailingDegree`

If `thm` is a theorem about `degree`s of polynomials, then `toTD thm` tries to add to the
environment the analogous result about `trailingDegree`s of polynomials.
-/

open Lean Elab Command

namespace Mathlib.ToNatDegree

/-- converts `WithBot _` to `ℕ∞` and `⊥` to `⊤`.
Useful when converting a `degree` with values in `WithBot ℕ` to a `trailingDegree` with values
in `ℕ∞`. -/
def WithBotToENat (stx : Syntax) : CommandElabM Syntax :=
  stx.replaceM fun s => do
    match s with
      | .node _ ``Lean.Parser.Term.app #[.ident _ _ `WithBot _, _] =>
        return some (← `(ℕ∞))
      | .node _ ``Lean.Parser.Term.app #[.ident _ _ na _, .node _ _ #[hb]] =>
        --logInfo m!"here '{s}', '{hb}'"
        match na with
          | .str ha "antisymm" => return some (← `($(mkIdent ``antisymm) $(mkIdent ha) $(⟨hb⟩)))
          | _ => return none
      | .node _ `«term⊥» #[.atom _ "⊥"] => return some (← `(⊤))
      | .node _ `«term_≤_» #[a, _, b] => return some (← `($(⟨b⟩) ≤ $(⟨a⟩)))
      | _ => return none

-- |-node Lean.Parser.Term.app, none
-- |   |-ident original: ⟨⟩⟨ ⟩-- (ha.antisymm,ha.antisymm)
-- |   |-node null, none
-- |   |   |-ident original: ⟨⟩⟨\n\n⟩-- (hb,hb)


def WithBotToENat' (stx : Syntax) : CommandElabM Syntax :=
  stx.replaceM fun s => do
    match s with
      | `(term| antisymm $ha $hb) => /-dbg_trace "fd";-/  return some (← `($(mkIdent ``antisymm) $hb $ha))
      | _ =>  /-dbg_trace "not";-/ return none


--|-node «term_≤_», none


/-- converts a name involving `degree` to a name involving `trailingDegree`. -/
def nameToTrailingDegree : Name → Name
  | .str a b =>
      let b := b.replace "degree" "trailingDegree"
      let b := b.replace "le_trailingDegree" "trailingDegree_le"
      let b := b.replace "max" "min"
      let b := b.replace "bot" "top"
      let b := b.replace "WithBot" "WithTop"
      let b := b.replace "le_sup" "inf_le"
      let b := b.replace "sup_mono" "inf_mono"
      let b := b.replace "min_eq_sup_coe" "min_eq_inf_coe"
      .str (nameToTrailingDegree a) b
  | _ => default

/-- converts a statement involving `degree` to a name involving `trailingDegree`. -/
def toTrailingDegree (stx : Syntax) : CommandElabM Syntax :=
  stx.replaceM fun s => do
    match s.getId with
      | .anonymous => return none
      | v => return some (mkIdent (nameToTrailingDegree v))

/--
If `thm` is a theorem about `degree`s of polynomials, then `toTD thm` tries to add to the
environment the analogous result about `trailingDegree`s of polynomials.
-/
elab "toTD " tk:"?"? cmd:command : command => do
  let newCmd ← WithBotToENat' <| ← WithBotToENat <| ← toTrailingDegree cmd
  if tk.isSome then logInfo m!"adding {indentD newCmd}"
  elabCommand cmd
  elabCommand newCmd

macro "toTD? " cmd:command : command => return (← `(toTD ? $cmd))
