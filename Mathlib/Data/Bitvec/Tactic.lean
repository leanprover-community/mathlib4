import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Data.Bitvec.Ruleset
import Mathlib.Tactic
import Aesop



namespace Bitvec.Tactic
  open Lean Meta Tactic Elab.Tactic

  /--
    Checks whether every occurence of free variable `x` is in an expression `get x i`, for
    possibly different values of `i`.
    Returns a list of all such `i` that were found, if indeed all occurences were guarded,
    or `none` if a non-guarded occurence of `x` was found
  -/
  def findBitvecGet : Expr → Option (Expr × Expr)
    | .app (.app (.app (.const ``Bitvec.get _) _) x) i =>
        -- dbg_trace "Found (get x i) pattern (x={y.name}, i={i}), looking for {x.name}"
        (x, i)

    | .proj _ _ e
    | .mdata _ e =>
        findBitvecGet e

    | .forallE _ e₁ e₂ _
    | .lam _ e₁ e₂ _
    | .app e₁ e₂ => do
        (findBitvecGet e₁).orElse fun _ => findBitvecGet e₂

    | .letE _ e₁ e₂ e₃ _ => do
        ((findBitvecGet e₁).orElse fun _ => findBitvecGet e₂).orElse fun _ => findBitvecGet e₃

    | _ =>
        -- All other expression constructors are atomic, and do not contain free vars
        none




  open Lean.PrettyPrinter (delab) in
  /--
    For every variable `x : Bitvec n`, if the goal only contains `x` as part of a
    `get x i` expression (for arbitary value of `i`), do a case split on `get x i`
  -/
  @[aesop safe 10 tactic (rule_sets [Mathlib.Data.Bitvec])]
  def bitblast_bitvec_get : TacticM Unit := do
    withMainContext do
      let goal ← getMainTarget
      match findBitvecGet goal with
        | some (x, i) =>
            let x ← delab x
            let i ← delab i
            let tct ← `(cases (Bitvec.get $x $i))
            dbg_trace "{tct}"
            evalTactic tct
        | none =>
            throwError "Could not find any instance of `get x i`, where `x` does not occur unguarded"

  elab "bitblast_bitvec_get" : tactic => bitblast_bitvec_get

  macro "aesop_bitvec" : tactic => `(tactic|
    aesop
      ( add 90% cases Bool, 90% Bitvec.ext,
      ) (
        rule_sets [Mathlib.Data.Bitvec]
      )
  )

end Bitvec.Tactic
