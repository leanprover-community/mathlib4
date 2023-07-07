import Mathlib.Data.Bitvec.ConstantLemmas
import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Data.Bitvec.Ruleset
import Mathlib.Data.Vector.Snoc
import Mathlib.Data.Vector.MapLemmas
import Mathlib.Tactic
import Aesop
import Qq



namespace Bitvec.Tactic
  open Lean Meta Tactic Elab.Tactic

  /--
    Checks whether every occurence of free variable `x` is in an expression `get x i`, for
    possibly different values of `i`.
    Returns a list of all such `i` that were found, if indeed all occurences were guarded,
    or `none` if a non-guarded occurence of `x` was found
  -/
  def findBitvecGet : Expr → Option (Expr)
    | e@(.app (.app (.app (.const ``Bitvec.get _) _) _) _) =>
        -- dbg_trace "Found (get x i) pattern (x={y.name}, i={i}), looking for {x.name}"
        e

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
  @[aesop unsafe 50% tactic (rule_sets [Mathlib.Data.Bitvec])]
  def bitblast_bitvec_get : TacticM Unit := do
    withMainContext do
      let goal ← getMainTarget
      match findBitvecGet goal with
        | some e =>
            let tgt ← delab e
            let tct ← `(tactic| cases ($tgt))
            dbg_trace "{tct}"
            evalTactic tct
        | none =>
            throwError "Could not find any instance of `get x i`, where `x` does not occur unguarded"

  elab "bitblast_bitvec_get" : tactic => bitblast_bitvec_get

  open Qq in
  /--
    If there is a variable `xs : Bitvec (n+1)` in the environment, then we can break this down
    into an `x : Bool` and `xs : Bitvec n`
  -/
  @[aesop safe tactic (rule_sets [Mathlib.Data.Bitvec])]
  def bitvec_elim_known_size : TacticM Unit := do
    withMainContext do
      let ctx ← getLCtx
      for var in ctx do
        let n : Q(Nat) ← mkFreshExprMVarQ q(Nat)
        if (←isDefEq var.type q(Bitvec (Nat.succ $n))) || (←isDefEq var.type q(Bitvec 0)) then
          let id := mkIdent var.userName
          evalTactic <|<- `(tactic|
            cases $id:ident using Vector.revCasesOn
          )
          return
      throwError "No variable of type `Bitvec (n+1)` found in the local context"

  elab "bitvec_elim_known_size" : tactic => bitvec_elim_known_size

  attribute [aesop safe 10 cases (rule_sets [Mathlib.Data.Bitvec])] Bool

  attribute [aesop norm simp (rule_sets [Mathlib.Data.Bitvec])]
    Bitvec.add
    Bitvec.adc
    Bool.carry
    Bool.xor3
    Bitvec.sub
    Bitvec.sbb
    Bitvec.neg
    Bitvec.not
    Bitvec.and
    Bitvec.or
    Bitvec.xor
    Vector.map₂_comm
    Vector.mapAccumr₂_comm

  section Desugar
    variable (x y : Bitvec n)

    @[aesop norm simp (rule_sets [Mathlib.Data.Bitvec])]
    protected theorem desugar_add : x + y = x.add y :=
      rfl

    @[aesop norm simp (rule_sets [Mathlib.Data.Bitvec])]
    protected theorem desugar_sub : x - y = x.sub y :=
      rfl

    @[aesop norm simp (rule_sets [Mathlib.Data.Bitvec])]
    protected theorem desugar_neg : -x  = Bitvec.neg x :=
      rfl

    @[aesop norm simp (rule_sets [Mathlib.Data.Bitvec])]
    protected theorem desugar_not : ~~~x = Bitvec.not x :=
      rfl

    @[aesop norm simp (rule_sets [Mathlib.Data.Bitvec])]
    protected theorem desugar_and : x &&& y = x.and y :=
      rfl

    @[aesop norm simp (rule_sets [Mathlib.Data.Bitvec])]
    protected theorem desugar_or : x ||| y = x.or y :=
      rfl

    @[aesop norm simp (rule_sets [Mathlib.Data.Bitvec])]
    protected theorem desugar_xor : x ^^^ y = x.xor y :=
      rfl

    @[aesop norm simp (rule_sets [Mathlib.Data.Bitvec])]
    protected theorem desugar_zero : (0 : Bitvec n) = Vector.replicate n false :=
      rfl

  end Desugar

  macro "aesop_bitvec" opt:Aesop.tactic_clause* : tactic =>
    `(tactic|
        simp only [
          (· * ·), Mul.mul,
          (· / ·), Div.div
        ] <;>
        aesop (rule_sets [Mathlib.Data.Bitvec]) (options := {terminal := false}) $opt*
    )

  macro "aesop_bitvec?" opt:Aesop.tactic_clause* : tactic =>
    `(tactic|
        simp only [
          (· * ·), Mul.mul,
          (· / ·), Div.div
        ] <;>
        aesop? (rule_sets [Mathlib.Data.Bitvec]) (options := {terminal := false}) $opt*
      )

end Bitvec.Tactic
