/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Lean.Expr.Rat
import Mathlib.Tactic.Hint
import Mathlib.Tactic.NormNum.Result
import Mathlib.Util.AtLocation
import Mathlib.Util.Qq
import Lean.Elab.Tactic.Location

/-!
## `norm_num` core functionality

This file sets up the `norm_num` tactic and the `@[norm_num]` attribute,
which allow for plugging in new normalization functionality around a simp-based driver.
The actual behavior is in `@[norm_num]`-tagged definitions in `Tactic.NormNum.Basic`
and elsewhere.
-/

open Lean
open Lean.Meta Qq Lean.Elab Term

/-- Attribute for identifying `norm_num` extensions. -/
syntax (name := norm_num) "norm_num " term,+ : attr

namespace Mathlib
namespace Meta.NormNum

initialize registerTraceClass `Tactic.norm_num

/--
An extension for `norm_num`.
-/
structure NormNumExt where
  /-- The extension should be run in the `pre` phase when used as simp plugin. -/
  pre := true
  /-- The extension should be run in the `post` phase when used as simp plugin. -/
  post := true
  /-- Attempts to prove an expression is equal to some explicit number of the relevant type. -/
  eval {u : Level} {α : Q(Type u)} (e : Q($α)) : MetaM (Result e)
  /-- The name of the `norm_num` extension. -/
  name : Name := by exact decl_name%

variable {u : Level}

/-- Read a `norm_num` extension from a declaration of the right type. -/
def mkNormNumExt (n : Name) : ImportM NormNumExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck NormNumExt opts ``NormNumExt n

/-- Each `norm_num` extension is labelled with a collection of patterns
which determine the expressions to which it should be applied. -/
abbrev Entry := Array (Array DiscrTree.Key) × Name

/-- The state of the `norm_num` extension environment -/
structure NormNums where
  /-- The tree of `norm_num` extensions. -/
  tree : DiscrTree NormNumExt := {}
  /-- Erased `norm_num`s. -/
  erased : PHashSet Name := {}
  deriving Inhabited

/-- Environment extensions for `norm_num` declarations -/
initialize normNumExt : ScopedEnvExtension Entry (Entry × NormNumExt) NormNums ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq NormNumExt := ⟨fun _ _ ↦ false⟩
  /- Insert `v : NormNumExt` into the tree `dt` on all key sequences given in `kss`. -/
  let insert kss v dt := kss.foldl (fun dt ks ↦ dt.insertCore ks v) dt
  registerScopedEnvExtension {
    mkInitial := pure {}
    ofOLeanEntry := fun _ e@(_, n) ↦ return (e, ← mkNormNumExt n)
    toOLeanEntry := (·.1)
    addEntry := fun { tree, erased } ((kss, n), ext) ↦
      { tree := insert kss ext tree, erased := erased.erase n }
  }

/-- Run each registered `norm_num` extension on an expression, returning a `NormNum.Result`. -/
def derive {α : Q(Type u)} (e : Q($α)) (post := false) : MetaM (Result e) := do
  if e.isRawNatLit then
    let lit : Q(ℕ) := e
    return .isNat (q(instAddMonoidWithOneNat) : Q(AddMonoidWithOne ℕ))
      lit (q(IsNat.raw_refl $lit) : Expr)
  profileitM Exception "norm_num" (← getOptions) do
    let s ← saveState
    let normNums := normNumExt.getState (← getEnv)
    let arr ← normNums.tree.getMatch e
    for ext in arr do
      if (bif post then ext.post else ext.pre) && ! normNums.erased.contains ext.name then
        try
          let new ← withReducibleAndInstances <| ext.eval e
          trace[Tactic.norm_num] "{ext.name}:\n{e} ==> {new}"
          return new
        catch err =>
          trace[Tactic.norm_num] "{ext.name} failed {e}: {err.toMessageData}"
          s.restore
    throwError "{e}: no norm_nums apply"

/-- Run each registered `norm_num` extension on a typed expression `e : α`,
returning a typed expression `lit : ℕ`, and a proof of `isNat e lit`. -/
def deriveNat {α : Q(Type u)} (e : Q($α))
    (_inst : Q(AddMonoidWithOne $α) := by with_reducible assumption) :
    MetaM ((lit : Q(ℕ)) × Q(IsNat $e $lit)) := do
  let .isNat _ lit proof ← derive e | failure
  pure ⟨lit, proof⟩

/-- Run each registered `norm_num` extension on a typed expression `e : α`,
returning a typed expression `lit : ℤ`, and a proof of `IsInt e lit` in expression form. -/
def deriveInt {α : Q(Type u)} (e : Q($α))
    (_inst : Q(Ring $α) := by with_reducible assumption) :
    MetaM ((lit : Q(ℤ)) × Q(IsInt $e $lit)) := do
  let some ⟨_, lit, proof⟩ := (← derive e).toInt | failure
  pure ⟨lit, proof⟩

/-- Run each registered `norm_num` extension on a typed expression `e : α`,
returning a rational number, typed expressions `n : ℤ` and `d : ℕ` for the numerator and
denominator, and a proof of `IsRat e n d` in expression form. -/
def deriveRat {α : Q(Type u)} (e : Q($α))
    (_inst : Q(DivisionRing $α) := by with_reducible assumption) :
    MetaM (ℚ × (n : Q(ℤ)) × (d : Q(ℕ)) × Q(IsRat $e $n $d)) := do
  let some res := (← derive e).toRat' | failure
  pure res

/-- Run each registered `norm_num` extension on a typed expression `p : Prop`,
and returning the truth or falsity of `p' : Prop` from an equivalence `p ↔ p'`. -/
def deriveBool (p : Q(Prop)) : MetaM ((b : Bool) × BoolResult p b) := do
  let .isBool b prf ← derive q($p) | failure
  pure ⟨b, prf⟩

set_option linter.style.commandStart false in -- TODO decide about this!
/-- Run each registered `norm_num` extension on a typed expression `p : Prop`,
and returning the truth or falsity of `p' : Prop` from an equivalence `p ↔ p'`. -/
def deriveBoolOfIff (p p' : Q(Prop)) (hp : Q($p ↔ $p')) :
    MetaM ((b : Bool) × BoolResult p' b) := do
  let ⟨b, pb⟩ ← deriveBool p
  match b with
  | true  => return ⟨true, q(Iff.mp $hp $pb)⟩
  | false => return ⟨false, q((Iff.not $hp).mp $pb)⟩

/-- Run each registered `norm_num` extension on an expression,
returning a `Simp.Result`. -/
def eval (e : Expr) (post := false) : MetaM Simp.Result := do
  if e.isExplicitNumber then return { expr := e }
  let ⟨_, _, e⟩ ← inferTypeQ' e
  (← derive e post).toSimpResult

/-- Erases a name marked `norm_num` by adding it to the state's `erased` field and
  removing it from the state's list of `Entry`s. -/
def NormNums.eraseCore (d : NormNums) (declName : Name) : NormNums :=
  { d with erased := d.erased.insert declName }

/--
Erase a name marked as a `norm_num` attribute.

Check that it does in fact have the `norm_num` attribute by making sure it names a `NormNumExt`
found somewhere in the state's tree, and is not erased.
-/
def NormNums.erase {m : Type → Type} [Monad m] [MonadError m] (d : NormNums) (declName : Name) :
    m NormNums := do
  unless d.tree.values.any (·.name == declName) && ! d.erased.contains declName
  do
    throwError "'{declName}' does not have [norm_num] attribute"
  return d.eraseCore declName

initialize registerBuiltinAttribute {
  name := `norm_num
  descr := "adds a norm_num extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind ↦ match stx with
    | `(attr| norm_num $es,*) => do
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'norm_num', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let ext ← mkNormNumExt declName
      let keys ← MetaM.run' <| es.getElems.mapM fun stx ↦ do
        let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e
      normNumExt.add ((keys, declName), ext) kind
    | _ => throwUnsupportedSyntax
  erase := fun declName => do
    let s := normNumExt.getState (← getEnv)
    let s ← s.erase declName
    modifyEnv fun env => normNumExt.modifyState env fun _ => s
}

/-- A simp plugin which calls `NormNum.eval`. -/
def tryNormNum (post := false) (e : Expr) : SimpM Simp.Step := do
  try
    return .done (← eval e post)
  catch _ =>
    return .continue

variable (ctx : Simp.Context) (useSimp := true) in
mutual
  /-- A discharger which calls `norm_num`. -/
  partial def discharge (e : Expr) : SimpM (Option Expr) := do (← deriveSimp e).ofTrue

  /-- A `Methods` implementation which calls `norm_num`. -/
  partial def methods : Simp.Methods :=
    if useSimp then {
      pre := Simp.preDefault #[] >> tryNormNum
      post := Simp.postDefault #[] >> tryNormNum (post := true)
      discharge? := discharge
    } else {
      pre := tryNormNum
      post := tryNormNum (post := true)
      discharge? := discharge
    }

  /-- Traverses the given expression using simp and normalises any numbers it finds. -/
  partial def deriveSimp (e : Expr) : MetaM Simp.Result :=
    (·.1) <$> Simp.main e ctx (methods := methods)
end

open Tactic in
/-- Constructs a simp context from the simp argument syntax. -/
def getSimpContext (cfg args : Syntax) (simpOnly := false) : TacticM Simp.Context := do
  let config ← elabSimpConfigCore cfg
  let simpTheorems ←
    if simpOnly then simpOnlyBuiltins.foldlM (·.addConst ·) {} else getSimpTheorems
  let { ctx, .. } ←
    elabSimpArgs args[0] (eraseLocal := false) (kind := .simp) (simprocs := {})
      (← Simp.mkContext config (simpTheorems := #[simpTheorems])
        (congrTheorems := ← getSimpCongrTheorems))
  return ctx

open Elab Tactic in
/--
Elaborates a call to `norm_num only? [args]` or `norm_num1`.
* `args`: the `(simpArgs)?` syntax for simp arguments
* `loc`: the `(location)?` syntax for the optional location argument
* `simpOnly`: true if `only` was used in `norm_num`
* `useSimp`: false if `norm_num1` was used, in which case only the structural parts
  of `simp` will be used, not any of the post-processing that `simp only` does without lemmas
-/
def elabNormNum (cfg args loc : Syntax) (simpOnly := false) (useSimp := true) :
    TacticM Unit := withMainContext do
  let ctx ← getSimpContext cfg args (!useSimp || simpOnly)
  let loc := expandOptLocation loc
  transformAtNondepPropLocation (fun e ctx ↦ deriveSimp ctx useSimp e) "norm_num" loc
    (failIfUnchanged := false) (mayCloseGoalFromHyp := true) ctx

end Meta.NormNum

namespace Tactic
open Lean.Parser.Tactic Meta.NormNum

/--
Normalize numerical expressions. Supports the operations `+` `-` `*` `/` `⁻¹` `^` and `%`
over numerical types such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ` and some general algebraic types,
and can prove goals of the form `A = B`, `A ≠ B`, `A < B` and `A ≤ B`, where `A` and `B` are
numerical expressions. It also has a relatively simple primality prover.
-/
elab (name := normNum)
    "norm_num" cfg:optConfig only:&" only"? args:(simpArgs ?) loc:(location ?) : tactic =>
  elabNormNum cfg args loc (simpOnly := only.isSome) (useSimp := true)

/-- Basic version of `norm_num` that does not call `simp`. -/
elab (name := normNum1) "norm_num1" loc:(location ?) : tactic =>
  elabNormNum mkNullNode mkNullNode loc (simpOnly := true) (useSimp := false)

open Lean Elab Tactic

@[inherit_doc normNum1] syntax (name := normNum1Conv) "norm_num1" : conv

/-- Elaborator for `norm_num1` conv tactic. -/
@[tactic normNum1Conv] def elabNormNum1Conv : Tactic := fun _ ↦ withMainContext do
  let ctx ← getSimpContext mkNullNode mkNullNode true
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := false))

@[inherit_doc normNum] syntax (name := normNumConv)
    "norm_num" optConfig &" only"? (simpArgs)? : conv

/-- Elaborator for `norm_num` conv tactic. -/
@[tactic normNumConv] def elabNormNumConv : Tactic := fun stx ↦ withMainContext do
  let ctx ← getSimpContext stx[1] stx[3] !stx[2].isNone
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := true))

/--
The basic usage is `#norm_num e`, where `e` is an expression,
which will print the `norm_num` form of `e`.

Syntax: `#norm_num` (`only`)? (`[` simp lemma list `]`)? `:`? expression

This accepts the same options as the `#simp` command.
You can specify additional simp lemmas as usual, for example using `#norm_num [f, g] : e`.
(The colon is optional but helpful for the parser.)
The `only` restricts `norm_num` to using only the provided lemmas, and so
`#norm_num only : e` behaves similarly to `norm_num1`.

Unlike `norm_num`, this command does not fail when no simplifications are made.

`#norm_num` understands local variables, so you can use them to introduce parameters.
-/
macro (name := normNumCmd) "#norm_num" cfg:optConfig o:(&" only")?
    args:(Parser.Tactic.simpArgs)? " :"? ppSpace e:term : command =>
  `(command| #conv norm_num $cfg:optConfig $[only%$o]? $(args)? => $e)

end Mathlib.Tactic

/-!
We register `norm_num` with the `hint` tactic.
-/

register_hint norm_num
