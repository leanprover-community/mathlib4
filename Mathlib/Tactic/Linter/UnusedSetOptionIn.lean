import Mathlib.adomaniLeanUtils.inspect_syntax
import Mathlib.Tactic.Lemma
import Lean

open Lean Elab Command

/-
node Lean.Parser.Command.in, none
|-node Lean.Parser.Command.set_option, none
|   |-atom original: ⟨⟩⟨ ⟩-- 'set_option'
|   |-ident original: ⟨⟩⟨ ⟩-- (maxHeartbeats,maxHeartbeats)
|   |-node null, none
|   |-node num, none
|   |   |-atom original: ⟨⟩⟨ ⟩-- '2'
|-atom original: ⟨⟩⟨\n⟩-- 'in'
|-node Lean.Parser.Command.declaration, none
-/

/-- converts
* `theorem x ...` to  `some (example ... , x)`,
* `lemma x ...`   to  `some (example ... , x)`,
* `example ...`   to ``some (example ... , `example)``,
*  everything else goes to `none`.
-/
def toExample {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m] :
    Syntax → m (Option (Syntax × Syntax))
  | `($dm:declModifiers theorem $did:declId $ds* : $t $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds* : $t $dv:declVal), did.raw[0])
  | `($dm:declModifiers lemma $did:declId $ds* : $t $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds* : $t $dv:declVal), did.raw[0])
  | `($dm:declModifiers example $ds:optDeclSig $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds $dv:declVal), mkIdent `example)
  | _ => return none

def findSetOptionIn (cmd : CommandElab) : CommandElab := fun stx => do
  let mut report? := (false, default)
  let s ← get
  match stx with
    | .node _ ``Lean.Parser.Command.in #[
        .node _ ``Lean.Parser.Command.set_option _,
        _,  -- atom `in`
        inner] => do
      if let some (exm, id) := (← toExample inner) then
        cmd exm
        let msgs := (← get).messages.toList
        report? := (msgs.isEmpty, id)
        set s
      if report?.1 then logInfoAt stx m!"unused 'set_option' in '{report?.2}'"
    | _ => return

/-- The `unusedSetOptionIn` linter warns against "most external" unused `set_option ... in`s. -/
register_option linter.unusedSetOptionIn : Bool := {
  defValue := true
  descr := "enable the unusedSetOptionIn linter"
}

/-- Gets the value of the `linter.unusedSetOptionIn` option. -/
def getSetOptionIn (o : Options) : Bool := Linter.getLinterValue linter.unusedSetOptionIn o

@[inherit_doc linter.unusedSetOptionIn]
def unusedSetOptionIn : Linter where run cmd := do --withSetOptionIn fun cmd => do
  if getSetOptionIn (← getOptions) then
    findSetOptionIn elabCommand cmd

initialize addLinter unusedSetOptionIn

elab "fso " cmd:command : command => findSetOptionIn elabCommand cmd
