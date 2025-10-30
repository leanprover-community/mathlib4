
import Lean

/-
# `Decidable`-to-`classical` Linter

This linter suggests replacing `Decidable*` hypotheses which are unused in the type of a theorem with the use of `classical` in the proof.

-/

/-
Possible designs:

## Capture the constant from the environment.
- Disadvantages:
  - can we even easily see which constants have just been added?
  - no access to syntax ranges...

## Traverse the infotrees
- Ugly, but might be the best. A chance to build more infotree infra, I suppose.
- Do we determine whether there is a thing in the hypothesis from the local context there? And then collect forward deps, I suppose. But we want to do it when everything has *finished*, i.e. want to avoid false positives from delayed-assigned mvars which try to depend on everything. What's in the infotree?

-/

set_option trace.Elab.info true

open Lean Meta Elab Command

def n := `decidableToClassical

#check CustomInfo
def Lean.Elab.Info.isCustomInfoOf (n : Name) : Info → Bool
| .ofCustomInfo { stx .. } => stx.getKind == n
| _ => false


def Lean.Syntax.isOriginal (stx : Syntax) : Bool := Id.run do
  for stx in stx.topDown do
    if stx matches .node .. then continue
    let some info := stx.getInfo? | return false
    match info with
    | .original .. => continue
    | _ => return false
  return true

def InfoT (m : Type → Type) := ReaderT

#check InfoTree.node
def run : Linter where
  name := n
  run stx := do
    if (← get).snapshotTasks.isEmpty then logInfo "no snaps"
    for task in (← get).snapshotTasks do
      logSnapshotTask task
    let trees ← getInfoTrees
    for t in trees do
      let some as ← t.visitM (postNode := fun ctx i ch as => do
          let as := as.reduceOption.flatten
          match i with
          | .ofCustomInfo { stx, value } =>
            if value.typeName == ``Term.BodyInfo then
              let val := value.get? (α := Lean.Elab.Term.BodyInfo) |>.bind (·.value?)
              let fmt : Format ← match val with
                | some v => liftCoreM do (Meta.ppExpr v).run' {  } { mctx := ctx.mctx }
                | none => pure f!"<no expr>"
              let cinfo ← getConstInfo ctx.parentDecl?.get!

              return f!"{ctx.parentDecl?}{ch.size} {cinfo.type} {value.typeName}: [{fmt}]\n{stx}" :: as
            else return as
          | _ => return as)
        | logInfo "none found"
      logInfo m!"{as}"
      let some as ← t.visitM (postNode := fun ctx i ch as => do
          let as := as.reduceOption.flatten
          match i with
          | .ofTermInfo { stx .. } =>
            if stx.isOriginal then return f!"{stx}" :: as else return as
          | _ => return as)
        | logInfo "none found"
      logInfo m!"{as}"

run_cmd do
  lintersRef.modify fun ls => ls.eraseP (·.name == n)
  addLinter run


#check mkDefView

variable (q : String)

mutual

def foo {α} [DecidableEq α] (a b : α) : Nat → ∀ x : Unit, a = a
| n => fun _ => rfl
where
  go (d : False) : True := True.intro

def r := true

end

inductive Foo {α} [DecidableEq α] where
| x
