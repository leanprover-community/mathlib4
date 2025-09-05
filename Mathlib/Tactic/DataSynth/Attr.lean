import Mathlib.Tactic.DataSynth.Decl
import Mathlib.Tactic.DataSynth.Types
import Mathlib.Tactic.DataSynth.Theorems

open Lean Meta

namespace Mathlib.Meta.DataSynth.Attr

syntax outParams := "out" ident*
syntax inParam := "in" ident*
syntax (name := data_synth) "data_synth" (ppSpace prio)? (outParams)? (inParam)? : attr

initialize dataSynthAttr : Unit ←
  registerBuiltinAttribute {
    name  := `data_synth
    descr := "data synthesis"
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName stx attrKind =>
       discard <| MetaM.run do
       let info ← getConstInfo declName

       forallTelescope info.type fun _ b => do
         if b.isSort then
           match stx with
           | `(attr| data_synth out $outArgs* $[in $inArg]?) =>
              let outArgs := outArgs.map (fun arg => arg.getId)
              let inArg := inArg.map (fun x => x.getId)
              addDataSynthDecl declName outArgs
           | _ => throwError "when declaring new `data_synth` the expected attribute syntax is: \
                            \n  @[data_syth out x₁ ... xₙ] \
                            \nwhere `xᵢ` are names of output arguments"
         else
           addTheorem declName attrKind (← getAttrParamOptPrio stx[1])
    erase := fun _declName =>
      throwError "can't remove `data_synth` attribute (not implemented yet)"}

end Mathlib.Meta.DataSynth.Attr
