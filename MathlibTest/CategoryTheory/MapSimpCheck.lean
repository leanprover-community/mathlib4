module

public import MathlibTest.CategoryTheory.MapSimp

open Lean Meta Elab Term Command

namespace Tests.MapSimpCheck

def hasSimpAttribute (env : Environment) (declName : Name) : Bool :=
  simpExtension.getState env |>.lemmaNames.contains <| .decl declName

run_cmd liftTermElabM do
  let env ← getEnv
  guard <| hasSimpAttribute env `Tests.MapSimp.comp_map_simp
  guard <| hasSimpAttribute env `Tests.MapSimp.comp_map_simp_map
  guard <| hasSimpAttribute env `Tests.MapSimp.comp_map_simp_op
  guard <| hasSimpAttribute env `Tests.MapSimp.comp_map_simp_op_map
  guard <| hasSimpAttribute env `Tests.MapSimp.comp_map_simp_assoc
  guard <| hasSimpAttribute env `Tests.MapSimp.comp_map_simp_map_assoc
  guard <| hasSimpAttribute env `Tests.MapSimp.comp_map_simp_op_assoc
  guard <| hasSimpAttribute env `Tests.MapSimp.comp_map_simp_op_map_assoc

end Tests.MapSimpCheck
