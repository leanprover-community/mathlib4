module

public import MathlibTest.CategoryTheory.MapSimp

open Lean Meta Elab Term Command

namespace Tests.MapSimpCheck

def hasSimpAttribute (env : Environment) (declName : Name) : Bool :=
  simpExtension.getState env |>.lemmaNames.contains <| .decl declName

-- Test that simp attributes are added to all four generated lemmas with
-- `@[map (attr := reassoc (attr := simp))]`.
run_cmd liftTermElabM do
  let env ← getEnv
  guard <| hasSimpAttribute env ``Tests.MapSimp.comp_map_simp
  guard <| hasSimpAttribute env ``Tests.MapSimp.comp_map_simp_map
  guard <| hasSimpAttribute env ``Tests.MapSimp.comp_map_simp_assoc
  guard <| hasSimpAttribute env ``Tests.MapSimp.comp_map_simp_map_assoc

end Tests.MapSimpCheck
