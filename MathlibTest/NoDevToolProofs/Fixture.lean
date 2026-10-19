module

public section

namespace MathlibTest.NoDevToolProofs.Fixture

def scalarValue : Nat := 7

private theorem hidden : True := True.intro

theorem visible : True := hidden

-- A proof need not be stored as a theorem declaration.
set_option linter.defProp false in
def proofValuedDefinition : True := True.intro

structure ToolData where
  value : Nat

-- Materialize the reserved injectivity theorem so the checker must inspect it too.
#guard_msgs (drop info) in
#check ToolData.mk.injEq
