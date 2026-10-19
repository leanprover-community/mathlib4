module

public import MathlibTest.NoDevToolProofs.Fixture

meta import MathlibTest.NoDevToolProofs.Check

open MathlibTest.NoDevToolProofs

run_cmd do
  let actual ← publicProofsFrom #["mathlib"]
  let expected := #[
    `MathlibTest.NoDevToolProofs.Fixture.ToolData.mk.inj,
    `MathlibTest.NoDevToolProofs.Fixture.ToolData.mk.injEq,
    `MathlibTest.NoDevToolProofs.Fixture.ToolData.mk.sizeOf_spec,
    `MathlibTest.NoDevToolProofs.Fixture.proofValuedDefinition,
    `MathlibTest.NoDevToolProofs.Fixture.visible]
  unless actual == expected do
    throwError "Unexpected public proof declarations: {actual}"

/-- error: Public proof declarations from restricted packages -/
#guard_msgs (substring := true) in
run_cmd assertNoPublicProofs #["mathlib"]

/-- error: No imported modules belong to restricted package 'nonexistent-test-package'. -/
#guard_msgs in
run_cmd assertNoPublicProofs #["nonexistent-test-package"]
