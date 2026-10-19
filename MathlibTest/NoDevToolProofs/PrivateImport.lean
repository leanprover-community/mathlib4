module

public meta import MathlibTest.NoDevToolProofs.PrivateFacade

meta import MathlibTest.NoDevToolProofs.Check

/-- info: 7 -/
#guard_msgs in
#eval MathlibTest.NoDevToolProofs.privateFacadeValue

-- The imported package is present, but its privately imported proofs are not public exports.
run_cmd MathlibTest.NoDevToolProofs.assertNoPublicProofs #["mathlib"]
