import Mathlib.Util.AddRelatedDecl

open Lean Meta Mathlib.Tactic

namespace AddRelatedDeclTest

theorem source : 0 + 0 = 0 := rfl

run_elab
  let attrs ← `(optAttrArg|)
  addRelatedDecl ``source `AddRelatedDeclTest.inferred (← getRef) attrs fun value levels => do
    let pf ← mkFreshExprMVar (← inferType value)
    pf.mvarId!.assign (← mkEqRefl (mkNatLit 0))
    return (pf, levels)
  addRelatedDeclWithType ``source `AddRelatedDeclTest.explicitType (← getRef) attrs
    fun value levels => do
      return (← inferType value, ← mkEqRefl (mkNatLit 0), levels)

-- The inferred-type API instantiates the assigned proof before inferring its type.
/-- info: AddRelatedDeclTest.inferred : 0 = 0 -/
#guard_msgs in
#check inferred

-- The explicit-type API preserves both sides, even though the proof is `Eq.refl 0`.
/-- info: AddRelatedDeclTest.explicitType : 0 + 0 = 0 -/
#guard_msgs in
#check explicitType

run_cmd do
  let env ← getEnv
  unless defeqAttr.hasTag env ``inferred && defeqAttr.hasTag env ``explicitType do
    throwError "Expected Lean to infer the defeq attributes"

end AddRelatedDeclTest
