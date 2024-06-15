import Mathlib.Tactic.DeprSinceAction

/-- The entrypoint to the `lake exe update_deprecations` command. -/
def main (args : List String) : IO UInt32 := UpdateDeprecations.updateDeprecations.validate args
