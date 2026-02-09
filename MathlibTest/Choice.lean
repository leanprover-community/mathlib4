import Lean.Environment
import Lean.Meta.Basic
import Lean.Elab.Command

open Lean Meta Elab Command

/-- Configuration for choice dependency analysis -/
structure ChoiceConfig where
  /-- Only analyze declarations in this namespace prefix (empty = all) -/
  namespacePrefix : String := ""
  /-- Show individual declarations (not just count) -/
  showDecls : Bool := false
  /-- Maximum number of declarations to show -/
  maxShow : Nat := 20
  /-- Maximum number of declarations to analyze (for quick testing, 0 = all) -/
  limit : Nat := 0
  deriving Inhabited

/-- Count how many declarations depend on the axiom of choice -/
def countChoiceDependentDecls (config : ChoiceConfig := {}) : MetaM (Nat × Nat × Array Name) := do
  let env ← getEnv
  let mut totalDecls := 0
  let mut choiceDependent := 0
  let mut choiceNames : Array Name := #[]

  -- Iterate through constants - using list but applying limit early
  let constList := env.constants.map₁.toList
  for (name, _) in constList do
    -- Check limit if specified
    if config.limit > 0 && totalDecls >= config.limit then
      break

    -- Filter by namespace prefix if specified
    if config.namespacePrefix != "" && !name.toString.startsWith config.namespacePrefix then
      continue

    totalDecls := totalDecls + 1

    -- Get axioms this declaration depends on
    let axioms ← collectAxioms name

    -- Check if it depends on Classical.choice
    if axioms.contains ``Classical.choice then
      choiceDependent := choiceDependent + 1
      choiceNames := choiceNames.push name

  return (choiceDependent, totalDecls, choiceNames)

/-- Command to count choice-dependent declarations -/
elab "#count_choice" limit:(num)? ns:(str)? showKw:("show")? : command => do
  let limitNum := limit.map (·.getNat) |>.getD 0
  let namespacePrefix := ns.map (·.getString) |>.getD ""
  let showDecls := showKw.isSome
  let config : ChoiceConfig := {
    namespacePrefix := namespacePrefix
    showDecls := showDecls
    limit := limitNum
  }

  let (choiceCount, total, names) ← liftTermElabM <| countChoiceDependentDecls config

  logInfo m!"Declarations depending on Classical.choice: {choiceCount} out of {total}"
  if total > 0 then
    logInfo m!"Percentage: {(choiceCount * 100 / total)}%"

  if showDecls then
    logInfo m!"\nFirst {min choiceCount config.maxShow} declarations:"
    for i in [0:min names.size config.maxShow] do
      logInfo m!"  {names[i]!}"
    if names.size > config.maxShow then
      logInfo m!"  ... and {names.size - config.maxShow} more"

-- Quick test on first 1000 declarations
#count_choice 100 show

-- For full analysis, uncomment:
-- #count_choice

-- Show specific declarations (uncomment to use):
-- #count_choice 1000 show

-- Analyze only Mathlib declarations (requires importing Mathlib):
-- #count_choice "Mathlib"
