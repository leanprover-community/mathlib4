module

public import Lean

/-! Helpers for checking the public proof declarations exported by imported packages. -/

public section

namespace MathlibTest.NoDevToolProofs

open Lean Elab Command Meta

/-- Find all named public proof declarations from the selected packages, including generated ones.
Package ownership comes from import metadata, rather than declaration namespaces. -/
def publicProofsFrom (packages : Array String) : CommandElabM (Array Name) := liftTermElabM do
  let env ← getEnv
  for package in packages do
    unless env.header.moduleNames.any (fun mod =>
        (env.getModuleIdx? mod |>.bind env.getModulePackageByIdx?) == some package) do
      throwError "No imported modules belong to restricted package '{package}'."
  let publicEnv := env.setExporting true
  let mut proofs := #[]
  for (name, info) in env.constants do
    if isPrivateName name || (publicEnv.find? name).isNone then continue
    let some moduleIdx := env.getModuleIdxFor? name | continue
    let some package := env.getModulePackageByIdx? moduleIdx | continue
    unless packages.contains package do continue
    -- Imported theorems can be represented by opaque/axiom information. Inspect their types,
    -- rather than relying on the ConstantInfo constructor or the declaration's meta flag.
    if ← isProp info.type then proofs := proofs.push name
  return proofs.qsort fun a b => a.toString < b.toString

/-- Fail if any selected package exports a proof declaration into the current public scope. -/
def assertNoPublicProofs (packages : Array String) : CommandElabM Unit := do
  let proofs ← publicProofsFrom packages
  unless proofs.isEmpty do
    throwError m!"Public proof declarations from restricted packages ({proofs.size}):\n\
      {MessageData.joinSep (proofs.toList.map MessageData.ofConstName) m!"\n"}"

end MathlibTest.NoDevToolProofs
