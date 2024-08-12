import Mathlib

open Lean Meta

#discr_tree_simp_key Submodule.smul_torsionBy

run_cmd do
  let env ← getEnv
  let noSuccess := env.getAllSimpSuccesses.filter (fun a => a.2 == 0)
  let mut arr := #[]
  for (n, _) in noSuccess do
    if let some attempts := env.getSimpHeartbeats? n then
      -- if attempts > 100 then
      arr := arr.push (n, attempts)
      -- msgs := msgs.push m!"{n} : {attempts}"
  arr := arr.qsort (fun a b => a.2 > b.2)
  logInfo m!"noSuccess: {arr}"
  -- logInfo m!"total heartbeats {arr.foldl (fun acc a => acc + a.2) 0}"

  -- let simpsAttempts := (env.getAllAttempts |>.qsort (fun a b => a.2 > b.2))[0:100]
  -- let mut msgs := #[]
  -- for (n, attempts) in simpsAttempts do
  --   let success := env.getSuccesses? n |>.get!
  --   let successRate := (success : ℚ) / attempts |>.toFloat
  --   if successRate < 0.05 then
  --   msgs := msgs.push m!"{n} : {successRate} : {attempts}"
  -- logInfo m!"simpsAttempts: {msgs}"


  -- logInfo m!"simpsAttempts: {simpsAttempts}"

run_cmd do
  let env ← getEnv
  let allHearts := env.getAllSimpHeartbeats
  let sorted := (allHearts.qsort (fun a b => a.2 > b.2))[0:100]
  let mut arr := #[]
  for (n, heartbeats) in sorted do
    let success := env.getSimpSuccesses? n |>.get!
    let attempts := env.getSimpAttempts? n |>.get!
    let successRate := (success : ℚ) / attempts |>.toFloat
    arr := arr.push (n, attempts, successRate, heartbeats)
  logInfo m!"sorted: {arr}"


run_cmd do
  let env ← getEnv
  let allHearts := env.getAllSimpHeartbeats
  let mut arr := #[]
  for (n, heartbeats) in allHearts do
    let attempts := env.getSimpAttempts? n |>.get!
    let success := env.getSimpSuccesses? n |>.get!
    let rate := (heartbeats : ℚ) / attempts |>.toFloat
    let successRate := (success : ℚ) / attempts |>.toFloat
    arr := arr.push (n, attempts, successRate, rate)
  let sorted := (arr.qsort (fun a b => a.2.1 > b.2.1))[0:100]
  logInfo m!"sorted: {sorted}"

run_cmd do
  let env ← getEnv
  let noSuccess := env.getAllSimpSuccesses.filter (fun a => a.2 == 0)
  let mut arr := #[]
  for (n, _) in noSuccess do
    let heartbeats := env.getSimpHeartbeats? n |>.get!
    let attempts := env.getSimpAttempts? n |>.get!
    arr := arr.push (n, attempts, heartbeats)
  arr := (arr.qsort (fun a b => a.2.2 > b.2.2))[0:100]
  logInfo m!"noSuccess: {arr}"

open Lean Meta Elab Tactic DiscrTreeKey in
open private mkKey from Lean.Elab.Tactic.DiscrTreeKey in
run_meta do
  let env ← getEnv
  let noSuccess := env.getAllSimpSuccesses.filter (fun a => a.2 == 0)
  let arr ← noSuccess.mapM (fun (n, _) => do
    let attempts := env.getSimpAttempts? n |>.get!
    let info ← getConstInfo n
    let keys ← liftMetaM <| mkKey info.type true
    return (n, attempts, keys))
  let sorted := (arr.qsort (fun a b => a.2.1 > b.2.1))[0:100]
  logInfo m!"noSuccess: {sorted}"

run_cmd do
  let env ← getEnv
  let attempts := (instStatExt.getState env).stats |>.toArray
  let sorted := (attempts.qsort (fun a b => a.2 > b.2))[0:100]
  logInfo m!"sorted: {sorted}"

