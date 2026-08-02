/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-!
# Native dependencies of the Mathlib cache

Mathlib's cache owns Lean artifacts, but a dependency can instead publish a
platform-specific Lake build archive. Prepare these dependencies before the
ordinary cache download so `lake exe cache get` still reconstructs a checkout
on which `lake build --no-build` succeeds.
-/

namespace Cache.Native

/-- Allowlisted dependency targets, in order. The release supplies the expensive
solver build; `CSDP` then refreshes its toolchain-sensitive Lean wrapper. -/
def prefetchTargets : Array String := #["@CSDP:release", "CSDP:shared"]

/-- Only commands which unpack the ordinary Mathlib cache promise a complete
build tree. `get-` intentionally downloads without unpacking and does not. -/
def shouldPrefetch (positionalArgs : List String) : Bool :=
  positionalArgs.head?.any fun command => command == "get" || command == "get!"

/-- Prepare every provider-owned native dependency, inheriting the terminal so
Lake can show download progress and diagnostics directly. -/
def prefetchDependencies : IO Unit := do
  for target in prefetchTargets do
    IO.println s!"Preparing native dependency {target}"
    let child ← IO.Process.spawn {cmd := "lake", args := #["build", target]}
    let exitCode ← child.wait
    unless exitCode == 0 do
      throw <| IO.userError s!"failed to prepare native dependency {target}"

end Cache.Native
