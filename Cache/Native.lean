/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-!
# Prebuilt native dependencies of the Mathlib cache

Mathlib's cache owns Lean artifacts, but a dependency can instead publish one
complete, platform-specific Lake build archive. Fetch such archives before the
ordinary cache download so `lake exe cache get` still reconstructs a checkout
on which `lake build --no-build` succeeds.
-/

namespace Cache.Native

/-- Required release facets which own build trees outside the Mathlib cache. -/
def releaseTargets : Array String := #["@CSDP:release"]

/-- Only commands which unpack the ordinary Mathlib cache promise a complete
build tree. `get-` intentionally downloads without unpacking and does not. -/
def shouldPrefetch (positionalArgs : List String) : Bool :=
  positionalArgs.head?.any fun command => command == "get" || command == "get!"

/-- Fetch every provider-owned native release, inheriting the terminal so Lake
can show download progress and diagnostics directly. -/
def prefetchReleases : IO Unit := do
  for target in releaseTargets do
    IO.println s!"Fetching prebuilt native dependency {target}"
    let child ← IO.Process.spawn {cmd := "lake", args := #["build", target]}
    let exitCode ← child.wait
    unless exitCode == 0 do
      throw <| IO.userError s!"failed to fetch prebuilt native dependency {target}"

end Cache.Native
