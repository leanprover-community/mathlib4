/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Requests

/-!
# Per-SHA cache markers

A marker is a tiny blob at `/m/{repo}/{sha}` whose existence signals that the
full `.ltar` upload for a commit completed. `cache put` writes it as the last
upload step, and `cache query` probes it to discover cached commits with a
cheap HEAD request instead of a blob listing.

This module holds everything about the marker except the transfer itself: the
path contract (`markerDirPath`, `markerPath`), the read-side URL
(`markerReadURL`), and the write mechanics and failure policy the upload
engines share (`uploadMarkerWith`).
-/

namespace Cache.Requests

open System (FilePath)

/--
Blob path of the directory that holds a repo's per-SHA markers: `m/{repo}`,
with `repo` lowercased via `normalizeRepo`. A marker for one commit lives at
`{markerDirPath repo}/{sha}`; its presence signals that the writing `put`
completed its upload to that destination.
-/
def markerDirPath (repo : String) : String :=
  s!"m/{normalizeRepo repo}"

/-- Blob path of the per-SHA marker: `m/{repo}/{sha}` (see `markerDirPath`). -/
def markerPath (repo sha : String) : String :=
  s!"{markerDirPath repo}/{sha}"

/--
Read-side URL for the per-SHA marker blob: probes follow the read base
(`Container.getURL`), unlike marker writes, which follow the resolved
upload destination (`StagedUploadDest.markerURL`).
-/
def markerReadURL (container : Container) (repo sha : String) : IO String := do
  return s!"{← container.getURL}/{markerPath repo sha}"

/--
Write the marker file for `sha` and hand it to `transfer`, which moves it to
`markerURL` — the marker mechanics every upload engine shares. The blob
content is the SHA itself, as a debugging aid; existence is the signal. A
marker overwrites freely (its content is its own name), so a re-upload of an
already-marked commit does not fail here.

Runs after the `.ltar` artifact uploads complete, and a `transfer` failure
warns instead of throwing: the artifacts are already uploaded — the only loss
is that `cache query` will not find this commit.

A marker applies only to its own destination: it records that the writing
`put` completed there. When several destinations receive uploads
independently, one destination's marker does not say that the destination
holds a commit's full transitive closure; the infrastructure documentation
governs when a destination's markers may be trusted for completeness.
-/
def uploadMarkerWith (markerURL sha : String) (transfer : FilePath → IO Unit) :
    IO Unit := do
  let dir ← IO.FS.createTempDir
  try
    let file := dir / sha
    IO.FS.writeFile file s!"{sha}\n"
    transfer file
  catch e =>
    IO.eprintln s!"warning: marker upload to {markerURL} failed: {e}"
  finally
    IO.FS.removeDirAll dir

end Cache.Requests
