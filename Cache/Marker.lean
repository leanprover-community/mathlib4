/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Cache.Requests

/-!
# Cache marker operations

`uploadMarker` uploads the marker derived from a location after its artifacts.
`checkMarker` probes that marker to check whether the commit has a cached build.
`Location.marker?` defines the marker path and whether a location has a marker.
-/

public section

namespace Cache.Requests

open System (FilePath)

/--
Upload the marker derived from `location`, if present. The temporary file
contains the marker's SHA and is removed after the transfer. `transfer`
receives the resolved marker and the file to upload. Repeated writes are
safe because the content is always the same SHA. The content helps with
debugging; the marker's presence signals completion.

Call this after the artifact uploads complete. A transfer failure warns
instead of throwing: the artifacts are already uploaded, and the only loss
is that `cache query` will not find this commit.

A marker records completion only at its own destination. When destinations
receive uploads independently, a marker does not establish that its
destination holds the commit's full transitive closure. The infrastructure
documentation governs when markers may be trusted for completeness.
-/
def uploadMarker (location : Location)
    (transfer : Location.Marker → FilePath → IO Unit) : IO Unit := do
  let some marker := location.marker? | return
  let dir ← IO.FS.createTempDir
  try
    let file := dir / marker.sha
    IO.FS.writeFile file s!"{marker.sha}\n"
    transfer marker file
  catch e =>
    IO.eprintln s!"warning: marker upload to {marker.url} failed: {e}"
  finally
    IO.FS.removeDirAll dir

/--
Probe the marker derived from `location`. Return `false` without a request
when the location has no marker. Otherwise issue an anonymous HEAD against
the marker URL and return `true` iff the response is 200. The marker is uploaded by `put-staged`
after a successful upload, so its presence means CI published this commit's
artifacts. Absence is a weaker signal: CI may not have built the commit yet,
or its build staged no files — a commit with no cache-relevant changes is
fully served by the master container, so CI uploads nothing for it, marker
included.

Cheaper than blob-listing: deterministic URL, headers-only response,
billed as a Read op.
-/
def checkMarker (location : Location) : IO Bool := do
  let some marker := location.marker? | return false
  -- Discard the response body to the platform null device (`NUL` on Windows),
  -- so curl reports a write error only on a genuine failure, not on every probe.
  let out ← IO.Process.output
    {cmd := (← IO.getCurl),
     args := #["-s", "-o", IO.nullDevice, "-w", "%{http_code}", "-I"] ++
       -- No retry flags: the probe is diagnostic and a false negative is
       -- cheap. The time bounds keep an unreachable endpoint from stalling
       -- the up-to-50-probe `cache query` walk.
       curlFollowRedirectArgs ++
       #["--connect-timeout", "10", "--max-time", "30", marker.url],
     cwd := "."}
  if out.exitCode != 0 then
    -- Network error; assume no cache at this SHA
    pure false
  else
    pure (out.stdout.trimAscii.toString == "200")

end Cache.Requests
