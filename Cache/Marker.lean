/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Requests

/-!
# Per-SHA cache markers

A marker is a tiny blob at `/m/{repo}/{sha}` whose existence signals that the
full `.ltar` upload for a commit completed. `put-staged` writes it as the last
upload step, and `cache query` probes it to discover cached commits with a
cheap HEAD request instead of a blob listing.
-/

namespace Cache.Requests

open System (FilePath)

/--
Blob path of the per-SHA marker under a container base: `m/{repo}/{sha}`,
where `normalizeRepo` lowercases `repo` so the path is case-insensitive
in the GitHub owner/repo name.

The marker is uploaded by `put-staged` as the last step when an upload is
SHA-scoped (`MATHLIB_CACHE_REPO_SCOPE` set). Its presence at this path
indicates that the full `.ltar` upload completed for this commit, and lets
`cache query` discover cached commits with a cheap HEAD probe rather than
a blob-listing call.
-/
def markerPath (repo sha : String) : String :=
  s!"m/{normalizeRepo repo}/{sha}"

/--
Upload-side URL for the per-SHA marker blob. Writes authenticate against
Azure and address it directly; read probes build their URL from
`Container.getURL` instead (see `probeContainerForSHA`).
-/
def markerURL (container : Container) (repo sha : String) : String :=
  s!"{container.azureURL}/{markerPath repo sha}"

/--
Read-side URL for the per-SHA marker blob: probes follow the read base
(`Container.getURL`), unlike `markerURL`, which addresses Azure directly for
writes.
-/
def markerReadURL (container : Container) (repo sha : String) : IO String := do
  return s!"{← container.getURL}/{markerPath repo sha}"

/--
Upload a tiny marker blob to `/m/{repo}/{sha}` in the given container. The
blob content is the SHA itself, as a debugging aid; existence is the
signal.

Called from `put` and `put-staged` after the `.ltar` artifact uploads
complete. If this PUT fails the artifacts are already uploaded — the only
loss is that `cache query` will not find this commit — so failures here
are logged but not fatal.
-/
def uploadMarker (container : Container) (repo sha : String) (auth : UploadAuth) :
    IO Unit := do
  let url := markerURL container repo sha
  let path := IO.CACHEDIR / s!"marker-{sha}"
  IO.FS.createDirAll IO.CACHEDIR
  IO.FS.writeFile path s!"{sha}\n"
  let azureDateHeader ← getAzureDateHeader
  try
    let args := match auth with
      | .azureSas token =>
        #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob",
          "-T", path.toString, s!"{url}?{token}"]
      | .azureBearer token =>
        #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "-H",
          azureBearerApiVersionHeader, "-H", azureDateHeader, "--oauth2-bearer", token,
          "-T", path.toString, url]
    -- The argument list carries the credential; keep it out of the failure message.
    discard <| IO.runCurl args (showArgsOnError := false)
  catch e =>
    IO.eprintln s!"warning: marker upload to {url} failed: {e}"
  IO.FS.removeFile path

end Cache.Requests
