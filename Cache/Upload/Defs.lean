/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Marker
import Cache.Upload.Azure
import Cache.Upload.S3

/-!
# The upload contract

The backend-neutral layer over the backend modules:

* the backend selection (`UploadBackend`). The backends implement the upload
  in `Cache/Upload/Azure.lean` and `Cache/Upload/S3.lean`: credentials,
  destination, transfer tool, and the transfer;
* the one location resolution every upload addresses (`uploadLocation`): the
  flat `MATHLIB_CACHE_PUT_URL` override, or the selected backend's own
  location. The location type itself (`Location`) lives in
  `Cache/Location.lean`, shared with the reads.

`Cache/Upload.lean` runs the complete `put`, dispatching to the selected
backend. The marker path contract and write mechanics live in
`Cache/Marker.lean`. The reads resolve their locations with the same
resolvers (`Container.location`, `Location.ofEndpoint`), so every upload
addresses the URLs the readers probe.
-/

namespace Cache.Requests

open System (FilePath)

/-- The storage backend an upload targets, selected with `--backend=NAME`.
Each backend implements the complete upload in its own module: credential
resolution, destination, transfer tool, and the transfer. `runPut` dispatches
on this type. -/
inductive UploadBackend where
  /-- Azure Blob Storage (`Cache/Upload/Azure.lean`); the default. -/
  | azure
  /-- An S3-compatible bucket (`Cache/Upload/S3.lean`). -/
  | s3
  deriving DecidableEq, Repr, BEq, Inhabited

namespace UploadBackend

/-- Canonical short name for a backend, used in the `--backend` flag. -/
def name : UploadBackend → String
  | .azure => "azure"
  | .s3    => "s3"

/-- All known backends, listed in their canonical declaration order. -/
def all : List UploadBackend := [.azure, .s3]

/-- Parse a short name back into an `UploadBackend`. Matching is
case-insensitive. -/
def parse? (s : String) : Option UploadBackend :=
  match s.toLower with
  | "azure" => some .azure
  | "s3"    => some .s3
  | _       => none

end UploadBackend

/--
Pure core of `uploadLocation`: resolve where a staged set uploads.

`MATHLIB_CACHE_PUT_URL` (`putUrl?`) wins on every backend: a flat endpoint
with the container policy off, while the selected backend signs the requests.
Any set value counts here, an empty one included: a misconfigured endpoint
fails the upload and does not divert it to the backend's destination. The
read variables take the opposite rule, where an empty value means unset.

Without it, the backend resolves its own location (`azureUploadLocationFrom`,
`s3UploadLocationFrom`): the container write, rebased under the base
`MATHLIB_CACHE_PUT_BASE_URL` names (`putBase?`, empty means unset). The azure
backend defaults to the Azure account when the base is unset; the s3 backend
has no default, because a bucket endpoint is account-specific.
-/
def uploadLocationFrom (backend : UploadBackend) (putUrl? putBase? : Option String)
    (container? : Option Container) (repo : String) (scope? : Option String) :
    Except String Location := do
  let dest ← if let some url := putUrl? then
      -- A user-supplied URL carries no container policy (`Location.ofEndpoint`).
      pure (.ofEndpoint url "(env override)" repo scope?)
    else
      let putBase? := normalizeBaseURL putBase?
      match backend with
      | .azure => azureUploadLocationFrom putBase? container? repo scope?
      | .s3 => s3UploadLocationFrom putBase? container? repo scope?
  -- An s3 root must have the form `https://endpoint/bucket[/prefix]`.
  if backend == .s3 then discard (s3EndpointSplit dest.root)
  return dest

/--
`uploadLocationFrom` on the endpoint variables in the environment. `scope?`
is the caller's resolved scope (`getRepoScope`); the location carries it to
the marker write, so one resolution serves the whole upload. The artifact puts
and the marker put, on every tool, address the location's URLs.
-/
def uploadLocation (backend : UploadBackend) (container? : Option Container)
    (repo : String) (scope? : Option String) : IO Location := do
  let putUrl? ← IO.getEnv "MATHLIB_CACHE_PUT_URL"
  let putBase? ← IO.getEnv "MATHLIB_CACHE_PUT_BASE_URL"
  IO.ofExcept <| uploadLocationFrom backend putUrl? putBase? container? repo scope?

end Cache.Requests
