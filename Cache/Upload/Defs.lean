/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Cache.Upload.Azure
public import Cache.Upload.S3

/-!
# The upload contract

The backend-neutral layer over the backend modules:

* the backend selection (`UploadBackend`). The backends implement the upload
  in `Cache/Upload/S3.lean` and `Cache/Upload/Azure.lean`: credentials,
  transfer tool, and the transfer;
* the location resolution that every upload uses (`uploadLocation`): the
  `MATHLIB_CACHE_PUT_URL` endpoint, or the location of the selected backend.
  `Location` lives in `Cache/Location.lean`, and the reads use it too.

`Cache/Upload.lean` runs the complete `put`, dispatching to the selected
backend. `Cache/Location.lean` derives the marker. `Cache/Marker.lean`
defines its read and write operations. The reads resolve their locations
with the same resolvers (`Container.location`, `Location.ofEndpoint`), so
every upload writes to the URLs that the reads probe.
-/

public section

namespace Cache.Requests

open System (FilePath)

/-- The storage backend an upload targets, selected with `--backend=NAME`.
Each backend implements the upload in its own module: credential
resolution, transfer tool, and the transfer. `runPut` dispatches on this
type. -/
inductive UploadBackend where
  /-- Azure Blob Storage (`Cache/Upload/Azure.lean`), at a flat endpoint only. -/
  | azure
  /-- An S3-compatible bucket (`Cache/Upload/S3.lean`); the default. -/
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
fails the upload and does not divert it to the backend's location. The
read variables take the opposite rule, where an empty value means unset.

Without it, the s3 backend writes the container layout under the bucket that
`MATHLIB_CACHE_PUT_BASE_URL` names (`putBase?`, empty means unset;
`s3UploadLocationFrom`). The azure backend has no container layout, so it
errors.
-/
def uploadLocationFrom (backend : UploadBackend) (putUrl? putBase? : Option String)
    (container? : Option Container) (repo : String) (scope? : Option String) :
    Except String Location := do
  let dest ← if let some url := putUrl? then
      pure (.ofEndpoint url "MATHLIB_CACHE_PUT_URL" repo scope?)
    else
      let putBase? := normalizeBaseURL putBase?
      match backend with
      | .azure => .error "the azure backend uploads only to a flat endpoint: \
          set MATHLIB_CACHE_PUT_URL"
      | .s3 => s3UploadLocationFrom putBase? container? repo scope?
  -- An s3 root must have the form `https://endpoint/bucket[/prefix]`.
  if backend == .s3 then discard (s3EndpointSplit dest.root)
  return dest

/--
`uploadLocationFrom` on the environment variables `MATHLIB_CACHE_PUT_URL` and
`MATHLIB_CACHE_PUT_BASE_URL`. `scope?` is the caller's resolved scope
(`getRepoScope`). A repo-namespaced location retains it in its scope.
The location derives both the file directory and its optional marker, so
every transfer tool uses one resolution.
-/
def uploadLocation (backend : UploadBackend) (container? : Option Container)
    (repo : String) (scope? : Option String) : IO Location := do
  let putUrl? ← IO.getEnv "MATHLIB_CACHE_PUT_URL"
  let putBase? ← IO.getEnv "MATHLIB_CACHE_PUT_BASE_URL"
  IO.ofExcept <| uploadLocationFrom backend putUrl? putBase? container? repo scope?

end Cache.Requests
