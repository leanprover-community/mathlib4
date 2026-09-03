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
* the one destination resolution every upload addresses
  (`stagedUploadDestFrom`): the `--container` write, under the container's
  Azure base or the root `MATHLIB_CACHE_PUT_URL` names. The destination contract
  itself (`StagedUploadDest`) lives in `Cache/Upload/Dest.lean`.

`Cache/Upload.lean` decides the upload and runs the complete `put`,
dispatching to the selected backend. The marker path contract and write mechanics live in
`Cache/Marker.lean`. The read side (`Cache/Requests.lean`) shares the path
contract through `fileDirPath` and `markerDirPath` (`Cache/Infra.lean`), so
every upload addresses the URLs the readers probe.
-/

namespace Cache.Requests

open System (FilePath)

/-- The storage backend an upload targets, selected with `--backend=NAME`.
Each backend implements the complete upload in its own module: credential
resolution, transfer tool, and the transfer. `uploadFiles` dispatches on this
type. -/
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

/-- The containers an upload can write: every container but the read-only `legacy`. -/
def uploadContainers : List Container := Container.all.filter (· != .legacy)

/--
Resolve where a staged set uploads. The artifact puts and the marker put, on
every tool, address `{base}/{prefix}/{name}` of the result.

An upload writes one container, `container?`, which `--container` names: the
container decides the layout under its root (`containerUploadDest`), flat for
`master` and repo-namespaced for the others. The root is the URL
`MATHLIB_CACHE_PUT_URL` names (`putURL?`), which moves the container's writes
to another store; without it the azure backend writes the container on the
Azure storage account (`Container.azureURL`). A bucket URL is
account-specific, so the s3 backend has no default and requires the variable,
in the form `https://endpoint/bucket[/prefix]` (`s3EndpointSplit`). An empty
value means unset.

A scope addresses a per-commit namespace, so it is an error on a container
without one (`Container.perCommit`). `legacy` is read-only.
-/
def stagedUploadDestFrom (backend : UploadBackend) (putURL? : Option String)
    (container? : Option Container) (repo : String) (scope? : Option String) :
    Except String StagedUploadDest := do
  let some c := container? | throw s!"an upload writes one container: pass --container=NAME \
    (one of {", ".intercalate (uploadContainers.map Container.name)})"
  if c == .legacy then throw "the legacy container is read-only"
  if let some sha := scope? then
    unless c.perCommit do
      throw s!"scope {sha} set for an upload to {c.name}, which has no per-commit namespaces: \
        unset --scope and MATHLIB_CACHE_REPO_SCOPE"
  let base ← match normalizeBaseURL putURL?, backend with
    | some url, _ => pure url
    | none, .azure => pure c.azureURL
    | none, .s3 => throw "the s3 backend writes under the URL MATHLIB_CACHE_PUT_URL names \
        (https://endpoint/bucket[/prefix], the container's root): set it"
  if backend == .s3 then discard (s3EndpointSplit base)
  return containerUploadDest base c repo scope?

end Cache.Requests
