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

* the backend selection (`UploadBackend`);
* the location resolution for every upload (`uploadLocation`).

`Cache/Upload.lean` runs the complete `put`, dispatching to the selected
backend. `Cache/Location.lean` derives the marker. `Cache/Marker.lean`
defines its read and write operations. The reads resolve their container
locations with `Container.location`, which builds on the same constructor
(`Container.locationAt`), so every upload writes to the URLs that the reads
probe.
-/

public section

namespace Cache.Requests

open System (FilePath)

/-- The storage backend an upload targets, selected with `--backend=NAME`.
`runPut` dispatches on this type. -/
inductive UploadBackend where
  /-- Azure Blob Storage (`Cache/Upload/Azure.lean`). -/
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

An upload writes one container, `container?`, which `--container` names. The
container decides the layout under its root (`Container.locationAt`): flat for
`master`, repo-namespaced for `forks`. The root is the URL
`MATHLIB_CACHE_PUT_URL` names (`putURL?`), on every backend. The tool has no
default root, because a store URL is account-specific. On the s3 backend the
root has the form `https://endpoint/bucket[/prefix]` (`s3EndpointSplit`). An
empty value means unset.

A scope addresses a per-commit namespace. A flat container has no per-commit
namespaces, so a scope on it is an error.
-/
def uploadLocationFrom (backend : UploadBackend) (putURL? : Option String)
    (container? : Option Container) (repo : String) (scope? : Option String) :
    Except String Location := do
  let some c := container? | throw s!"an upload writes one container: pass --container=NAME \
    (one of {", ".intercalate (Container.all.map Container.name)})"
  if let some sha := scope? then
    if c.flatPath then
      throw s!"scope {sha} set for an upload to {c.name}, which has no per-commit namespaces: \
        unset --scope and MATHLIB_CACHE_REPO_SCOPE"
  let some root := normalizeBaseURL putURL?
    | throw "an upload writes under the URL MATHLIB_CACHE_PUT_URL names, the container's \
        root: set it"
  if backend == .s3 then discard (s3EndpointSplit root)
  return c.locationAt root repo scope?

/--
`uploadLocationFrom` on the environment variable `MATHLIB_CACHE_PUT_URL`.
`scope?` is the caller's resolved scope (`getRepoScope`). A repo-namespaced
location retains it in its scope. The location derives both the file
directory and its optional marker, so every transfer tool uses one
resolution.
-/
def uploadLocation (backend : UploadBackend) (container? : Option Container)
    (repo : String) (scope? : Option String) : IO Location := do
  IO.ofExcept <| uploadLocationFrom backend (← IO.getEnv "MATHLIB_CACHE_PUT_URL")
    container? repo scope?

end Cache.Requests
