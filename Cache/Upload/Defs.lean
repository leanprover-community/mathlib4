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
* the location resolution for every upload (`uploadLocationFrom`).

`Cache/Upload.lean` runs the complete `put`, dispatching to the selected
backend. `Cache/Location.lean` derives the marker. `Cache/Marker.lean`
defines its read and write operations. The reads resolve their locations
with the same container layout (`Container.locationAt`), so every upload
writes to the URLs that the reads probe.
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
Resolve where a staged set uploads. The artifact puts and the marker put, on
every tool, address the resulting location.

An upload writes one container, `container?`, which `--container` names: the
container decides the layout under its root (`Container.locationAt`), flat for
`master` and repo-namespaced for `forks`. The root is the URL
`MATHLIB_CACHE_PUT_URL` names (`putURL?`), and every backend requires it. The
s3 backend requires the form `https://endpoint/bucket[/prefix]`
(`s3EndpointSplit`). An empty value means unset.

A scope addresses a per-commit namespace, so it is an error on a container
without one (`Container.perCommit`).
-/
def uploadLocationFrom (backend : UploadBackend) (putURL? : Option String)
    (container? : Option Container) (repo : String) (scope? : Option String) :
    Except String Location := do
  let some c := container? | throw s!"an upload writes one container: pass --container=NAME \
    (one of {", ".intercalate (Container.all.map Container.name)})"
  if let some sha := scope? then
    unless c.perCommit do
      throw s!"scope {sha} set for an upload to {c.name}, which has no per-commit namespaces: \
        unset --scope and MATHLIB_CACHE_REPO_SCOPE"
  let some root := normalizeBaseURL putURL? | throw s!"the {backend.name} backend writes under \
    the URL MATHLIB_CACHE_PUT_URL names (the container's root): set it"
  -- An s3 root must have the form `https://endpoint/bucket[/prefix]`.
  if backend == .s3 then discard (s3EndpointSplit root)
  return c.locationAt root repo scope?

end Cache.Requests
