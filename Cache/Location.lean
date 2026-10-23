/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Cache.Infra

/-!
# Cache locations

A location is a root URL and an optional scope. A scope names a repo and,
optionally, a commit. Files use the scope as a directory under `f`. A commit
marker uses the same scope as a file under `m`. Flat locations and repo
scopes without a commit have no marker.

`Container.location` and `Container.locationAt` select the layout of a known
container. `Location.flat` is the flat layout of a user-supplied endpoint.
The constructors trim whitespace and remove trailing slashes from URLs.
The location constructs the file paths and derives its marker. A read tries
the locations its workflow builds, in trust order (`Cache.Workflow`). An
upload writes to one location (`uploadLocationFrom`). `Cache/Marker.lean`
defines the marker read and write operations.
-/

public section

namespace Cache.Requests

/-- The repo namespace, optionally restricted to a commit. -/
structure Location.Scope where
  repo : String
  sha? : Option String
  deriving Repr, BEq, Inhabited

/-- The shared path under the file and marker trees. -/
def Location.Scope.path (scope : Location.Scope) : String :=
  let repo := normalizeRepo scope.repo
  match scope.sha? with
  | none => repo
  | some sha => s!"{repo}/{sha}"

/-- A cache root and its scope. An absent scope selects the flat file layout.
`root` has no trailing slash. `label` names the location in messages. -/
structure Location where
  root : String
  label : String
  scope? : Option Location.Scope
  deriving Repr, BEq, Inhabited

namespace Location

/-- Normalize a URL without treating an empty value as an absent endpoint. -/
private def normalizeRoot (url : String) : String :=
  (url.trimAscii.dropEndWhile '/').copy

/-- The directory of cache files relative to the root. -/
def filesDir (location : Location) : String :=
  match location.scope? with
  | none => "f"
  | some scope => s!"f/{scope.path}"

/-- The URL of one cache file. -/
def fileURL (location : Location) (fileName : String) : String :=
  s!"{location.root}/{location.filesDir}/{fileName}"

/-- The commit SHA for read messages and summaries, if the scope names one. -/
def sha? (location : Location) : Option String :=
  location.scope?.bind (·.sha?)

/-- A resolved commit marker. Its SHA also supplies the marker's contents. -/
structure Marker where
  root : String
  path : String
  sha : String
  deriving Repr, BEq, Inhabited

/-- The URL of a resolved marker. -/
def Marker.url (marker : Marker) : String :=
  s!"{marker.root}/{marker.path}"

/-- Derive the marker an upload writes after its files. Flat locations and
repo scopes without a SHA have no marker. A commit scope is a directory
under `f` and a marker file under `m`. -/
def marker? (location : Location) : Option Marker := do
  let scope ← location.scope?
  let sha ← scope.sha?
  return { root := location.root, path := s!"m/{scope.path}", sha }

/-- The URL of the location's marker, if present. -/
def markerURL? (location : Location) : Option String :=
  location.marker?.map (·.url)

/-- A user-supplied endpoint, read flat at `{url}/f/{fileName}` whatever the
repo. -/
def flat (url label : String) : Location :=
  { root := normalizeRoot url, label, scope? := none }

end Location

/-- The location of container `c` at `root`, the URL that holds the
container's `f/` and `m/` trees. The container selects a flat layout or a repo
scope. The location constructs the file and marker paths. -/
def Container.locationAt (c : Container) (root repo : String)
    (sha? : Option String) : Location :=
  { root := Location.normalizeRoot root, label := c.name,
    scope? := if c.flatPath then none else some { repo, sha? } }

/-- The location of container `c` under `base`, a host that serves the
`/{container}/{key}` namespace: `Container.locationAt` at the container's
URL under `base`. -/
def Container.location (c : Container) (base repo : String)
    (sha? : Option String) : Location :=
  c.locationAt (c.urlUnder (Location.normalizeRoot base)) repo sha?

end Cache.Requests
