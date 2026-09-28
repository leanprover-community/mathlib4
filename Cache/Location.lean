/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Cache.Marker

/-!
# Cache locations

A location is where a set of cache files and their per-SHA markers live: a
root URL, and the directories of the files and of the markers under it. Every
read and every upload builds its URLs from a location (`Location.fileURL`,
`Location.markerURL`), so reads and uploads share one path contract.

Two resolvers build a location:
* `Container.location`, for a known container. The root is the container's
  URL (`Container.urlUnder`), and the files follow the container's layout.
* `Location.ofEndpoint`, for a user-supplied URL (`MATHLIB_CACHE_GET_URL`,
  `MATHLIB_CACHE_PUT_URL`). The files follow the repo.

A read tries a trust-ordered list of locations (`readLocations`). An upload
writes to one location (`uploadLocation`).
-/

public section

namespace Cache.Requests

/--
Where a set of cache files and their per-SHA markers live. `root` is the URL
that holds the `f/` and `m/` trees, without a trailing slash: a container's URL
on a read host or on an upload base, or a user-supplied endpoint. `filesDir`
and `markerDir` are relative to `root`, without a trailing slash. `scope?` is
the per-SHA scope, if any. The resolvers pass it to the file layout
(`fileDirPath`), and an upload writes the marker of that SHA after the files.
`label` names the location in messages.
-/
structure Location where
  root : String
  label : String
  filesDir : String
  markerDir : String
  scope? : Option String := none
  deriving Repr, BEq, Inhabited

namespace Location

/-- URL of the cache file `fileName`: `{root}/{filesDir}/{fileName}`. -/
def fileURL (l : Location) (fileName : String) : String :=
  s!"{l.root}/{l.filesDir}/{fileName}"

/-- URL of the per-SHA marker of `sha`: `{root}/{markerDir}/{sha}`. -/
def markerURL (l : Location) (sha : String) : String :=
  s!"{l.root}/{l.markerDir}/{sha}"

/-- The location of the user-supplied endpoint `url` for `repo` at the per-SHA
scope `scope?`. The files are flat for `MATHLIBREPO` and repo-namespaced
otherwise (`fileDirPath none`). -/
def ofEndpoint (url label : String) (repo : String) (scope? : Option String) : Location :=
  { root := url, label, scope?,
    filesDir := fileDirPath none repo scope?, markerDir := markerDirPath repo }

end Location

/--
The location of container `c` at `root`, for `repo` at the per-SHA scope
`scope?`. `root` is the container's URL on a read host or on an upload base
(`Container.urlUnder`). The files follow the container's layout
(`fileDirPath`).
-/
def Container.location (c : Container) (root : String) (repo : String)
    (scope? : Option String) : Location :=
  { root, label := c.name, scope?,
    filesDir := fileDirPath (some c) repo scope?, markerDir := markerDirPath repo }

end Cache.Requests
