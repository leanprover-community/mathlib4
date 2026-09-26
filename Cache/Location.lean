/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Marker

/-!
# Cache locations

A location is where a set of cache files lives: a root URL, and the
directories of the files and of the per-SHA markers under it. Every read and
every upload builds its URLs from a location (`Location.fileURL`,
`Location.markerURL`), so the two sides share one path contract.

A location knows nothing of containers. A known container is a shorthand
that resolves to a location (`Container.location`): its layout
(`fileDirPath`) under its root. A user-supplied URL
(`MATHLIB_CACHE_GET_URL`, `MATHLIB_CACHE_PUT_URL`) resolves through
`Location.ofEndpoint`. A read resolves a trust-ordered list of locations and
downloads through it (`readLocations`); an upload resolves one location and
writes to it (`uploadLocation`).
-/

namespace Cache.Requests

/--
Where a set of cache files lives. `root` is the URL that holds the `f/` and
`m/` trees, with no trailing slash: a container's URL on a read host, a
container on an upload base, or a user-supplied endpoint. `filesDir` and
`markerDir` are relative to it and carry no trailing slash. `scope?` is the
per-SHA scope of the files, if any; an upload writes its marker after the
files when it is set. `label` names the location in messages.
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

/-- The location of a user-supplied endpoint `url` for `repo` at the per-SHA
scope `scope?`. No container policy applies: the files are flat for
`MATHLIBREPO` and repo-namespaced otherwise (`fileDirPath none`). -/
def ofEndpoint (url label : String) (repo : String) (scope? : Option String) : Location :=
  { root := url, label, scope?,
    filesDir := fileDirPath none repo scope?, markerDir := markerDirPath repo }

end Location

/--
The location container `c` stands for at `root`, the container's URL on a
read host or an upload base (`Container.urlUnder`), for `repo` at the per-SHA
scope `scope?`. The files follow the container's layout (`fileDirPath`).
-/
def Container.location (c : Container) (root : String) (repo : String)
    (scope? : Option String) : Location :=
  { root, label := c.name, scope?,
    filesDir := fileDirPath (some c) repo scope?, markerDir := markerDirPath repo }

end Cache.Requests
