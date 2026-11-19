/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Cache.Upload
public import Lake.Config.Cache
public import Lake.Load.Manifest

/-!
# Lake's cache, keyed by the mathlib commit

`cache lake put` and `cache lake get` transfer the outputs of mathlib and of its dependencies in
the format of Lake's cache (`lake cache`). Every package keeps its artifacts and its revision files
under its own scope, `<prefix>/<name>/<toolchain-slug>`:

    artifacts/<prefix>/<name>/<toolchain-slug>/<content-hash>.art
    revisions/<prefix>/<name>/<toolchain-slug>/<mathlib-sha>.jsonl

`<name>` is the package name, `mathlib` for mathlib. The revision file of every package is named
by the mathlib commit, not by the package's own commit. The mathlib commit fixes the revisions of
all the packages in its manifest, so a revision file holds exactly the outputs of one build. Two
mathlib commits that pin one aesop revision against different batteries revisions therefore keep
separate revision files, and an artifact with identical bytes is stored once.

Lake stores a downloaded revision file as `revisions/<name>/<rev>.jsonl` in its local cache, and
reuses it. With the mathlib commit as `<rev>`, the local file also identifies exactly one build.

`put` signs its uploads with the S3 credentials of `cache put` (`getS3Auth`), so it accepts a
temporary credential with a session token. `get` makes the calls of `lake cache get` with the
revision file and the artifacts under these scopes.
-/

public section

namespace Cache.LakeCache

open Lake System Cache.IO Cache.Requests

/-- The package name of mathlib in the cache layout and in Lake's local cache. -/
def mathlibName : String := "mathlib"

/-- The file that `lake cache stage` writes in a staging directory. -/
def stagedOutputsFile : FilePath := "outputs.jsonl"

/-- The directory name of a toolchain: every character outside `A-Za-z0-9._-` becomes `-`. -/
def toolchainSlug (toolchain : String) : String :=
  toolchain.trimAscii.copy.map fun c =>
    if c.isAlphanum || c == '.' || c == '_' || c == '-' then c else '-'

/-- The scope of one package: its artifacts and its revision files. -/
def packageScope (pfx name slug : String) : String :=
  s!"{pfx}/{name}/{slug}"

/-- The URL of an artifact under `root`. Lake names every remote artifact `<hash>.art`, whatever
the extension of the local file. -/
def artifactURL (root scope : String) (descr : ArtifactDescr) : String :=
  s!"{root}/artifacts/{scope}/{descr.hash.hex}.art"

/-- The URL of a revision file under `root`. -/
def revisionURL (root scope rev : String) : String :=
  s!"{root}/revisions/{scope}/{rev}.jsonl"

/-- The commit, the toolchain slug and the prefix that select the revision files. -/
structure Target where
  pfx : String
  rev : String
  slug : String

/-- Resolves the target in the Mathlib checkout of `CacheM`. `rev?` is a git ref, `HEAD` when
absent. The toolchain slug comes from the checkout's `lean-toolchain`. -/
def resolveTarget (pfx : String) (rev? : Option String) : CacheM Target := do
  let rev ← resolveGitRef (rev?.getD "HEAD")
  let toolchain ← IO.FS.readFile ((← read).mathlibDepPath / "lean-toolchain")
  return { pfx, rev, slug := toolchainSlug toolchain }

/-- Runs a Lake logging action, and throws if it fails. -/
def runLogger (x : LoggerIO α) : IO α := do
  let some a ← x.toBaseIO
    | throw <| IO.userError "the Lake cache operation failed"
  return a

/-- The packages that `dir` stages: each subdirectory with an `outputs.jsonl`, by name, mathlib
last. -/
def stagedPackages (dir : FilePath) : IO (Array (String × FilePath)) := do
  let mut pkgs := #[]
  for entry in ← dir.readDir do
    if (← entry.path.isDir) && (← (entry.path / stagedOutputsFile).pathExists) then
      pkgs := pkgs.push (entry.fileName, entry.path)
  let sorted := pkgs.qsort (·.1 < ·.1)
  return sorted.filter (·.1 != mathlibName) ++ sorted.filter (·.1 == mathlibName)

/--
Uploads the packages that `stagingDir` stages, one subdirectory per package, as
`lake cache stage` writes it. The upload root is `MATHLIB_LAKE_CACHE_PUT_URL`, an S3 URL of the
form `https://endpoint/bucket[/prefix]`.

All artifacts go first, and then the revision files, mathlib's last. A reader that finds a
revision file therefore finds its artifacts. An artifact that is already present is not
overwritten. A revision file is.
-/
def put (stagingDir : FilePath) (target : Target) : CacheM Unit := do
  let some root := normalizeBaseURL (← IO.getEnv "MATHLIB_LAKE_CACHE_PUT_URL")
    | throw <| IO.userError "cache lake put needs MATHLIB_LAKE_CACHE_PUT_URL"
  discard (IO.ofExcept (s3EndpointSplit root))
  let signArgs := s3CurlArgs (← getS3Auth) (← getS3Region)
  discard <| validateCurl (upload := true)
  let pkgs ← stagedPackages stagingDir
  if pkgs.isEmpty then
    throw <| IO.userError s!"{stagingDir} stages no package: no subdirectory has an \
      {stagedOutputsFile}"
  let config := curlConfigIn stagingDir
  for (name, dir) in pkgs do
    let scope := packageScope target.pfx name target.slug
    let map ← runLogger (CacheMap.load (dir / stagedOutputsFile) (platformIndependent := true))
    let descrs ← runLogger map.collectOutputDescrs
    let uploads ← descrs.mapM fun descr => do
      let file := dir / descr.relPath
      unless ← file.pathExists do
        throw <| IO.userError s!"{file}: the staged artifact is missing"
      return (file, artifactURL root scope descr)
    putFilesViaCurl s!"{root}/artifacts/{scope}" uploads config (overwrite := false)
      (signArgs ++ #["-H", s!"Content-Type: {CacheService.artifactContentType}"])
  for (name, dir) in pkgs do
    let scope := packageScope target.pfx name target.slug
    putFilesViaCurl s!"{root}/revisions/{scope}"
      #[(dir / stagedOutputsFile, revisionURL root scope target.rev)] config (overwrite := true)
      (signArgs ++ #["-H", s!"Content-Type: {CacheService.mapContentType}"])

/-- The packages that `get` downloads: mathlib and the packages of mathlib's manifest. -/
def packageNames : CacheM (Array String) := do
  let entries ← Lake.Manifest.tryLoadEntries ((← read).mathlibDepPath / "lake-manifest.json")
  return #[mathlibName] ++ entries.map (·.name.toString (escape := false))

/--
Downloads the revision file and the artifacts of every package into Lake's cache for the
workspace in the current directory: `LAKE_CACHE_DIR` when it is set, `.lake/cache` otherwise.
The download root is `MATHLIB_LAKE_CACHE_GET_URL`.

A missing revision file of mathlib is an error. A missing revision file of a dependency is a
warning, and that dependency builds from source.
-/
def get (target : Target) : CacheM Unit := do
  let some root := normalizeBaseURL (← IO.getEnv "MATHLIB_LAKE_CACHE_GET_URL")
    | throw <| IO.userError "cache lake get needs MATHLIB_LAKE_CACHE_GET_URL"
  let cacheDir := (← getEnvNonEmpty "LAKE_CACHE_DIR").getD ".lake/cache"
  let cache : Lake.Cache := ⟨cacheDir⟩
  let service := CacheService.downloadService s!"{root}/artifacts" s!"{root}/revisions"
  for name in ← packageNames do
    let scope := CacheServiceScope.ofString (packageScope target.pfx name target.slug)
    let some map ← runLogger (service.downloadRevisionOutputs? target.rev cache name scope)
      | if name == mathlibName then
          throw <| IO.userError s!"the Lake cache has no outputs of {name} for \
            commit {target.rev}"
        else
          IO.eprintln s!"Warning: the Lake cache has no outputs of {name} for commit \
            {target.rev}; {name} builds from source"
          continue
    cache.writeMap name map (remoteScope? := some scope)
    runLogger (do service.downloadArtifacts (← map.collectOutputDescrs) cache scope)

/-- The usage of `cache lake`. -/
def usage : String :=
  "Usage: cache lake put <staging-dir> [--prefix=PREFIX] [--rev=REF]\n       \
    cache lake get [--prefix=PREFIX] [--rev=REF]\n\n\
    PREFIX defaults to `mathlib4`. REF is a git ref of the Mathlib checkout, `HEAD` by default."

/-- Runs `cache lake` with the arguments that follow `lake` on the command line. -/
def main (args : List String) : CacheM Unit := do
  let (opts, pos) := args.partition (·.startsWith "--")
  let opt? (name : String) : Option String :=
    (opts.reverse.find? (·.startsWith s!"--{name}=")).map (·.drop (name.length + 3) |>.copy)
  for o in opts do
    unless o.startsWith "--prefix=" || o.startsWith "--rev=" do
      IO.eprintln s!"Unknown option '{o}'\n{usage}"
      IO.Process.exit 1
  let target ← resolveTarget ((opt? "prefix").getD "mathlib4") (opt? "rev")
  match pos with
  | ["put", dir] => put dir target
  | ["get"] => get target
  | _ =>
    IO.eprintln usage
    IO.Process.exit 1

end Cache.LakeCache
