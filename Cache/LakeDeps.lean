/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Lake.Config.Cache
public import Lake.Util.Log

/-!
# Dependency mappings under a separate revision scope

`lake cache put-staged` and `lake cache get` use one scope for a package's revision file and for
its artifacts. This module calls the same Lake functions with two scopes:

* the artifact scope holds the artifacts, which are content addressed and shared by every
  revision of the package;
* the revision scope holds the revision file, the input-to-output mappings of one build.

A revision file that the revision scope qualifies, for example by the mathlib commit, then does not
duplicate the artifacts.

`lake exe cache lake-dep put <staging-dir> OPTIONS` uploads a directory that `lake cache stage`
wrote. `lake exe cache lake-dep get OPTIONS` downloads the revision file, records its mappings for
the package in the local Lake cache, and downloads the artifacts.

Options, all required except where stated:

* `--artifact-endpoint=URL` and `--revision-endpoint=URL`: the endpoints of the cache service;
* `--scope=SCOPE`: the artifact scope;
* `--rev-scope=SCOPE`: the revision scope;
* `--rev=REV`: the revision that names the revision file;
* `--package=NAME` (`get` only): the package whose mappings `get` records;
* `--service=NAME` (`get` only, optional): the service name that the local cache records, so that
  Lake can download a missing artifact later. It must name a service in Lake's system
  configuration.

`put` signs its uploads with `LAKE_CACHE_KEY`. `get` writes to the Lake cache directory in
`LAKE_CACHE_DIR`.
-/

public section

namespace Cache.LakeDeps

open Lake System

/-- The arguments of `lake-dep`, parsed from `--name=value` options. -/
structure Args where
  artifactEndpoint : String
  revisionEndpoint : String
  scope : CacheServiceScope
  revScope : CacheServiceScope
  rev : String
  package? : Option String := none
  service? : Option String := none

/-- Returns the value of the last `--name=value` option, if any. -/
def namedOpt? (name : String) (opts : List String) : Option String :=
  let pref := s!"--{name}="
  (opts.reverse.find? (·.startsWith pref)).map (·.drop pref.length |>.toString)

/-- Parses the options of `lake-dep`. Returns an error message for a missing option. -/
def parseArgs (opts : List String) : Except String Args := do
  let req (name : String) : Except String String :=
    match namedOpt? name opts with
    | some v => if v.isEmpty then .error s!"--{name} is empty" else .ok v
    | none => .error s!"--{name}= is required"
  return {
    artifactEndpoint := ← req "artifact-endpoint"
    revisionEndpoint := ← req "revision-endpoint"
    scope := .ofString (← req "scope")
    revScope := .ofString (← req "rev-scope")
    rev := ← req "rev"
    package? := namedOpt? "package" opts
    service? := namedOpt? "service" opts
  }

/-- Uploads the staged mappings and artifacts of one package. -/
def put (stagingDir : FilePath) (args : Args) : LoggerIO Unit := do
  let some key := (← IO.getEnv "LAKE_CACHE_KEY").map (·.trimAscii.toString)
    | error "uploads require an authentication key configured through `LAKE_CACHE_KEY`"
  let service := CacheService.uploadService key args.artifactEndpoint args.revisionEndpoint
  let outputs := stagingDir / "outputs.jsonl"
  let map ← CacheMap.load outputs
  let descrs ← map.collectOutputDescrs
  let paths ← (Vector.mk descrs rfl).mapM fun descr => do
    let path := stagingDir / descr.relPath
    unless (← path.pathExists) do
      error s!"artifact not found in staging directory: {path}"
    return path
  service.uploadArtifacts ⟨descrs, rfl⟩ paths args.scope
  -- The revision file follows its artifacts, so a reader that finds the file finds them too.
  service.uploadRevisionOutputs args.rev outputs args.revScope

/-- Downloads one package's mappings and artifacts into the local Lake cache. -/
def get (args : Args) : LoggerIO Unit := do
  let some pkg := args.package?
    | error "--package= is required"
  let some dir ← IO.getEnv "LAKE_CACHE_DIR"
    | error "`LAKE_CACHE_DIR` must name the Lake cache directory"
  let cache : Lake.Cache := ⟨dir⟩
  let service := CacheService.downloadService args.artifactEndpoint args.revisionEndpoint
    (args.service?.map .ofString)
  -- The local copy is `revisions/<pkg>/<rev>.jsonl`, so `--rev` must distinguish two revision
  -- files of one package.
  let some map ← service.downloadRevisionOutputs? args.rev cache pkg args.revScope
    | error s!"{args.revScope}: outputs not found for revision {args.rev}"
  cache.writeMap pkg map service.name? (some args.scope)
  service.downloadArtifacts (← map.collectOutputDescrs) cache args.scope

/-- The usage line of `lake-dep`. -/
def usage : String :=
  "Usage: cache lake-dep put <staging-dir> --artifact-endpoint=URL --revision-endpoint=URL \
    --scope=SCOPE --rev-scope=SCOPE --rev=REV\n       \
    cache lake-dep get --package=NAME --artifact-endpoint=URL --revision-endpoint=URL \
    --scope=SCOPE --rev-scope=SCOPE --rev=REV [--service=NAME]"

/-- Runs `lake-dep` with the arguments that follow it on the command line. -/
def main (args : List String) : IO UInt32 := do
  let (opts, pos) := args.partition (·.startsWith "--")
  let parsed ← match parseArgs opts with
    | .ok a => pure a
    | .error e =>
      IO.eprintln s!"{e}\n{usage}"
      return 1
  let act : LoggerIO Unit ← match pos with
    | ["put", dir] => pure (put dir parsed)
    | ["get"] => pure (get parsed)
    | _ =>
      IO.eprintln usage
      return 1
  match ← act.toBaseIO with
  | some () => return 0
  | none => return 1

end Cache.LakeDeps
