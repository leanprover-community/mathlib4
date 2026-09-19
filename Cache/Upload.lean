/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Upload.Defs
import Cache.Scope

/-!
# The upload

An upload writes a staged set of `.ltar` files under a URL, in one of two
forms (`Upload`), and `put` decides both before it transfers anything, as
`get` decides its workflow. The URL is `MATHLIB_CACHE_PUT_URL`. The form is
flat, `{url}/f/{hash}.ltar`, the layout of the public cache's `master`
container, unless `--dev-cache` selects the developer-cache upload: the
repo-namespaced layout of the developer cache's containers,
`{url}/f/{repo}/{hash}.ltar`, and, with a per-commit scope, the fork's
namespace `{url}/f/{repo}/{sha}/{hash}.ltar` followed by the marker
`{url}/m/{repo}/{sha}` that `cache query` probes. A well-known container
stands for both at once (`Config`, `--container=NAME`): its base on the Azure
storage account, and the developer-cache form for `forks`, `nightly-testing`,
and `pr-toolchain-tests`, the flat form for `master`. `uploadFiles` runs the
transfer on the selected backend (`azurePutStaged` in
`Cache/Upload/Azure.lean`, `s3PutStaged` in `Cache/Upload/S3.lean`). The
layout under the URL is the one the readers probe (`fileDirPath`,
`markerDirPath`).

The whole upload path is internal to mathlib CI: the commands, the backends,
and their credential and destination variables follow the CI storage layout.
An external cache should not build on it: its operator publishes a staged
artifact set (`stage`) with any storage client and serves readers through
`MATHLIB_CACHE_GET_URL`, one flat location.
-/

namespace Cache.Requests

open System (FilePath)

/-- The two uploads; see the module docstring. -/
inductive Upload where
  /-- `f/{hash}.ltar` under the URL: the public cache's `master` container. -/
  | flat
  /-- The developer cache: `f/{repo}/{hash}.ltar` under the URL, or with a
  per-commit scope `f/{repo}/{sha}/{hash}.ltar` and then the marker
  `m/{repo}/{sha}`. -/
  | devCache (repo : String) (sha? : Option String)
  deriving Repr, BEq, Inhabited

namespace Upload

/-- The upload's name in messages. -/
def name : Upload → String
  | .flat => "flat"
  | .devCache .. => "developer cache"

/-- `--dev-cache`: the developer-cache upload. -/
def devCacheFlag : Cli.Flag := .paramless
  (longName := "dev-cache")
  (description := "Upload to the developer cache: the repo-namespaced layout f/REPO/ under the \
    URL, and with --scope (or MATHLIB_CACHE_REPO_SCOPE) the per-commit namespace f/REPO/SHA/ \
    followed by the marker cache query probes. Takes --repo. Without it the upload is flat: f/ \
    under the URL. --container=forks, nightly-testing and pr-toolchain-tests imply it.")

/-- What a well-known container stands for on the write side: the URL its
uploads go under and whether they are developer-cache uploads. -/
structure Config where
  /-- The container's base on the Azure storage account. -/
  url : String
  /-- The developer-cache form: the container's layout is repo-namespaced. -/
  devCache : Bool
  deriving Repr, BEq, Inhabited

/-- The configuration `--container=NAME` stands for: the container's Azure base
(`Container.azureURL`), and the developer-cache form for every container but
`master` (`Container.flatPath`). `legacy` is read-only. -/
def configOf : Container → Except String Config
  | .legacy => .error "the legacy container is read-only."
  | .master => .ok { url := Container.master.azureURL, devCache := false }
  | c => .ok { url := c.azureURL, devCache := true }

/-- `--container=NAME`: a well-known configuration, the URL and the form at
once (`configOf`). -/
def containerFlag : Cli.Flag := {
  longName := "container"
  description := s!"A well-known configuration: the container's base on the Azure storage \
    account as the URL, and the form, developer-cache for forks, nightly-testing and \
    pr-toolchain-tests, flat for master. One of \
    {", ".intercalate ((Container.all.filter (· != .legacy)).map Container.name)}. \
    MATHLIB_CACHE_PUT_URL overrides the URL and keeps the form."
  type := Container }

/-- The inputs of a `put`'s decision: the flags and the environment. -/
structure Options where
  /-- `--dev-cache`. -/
  devCache : Bool := false
  /-- `--container=NAME`, the well-known configuration. -/
  container? : Option Container := none
  /-- `--repo=OWNER/REPO`, the repository of a developer-cache upload. -/
  repo? : Option String := none
  /-- `--scope` or `MATHLIB_CACHE_REPO_SCOPE`. -/
  scope? : Option Scope := none
  /-- `MATHLIB_CACHE_PUT_URL`. -/
  putURL? : Option String := none
  deriving Inhabited

/--
The configuration of a `put`: the URL and the form. With `--container`, both
come from the container (`configOf`); `MATHLIB_CACHE_PUT_URL`, when set,
overrides the URL and keeps the form, which is how a container's uploads move
to another store; `--dev-cache` on a container whose uploads are flat is an
error. Without a container, the URL is `MATHLIB_CACHE_PUT_URL`, required, and
`--dev-cache` selects the form.
-/
def config (o : Options) : Except String Config := do
  match o.container? with
  | some c =>
    let cfg ← configOf c
    if o.devCache && !cfg.devCache then
      throw s!"--dev-cache with --container={c.name}: the container's uploads are flat; the \
        developer-cache form is for forks, nightly-testing, and pr-toolchain-tests."
    return { cfg with url := o.putURL?.getD cfg.url }
  | none =>
    match o.putURL? with
    | some url => return { url, devCache := o.devCache }
    | none => throw "an upload needs MATHLIB_CACHE_PUT_URL, the URL the files go under \
        ({url}/f/{hash}.ltar flat, {url}/f/{repo}/[{sha}/]{hash}.ltar with --dev-cache), or \
        --container=NAME, a well-known configuration."

/--
The form of an upload from its configuration and options. The developer-cache
upload is for `repo?` (the canonical repository by default: its own PR
branches build with fork trust), in the per-commit namespace when a scope is
set; a container without per-commit namespaces (`Container.perCommit`)
rejects a scope. The flat upload takes no scope, because it has no namespace
for one to address, and it ignores `--repo`.
-/
def form (cfg : Config) (o : Options) : Except String Upload := do
  if cfg.devCache then
    if let some c := o.container? then
      if let some scope := o.scope? then
        unless c.perCommit do
          throw s!"scope {scope.sha} set for an upload to {c.name}: the container has no \
            per-commit namespaces. Unset --scope and MATHLIB_CACHE_REPO_SCOPE."
    return .devCache (o.repo?.getD MATHLIBREPO) (o.scope?.map (·.sha))
  else
    if let some scope := o.scope? then
      throw s!"scope {scope.sha} set for a flat upload: only a developer-cache upload has \
        per-commit namespaces. Unset --scope and MATHLIB_CACHE_REPO_SCOPE."
    return .flat

/-- The decision of a `put`: the upload and the URL it goes under. -/
def decide (o : Options) : Except String (Upload × String) := do
  let cfg ← config o
  return (← form cfg o, cfg.url)

/-- The per-commit scope of the upload; the marker is written iff it is set. -/
def scope? : Upload → Option String
  | .flat => none
  | .devCache _ sha? => sha?

/-- The destination under `url`: the layout the readers probe, flat
(`fileDirPath` of `master`) or repo-namespaced with the optional scope
(`fileDirPath` of the developer cache's containers, `markerDirPath`). -/
def dest (u : Upload) (url : String) : StagedUploadDest :=
  match u with
  | .flat =>
    { base := url, label := "flat", filesPrefix := "f", markerPrefix := "m" }
  | .devCache repo sha? =>
    { base := url, label := s!"developer cache, {repo}" ++ (sha?.map (s!" at {·}")).getD "",
      filesPrefix := fileDirPath (some .forks) repo sha?, markerPrefix := markerDirPath repo }

end Upload

/--
The complete `put` operation: resolve the backend's credentials, then upload
the `.ltar` files `getFileNames` produces under `srcDir` to `u.dest url` on
the selected backend. The resolutions run before `getFileNames`, so a
misconfiguration fails before `put`'s expensive packing pass. A scoped
developer-cache upload writes the per-SHA marker after the files: it lets
`cache query` discover cached commits with a cheap HEAD probe.
-/
def uploadFiles [Monad m] [MonadLiftT IO m] (u : Upload) (url : String) (backend : UploadBackend)
    (srcDir : FilePath) (getFileNames : m (Array String)) (overwrite : Bool) : m Unit := do
  let dest := u.dest url
  match backend with
  | .azure =>
    let token ← getAzureAuth
    let fileNames ← getFileNames
    azurePutStaged dest token srcDir fileNames overwrite u.scope?
  | .s3 =>
    -- The URL must name the bucket by path; fail before packing.
    let _ ← (IO.ofExcept (s3EndpointSplit dest.base) : IO _)
    let creds ← getS3Auth
    let region ← getS3Region
    let fileNames ← getFileNames
    s3PutStaged dest creds region srcDir fileNames overwrite u.scope?

end Cache.Requests
