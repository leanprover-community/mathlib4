/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Upload.Defs

/-!
# The upload

An upload writes a staged set of `.ltar` files under a URL, in a layout
(`Layout`, `Cache/Infra.lean`), and `put` decides both before it transfers
anything (`Upload.decide`). The URL is `MATHLIB_CACHE_PUT_URL`. The layout is
flat, `{url}/f/{hash}.ltar`, unless `--namespaced` selects the repo-namespaced
layout, `{url}/f/{repo}/{hash}.ltar`, or, with a per-commit scope,
`{url}/f/{repo}/{sha}/{hash}.ltar` followed by the marker `{url}/m/{repo}/{sha}`
that `cache query` probes. The layout is the one the readers of the upload's
trust class probe: flat for `master`, namespaced for `forks` (with the scope),
`nightly-testing`, and `pr-toolchain-tests`.

`--container=NAME` names an Azure container instead: the URL is the
container's base on the storage account (`Container.azureURL`) and the layout
is the container's (`Container.layout`). `MATHLIB_CACHE_PUT_URL`, when set
with a container, overrides the URL and keeps the layout.

`uploadFiles` runs the transfer on the selected backend (`azurePutStaged` in
`Cache/Upload/Azure.lean`, `s3PutStaged` in `Cache/Upload/S3.lean`). A backend
sees the URL and the destination's prefixes (`StagedUploadDest`), never a
container.

The whole upload path is internal to mathlib CI: the commands, the backends,
and their credential and destination variables follow the CI storage layout.
An external cache should not build on it: its operator publishes a staged
artifact set (`stage`) with any storage client and serves readers through
`MATHLIB_CACHE_GET_URL`, one flat location.
-/

namespace Cache.Requests

open System (FilePath)

namespace Upload

/-- The inputs of a `put`'s decision: the flags and the environment. -/
structure Options where
  /-- `--namespaced`. -/
  namespaced : Bool := false
  /-- `--container=NAME`, an Azure container. -/
  container? : Option Container := none
  /-- `--repo=OWNER/REPO`, the repository of a namespaced upload. -/
  repo? : Option String := none
  /-- The per-commit scope, from `--scope` or `MATHLIB_CACHE_REPO_SCOPE`. -/
  scope? : Option String := none
  /-- `MATHLIB_CACHE_PUT_URL`. -/
  putURL? : Option String := none
  deriving Inhabited

/--
The decision of a `put`: the layout and the URL the files go under.

Without a container, the URL is `MATHLIB_CACHE_PUT_URL`, required, and
`--namespaced` selects the layout: namespaced for `repo?` (the canonical
repository by default: its own PR branches build with fork trust), in the
per-commit namespace when a scope is set; flat otherwise, ignoring `--repo`.
A scope on a flat upload is an error, because the layout has no namespace for
it.

With `--container`, the layout is the container's (`Container.layout`) and
the URL is the container's Azure base, or `MATHLIB_CACHE_PUT_URL` when set.
`--namespaced` with a container is an error, since the container decides the
layout, and so is a scope on a container without per-commit namespaces
(`Container.perCommit`). `legacy` is read-only.
-/
def decide (o : Options) : Except String (Layout × String) := do
  let repo := o.repo?.getD MATHLIBREPO
  match o.container? with
  | some .legacy => throw "the legacy container is read-only."
  | some c =>
    if o.namespaced then
      throw s!"--namespaced with --container={c.name}: the container decides the layout. Drop \
        the flag, or drop the container and set MATHLIB_CACHE_PUT_URL."
    if let some scope := o.scope? then
      unless c.perCommit do
        throw s!"scope {scope} set for an upload to {c.name}: the container has no per-commit \
          namespaces. Unset --scope and MATHLIB_CACHE_REPO_SCOPE."
    return (c.layout repo o.scope?, o.putURL?.getD c.azureURL)
  | none =>
    let some url := o.putURL?
      | throw "an upload needs MATHLIB_CACHE_PUT_URL, the URL the files go under \
          ({url}/f/{hash}.ltar flat, {url}/f/{repo}/[{sha}/]{hash}.ltar with --namespaced), \
          or --container=NAME, an Azure container."
    if o.namespaced then
      return (.namespaced repo o.scope?, url)
    if let some scope := o.scope? then
      throw s!"scope {scope} set for a flat upload: only a namespaced upload has per-commit \
        namespaces. Pass --namespaced, or unset --scope and MATHLIB_CACHE_REPO_SCOPE."
    return (.flat, url)

/-- The destination under `url`: the layout's file directory (`Layout.fileDir`)
and, for a namespaced layout, the repo's marker directory (`markerDirPath`). -/
def dest (layout : Layout) (url : String) : StagedUploadDest :=
  match layout with
  | .flat =>
    { base := url, label := "flat", filesPrefix := layout.fileDir, markerPrefix := "m" }
  | .namespaced repo scope? =>
    { base := url, label := s!"namespaced, {repo}" ++ (scope?.map (s!" at {·}")).getD "",
      filesPrefix := layout.fileDir, markerPrefix := markerDirPath repo }

end Upload

/--
The complete `put` operation: resolve the backend's credentials, then upload
the `.ltar` files `getFileNames` produces under `srcDir` to
`Upload.dest layout url` on the selected backend. The resolutions run before
`getFileNames`, so a misconfiguration fails before `put`'s expensive packing
pass. A scoped upload writes the per-SHA marker after the files: it lets
`cache query` discover cached commits with a cheap HEAD probe.
-/
def uploadFiles [Monad m] [MonadLiftT IO m] (layout : Layout) (url : String)
    (backend : UploadBackend) (srcDir : FilePath) (getFileNames : m (Array String))
    (overwrite : Bool) : m Unit := do
  let dest := Upload.dest layout url
  match backend with
  | .azure =>
    let token ← getAzureAuth
    let fileNames ← getFileNames
    azurePutStaged dest token srcDir fileNames overwrite layout.scope?
  | .s3 =>
    -- The URL must name the bucket by path; fail before packing.
    let _ ← (IO.ofExcept (s3EndpointSplit dest.base) : IO _)
    let creds ← getS3Auth
    let region ← getS3Region
    let fileNames ← getFileNames
    s3PutStaged dest creds region srcDir fileNames overwrite layout.scope?

end Cache.Requests
