/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Upload.Defs
import Cache.Scope

/-!
# The upload operation

`Upload.decide` and `uploadFiles` implement the complete `put` from the command
inputs. The routing is the backend: the shared arbitration resolves the
destination (`stagedUploadDestFrom`, through `Upload.decide`), and the selected
backend resolves its credentials and transfer tool and runs the transfer
(`azurePutStaged` in `Cache/Upload/Azure.lean`, `s3PutStaged` in
`Cache/Upload/S3.lean`).

The whole upload path is internal to mathlib CI: the commands, the backends,
and their credential and destination variables follow the CI storage layout.
An external cache should not build on it: its operator publishes a staged
artifact set (`stage`) with any storage client and serves readers through
`MATHLIB_CACHE_GET_URL`, one flat location.
-/

namespace Cache.Requests

open System (FilePath)

/-- A decided upload: where the files go, and the per-commit scope whose
marker follows them. -/
structure Upload where
  /-- The destination: the container's layout under its root. -/
  dest : StagedUploadDest
  /-- The per-commit scope; the marker is written iff it is set. -/
  scope? : Option String
  deriving Repr, BEq

namespace Upload

/-- The inputs of a `put`'s decision: the flags and the environment. -/
structure Options where
  /-- `--container=NAME`. -/
  container? : Option Container := none
  /-- `--repo=OWNER/REPO`, the repository of a repo-namespaced upload. -/
  repo? : Option String := none
  /-- `--scope` or `MATHLIB_CACHE_REPO_SCOPE`. -/
  scope? : Option Scope := none
  /-- `MATHLIB_CACHE_PUT_URL`. -/
  putURL? : Option String := none
  /-- `--backend`. -/
  backend : UploadBackend := .azure
  deriving Inhabited

/-- The decision of a `put` (`stagedUploadDestFrom`). The repository defaults
to the canonical one, whose own PR branches build with fork trust. -/
def decide (o : Options) : Except String Upload := do
  let scope? := o.scope?.map (·.sha)
  let dest ← stagedUploadDestFrom o.backend o.putURL? o.container? (o.repo?.getD MATHLIBREPO)
    scope?
  return { dest, scope? }

end Upload

/--
The complete `put` operation, for the decided upload `u`: resolve the
backend's credentials, then upload the `.ltar` files `getFileNames` produces
under `srcDir` to `u.dest` on the selected backend. The resolutions run before
`getFileNames`, so a misconfiguration fails before `put`'s expensive packing
pass. The per-SHA marker is written when the upload has a scope, from
`--scope` or `MATHLIB_CACHE_REPO_SCOPE`: it lets `cache query` discover cached
commits with a cheap HEAD probe.
-/
def uploadFiles [Monad m] [MonadLiftT IO m] (u : Upload) (backend : UploadBackend)
    (srcDir : FilePath) (getFileNames : m (Array String)) (overwrite : Bool) : m Unit := do
  match backend with
  | .azure =>
    let token ← getAzureAuth
    let fileNames ← getFileNames
    azurePutStaged u.dest token srcDir fileNames overwrite u.scope?
  | .s3 =>
    let creds ← getS3Auth
    let region ← getS3Region
    let fileNames ← getFileNames
    s3PutStaged u.dest creds region srcDir fileNames overwrite u.scope?

end Cache.Requests
