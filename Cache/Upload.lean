/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Cache.Upload.Defs
public import Cache.Scope

/-!
# The upload operation

`Upload.decide` and `uploadFiles` implement the complete `put` from the command
inputs. `Upload.decide` resolves the location (`uploadLocationFrom`), and the
selected backend resolves its credentials and transfer tool and runs the
transfer (`azurePutStaged` in `Cache/Upload/Azure.lean`, `s3PutStaged` in
`Cache/Upload/S3.lean`).

The whole upload path is internal to mathlib CI: the commands, the backends,
and their credential and location variables follow the CI storage layout.
An external cache should not build on it: its operator publishes a staged
artifact set (`stage`) with any storage client and serves readers through
`MATHLIB_CACHE_GET_URL`, one flat location.
-/

public section

namespace Cache.Requests

open System (FilePath)

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
  backend : UploadBackend := .s3
  deriving Inhabited

/-- The location of a `put` (`uploadLocationFrom`). The repository defaults
to the canonical one, whose own PR branches build with fork trust. The
location derives the marker that follows the files when the upload has a
scope. -/
def decide (o : Options) : Except String Location :=
  uploadLocationFrom o.backend o.putURL? o.container? (o.repo?.getD MATHLIBREPO)
    (o.scope?.map (·.sha))

end Upload

/--
The complete `put` operation, for the decided location `dest`: resolve the
backend's credentials, then upload the `.ltar` files `getFileNames` produces
under `srcDir` on the selected backend. The resolutions run before
`getFileNames`, so a misconfiguration fails before `put`'s expensive packing
pass. The upload writes the marker derived by `Location.marker?`, if present.
The marker lets `cache query` discover cached commits with a cheap HEAD probe.
-/
def uploadFiles [Monad m] [MonadLiftT IO m] (dest : Location) (backend : UploadBackend)
    (srcDir : FilePath) (getFileNames : m (Array String)) (overwrite : Bool) : m Unit := do
  match backend with
  | .azure =>
    let token ← getAzureAuth
    let fileNames ← getFileNames
    azurePutStaged dest token srcDir fileNames overwrite
  | .s3 =>
    let creds ← getS3Auth
    let region ← getS3Region
    let fileNames ← getFileNames
    s3PutStaged dest creds region srcDir fileNames overwrite

end Cache.Requests
