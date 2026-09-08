/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Upload.Curl
import Cache.Upload.Rclone

/-!
# Upload tool selection and dispatch

The transfer tools implement the same operation — a staged set of `.ltar`
files, then its per-SHA marker, to a resolved destination — one tool per
module (`Cache/Upload/Curl.lean`, `Cache/Upload/Rclone.lean`), signing each
request per the storage backend (`Cache/Upload/Azure.lean`,
`Cache/Upload/S3.lean`). This module resolves which tool a `put` uses
(`UploadTool`, `resolveUploadTool`) and dispatches to it (`putStaged`).
-/

namespace Cache.Requests

open System (FilePath)

/--
The transfer tool `put` uses, resolved together with the credentials it
signs with. The built-in curl tool works with every credential mechanism.
rclone signs only S3 requests, so its constructor carries the S3 credentials;
an rclone tool with a non-S3 credential is unrepresentable.
-/
inductive UploadTool where
  | curl
  | rclone (creds : S3Credentials)
  deriving DecidableEq, Repr, BEq

/--
The transfer tool for an S3 credential: a system rclone when one works on
PATH, curl otherwise. `forceCurl` (the `MATHLIB_CACHE_PUT_FORCE_CURL` flag)
selects curl whether rclone is available or not.

Pure so the policy is testable; `resolveUploadTool` wires the environment and
the availability probe in.
-/
def s3UploadToolFrom (creds : S3Credentials) (forceCurl rcloneAvailable : Bool) :
    UploadTool :=
  if !forceCurl && rcloneAvailable then .rclone creds else .curl

/--
Resolve the transfer tool from the credentials. An Azure credential always
takes curl: rclone signs only S3 requests. An S3 credential takes
`s3UploadToolFrom`; only this branch reads the `MATHLIB_CACHE_PUT_FORCE_CURL`
flag, and the availability probe runs only when the flag does not already
force curl.
-/
def resolveUploadTool (auth : UploadAuth) : IO UploadTool := do
  match auth with
  | .azureBearer _ => return .curl
  | .s3 creds =>
    let forceCurl ← getEnvFlag "MATHLIB_CACHE_PUT_FORCE_CURL" (ifUnset := false)
    let available ← if forceCurl then pure false else rcloneAvailable
    return s3UploadToolFrom creds forceCurl available

/--
Upload a staged set on the resolved `tool`: the `.ltar` files named by
`fileNames` under `srcDir`, then the per-SHA marker when `markerSha?` names
one, to `dest`. The curl tool validates the system curl before it transfers.
-/
def putStaged (dest : StagedUploadDest) (auth : UploadAuth) (tool : UploadTool)
    (srcDir : FilePath) (fileNames : Array String) (overwrite : Bool)
    (markerSha? : Option String) : IO Unit := do
  match tool with
  | .curl =>
    discard IO.validateCurl
    putStagedViaCurl dest srcDir fileNames overwrite auth markerSha?
  | .rclone creds =>
    putStagedViaRclone dest creds markerSha? srcDir fileNames overwrite

/--
The complete `put` operation, from the command inputs: resolve the
destination, credentials, and tool, then upload the `.ltar` files
`getFileNames` produces under `srcDir` (`putStaged`). The resolutions run
before `getFileNames`, so a misconfiguration fails before `put`'s expensive
packing pass. The per-SHA marker is written when the upload names a container
and a scope: it lets `cache query` discover cached commits with a cheap HEAD
probe.
-/
def runPut [Monad m] [MonadLiftT IO m] (container? : Option Container)
    (repo? : Option String) (backend : UploadBackend) (srcDir : FilePath)
    (getFileNames : m (Array String)) (overwrite : Bool) : m Unit := do
  let dest ← stagedUploadDest backend container? (repo?.getD MATHLIBREPO)
  let auth ← getUploadAuth backend
  let tool ← resolveUploadTool auth
  let markerSha? ← if container?.isSome then getRepoScope else pure (none : Option String)
  let fileNames ← getFileNames
  putStaged dest auth tool srcDir fileNames overwrite markerSha?

end Cache.Requests
