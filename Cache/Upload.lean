/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Upload.Defs

/-!
# The upload operation

`runPut` implements the complete `put` from the command inputs. The routing
is the backend: the shared arbitration resolves the destination
(`stagedUploadDest`), and the selected backend resolves its credentials and
transfer tool and runs the transfer (`azurePutStaged` in
`Cache/Upload/Azure.lean`, `s3PutStaged` in `Cache/Upload/S3.lean`).

The whole upload path is internal to mathlib CI: the commands, the backends,
and their credential and destination variables follow the CI storage layout.
An external cache should not build on it: its operator publishes a staged
artifact set (`stage`) with any storage client and serves readers through
`MATHLIB_CACHE_GET_URL`, one flat location.
-/

namespace Cache.Requests

open System (FilePath)

/--
The complete `put` operation, from the command inputs: resolve the
destination and the backend's credentials, then upload the `.ltar` files
`getFileNames` produces under `srcDir` on the selected backend. The
resolutions run before `getFileNames`, so a misconfiguration fails before
`put`'s expensive packing pass. The per-SHA marker is written when the
upload names a container and a scope: it lets `cache query` discover cached
commits with a cheap HEAD probe.
-/
def runPut [Monad m] [MonadLiftT IO m] (container? : Option Container)
    (repo? : Option String) (backend : UploadBackend) (srcDir : FilePath)
    (getFileNames : m (Array String)) (overwrite : Bool) : m Unit := do
  let scope? ← getRepoScope
  let dest ← stagedUploadDest backend container? (repo?.getD MATHLIBREPO) scope?
  let markerSha? := if container?.isSome then scope? else none
  match backend with
  | .azure =>
    let token ← getAzureAuth
    let fileNames ← getFileNames
    azurePutStaged dest token srcDir fileNames overwrite markerSha?
  | .s3 =>
    let creds ← getS3Auth
    let region ← getS3Region
    let fileNames ← getFileNames
    s3PutStaged dest creds region srcDir fileNames overwrite markerSha?

end Cache.Requests
