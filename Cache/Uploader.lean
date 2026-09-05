/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.UploadCurl
import Cache.UploadRclone

/-!
# Upload engine selection and dispatch

The transfer engines implement the same operation — a staged set of `.ltar`
files, then its per-SHA marker, to a resolved destination — one engine per
module (`Cache/UploadCurl.lean`, `Cache/UploadRclone.lean`). This module
resolves which engine a `put` uses (`UploadEngine`, `resolveUploadEngine`)
and dispatches to it (`putStaged`).
-/

namespace Cache.Requests

open System (FilePath)

/--
The transfer engine `put` uses, resolved together with the credentials it
signs with: the built-in curl engine works with every credential mechanism,
while rclone signs S3 requests only, so its constructor carries the S3
credentials — an rclone engine holding a non-S3 credential is unrepresentable.
-/
inductive UploadEngine where
  | curl
  | rclone (keyId secret : String) (sessionToken? : Option String)
  deriving DecidableEq, Repr, BEq

/--
Resolve the transfer engine from the `--uploader=` option (`uploader?`):

* unset or `curl`: the built-in curl engine.
* `rclone`: a system rclone, required — a missing binary or non-S3
  credentials error rather than silently changing engines. rclone signs S3
  requests only, so the Azure mechanisms always take the curl engine.

Pure so the policy is testable; `resolveUploadEngine` wires the availability
probe in.
-/
def uploadEngineFrom (uploader? : Option String) (auth : UploadAuth)
    (rcloneAvailable : Bool) : Except String UploadEngine :=
  let rclone? : Option UploadEngine := match auth with
    | .s3 keyId secret sessionToken? => some (.rclone keyId secret sessionToken?)
    | .azureBearer _ => none
  match uploader? with
  | none | some "curl" => .ok .curl
  | some "rclone" =>
    match rclone? with
    | none => .error "--uploader=rclone signs uploads with the S3 credential pair, \
        and the environment provides a different upload mechanism"
    | some engine =>
      if rcloneAvailable then .ok engine
      else .error "--uploader=rclone, but no working rclone was found on PATH"
  | some other =>
    .error s!"unknown --uploader value '{other}' (known: curl, rclone)"

/--
`uploadEngineFrom` with the availability probe wired in. The probe runs only
when `--uploader=rclone` asks for the binary.
-/
def resolveUploadEngine (uploader? : Option String) (auth : UploadAuth) :
    IO UploadEngine := do
  let available ← if uploader? == some "rclone" then rcloneAvailable else pure false
  IO.ofExcept <| uploadEngineFrom uploader? auth available

/--
Upload a staged set on the resolved `engine`: the `.ltar` files named by
`fileNames` under `srcDir`, then the per-SHA marker when `markerSha?` names
one, to `dest`. The curl engine validates the system curl before it transfers.
-/
def putStaged (dest : StagedUploadDest) (auth : UploadAuth) (engine : UploadEngine)
    (srcDir : FilePath) (fileNames : Array String) (overwrite : Bool)
    (markerSha? : Option String) : IO Unit := do
  match engine with
  | .curl =>
    discard IO.validateCurl
    putStagedViaCurl dest srcDir fileNames overwrite auth markerSha?
  | .rclone keyId secret sessionToken? =>
    putStagedViaRclone dest keyId secret sessionToken? markerSha? srcDir fileNames overwrite

end Cache.Requests
