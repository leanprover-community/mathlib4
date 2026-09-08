/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Upload.Dest
import Cache.Upload.Curl

/-!
# The Azure Blob Storage backend

The complete azure upload path: the destination resolution
(`azureUploadDestFrom`), the credential resolution (`azureAuthFrom`), the
request signing (`azureBearerCurlArgs`), and the transfer entry point
(`azurePutStaged`). rclone signs only S3 requests, so the backend always
transfers with the curl tool.

The storage account URL and the container model live in `Cache/Infra.lean`,
because the read side uses them too.
-/

namespace Cache.Requests

open System (FilePath)

/--
The upload destination for the azure backend: the chosen `--container` on the
`lakecache` Azure storage account. A missing container errors: an upload
targets exactly one container. The account is fixed:
`MATHLIB_CACHE_PUT_BASE_URL` (`putBase?`) configures the s3 backend's
endpoint, so a set value here is a misconfiguration and errors.
-/
def azureUploadDestFrom (putBase? : Option String) (container? : Option Container)
    (repo : String) (scope? : Option String) : Except String StagedUploadDest :=
  if putBase?.isSome then
    .error "MATHLIB_CACHE_PUT_BASE_URL is set, which names the s3 backend's bucket \
      endpoint; the azure backend writes to the Azure storage account. Pass \
      --backend=s3, or unset the variable."
  else match container? with
    | some c => .ok (containerUploadDest azureAccountURL c repo scope?)
    | none => .error
        s!"an upload targets one container: pass --container=NAME (known: \
        {", ".intercalate (Container.all.map Container.name)}), or set \
        MATHLIB_CACHE_PUT_URL for a flat upload"

/-- The api-version header that every bearer-authenticated Azure request
sends. Bearer authentication requires an api-version that supports OAuth. -/
def azureBearerApiVersionHeader : String := "x-ms-version: 2026-02-06"

/-- The `x-ms-date` header that every bearer-authenticated Azure request
sends: the current time, in the RFC 1123 format Azure requires. -/
def getAzureDateHeader : IO String := do
  let out ← IO.Process.output
    { cmd := "date", args := #["-u", "+%a, %d %b %Y %H:%M:%S GMT"] }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"failed to produce x-ms-date header (exit code {out.exitCode})"
  return s!"x-ms-date: {out.stdout.trimAscii.copy}"

/--
The curl arguments for an upload authenticated with an Azure OAuth bearer
token: the `x-ms-blob-type` header a blob PUT requires, the api-version and
date headers, and the token itself. The argument list carries the token, so
callers print curl failures without the argument list.
-/
def azureBearerCurlArgs (token : String) : IO (Array String) := do
  return #["-H", "x-ms-blob-type: BlockBlob",
    "-H", azureBearerApiVersionHeader, "-H", ← getAzureDateHeader,
    "--oauth2-bearer", token]

/--
The azure upload credential, from the raw environment value: the OAuth
bearer token `MATHLIB_CACHE_AZURE_BEARER_TOKEN` (`bearer?`).

Pure so the policy is testable; `getAzureAuth` wires the environment in.
-/
def azureAuthFrom (bearer? : Option String) : Except String String :=
  match bearer? with
  | some token => .ok token
  | none => .error
      "the azure backend (the default) uploads with an Azure OIDC bearer token: \
      set MATHLIB_CACHE_AZURE_BEARER_TOKEN, or pass --backend=s3 to upload \
      with the S3 credential pair"

/-- Retrieves the azure upload credential from the environment via
`azureAuthFrom`. -/
def getAzureAuth : IO String := do
  IO.ofExcept <| azureAuthFrom (← getEnvNonEmpty "MATHLIB_CACHE_AZURE_BEARER_TOKEN")

/--
The staged put on the azure backend: the curl tool against `dest`, each
request signed with the bearer token (`azureBearerCurlArgs`).
-/
def azurePutStaged (dest : StagedUploadDest) (token : String) (srcDir : FilePath)
    (fileNames : Array String) (overwrite : Bool) (markerSha? : Option String) :
    IO Unit :=
  putStagedViaCurl dest (azureBearerCurlArgs token) srcDir fileNames overwrite markerSha?

end Cache.Requests
