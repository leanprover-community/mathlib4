/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Upload.Dest

/-!
# The Azure Blob Storage backend

The Azure-specific upload logic: the destination resolution
(`azureUploadDestFrom`), and the headers a blob PUT requires with the
bearer-token authentication, rendered as curl arguments
(`azureBearerCurlArgs`). rclone signs only S3 requests, so Azure uploads use
the curl tool alone and this backend renders curl arguments alone.

The storage account URL and the container model live in `Cache/Infra.lean`,
because the read side uses them too.
-/

namespace Cache.Requests

/--
The upload destination for the azure backend: the chosen container on the
`lakecache` Azure storage account, or the `legacy` container when no
container is chosen (the IO wrapper warns). The account is fixed:
`MATHLIB_CACHE_PUT_BASE_URL` (`putBase?`) configures the s3 backend's
endpoint, so a set value here is a misconfiguration and errors.
-/
def azureUploadDestFrom (putBase? : Option String) (container? : Option Container)
    (repo : String) (scope? : Option String) : Except String StagedUploadDest :=
  if putBase?.isSome then
    .error "MATHLIB_CACHE_PUT_BASE_URL is set, which names the s3 backend's bucket \
      endpoint; the azure backend writes to the Azure storage account. Pass \
      --backend=s3, or unset the variable."
  else
    .ok (containerUploadDest azureAccountURL (container?.getD .legacy) repo scope?)

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

end Cache.Requests
