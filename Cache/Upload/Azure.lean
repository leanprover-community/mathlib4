/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

/-!
# The Azure Blob Storage backend

The Azure-specific upload logic: the headers a blob PUT requires and the
bearer-token authentication, rendered as curl arguments
(`azureBearerCurlArgs`). rclone signs only S3 requests, so Azure uploads use
the curl engine alone and this backend renders curl arguments alone.

The storage account URL and the container model live in `Cache/Infra.lean`,
because the read side uses them too.
-/

namespace Cache.Requests

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
