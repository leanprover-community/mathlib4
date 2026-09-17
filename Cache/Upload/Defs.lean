/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Marker
import Cache.Upload.Azure
import Cache.Upload.S3

/-!
# The upload contract

The backend-neutral layer over the backend modules:

the backend selection (`UploadBackend`). The backends implement the upload in
`Cache/Upload/Azure.lean` and `Cache/Upload/S3.lean`: credentials, transfer
tool, and the transfer, against the destination contract of
`Cache/Upload/Dest.lean` (`StagedUploadDest`).

`Cache/Upload.lean` decides the upload's layout and URL and runs the complete
`put`, dispatching to the selected backend. The marker path contract and write
mechanics live in `Cache/Marker.lean`. The read side (`Cache/Requests.lean`)
shares the layout (`Layout`, `Cache/Infra.lean`) and the marker path
(`markerDirPath`), so every upload addresses the URLs the readers probe.
-/

namespace Cache.Requests

open System (FilePath)

/-- The storage backend an upload targets, selected with `--backend=NAME`.
Each backend implements the complete upload in its own module: credential
resolution, transfer tool, and the transfer. `uploadFiles` dispatches on this
type. -/
inductive UploadBackend where
  /-- Azure Blob Storage (`Cache/Upload/Azure.lean`); the default. -/
  | azure
  /-- An S3-compatible bucket (`Cache/Upload/S3.lean`). -/
  | s3
  deriving DecidableEq, Repr, BEq, Inhabited

namespace UploadBackend

/-- Canonical short name for a backend, used in the `--backend` flag. -/
def name : UploadBackend → String
  | .azure => "azure"
  | .s3    => "s3"

/-- All known backends, listed in their canonical declaration order. -/
def all : List UploadBackend := [.azure, .s3]

/-- Parse a short name back into an `UploadBackend`. Matching is
case-insensitive. -/
def parse? (s : String) : Option UploadBackend :=
  match s.toLower with
  | "azure" => some .azure
  | "s3"    => some .s3
  | _       => none

end UploadBackend

end Cache.Requests
