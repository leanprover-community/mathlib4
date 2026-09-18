/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Marker

/-!
# The upload destination contract

The destination every upload consumes (`StagedUploadDest`): the URL the
files go under and the prefixes of the files and the marker beneath it.
`Upload.dest` (`Cache/Upload.lean`) builds it from the upload's layout and
URL; the backends transfer to it. The prefixes build on `Layout.fileDir` and
`markerDirPath` (`Cache/Infra.lean`, `Cache/Marker.lean`), the same policies
the reads use, so every upload path follows the read-side path contract.
-/

namespace Cache.Requests

/--
The resolved destination of a staged (`put`) upload. `base` is the upload
base; the prefixes are relative to it and carry no trailing slash.
Every staged file goes under `filesPrefix` and keeps its base name; the
per-SHA marker goes under `markerPrefix` with the SHA as its name (`fileURL`,
`markerURL`). `label` names the destination in progress and warning messages.
-/
structure StagedUploadDest where
  base : String
  label : String
  filesPrefix : String
  markerPrefix : String
  deriving Repr, BEq

/-- Upload URL of a staged file: `{base}/{filesPrefix}/{fileName}`. Every
tool addresses this URL (rclone through its `:s3:` remote syntax). -/
def StagedUploadDest.fileURL (dest : StagedUploadDest) (fileName : String) : String :=
  s!"{dest.base}/{dest.filesPrefix}/{fileName}"

/-- Upload URL of the per-SHA marker: `{base}/{markerPrefix}/{sha}`. Every
tool addresses this URL (rclone through its `:s3:` remote syntax). -/
def StagedUploadDest.markerURL (dest : StagedUploadDest) (sha : String) : String :=
  s!"{dest.base}/{dest.markerPrefix}/{sha}"

end Cache.Requests
