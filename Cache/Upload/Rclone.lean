/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Upload.Dest

/-!
# The rclone upload tool

An opt-in transfer tool: a system [rclone](https://rclone.org) against the
resolved destination (`StagedUploadDest`). The tool holds only transfer
mechanics and addresses the destination through rclone's `:s3:` remote
syntax, so only the s3 backend calls it. `Cache/Upload/S3.lean` assembles
the child environment that carries the credentials and endpoint, splits the
bucket path out of the destination base, and calls the tool's entry point,
`putStagedViaRclone`.
-/

namespace Cache.Requests

open System (FilePath)

/-- Whether a working rclone is available on PATH. -/
def rcloneAvailable : IO Bool := do
  try
    let out ← IO.Process.output { cmd := "rclone", args := #["version"] }
    return out.exitCode == 0
  catch _ =>
    return false

/-- The rclone flags every `put` transfer carries. `--s3-no-check-bucket`
skips the bucket-creation probe a scoped credential cannot pass. -/
def rcloneCommonFlags : Array String := #["--s3-no-check-bucket", "--retries", "5"]

/--
The rclone invocation for the `.ltar` files: a copy from `srcDir` into the
files prefix, restricted to the `--files-from` list, so only the files the
caller names leave the machine. A non-overwrite put passes
`--ignore-existing`, which skips objects the destination already holds; this
matches the curl tool's `If-None-Match: *`. Artifact names are content
hashes, so a skipped re-put loses nothing.
-/
def rcloneFilesArgs (bucketPath : String) (dest : StagedUploadDest)
    (srcDir filesFrom : FilePath) (overwrite : Bool) : Array String :=
  #["copy", srcDir.toString, s!":s3:{bucketPath}/{dest.filesPrefix}",
    "--files-from", filesFrom.toString, "--transfers", "16"] ++
    (if overwrite then #[] else #["--ignore-existing"]) ++ rcloneCommonFlags

/--
The rclone invocation for the per-SHA marker: a single-file copy to the
marker path. A marker's content is the SHA that names it, so an overwrite is
safe and the copy omits `--ignore-existing`, like the curl tool's marker
put.
-/
def rcloneMarkerArgs (bucketPath : String) (dest : StagedUploadDest)
    (markerFile : FilePath) (sha : String) : Array String :=
  #["copyto", markerFile.toString, s!":s3:{bucketPath}/{dest.markerPrefix}/{sha}"] ++
    rcloneCommonFlags

/--
The staged put on a system rclone. `env` is the child environment the caller
assembled (`rcloneEnv`), so no credential reaches a command line, and
`bucketPath` is the bucket the `:s3:` remotes address. `srcDir` holds the
files and `fileNames` lists the ones to upload; the list is passed as a
`--files-from` file, so only the named files leave the machine. The files
upload first, then the per-SHA marker, in the same order as the curl tool. A
files failure exits 1; a marker failure only warns (see `uploadMarkerWith`).
The `rclone` parameter names the binary and exists for the tests; production
callers use the default.
-/
def putStagedViaRclone (dest : StagedUploadDest) (env : Array (String × Option String))
    (bucketPath : String) (markerSha? : Option String)
    (srcDir : FilePath) (fileNames : Array String) (overwrite : Bool)
    (rclone : String := "rclone") : IO Unit := do
  let run (args : Array String) : IO UInt32 := do
    let child ← IO.Process.spawn { cmd := rclone, args, env }
    child.wait
  if fileNames.isEmpty then
    IO.println "No files to upload"
  else
    IO.println s!"Uploading {fileNames.size} file(s) via rclone to \
      {dest.base}/{dest.filesPrefix}"
    let dir ← IO.FS.createTempDir
    let code ← try
      let filesFrom := dir / "files-from.txt"
      IO.FS.writeFile filesFrom ("\n".intercalate fileNames.toList ++ "\n")
      run (rcloneFilesArgs bucketPath dest srcDir filesFrom overwrite)
    finally
      IO.FS.removeDirAll dir
    if code != 0 then
      IO.eprintln s!"rclone upload failed with exit code {code}"
      IO.Process.exit 1
  if let some sha := markerSha? then
    uploadMarkerWith (dest.markerURL sha) sha fun file => do
      let code ← run (rcloneMarkerArgs bucketPath dest file sha)
      unless code == 0 do
        throw <| IO.userError s!"rclone exited with code {code}"

end Cache.Requests
