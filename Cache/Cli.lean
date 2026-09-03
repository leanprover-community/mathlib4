/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cli
import Cache.Upload.Defs

/-!
# The command line's shared vocabulary

The `cache` command line is parsed by the `Cli` library. This module holds
what several commands share: the value types a flag can carry
(`Cli.ParseableType` instances for the tool's own types, so the parser
validates a container or a backend name itself) and the flags no workflow
owns (`CommonFlag`). The command tree is `Cache.Commands`; each read workflow
declares its own flags (`Cache.Workflow`).
-/

namespace Cache

open Cache.Requests
open System (FilePath)

/-- A container by name, for the `--container` shortcut of an upload. -/
instance : Cli.ParseableType Container where
  name := "container"
  parse? := Container.parse?

/-- A trust-ordered, comma-separated list of containers, for `--cache-from`. -/
instance : Cli.ParseableType (List Container) where
  name := "containers"
  parse? := parseCacheFromList

/-- A storage backend by name, for `--backend`. -/
instance : Cli.ParseableType UploadBackend where
  name := "backend"
  parse? := UploadBackend.parse?

/-- A non-empty path, for `--staging-dir`. -/
instance : Cli.ParseableType FilePath where
  name := "path"
  parse? s := if s.isEmpty then none else some s

/-! The flags several commands share and no workflow owns: `--repo` for
`get`, `put --dev-cache`, and `query`; `--backend` and `--staging-dir` for
the upload and staging commands. Each flag comes with its typed reader from a
parsed command line. -/
namespace CommonFlag

/-- `--repo=OWNER/REPO`: the repository whose cache to read or write. -/
def repo : Cli.Flag := {
  longName := "repo"
  description := "The repository whose cache to read, as OWNER/REPO; the default is the \
    checkout's git remote, and it selects the workflow of a read (see `cache --help`). For a \
    --dev-cache upload, the fork the upload is for."
  type := String }

/-- The `--repo` of the parsed command line `p`, if given. -/
def repoOf (p : Cli.Parsed) : Option String := (p.flag? repo.longName).map (·.as! String)

/-- `--backend=NAME`: the storage backend of a write. -/
def backend : Cli.Flag := {
  longName := "backend"
  description := s!"The storage backend of an upload, one of \
    {", ".intercalate (UploadBackend.all.map UploadBackend.name)} (default azure)."
  type := UploadBackend }

/-- The `--backend` of the parsed command line `p`, `azure` by default. -/
def backendOf (p : Cli.Parsed) : UploadBackend :=
  ((p.flag? backend.longName).map (·.as! UploadBackend)).getD .azure

/-- `--staging-dir=DIR`: the staging directory. -/
def stagingDir : Cli.Flag := {
  longName := "staging-dir"
  description := "The staging directory: where stage writes the .ltar files, and what \
    unstage and put-staged read."
  type := FilePath }

/-- The `--staging-dir` of the parsed command line `p`, if given. -/
def stagingDirOf (p : Cli.Parsed) : Option FilePath :=
  (p.flag? stagingDir.longName).map (·.as! FilePath)

/-- The long names of the common flags, with the `help` flag `Cli` adds. -/
def names : List String :=
  "help" :: [repo, backend, stagingDir].map (·.longName)

end CommonFlag

end Cache
