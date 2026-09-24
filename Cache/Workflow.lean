/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Workflow.Public
import Cache.Workflow.Developer
import Cache.Workflow.Nightly

/-!
# The read workflows

A `get` runs one of three workflows, and decides which before it reads:

* the public-cache workflow (`Cache.Workflow.Public`): a canonical mathlib
  checkout, a project that depends on Mathlib, or a read pointed at an
  external endpoint. One fetch from one URL. No flags of its own.
* the developer-cache workflow (`Cache.Workflow.Developer`): a fork checkout,
  or a read on the canonical repository that names a container chain, a
  scope, or `--unsafe`. The
  trust-ordered chain across the public cache and the developer cache, with
  the fork's per-commit namespace. Owns the chain-read flags, and `query`.
* the nightly workflow (`Cache.Workflow.Nightly`): the nightly-testing
  repository. Its own chain, read through the public endpoint. Owns the
  chain and scope flags.

Each workflow declares its flags, and a `get` command declares their union
(`flags`), so the `Cli` parser rejects a flag no workflow accepts before
anything runs. A read then runs in three steps:

1. decide (`forRead`): the workflow, from the resolved repository, the flat
   endpoint, and whether a chain read was requested (`chainReadRequested`).
   The triggers of a chain read are the decision's own list
   (`chainReadFlags`, `chainReadVariables`), so a workflow's flags can change
   without moving a read to another workflow;
2. plan (`plan`): the chosen workflow parses and checks its own flags and
   settings and rejects those of another workflow. The command plans before
   it hashes, so an invalid option fails fast;
3. read (`Plan.read`): the workflow's read, on the hashed files.

Each workflow owns its chain and the hosts it reads. The three workflow
modules share the mechanisms below them (the transfers, the container chain,
the notice, the markers); their code paths meet only in this module.

The workflows are a matter of reads. An upload writes the container
`--container` names (`Upload`), and the local commands touch no workflow.
-/

namespace Cache

open Cache.Requests
open Cache.Workflow
open System (FilePath)

/-- The workflow a `get` runs under; see the module docstring. -/
inductive Workflow where
  /-- The public cache alone. `public` is a reserved word, hence the name. -/
  | publicCache
  /-- The developer cache: the fork chain. -/
  | developer
  /-- The nightly-testing repository's chain. -/
  | nightly
  deriving DecidableEq, Repr, BEq, Inhabited

namespace Workflow

/-- The workflow's name in messages. -/
def name : Workflow → String
  | .publicCache => Public.name
  | .developer => Developer.name
  | .nightly => Nightly.name

/-- The flags of several workflows, merged by name: a flag two workflows
share (`--scope`) appears once, with the first declaration's description. -/
def unionFlags (groups : List (Array Cli.Flag)) : Array Cli.Flag :=
  groups.foldl (Cli.Array.leftUnionBy (·.longName)) #[]

/-- The flags of a read under any workflow. -/
def flags : Array Cli.Flag := unionFlags [Public.flags, Developer.flags, Nightly.flags]

/--
The flags that ask for a container-chain read: `--cache-from`, `--scope`,
`--unsafe`, and `--unsafe-window`. On the canonical repo each one selects the
developer workflow (`forRead`). The list is the decision's own, apart from the
flags any workflow declares, so a flag a workflow adds does not change which
workflow a read runs.
-/
def chainReadFlags : List Cli.Flag :=
  [ChainOptions.flag, Scope.flag, Developer.unsafeFlag, Developer.unsafeWindowFlag]

/-- The variables that ask for a container-chain read, with their values in
the settings `s`: the chain `MATHLIB_CACHE_FROM` and the scope
`MATHLIB_CACHE_REPO_SCOPE`. -/
def chainReadVariables (s : Settings) : List (String × Option String) :=
  [("MATHLIB_CACHE_FROM", s.cacheFrom?), ("MATHLIB_CACHE_REPO_SCOPE", s.repoScope?)]

/-- Whether the parsed command line `p` carries a flag of `chainReadFlags`. -/
def chainReadFlagged (p : Cli.Parsed) : Bool :=
  chainReadFlags.any fun f => p.hasFlag f.longName

/-- Whether the read asks for a container-chain read: a flag of
`chainReadFlags` is present, or a variable of `chainReadVariables` is set. -/
def chainReadRequested (p : Cli.Parsed) (s : Settings) : Bool :=
  chainReadFlagged p || (chainReadVariables s).any (·.2.isSome)

/--
The workflow a repo alone selects: the nightly-testing repository is
`nightly`, the canonical repository is `publicCache`, every other repo is a
fork and `developer`. The read decision (`forRead`) refines this.
-/
def forRepo (repo : String) : Workflow :=
  if repo == NIGHTLY_TESTING_REPO then .nightly
  else if repo == MATHLIBREPO then .publicCache
  else .developer

/--
The workflow of a read, from the resolved repo (see `resolveRepo`), the flat
endpoint, and whether a chain read was requested (`chainReadRequested`).

A flat endpoint (`getURL?`, from `MATHLIB_CACHE_GET_URL`) is a public cache
served elsewhere, so it selects the public-cache workflow whatever the repo.
Otherwise the canonical repo reads the public cache unless a chain-read option
selects the developer workflow. A fork or the nightly-testing repository
selects its workflow whatever the options say.
-/
def forRead (repo : String) (getURL? : Option String) (chainRead : Bool) : Workflow :=
  if getURL?.isSome then .publicCache
  else match forRepo repo with
    | .publicCache => if chainRead then .developer else .publicCache
    | w => w

/-- A read with its options parsed and checked: the chosen workflow and what
it reads with. -/
inductive Plan where
  /-- The public cache: the one URL it reads. -/
  | publicCache (url : String)
  /-- The developer cache and its options. -/
  | developer (options : Developer.Options)
  /-- The nightly chain and its options. -/
  | nightly (options : Nightly.Options)

/-- The plan of the workflow `w`: its options from the parsed command line `p`
and the settings of `ctx`, with `--scope` refs resolved in the mathlib
checkout. Throws on an invalid option. -/
def plan (w : Workflow) (p : Cli.Parsed) (ctx : ReadContext) : IO Plan := do
  match w with
  | .publicCache => return .publicCache (← Public.plan p ctx.settings)
  | .developer => return .developer (← Developer.parseOptions p ctx.settings ctx.mathlibCwd)
  | .nightly => return .nightly (← Nightly.parseOptions p ctx.settings ctx.mathlibCwd)

/-- Run the planned read. -/
def Plan.read (plan : Plan) (ctx : ReadContext) (req : ReadRequest) : IO.CacheM Unit := do
  match plan with
  | .publicCache url => Public.get url req
  | .developer options => Developer.get options ctx req
  | .nightly options => Nightly.get options ctx req

end Workflow

end Cache
