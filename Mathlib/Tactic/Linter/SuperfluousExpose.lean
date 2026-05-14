/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public meta import Lean.Elab.Command
public import Lean.Environment
public import Lean.Class
public import Lean.Structure
public import Lean.Meta.Instances
public import Lean.ReducibilityAttrs
public import Lean.ProjFns
public import Lean.Meta.Match.MatcherInfo
public import Lean.Meta.Match.MatchPatternAttr
public import Batteries.Tactic.Lint.Basic
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# Superfluous-expose linter

This linter is the dual of `privateModule`: it lints against modules with an
`@[expose] public section` header but no declaration whose body needs to be
visible downstream. It suggests removing the `@[expose]` modifier, flipping
the file's default from bodies-exposed to bodies-hidden with no semantic
effect on downstream typechecking.

A declaration "benefits from exposure" iff its body matters to downstream
proofs or elaboration. Plain `def`, plain `inductive`, `@[match_pattern]`
defs, `@[irreducible]` defs (downstream `rw`/`unfold` still needs the body),
and `@[to_additive]`-decorated defs all benefit. Theorems, abbrevs, classes,
structures, instances, `unsafe`/`partial` defs, projections, matchers, and
notation-generated parser entries do not. Compiler-generated auxiliary
declarations (recursors, no-confusion lemmas, equation lemmas, etc.) are
identified by `Batteries.Tactic.Lint.isAutoDecl` and skipped.

## Implementation notes

Like `privateModule`, this linter acts on the end-of-input
`Parser.Command.eoi` token, so it has access to the full elaborated
environment. It walks `env.constants.map₂` to enumerate locally-defined
constants.

Before linting, the file's source text is scanned (via `getFileMap`) for the
presence of `@[expose] public section`. If no such header is present, the
linter exits silently — the suggestion to remove `@[expose]` wouldn't apply.
Only `public section`s are checked because `@[expose]` only affects
downstream visibility, which is exclusive to `public section`.

The more elegant approach — inspecting `(← getScope).attrs` directly for the
`expose` token — is unavailable here: every `@[expose] public section` is
already closed by the time `eoi` fires, so the root scope's `attrs` is
empty. Tracking scope state across commands via an environment extension
would in principle bridge the gap, but linter `modifyEnv` calls don't
persist across `Linter.run` invocations, so we fall back to a small block-
comment-aware text scan.

The linter is conservative: every known limitation produces a false negative
(the linter stays silent on a file where the warning would have applied),
never a false positive. The known cases are:

* **File-level granularity.** In a file with multiple `@[expose] public
  section`s where only some are needed, the linter stays silent if any decl
  in the file benefits from exposure — the superfluous `@[expose]` on the
  other section(s) is undetected.
* **Tactic-implementation `def`s.** Decls produced by `simproc_decl`, `elab`,
  `macro_rules`, `scoped macro`, … are treated as ordinary defs that benefit
  from exposure, so files made up only of such decls will not warn.
* **Scoped/local instances.** `Lean.Meta.isInstanceCore` catches globally-
  registered instances but misses `scoped instance` and `local instance`.
  In the environment, those are indistinguishable from `@[implicit_reducible]
  def` non-instance shortcuts (whose bodies *do* need exposure), so we don't
  attempt to recover them. Files containing only scoped or local instances
  will not warn.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- The `superfluousExpose` linter detects modules with `@[expose] public section`
where no declaration needs its body visible downstream, and suggests removing
the `@[expose]` modifier. -/
public register_option linter.superfluousExpose : Bool := {
  defValue := false
  descr := "Enable the `superfluousExpose` linter, which detects modules \
    where `@[expose] public section` is superfluous."
}

/-- True iff `info`'s return type — the codomain after stripping all `∀`/`→`
binders — has head constant `name`. -/
private def returnTypeHeadIs (info : ConstantInfo) (name : Name) : Bool :=
  match info.type.getForallBody.getAppFn with
  | .const n _ => n == name
  | _ => false

/-- True iff the def is plausibly a `notation`/`infix`/`syntax`/`macro`-
generated parser entry. Requires both a conventional leaf-name prefix
(`term…` / `binder…` / `stx…` / `tactic…`) AND a return type that is one of
Lean's parser- or macro-descriptor types. The conjunction avoids false
positives on user defs that happen to share the prefix.

The prefix check is permissive (`term` rather than `term_`) because the leaf
name's shape depends on the notation's syntax: an infix `notation:65 a " ⋄ " b`
generates `«term_⋄_»` (with leading underscore for the leading arg), whereas
a function-like `notation "F(" a ")"` generates `«termF(_)»` (no underscore
separator). The return-type gate is doing the real classification work; the
prefix is just a cheap filter. -/
private def looksLikeNotationDecl (info : ConstantInfo) (name : Name) : Bool :=
  let nameMatches := match name with
    | .str _ s => s.startsWith "term" || s.startsWith "binder" ||
                  s.startsWith "stx" || s.startsWith "tactic"
    | _ => false
  let typeMatches :=
    returnTypeHeadIs info ``Lean.ParserDescr ||
    returnTypeHeadIs info ``Lean.TrailingParserDescr ||
    returnTypeHeadIs info ``Lean.Macro
  nameMatches && typeMatches

/-- A constant info "benefits from exposure" iff its body is semantically
relevant to downstream typechecking. Callers must filter
`Batteries.Tactic.Lint.isAutoDecl` names beforehand. -/
private def benefitsFromExposure (env : Environment) (name : Name)
    (info : ConstantInfo) : Bool :=
  if isPrivateName name then false else
  if looksLikeNotationDecl info name then false else
  if (env.getProjectionFnInfo? name).isSome then false else
  if Lean.Meta.isMatcherCore env name then false else
  match info with
  | .defnInfo dv =>
      if Lean.Meta.isInstanceCore env name then false
      else if dv.safety != .safe then false   -- `unsafe def` / `partial def`
      -- `@[match_pattern]` needs the body for pattern-match elaboration,
      -- even when the def is `@[reducible]`. Example:
      --   @[match_pattern, reducible] def myPat : α ⊕ β := Sum.inl _
      --   -- downstream:  match x with | myPat a => …   needs myPat's body
      else if Lean.hasMatchPatternAttribute env name then true
      else
        match Lean.getReducibilityStatusCore env name with
        -- `abbrev`: bodies exposed by default in modules regardless of `@[expose]`.
        | .reducible => false
        -- Plain `def`, `@[irreducible] def`, `irreducible_def`, and
        -- `@[implicit_reducible]` all need the body downstream. `@[irreducible]`
        -- does not save us — downstream code can still `rw`/`unfold` explicitly:
        --   irreducible_def myConst : Nat := 42
        --   -- downstream:  theorem … := by rw [myConst]   needs myConst's body
        | _ => true
  | .inductInfo _ =>
      -- Plain inductives benefit (pattern matching, recursor calls); structures
      -- and classes go through auto-generated projections.
      !Lean.isStructure env name
  | _ => false

/-- True iff `src` contains an `@[expose] public (meta)? section` header at a
line start (after leading whitespace) and outside any block comment. Only
`public section`s are matched: `@[expose]` only affects downstream
visibility, which is exclusive to `public section`. -/
private def fileHasExposeSection (src : String) : Bool :=
  go (src.splitOn "\n") 0
where
  /-- True iff `line` opens a `public section` after stripping leading whitespace. -/
  lineOpensExposeSection (line : String) : Bool :=
    let trimmed := line.trimAsciiStart
    if !trimmed.startsWith "@[expose]" then false else
      let rest := (trimmed.drop "@[expose]".length).trimAsciiStart
      rest.startsWith "public section" || rest.startsWith "public meta section"
  /-- Block-comment depth after consuming `chars`, given a starting depth.
  Tracks balanced `/-` / `-/` pairs; treats `--` at depth 0 as starting a
  line comment that consumes the rest of the line. -/
  commentDepthAfter : List Char → Nat → Nat
    | [], d => d
    | '-' :: '-' :: _, 0 => 0
    | '/' :: '-' :: rest, d => commentDepthAfter rest (d + 1)
    | '-' :: '/' :: rest, d => commentDepthAfter rest d.pred
    | _ :: rest, d => commentDepthAfter rest d
  go : List String → Nat → Bool
    | [], _ => false
    | line :: rest, depth =>
        (depth == 0 && lineOpensExposeSection line) ||
        go rest (commentDepthAfter line.toList depth)

/--
The `superfluousExpose` linter detects modules with `@[expose] public section`
where no declaration in the file needs its body exposed downstream. Suggests
removing the `@[expose]` modifier.

This linter only acts on the end-of-input `Parser.Command.eoi` token, and
ignores all other syntax. It logs its message at the top of the file.
-/
def superfluousExpose : Linter where run stx := do
  if stx.isOfKind ``Parser.Command.eoi then
    unless getLinterValue linter.superfluousExpose (← getLinterOptions) do
      return
    let env ← getEnv
    if !env.header.isModule then return
    if env.constants.map₂.isEmpty then return
    unless fileHasExposeSection (← getFileMap).source do return
    for (decl, info) in env.constants.map₂ do
      if ← liftCoreM (Batteries.Tactic.Lint.isAutoDecl decl) then continue
      if benefitsFromExposure env decl info then return
    let topOfFileRef := Syntax.atom (.synthetic ⟨0⟩ ⟨0⟩) ""
    logLint linter.superfluousExpose topOfFileRef
      "This module has `@[expose] public section` but no declaration that \
      would benefit from body exposure. The `@[expose]` modifier can be \
      safely removed: it would only affect `def`/`inductive` bodies, and \
      there are none here that need exposure (only theorems, instances, \
      classes/structures, abbrevs, notation, or auto-generated decls)."

initialize addLinter superfluousExpose

end Mathlib.Linter
