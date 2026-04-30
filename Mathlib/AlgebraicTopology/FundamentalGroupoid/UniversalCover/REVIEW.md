# Universal cover — deferred review items

This file records review items raised during a self-review of the
universal-cover construction (PR #38292) against `mathlib-standards.md`,
deferred to a follow-up PR. The corresponding "fix-now" items have already
been addressed on this branch.

## Modularise long proofs

- **`Path.paste_segment_homotopies`** (`SemilocallySimplyConnected.lean`,
  ≈l. 679–810). Single ≈130-line proof with two opaque `convert` blocks
  used to dodge "motive is not type correct" errors. Extract the auxiliary
  paths and the base / step lemmas as named `private` lemmas.
- **`BasedPath.toPath_homotopic_of_joinedIn_slsc`** (`BasedPath.lean`,
  ≈l. 748–859). Single ≈110-line proof. The four boundary-evaluation
  sub-`have`s (`hK_zero`, `hK_one`, `hK_at_zero`, `hK_at_one`) deserve to
  be top-level lemmas about the reparametrisations
  `joinedInSLSC_uFn` / `joinedInSLSC_vFn`.
- **`UniversalCover.joined_basepoint_of_ofBasedPath`** (`Covering.lean`,
  ≈l. 73–121). ≈50 lines of `Subtype.ext` / `unitInterval` arithmetic
  boilerplate, a symptom of missing API on `unitInterval` multiplication.

## API gaps for new definitions

- `BasedPath` (`BasedPath.lean`): no `mk` simp lemma, no `BasedPath.refl`,
  no characterisation of the round-trip
  `(γ : BasedPath x₀) ↔ (Path x₀ (endpoint γ))` via `toPath` / `ofPath`.
- `BasedPath.deformTerminal`: missing `endpoint`, missing
  continuity-in-parameters lemma, and no specialisation when the
  deforming path is `refl`.
- `Path.initialSegmentFamily` (`BasedPath.lean`): only zero/one
  evaluation lemmas. Missing a general `apply` lemma giving the value at
  arbitrary `(t, s)`.
- `UniversalCover.basedPathComponent` / `basedPathSheet` / `sheet`
  (`UniversalCover/Basic.lean`): no `mem_iff` characterisations, no
  `sheet_self` lemma, no
  `sheet_eq_image_of_pathComponent`.

## `@[simp] endpoint_def`

`BasedPath.lean:77` is `@[simp] theorem endpoint_def : endpoint γ = γ.1 1 := rfl`,
which makes `simp` unfold the `endpoint` abstraction immediately. Standards-wise
this is bad — but it is currently relied on by at least
`deformTerminal_apply_of_lt` (`BasedPath.lean:179`), and dropping the tag
introduces a `sorry` there. Cleanup requires adding intermediate
`endpoint`-aware simp lemmas to those proofs first.

## Module-system migration

`BasedPath.lean` and `SemilocallySimplyConnected.lean` both still open with
`@[expose] public section`. A prior commit on this branch (`4adb0d0e`)
removed the same line from `Covering.lean` by individually tagging each
public-facing declaration with `public` (and dropping `private` from helpers
that became public-by-default). The same migration should happen here, but
both files are large and the change is mechanical-but-not-trivial; defer to
a follow-up.

## Style and abstraction

- **Brittle `simpa` chains.** `BasedPath.lean` contains roughly twenty
  `simpa [endpoint, ofPath, …]`-style invocations with explicit unfold
  lists. These break under minor refactor. Replace with a small dedicated
  `@[simp]` set characterising `endpoint` and `ofPath`.
- **Weak doc strings.** Several BasedPath defs around l. 95–200
  (`ofPath`, `append`, `terminalTail`, `initialSegmentFamily`) have
  one-line doc strings that just restate the type. Expand to explain the
  intent (and, where applicable, the formula).
