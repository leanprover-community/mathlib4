# Universal cover — deferred review items

This file records review items raised during a self-review of the
universal-cover construction (PR #38292) against `mathlib-standards.md`,
deferred to a follow-up PR. The corresponding "fix-now" items have already
been addressed on this branch.

## Modularise long proofs

- **`BasedPath.toPath_homotopic_of_joinedIn_slsc`** (`BasedPath.lean`,
  ≈l. 748–859). Single ≈110-line proof. The four boundary-evaluation
  sub-`have`s (`hK_zero`, `hK_one`, `hK_at_zero`, `hK_at_one`) deserve to
  be top-level lemmas about the reparametrisations
  `joinedInSLSC_uFn` / `joinedInSLSC_vFn`.

## API gaps for new definitions

- `BasedPath` (`BasedPath.lean`): no `mk` simp lemma, no `BasedPath.refl`.
  (Round-trip `ofPath_toPath_self` and the `ofPath_cast` simp lemma are
  now in place.)
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

## `endpoint` abstraction (tentative)

The original review item here proposed dropping `@[simp]` from
`endpoint_def : endpoint γ = γ.1 1` on the grounds that the simp tag
"breaks the abstraction." On further inspection that framing was wrong:

- `endpoint` is declared `@[expose] public def`, so its body is already part
  of the public surface — clients can (and do) unfold it freely.
- The file itself treats `endpoint` as transparent: there are ~20
  `simpa [endpoint, …]` invocations, plus an explicit `rw
  [BasedPath.endpoint_def]` in `Covering.lean`. There is no abstraction
  barrier in practice.
- `@[simp] endpoint_def` is doing load-bearing work pinning simp's
  *confluence*: in the construction of `deformTerminal` and across the
  `deformTerminal_apply_*` family, multiple `simpa … using …` proofs rely
  on goal and using-term landing on the same normal form. Removing the
  tag breaks `deformTerminal`'s `target'` proof and makes every
  `deformTerminal_apply_*` produce `sorry`. Compensating proofs would be
  explicit `calc` / `show` chains hard-coding the intermediate form —
  more verbose, more brittle to other simp lemma changes, and arguably
  worse than the status quo.

So: leave `@[simp] endpoint_def` alone.

The interesting follow-up — to be treated as **a tentative experiment**,
not a planned change — is to go the *opposite* direction:

- Drop `@[expose]` from `endpoint` so the body genuinely is opaque to
  clients.
- Replace the unfolding `@[simp] endpoint_def` with a curated simp set
  in the *folding* direction:
  - `@[simp] endpoint_apply : γ.1 1 = endpoint γ` (or a `toPath`-flavoured
    variant), turning `γ.1 1` into `endpoint γ` rather than the reverse.
  - Keep / extend the existing `endpoint_ofPath`, `endpoint_append`,
    `endpoint_deformTerminal` simp lemmas.
- Rewrite the `simpa [endpoint, ofPath, …]` chains to use this folded
  simp set.

This *might* improve readability of intermediate goals (fewer `γ.1 1`
terms, more `endpoint γ`) and reduce coupling to the underlying
`Subtype` projection. It might also make things worse if folding
conflicts with simp normal forms in `Path` / `ContinuousMap`. The only
way to know is to try it on a branch and compare proof length and
goal readability before/after.

Treat this as an idea worth probing, not a deferred TODO. If the
experiment doesn't yield a clear win, this section can simply be
deleted.

## Style and abstraction

- **Brittle `simpa` chains.** `BasedPath.lean` contains roughly twenty
  `simpa [endpoint, ofPath, …]`-style invocations with explicit unfold
  lists. These break under minor refactor. Replace with a small dedicated
  `@[simp]` set characterising `endpoint` and `ofPath`.
- **Weak doc strings.** Several BasedPath defs around l. 95–200
  (`ofPath`, `append`, `terminalTail`, `initialSegmentFamily`) have
  one-line doc strings that just restate the type. Expand to explain the
  intent (and, where applicable, the formula).
