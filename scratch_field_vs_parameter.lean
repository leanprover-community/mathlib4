import Mathlib.Data.Sum.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finite.Sum
import Mathlib.RingTheory.Extension.Generators
import Mathlib.GroupTheory.Generators

/-!
# Scratch: index type as a structure FIELD vs a structure PARAMETER

The index type of a generating family can live in two places. It can be
data inside each term (a FIELD, `GensF` below), or part of the term's
type (a PARAMETER, `GensP`). Which is better? Context: the TODO in
`Mathlib/RingTheory/Extension/Generators.lean` (lines 41–48) and
PR #25085, which moved `Algebra.Generators` to the PARAM style.

The demo is a `union` construction whose index type is a sum, built in
both styles. In the FIELD style the `⊕` is present definitionally but
never appears in a goal; goals say `(P.union Q).ι` instead. `rw`, `simp`,
and instance search all match syntax, so mathlib's entire `Sum` API
misses (Tests 1–5). In the PARAM style the `⊕` is written in the type,
and everything fires.

Each failing FIELD example is followed by its escape hatches, where any
exist, and then by its PARAM twin. Nine examples are marked EXPECTED
ERROR: six in the toy demo, three on the reconstructed old API at the
bottom. They are supposed to fail. That is the demo.

The `Context` section just below shows the real thing in quotes: the old
FIELD-style `Algebra.Generators` and the PARAM style it became. At the
bottom, the old API is rebuilt at demo scale and fails the same tests,
and the demo re-runs against the live post-#25085 API.

Scratch material, not part of the library. Delete freely.
-/

/-! ## Context: the real migration — `Algebra.Generators` before and after

`GensF` and `GensP` are distilled from an actual mathlib refactor. Until
June 2025, `Algebra.Generators` stored its variable type as a field, and
its composition hid the `⊕` in the body. This is our `GensF.union`,
life-size:

```
structure Algebra.Generators (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] where
  vars : Type w                     -- the index type, stored as a FIELD
  val : vars → S
  σ' : S → MvPolynomial vars R
  aeval_val_σ' : ∀ s, aeval val (σ' s) = s
  ...                               -- (algebra-instance bookkeeping elided)

def comp (Q : Generators S T) (P : Generators R S) : Generators R T where
  vars := Q.vars ⊕ P.vars           -- the `⊕`, invisible from outside
  ...
```

(Source: `git show 966daba4dd6^:Mathlib/RingTheory/Extension/Generators.lean`;
`structure` at line 57, `comp` at line 198.  Signatures verbatim, fields
elided as marked.)

The TODO that motivated the refactor still sits at
`Mathlib/RingTheory/Extension/Generators.lean:41-48`. It reads like a
field report of Tests 1–5 below:

> Currently, Lean does not see through the `ι` field of terms of
> `Generators R S` obtained from constructions, e.g. composition.  This
> causes fragile and cumbersome proofs, because `simp` and `rw` often don't
> work properly.  `Generators R S` (and `Presentation R S`, etc.) should be
> refactored in a way that makes these equalities reducibly def-eq, for
> example by unbundling the `ι` field […]

PR #25085 (https://github.com/leanprover-community/mathlib4/pull/25085,
merged 2025-06-02 as commit `966daba4dd6`) did the unbundling. Today `ι`
is a parameter, and `comp` shows its `⊕` in the signature. This is our
`GensP.union`:

```
structure Algebra.Generators (R S ι : Type*) [CommRing R] [CommRing S] [Algebra R S] where
  val : ι → S
  σ' : S → MvPolynomial ι R
  aeval_val_σ' : ∀ s, aeval val (σ' s) = s
  ...

def comp (Q : Generators S T ι') (P : Generators R S ι) :
    Generators R T (ι' ⊕ ι) where
  val := Sum.elim Q.val (algebraMap S T ∘ P.val)
  ...
```

(Source: `Mathlib/RingTheory/Extension/Generators.lean` at this checkout —
`structure Algebra.Generators` at line 64, `comp` at line 231.)

#25085 was not a one-off. Mathlib has unbundled index-type fields
repeatedly, and never done the reverse. `IsFreeGroup` stored a specific
generating family until PR #7698
(https://github.com/leanprover-community/mathlib4/pull/7698, commit
`bab05758f84`, 2023-10-28) replaced it with `FreeGroupBasis ι G`. Its
commit message calls the bundled data "bad, as there are many sets of
generators in a free group, and changing sets of generators happens all
the time in geometric group theory". `Computability.Encoding` unbundled
its alphabet `Γ` in PR #37928
(https://github.com/leanprover-community/mathlib4/pull/37928, commit
`ca158545413`, 2026-06-30), deleting `FinEncoding` in favour of `[Fintype Γ]`.

Two present-day data points. `Module.Relations`
(`Mathlib/Algebra/Module/Presentation/Basic.lean:55`) still bundles both
of its index types as fields (`G : Type w₀`, `R : Type w₁`) behind
`set_option linter.checkUnivs false`: the FIELD style surviving, universe
bump and all. And this branch's `Group.Generators G α` and
`Group.Presentation G α` (`Mathlib/GroupTheory/Generators.lean:44`,
`Mathlib/GroupTheory/Presentation.lean:47`) are born PARAM-style,
`Fin n` existential bridge included. -/

/-! ## The two styles -/

/-- FIELD: the index type is data stored in each term. -/
structure GensF (G : Type) where
  ι : Type
  val : ι → G

/-- PARAMETER: the index type is part of the structure's type — the shape of
`Algebra.Generators R S ι` and of `Group.Generators G α`. -/
structure GensP (G : Type) (ι : Type) where
  val : ι → G

/-! ## The `union` construction

The same construction twice, with one difference. `GensF.union` puts the
`⊕` in the body, where only unfolding `union` can reveal it. `GensP.union`
puts it in the type signature, so every downstream goal shows it. -/

def GensF.union {G : Type} (P Q : GensF G) : GensF G :=
  ⟨P.ι ⊕ Q.ι, Sum.elim P.val Q.val⟩

def GensP.union {G ι κ : Type} (P : GensP G ι) (Q : GensP G κ) :
    GensP G (ι ⊕ κ) :=
  ⟨Sum.elim P.val Q.val⟩

/-! ## The equation lemmas -/

/-! **FIELD** -/

/- Says: the union's index type is the sum of the two index types.
True by `rfl`: the equality exists, it just never appears in a goal.
Test 1 shows that no rewrite can actually use it. -/
@[simp] theorem GensF.union_ι {G : Type} (P Q : GensF G) :
    (P.union Q).ι = (P.ι ⊕ Q.ι) := rfl

/- Says: the union family evaluates by cases. Left indices go through
`P.val` and right indices through `Q.val`; that is what `Sum.elim` means.
Also true by `rfl`, but crooked: the left side has type
`(P.union Q).ι → G`, the right side `P.ι ⊕ Q.ι → G`, and the two agree
only definitionally. We deliberately do not tag it `@[simp]`. Tagging it
would close Test 2, but that repair costs one hand-written cross-type
lemma per projection per construction. -/
theorem GensF.union_val {G : Type} (P Q : GensF G) :
    (P.union Q).val = Sum.elim P.val Q.val := rfl

/-! **PARAM** -/

/- No `union_ι` exists or is needed, because there is no `.ι` projection.
The typechecker does its job. Says: the union of a family indexed by `ι`
and one indexed by `κ` is a family indexed by `ι ⊕ κ`. The whole proof is
that the example elaborates: -/
example {G ι κ : Type} (P : GensP G ι) (Q : GensP G κ) :
    GensP G (ι ⊕ κ) := P.union Q

/- This `val` equation is honest: both sides have the same syntactic
type. So it is safe as a simp lemma. Test 2 relies on it. -/
@[simp] theorem GensP.union_val {G ι κ : Type} (P : GensP G ι) (Q : GensP G κ) :
    (P.union Q).val = Sum.elim P.val Q.val := rfl

/-! ## Test 1: can `Sum.forall` split a quantifier over the union's index?

Every example here states the same triviality: every index of the union
family is sent to some group element (take `g` to be that element). The
claim does not matter; its shape does. It is a `∀` over the union's index
type, and the proof wants to split it into "indices from `P`" and
"indices from `Q`" via
`Sum.forall : (∀ x : α ⊕ β, p x) ↔ (∀ a, p (.inl a)) ∧ (∀ b, p (.inr b))`. -/

/-! **FIELD** -/

/- No. `rw` matches syntax (at reducible transparency), and the goal says
`(P.union Q).ι`, never `⊕`. Definitional truth does not help.
EXPECTED ERROR: Did not find an occurrence of the pattern `∀ (x : ?α ⊕ ?β), …` -/
example {G : Type} (P Q : GensF G) :
    ∀ x : (P.union Q).ι, ∃ g, (P.union Q).val x = g := by
  rw [Sum.forall]

/- The repair lemma `union_ι` cannot fire either. The rest of the goal
depends on the binder type, because `val` demands an argument of type
`(P.union Q).ι`. Abstracting the type out is therefore ill-typed. The
`⊕` cannot be exposed, precisely because it is hidden.
EXPECTED ERROR: motive is not type correct -/
example {G : Type} (P Q : GensF G) :
    ∀ x : (P.union Q).ι, ∃ g, (P.union Q).val x = g := by
  rw [GensF.union_ι]

/-! **FIELD** escape hatches -/

/- Each failure is fixable. The fix is always to spend, by hand, the
unfolding that `rw` and `simp` refuse to do on their own. But every fix
writes the body of `union` into the proof. The definition's abstraction
boundary is gone, and none of it scales to a library. PARAM needs no
escape hatches. -/

/- (a) Unfolding `union` by name exposes the `⊕`. Now `Sum.forall` fires,
    and the proof finishes exactly like the PARAM twin. -/
example {G : Type} (P Q : GensF G) :
    ∀ x : (P.union Q).ι, ∃ g, (P.union Q).val x = g := by
  unfold GensF.union
  rw [Sum.forall]
  exact ⟨fun i => ⟨_, rfl⟩, fun j => ⟨_, rfl⟩⟩

/- (b) `show` does the same unfolding by hand: it moves to a defeq goal
    that says `⊕`. The price is starker. The `show` line is the body of
    `union`, typed out verbatim. -/
example {G : Type} (P Q : GensF G) :
    ∀ x : (P.union Q).ι, ∃ g, (P.union Q).val x = g := by
  show ∀ x : P.ι ⊕ Q.ι, ∃ g, Sum.elim P.val Q.val x = g
  rw [Sum.forall]
  exact ⟨fun i => ⟨_, rfl⟩, fun j => ⟨_, rfl⟩⟩

/- (c) Or skip `Sum.forall` altogether. `rintro` and `cases` unfold at
    default transparency, so the manual case split works directly. But
    its branch goals land back in the shape that defeats `simp` in
    Test 2 below. -/
example {G : Type} (P Q : GensF G) :
    ∀ x : (P.union Q).ι, ∃ g, (P.union Q).val x = g := by
  rintro (i | j) <;> exact ⟨_, rfl⟩

/-! **PARAM** -/

/- The goal says `⊕`, so `Sum.forall` just fires. -/
example {G ι κ : Type} (P : GensP G ι) (Q : GensP G κ) :
    ∀ x : ι ⊕ κ, ∃ g, (P.union Q).val x = g := by
  rw [Sum.forall]
  exact ⟨fun i => ⟨_, rfl⟩, fun j => ⟨_, rfl⟩⟩

-- homeow: so it's better for the user to have to write the pattern instead of having it unfold?
-- looks like it but in the second example, we see how union works when it's a parameter.

/-! ## Test 2: does `simp` see `Sum.elim` through `.val`?

Every example here states: evaluating the union family at `Sum.inl i`, an
index from the left summand, gives `P`'s own value at `i`. In short, the
union restricted to its left half is `P`. The obvious proof rewrites
`.val` to `Sum.elim` and lets `Sum.elim_inl` compute. The test is whether
`simp` finds it. -/

/-! **FIELD** -/

/- No. `Sum.elim_inl` needs the head to say `Sum.elim`, and here it says
`(P.union Q).val`. The error's note reveals more: at simp's transparency
the goal is not even type-correct. Only the elaborator's deeper unfolding
let `Sum.inl i` be accepted at type `(P.union Q).ι` at all.
EXPECTED ERROR: `simp` made no progress -/
example {G : Type} (P Q : GensF G) (i : P.ι) :
    (P.union Q).val (Sum.inl i) = P.val i := by
  simp

/-! **FIELD** escape hatches (same caveats as in Test 1) -/

/- (a) The kernel unfolds without limit, so bare `rfl` proves it outright. -/
example {G : Type} (P Q : GensF G) (i : P.ι) :
    (P.union Q).val (Sum.inl i) = P.val i := rfl

/- (b) Naming the definition lets `simp` unfold it. -/
example {G : Type} (P Q : GensF G) (i : P.ι) :
    (P.union Q).val (Sum.inl i) = P.val i := by
  simp [GensF.union]

/-! **PARAM** -/

/- `union_val` rewrites the head to `Sum.elim`, then `Sum.elim_inl`
fires. -/
example {G ι κ : Type} (P : GensP G ι) (Q : GensP G κ) (i : ι) :
    (P.union Q).val (Sum.inl i) = P.val i := by
  simp

/-! ## Test 3: can `h : R = P.union Q` be used to rewrite?

`R` is a black box. The only thing we know about it is the hypothesis
`h`, which says `R` equals the union of `P` and `Q`.

Both examples prove the same deliberately boring statement: every index
of `R` is sent to some group element. That is true of any function
whatsoever. As in the earlier tests, the boring statement is the point.
The only thing under test is the proof step `rw [h]`, the
find-and-replace that swaps the black box `R` for the concrete
`P.union Q` in the goal.

This swap is the first move of essentially every proof that uses a
presentation API. The library states its lemmas about the constructions
(`union_val`, `Sum.elim_inl`, ...). Your goal is stated about `R`.
Rewriting along an equation like `h` is the only bridge from one to the
other. A design that breaks the swap breaks every proof downstream of
it. -/

/-! **FIELD** -/

/- No. This time nothing is definitional, so there is no escape hatch.
A goal that mentions `R.val x` also mentions `x : R.ι`, so abstracting
`R` is ill-typed: the index type infects every occurrence of the term.
(`subst h` happens to work, but only because `R` is a free variable.)
EXPECTED ERROR: motive is not type correct -/
example {G : Type} (P Q R : GensF G) (h : R = P.union Q) (x : R.ι) :
    ∃ g, R.val x = g := by
  rw [h]

/-! **PARAM** -/

/- `x : ι ⊕ κ` doesn't mention `R`, so `rw [h]` just works. -/
example {G ι κ : Type} (P : GensP G ι) (Q : GensP G κ) (R : GensP G (ι ⊕ κ))
    (h : R = P.union Q) (x : ι ⊕ κ) :
    ∃ g, R.val x = g := by
  rw [h]
  exact ⟨_, rfl⟩

/- TEMP EXERCISE (delete freely). `rw!` in cast mode `.all` is willing
to put a `▸` sticker on `x`. Predict: will it actually need one here?
Check the goal after the `rw!` line, then close the proof by replacing
the `sorry`. -/
example {G ι κ : Type} (P : GensP G ι) (Q : GensP G κ) (R : GensP G (ι ⊕ κ))
    (h : R = P.union Q) (x : ι ⊕ κ) :
    ∃ g, R.val x = g := by
  rw! (castMode := .all) [h]
  sorry

/-! ## Test 4: can two families' `val`s even be compared?

Before proving anything, one must state "`P` and `Q` pick out the same
elements of `G`". The first FIELD example tries the honest statement and
fails at elaboration, before any proving could start. The next two are
`Prop`-valued and prove nothing. They exhibit the only two ways the FIELD
style can phrase the sentence at all. The PARAM example states it
honestly and proves it. -/

/-! **FIELD** -/

/- The honest statement does not elaborate. `P.val : P.ι → G` and
`Q.val : Q.ι → G` have different types, and the elaborator will not
consult the propositional hypothesis `h` to reconcile them. Note the
second error too: the only `h` one could even offer `funext` is an
equality of types, not a pointwise one.
EXPECTED ERROR: Type mismatch: `Q.val` has type `Q.ι → G`, expected `P.ι → G` -/
example {G : Type} (P Q : GensF G) (h : P.ι = Q.ι) :
    P.val = Q.val :=
  funext h

/- Two phrasings do elaborate. Each bakes transport in forever: -/
example {G : Type} (P Q : GensF G) (h : P.ι = Q.ι) : Prop :=
  P.val = Q.val ∘ cast h                    /- (a) a `cast` in the equation… -/

example {G : Type} (P Q : GensF G) : Prop :=
  P.ι = Q.ι ∧ HEq P.val Q.val               /- (b) …or heterogeneous equality -/

/-! **PARAM** -/

/- Says: pointwise-equal families are equal. Same parameter, honest `=`,
proved by `funext`. -/
example {G ι : Type} (P Q : GensP G ι) (h : ∀ i, P.val i = Q.val i) :
    P.val = Q.val :=
  funext h

/-! **Lean's own verdict** -/

/- Compare the auto-generated injectivity lemmas: -/
#check @GensF.mk.injEq   /- forced into `HEq` (`≍`) -/
#check @GensP.mk.injEq   /- honest `=` -/

/-! ## Test 5: does instance search find `Finite`?

Both examples state: the union of two finitely-indexed families is
finitely indexed. Mathlib already knows
`Finite α → Finite β → Finite (α ⊕ β)`. The test is whether instance
search can see that the union's index is a sum. -/

/-! **FIELD** -/

/- No. Instance search is syntactic too. It will not unfold the
semireducible `union`, so it never finds the two instances in scope.
EXPECTED ERROR: failed to synthesize `Finite (P.union Q).ι` -/
example {G : Type} (P Q : GensF G) [Finite P.ι] [Finite Q.ι] :
    Finite (P.union Q).ι := inferInstance

/-! **PARAM** -/

/- The instance goal is literally `Finite (ι ⊕ κ)`. There is nothing to
see through, and mathlib's `Sum` instance fires. -/
example {ι κ : Type} [Finite ι] [Finite κ] : Finite (ι ⊕ κ) := inferInstance

/-! ## Also: the universe bump

Storing a `Type` inside the structure pushes the structure above it:
`GensF : Type → Type 1`. `@[nolint checkUnivs]` suppressed this warning
on the old bundled `Algebra.Presentation`. `Module.Relations` still
suppresses it today, and pays with its `IsPresentationCore`/`down`
universe-shrinking apparatus. -/

#check (GensF : Type → Type 1)         /- forced up (`Type → Type` is a type error) -/
#check (GensP : Type → Type → Type)    /- stays put -/

/-! ## The one thing FIELD does better: plain existentials

"`G` has a finite generating family" wants a single type to quantify over.
FIELD has one; PARAM does not. Mathlib therefore phrases it with `Fin n`
and `Nonempty` (see `Algebra.FiniteType.iff_exists_generators`,
`Group.fg_iff_nonempty_finite_generators`). The price is small, a single
`Finite.exists_equiv_fin` shuffle: -/

/-! **FIELD** -/

/-- FIELD phrasing of "`G` has a finite generating family": one existential
over the bundled structure. -/
def FGField (G : Type) : Prop := ∃ P : GensF G, Finite P.ι

/-! **PARAM** -/

/-- PARAM phrasing of the same. There is no single type to quantify over,
so we range over the canonical finite index types `Fin n`. -/
def FGParam (G : Type) : Prop := ∃ n : ℕ, Nonempty (GensP G (Fin n))

/-! **The bridge** -/

/- Says: the two phrasings agree. PARAM's awkwardness here costs exactly
one `Finite.exists_equiv_fin` shuffle, paid once. -/
example {G : Type} : FGField G ↔ FGParam G := by
  constructor
  · rintro ⟨P, hP⟩
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin P.ι
    exact ⟨n, ⟨⟨P.val ∘ e.symm⟩⟩⟩
  · rintro ⟨n, ⟨P⟩⟩
    /- `inferInstance` succeeds here: `⟨Fin n, P.val⟩.ι` projects a
    literal constructor, and instance search does reduce that. Contrast
    Test 5, where it gave up on the named construction `(P.union Q).ι`.
    Real code only ever sees the named ones. -/
    exact ⟨⟨Fin n, P.val⟩, inferInstance⟩

/- TEMP EXERCISE (delete freely). The "honest" PARAM phrasing writes the
type quantifier out instead of ranging over `Fin n`, and it does
elaborate for this file's universe-0 groups. Prove it agrees with
`FGParam`. The → direction is the bridge's `Finite.exists_equiv_fin`
shuffle again. The ← direction is one line: what is the witness for
`ι`? -/
example {G : Type} :
    (∃ ι : Type, Nonempty (GensP G ι) ∧ Finite ι) ↔ FGParam G := by
  constructor
  · rintro ⟨ι, ⟨P⟩, hP⟩
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
    exact ⟨n, ⟨⟨P.val ∘ e.symm⟩⟩⟩
  · rintro ⟨n, ⟨P⟩⟩
    /- The fold, one tactic at a time. Each line of the old script wrote
    one piece of a term. Watch the term grow as we replay them:

        refine ⟨Fin n, ?_, ?_⟩     term so far: ⟨Fin n, ?_,        ?_⟩
        constructor                term so far: ⟨Fin n, ⟨?_⟩,      ?_⟩
        · use P.val                term so far: ⟨Fin n, ⟨⟨P.val⟩⟩, ?_⟩
        · infer_instance           term so far: ⟨Fin n, ⟨⟨P.val⟩⟩, inferInstance⟩

    `constructor` added a bracket pair and left its one field blank;
    `use P.val` filled that blank with another bracketed node. Two tactic
    lines, two bracket layers. Once no blank is left, the term is
    finished, and a finished term is handed over with `exact`: -/
    exact ⟨Fin n, ⟨⟨P.val⟩⟩, inferInstance⟩

/-! ## The old API, reconstructed — the problems the refactor fixed

The pre-#25085 structure, rebuilt at demo scale. We keep only the two
data fields plus the old `comp`, since `σ'` and the algebra bookkeeping
play no part in the syntax problems. Tests 1, 2, and 5 are then reprised
on it, EXPECTED ERRORs and all: the toy `GensF` failures, wearing their
historical names.

Two details are faithful to history. First, the old API knew about the
repair lemma. `comp` was tagged `@[simps val, simps -isSimp vars σ]`
(line 196 of the pinned file above), so simps generated
`comp_vars : (Q.comp P).vars = Q.vars ⊕ P.vars` but deliberately kept it
out of the default simp set. That is exactly the situation of our
untagged `GensF.union_ι` and `union_val`. Second, downstream files paid
at every use site. Below are deleted lines from the PR diff, the first
four from `Mathlib/RingTheory/Kaehler/JacobiZariski.lean`, the last from
`Mathlib/RingTheory/Smooth/StandardSmooth.lean` (`git show 966daba4dd6 -- <file>`):

```
-  ext; simpa only [comp_vars, val_mk, Ideal.toCotangent_eq, sub_sub_cancel, pow_two, z]
-  simp only [comp_vars, Basis.prod_repr_inr, Basis.baseChange_repr_tmul, …
-  · simp only [comp_vars, Sum.elim_inl, δAux_X, smul_zero, aeval_X, …
-  · simp only [comp_vars, Sum.elim_inr, Function.comp_apply, algHom_C, δAux_C, …
-  simp only [algHom_C, algebraMap_eq, eval₂_C, ← Generators.comp_vars, …
```

`comp_vars` had to be supplied by hand, `simp only` after `simp only`.
It fires where `vars` sits in a non-dependent position (a `Basis`, a
matrix, a `Finsupp`), and once it even runs backwards (`← comp_vars`) to
re-hide the sum. These are this file's escape hatches as daily
practice. -/

namespace OldAPI

/-- The pre-#25085 `Algebra.Generators`, data fields only.  Source:
`git show 966daba4dd6^:Mathlib/RingTheory/Extension/Generators.lean`,
line 57; `σ'`, `aeval_val_σ'`, and the algebra fields elided. -/
structure Generators (R S : Type) [CommRing R] [CommRing S] [Algebra R S] where
  /-- The type of variables — the index type, stored as a FIELD. -/
  vars : Type
  /-- The assignment of each variable to a value in `S`. -/
  val : vars → S

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T]

/-- The old composition, with the `⊕` in the body: `GensF.union` at real
scale. Source: same pinned file, line 198; `noncomputable`, `σ'`, and its
section proof elided. -/
def Generators.comp (Q : Generators S T) (P : Generators R S) : Generators R T where
  vars := Q.vars ⊕ P.vars
  val := Sum.elim Q.val (algebraMap S T ∘ P.val)

/-- The repair lemma. The old API generated it but kept it out of the
default simp set (`-isSimp`). Source: the attribute
`@[simps val, simps -isSimp vars σ]` on `comp`, same pinned file,
line 196. -/
lemma Generators.comp_vars (Q : Generators S T) (P : Generators R S) :
    (Q.comp P).vars = (Q.vars ⊕ P.vars) := rfl

variable (Q : Generators S T) (P : Generators R S)

/- Test 1, historical edition: the TODO's "constructions, e.g. composition".
EXPECTED ERROR: Did not find an occurrence of the pattern -/
example : ∀ x : (Q.comp P).vars, ∃ t, (Q.comp P).val x = t := by
  rw [Sum.forall]

/- Test 2, historical edition.
EXPECTED ERROR: `simp` made no progress -/
example (j : Q.vars) : (Q.comp P).val (Sum.inl j) = Q.val j := by
  simp

/- In dependent positions like these, `comp_vars` has nothing syntactic
to grab (compare Test 1's motive failure). The way through is unfolding
`comp` itself: the escape hatch, at real scale. -/
example (j : Q.vars) : (Q.comp P).val (Sum.inl j) = Q.val j := by
  simp [Generators.comp]

/- Test 5, historical edition.
EXPECTED ERROR: failed to synthesize `Finite (Q.comp P).vars` -/
example [Finite Q.vars] [Finite P.vars] : Finite (Q.comp P).vars := inferInstance

/- Test 4's verdict, on the real field names: `val`s compare only by `≍`. -/
#check @OldAPI.Generators.mk.injEq

/- And the universe bump: `vars : Type` inside forces `… → Type 1`
(the original: `Generators.{w} R S : Type (max u v (w + 1))`). -/
#check @OldAPI.Generators

end OldAPI

/-! ## The new API, live -/

section RealAPI

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] {ι ι' : Type}

/- The `⊕` sits in the real signature: -/
#check @Algebra.Generators.comp

/- Test 2, re-run against the live post-#25085 API. `comp_val`, which
`@[simps val]` auto-generates, exposes `Sum.elim`; then `Sum.elim_inl`
fires. -/
example (Q : Algebra.Generators S T ι') (P : Algebra.Generators R S ι) (j : ι') :
    (Q.comp P).val (Sum.inl j) = Q.val j := by
  simp

/- Test 4, against this branch's `Group.Presentation` API: same parameter,
honest `=` between generating families. -/
example {G : Type} [Group G] {α : Type} (P Q : Group.Generators G α)
    (h : ∀ a, P.val a = Q.val a) : P.val = Q.val :=
  funext h

/- The `Fin n + Nonempty` bridge, live (the `FGParam` pattern): -/
#check @Group.fg_iff_nonempty_finite_generators

end RealAPI

/-! ## References

The citation base for this sheet's argument; it distills directly into a
PR description.

All paths are files in the mathlib tree of this project; `path:line` points at
the definition. Before-states of refactors are viewable with
`git show <commit>^:<path>`. Quotes are verbatim.

### The refactor trail (FIELD → PARAM, three times; never the reverse)

* `IsFreeGroup` → `FreeGroupBasis` — [PR #7698](https://github.com/leanprover-community/mathlib4/pull/7698),
  commit `bab05758f84`, 2023-10-28 (S. Gouëzel).
  Now `Mathlib/GroupTheory/FreeGroup/IsFreeGroup.lean:55` (basis) and `:64` (Prop class).
  Before: `class IsFreeGroup` with fields `Generators : Type u`,
  `MulEquiv' : FreeGroup Generators ≃* G`.
  Commit message: "Currently, the class `IsFreeGroup` contains data (namely, a specific set of
  generators). This is bad, as there are many sets of generators in a free group, and changing
  sets of generators happens all the time in geometric group theory." … "we define
  `FreeGroupBasis`, following the definition and API of bases of vector spaces."
* `Algebra.Generators` / `Algebra.Presentation` — [PR #25085](https://github.com/leanprover-community/mathlib4/pull/25085),
  commit `966daba4dd6`, 2025-06-02 (A. Yang). `vars`/`rels` fields became parameters `ι`/`σ`;
  the `IsFinite` class was deleted in favor of `[Finite ι] [Finite σ]`.
  Residual TODO: `Mathlib/RingTheory/Extension/Generators.lean:41`.
* `Computability.Encoding` — [PR #37928](https://github.com/leanprover-community/mathlib4/pull/37928),
  commit `ca158545413`, 2026-06-30. `Mathlib/Computability/Encoding.lean:40`.
  Commit message: "The alphabet `Γ` is now an explicit parameter" … "`FinEncoding`: Removed.
  Finiteness is now handled via standard typeclasses."

### PARAM-style structures (the Basis family and friends)

* `Module.Basis` — `Mathlib/LinearAlgebra/Basis/Defs.lean:90`. The archetype: one field
  `repr : M ≃ₗ[R] ι →₀ R`. Bundled from the `is_basis` predicate in mathlib3 PR #7496
  ("refactor(*): bundle `is_basis`", A. Baanen, merged 2021-05-10, commit `ef90a7ab6c0`); the idea
  originated in the RFC discussion on mathlib3 PR #4949 (Y. Kudryashov, Nov 2020, closed
  unmerged) and the "Bundled basis" Zulip thread (Apr 2021), where bundling the *index* was
  raised and rejected (E. Wieser: "to talk about bases over the same index you have to start
  inserting proofs that the indexes are the same"; M. Carneiro: "it's generally not a good idea
  to bundle types for the reason Eric Wieser mentioned").
  Implementation notes on family-vs-set: same file, ~lines 50–53.
* `OrthonormalBasis` — `Mathlib/Analysis/InnerProductSpace/PiL2.lean:392` (repr clone).
* `HilbertBasis` — `Mathlib/Analysis/InnerProductSpace/l2Space.lean:371` (repr clone).
* `AffineBasis` — `Mathlib/LinearAlgebra/AffineSpace/Basis.lean:86`. No repr target exists, so it
  bundles the raw family + two defining Props over a parameter index — the `Group.Generators` shape.
* `GeneralSchauderBasis` — `Mathlib/Analysis/Normed/Module/Bases.lean:98` (family + coords + Props).
* `LieAlgebra.Basis` — `Mathlib/Algebra/Lie/Basis.lean:54` (families + Cartan matrix over param ι).
* `Module.Basis.SmithNormalForm` — `Mathlib/LinearAlgebra/FreeModule/PID.lean:409`. Makes even the
  nat `n` a parameter (`Fin n` index) — contrast `PowerBasis` below.
* `CoxeterSystem` — `Mathlib/GroupTheory/Coxeter/Basic.lean:157`; `IsCoxeterGroup` at `:162`.
  Introduced PR #8223 (2024-02-07, `e4d4665e31b`); refactor PR #11836 (2024-04-22, `24e020ad0be`)
  removed its FunLike: "it is unintuitive to think of a Coxeter system as a function."
* `RootPairing` — `Mathlib/LinearAlgebra/RootSystem/Defs.lean:82`; `IsRootSystem` mixin at `:118`
  (mixin since PR #32885). Docstring (lines 44–52) argues for the index parameter: avoids the
  root↔coroot bijection "being a dependently-typed object"; "providing the user with the
  additional definitional power to specify an indexing type `ι` is a benefit and the junk-value
  pattern is a cost."
* `FreeAbelianGroup.basis` — `Mathlib/GroupTheory/FreeGroup/GeneratorEquiv.lean:26` (no bespoke
  structure; reuses `Basis α ℤ`).

### Existential Prop layer over a PARAM structure

* `Module.Free` — `Mathlib/LinearAlgebra/FreeModule/Basic.lean:43`. `Nonempty ((I : Type v) ×
  Basis I R M)`, universe-pinned; `free_iff_set` at `:49`, `ChooseBasisIndex` at `:79`.
* `IsFreeGroup` — `Mathlib/GroupTheory/FreeGroup/IsFreeGroup.lean:64` (`∃ ι : Type u`, pinned).
* `IsCoxeterGroup` — `Mathlib/GroupTheory/Coxeter/Basic.lean:162` (`∃ B : Type u`, pinned).
* `Algebra.FinitePresentation` — `Mathlib/RingTheory/FinitePresentation.lean:44`. Normalizes the
  index to `Fin n` instead of pinning a universe — the shape used by
  `Group.isFinitelyPresented_iff_exists_finite_presentation`.
* `IsCyclic` — `Mathlib/Algebra/Group/Defs.lean:1055` (the one-generator degenerate case).

### FIELD-style holdouts, each paying a visible cost

* `Module.Relations` — `Mathlib/Algebra/Module/Presentation/Basic.lean:55` (PR #18295, J. Riou).
  Needs `set_option linter.checkUnivs false` (`:51`) and the `IsPresentationCore` universe
  apparatus (`:423`).
* `SheafOfModules.GeneratingSections` — `Mathlib/Algebra/Category/ModuleCat/Sheaf/Generators.lean:44`
  (PR #13720). Bundles `I : Type u`; finiteness is a class on the structure (`:95`); needs a
  `shrink` def (`:124`). Likewise `QuasicoherentData`,
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:202`.
* `PowerBasis` — `Mathlib/RingTheory/PowerBasis.lean:60`. Bundles `dim : ℕ` (index `Fin dim`);
  all comparison routed through equivs; "`PowerBasis` cannot be a class" (`:76`).
* `IsFreeGroupoid` — `Mathlib/GroupTheory/FreeGroup/NielsenSchreier.lean:77`. Data-carrying class,
  bundled generator quiver; own docstring: "This definition is nonstandard." (`:75`).
* `ContextFreeGrammar` — `Mathlib/Computability/ContextFreeGrammar.lean` (bundled `NT : Type`).
* `Algebra.Smooth.DescentAux` — `Mathlib/RingTheory/Smooth/NoetherianDescent.lean:34`. The
  legitimate use of FIELD: locally re-bundles the parameterized `Presentation` when a proof needs
  "some presentation" as a single existential package.

### Never-bundled predicates (pre-#4949 style, still the norm in their niches)

* `AlgebraicIndependent` / `IsTranscendenceBasis` —
  `Mathlib/RingTheory/AlgebraicIndependent/Defs.lean:54` / `:173`.
* `Orthonormal` — `Mathlib/Analysis/InnerProductSpace/Orthonormal.lean:49`.
* `Module.DualBases` — `Mathlib/LinearAlgebra/Dual/Basis.lean:223`.

### Set/Finset-closure Props (the FG layer; no index type at all)

* `Submodule.FG` / `Module.Finite` — `Mathlib/RingTheory/Finiteness/Defs.lean:42` / `:117`.
* `Subalgebra.FG` — `Mathlib/RingTheory/Adjoin/FG.lean:95`; `Algebra.FiniteType` —
  `Mathlib/RingTheory/FiniteType.lean:39`.
* `Submonoid.FG` / `Monoid.FG` / `Subgroup.FG` / `Group.FG` —
  `Mathlib/GroupTheory/Finiteness.lean:49` / `:160` / `:303` / `:395`.
-/
