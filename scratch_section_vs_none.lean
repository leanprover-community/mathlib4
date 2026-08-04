import Mathlib.Algebra.Group.PUnit
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.Generators
import Mathlib.RingTheory.Extension.Generators

/-!
# Scratch: a bundled SECTION vs NONE

Should a generators structure carry a *chosen set-theoretic section* of the
evaluation map `FreeGroup α →* G` (a SECTION field — `GensS` below), or only
the proposition that the map is surjective (NONE — `GensN`, the shape of this
branch's `Group.Generators`)?  Context: `Algebra.Generators` bundles such a
section (`σ' : S → MvPolynomial ι R`), and the choice was debated — and
settled — in review of PR #12518 (see the `Context` section just below).

The two styles are *propositionally* the same: a section exists iff the map is
surjective.  Everything below is about what each style costs and buys at the
**data** level.

* Tests 1–3 (NONE wins): making terms from surjectivity is computable in NONE
  but needs choice in SECTION; terms with the same generating family are equal
  in NONE but not in SECTION; every construction in SECTION must hand-build a
  composite section.
* Test 4 (a draw): the `Prop`-layer (`Group.FG`-style existentials) cannot
  tell the styles apart — `Nonempty` erases the extra data.
* Test 5 (SECTION wins): a bundled section is *data with definitional
  control* — canonical terms get canonical sections and `rfl`-computation
  rules.
* Test 6 (SECTION wins, and this is the real reason): in commutative algebra
  a section is a *normal form*, not a choice.  Every element of a localization
  is `a / rⁿ`, and `Algebra.Generators.localizationAway` writes exactly that
  down as its σ.  Groups have no such formula in general.  That one sentence
  is the whole verdict of the sheet.  The Context section adds the other half:
  two mathlib lemmas prove that the invariants cannot see σ at all.

The examples marked EXPECTED ERROR — three in total — are *supposed* to fail;
that is the demo.  The `Context` section quotes the real
`Algebra.Generators` (the section's true consumers, and the PR #12518 review
exchange where NONE was proposed and declined) and the real `Group.Generators`
(whose consumers are all `Prop`-shaped, so it takes NONE).

Scratch material, not part of the library.  Delete freely.
-/

/-! ## Context: the real thing — `Algebra.Generators` keeps σ, `Group.Generators` takes NONE

`Algebra.Generators` has bundled its section since day one (PR #12518, commit
`913dc471aee`, 2024-06-10, original path `Mathlib/RingTheory/Generators.lean`;
`git show 913dc471aee:Mathlib/RingTheory/Generators.lean`):

```
structure Algebra.Generators where
  /-- The type of variables.  -/
  vars : Type w
  /-- The assignment of each variable to a value in `S`. -/
  val : vars → S
  /-- A section of `R[X] → S`. -/
  σ' : S → MvPolynomial vars R
  aeval_val_σ' : ∀ s, aeval val (σ' s) = s
```

The NONE design was proposed in that PR's review and declined (quotes
verbatim, from the #12518 discussion):

* Joël Riou: "Could not this be replaced by the assumption that the map
  `R[I] → S` is surjective? Then, `σ` could be chosen afterwards."
  (https://github.com/leanprover-community/mathlib4/pull/12518#discussion_r1583705606)
* Andrew Yang: "I thought about it as well, but I'd prefer good definitional
  equalities when considering the canonical presentation `R[S] → S`."
  (https://github.com/leanprover-community/mathlib4/pull/12518#discussion_r1583710932)
* Christian Merten: "I like the idea of `Algebra.Presentation` computably
  carrying all the data to describe `S` as an `R`-algebra."
  (https://github.com/leanprover-community/mathlib4/pull/12518#discussion_r1585191380)

And the section is no dead weight there — its consumers are definitions, not
propositions (all live in this tree):

* the `S`-module structure on the conormal space `I/I²`:
  `Extension.Cotangent.module`, `Mathlib/RingTheory/Extension/Basic.lean:369`
  (`smul := fun r s ↦ .of (P.σ r • s.val)`), with payoff
  `Cotangent.val_smul … := rfl` (`:403`);
* the canonical hom between any two generator families:
  `Generators.defaultHom` (`Mathlib/RingTheory/Extension/Generators.lean:468`:
  `⟨P'.σ ∘ algebraMap S S' ∘ P.val, …⟩`), which yields
  `Inhabited (Hom P P')` and powers `Generators.H1Cotangent.equiv` —
  "`H¹(L_{S/R})` is independent of the presentation chosen"
  (`Mathlib/RingTheory/Extension/Cotangent/Basic.lean:549`);
* proofs that *reason about the section's values*:
  `Presentation.relation_comp_localizationAway_inl` hypothesizes
  `(h1 : P.σ (-1) = -1) (h0 : P.σ 0 = 0)`
  (`Mathlib/RingTheory/Extension/Presentation/Basic.lean:462`) — meaningless
  for an opaque `choose`;
* and `Generators.naive` documents the policy in one line: "If the
  definitional equality of the section matters, it can be explicitly
  provided." (`Mathlib/RingTheory/Extension/Generators.lean:358`).

But mathlib also says out loud what σ *cannot* affect.  Two lemmas fence it in.

* The action on `I/I²` does not depend on which lift is used.
  `Extension.Cotangent.val_smul'`
  (`Mathlib/RingTheory/Extension/Basic.lean:407`):

      lemma Cotangent.val_smul' (r : P.Ring) (x : P.Cotangent) :
          (r • x).val = r • x.val

  The two `•` are different actions.  On the right, `r` acts as an honest
  element of `P`.  On the left, `r` is sent down to `S` and lifted back by σ.
  So σ's lift and `r` itself give the same answer.  Feed the lemma two lifts of
  the same element of `S` and they agree with each other.  Its one-line proof
  is the classical argument: the difference of two lifts lies in `I`, and `I`
  kills `I/I²`.
* The map induced on `H¹` does not depend on which hom was built.
  `Extension.H1Cotangent.map_eq`
  (`Mathlib/RingTheory/Extension/Cotangent/Basic.lean:391`):

      lemma H1Cotangent.map_eq (f g : Hom P P') : map f = map g

  σ's only job in `defaultHom` was to produce one hom, so `H¹` cannot see it.
  Note where the quantifier sits: one level down this is false.  The induced
  map `Cotangent.map f` on `I/I²` itself does depend on `f`.

So the section earns nothing on the invariants.  What it earns is the ability
to write a NEW PRESENTATION down, and there it is not an arbitrary choice at
all.  It is a normal form.  Test 6 makes that concrete.

Two boundary stones.  When PR #25085 unbundled `vars`/`rels` into parameters,
nobody proposed touching σ′ — and the follow-up experiment that tried to
unbundle `Extension` further was abandoned (Christian Merten, #25085:
"the experiment for doing the same with `Extension` horribly failed (#25191)",
https://github.com/leanprover-community/mathlib4/pull/25085#issuecomment-2929585639).
The bundled section is the *stable* part of the design.

This branch's `Group.Generators` (`Mathlib/GroupTheory/Generators.lean:44`)
takes NONE, and the same consumer test says it should: everything downstream —
`Group.Generators.fg`, `Group.fg_iff_nonempty_finite_generators`,
`Group.Presentation.presentedGroupEquiv`, and the geometric-group-theory
material a marked-groups library grows into (word metrics as infima over all
representative words, Cayley graphs, marked-group topology) — consumes
`lift_surjective`, a `Prop`.  No planned definition takes a dictionary
`G → FreeGroup α` as input.  Until one does (a normal-form or automatic-
structure API would — and would deserve its own structure extending this one,
with the *language*, not just a section, as its data), the section field would
be all cost (Tests 1–3 below) and no payoff (Test 5's consumer never arrives): -/

#check @Group.Generators.ofLiftSurjective  /- a plain computable `def` (Test 1) -/
#check @Algebra.Generators.ofSurjective    /- `noncomputable` (its Test 1 price) -/

/-! ## The two styles -/

/-- NONE: a generating family plus the `Prop` that it generates — the shape of
this branch's `Group.Generators G α`. -/
structure GensN (G : Type) [Group G] (α : Type) where
  val : α → G
  closure_eq_top : Subgroup.closure (Set.range val) = ⊤

/-- SECTION: a generating family plus a chosen set-theoretic section of
`FreeGroup.lift val` — the shape of `Algebra.Generators R S ι`, transported to
groups.  `sec g` is a *chosen word* evaluating to `g`; `lift_val_sec` says the
choice is a section.  No surjectivity field is needed: it follows (below). -/
structure GensS (G : Type) [Group G] (α : Type) where
  val : α → G
  sec : G → FreeGroup α
  lift_val_sec : ∀ g, FreeGroup.lift val (sec g) = g

variable {G : Type} [Group G] {α β : Type}

/-! **SECTION is strictly more information.**  Both `Prop`s of NONE are
one-liners from the section — mirroring `Algebra.Generators`, which derives
`aeval_val_surjective` from `σ`
(`Mathlib/RingTheory/Extension/Generators.lean:116`): -/

theorem GensS.lift_surjective (P : GensS G α) :
    Function.Surjective (FreeGroup.lift P.val) :=
  fun g ↦ ⟨P.sec g, P.lift_val_sec g⟩

theorem GensS.closure_eq_top (P : GensS G α) :
    Subgroup.closure (Set.range P.val) = ⊤ := by
  rw [← FreeGroup.range_lift_eq_closure, MonoidHom.range_eq_top]
  exact P.lift_surjective

/-- The forgetful conversion SECTION → NONE: total, computable, one line. -/
def GensS.toGensN (P : GensS G α) : GensN G α :=
  ⟨P.val, P.closure_eq_top⟩

/-! ## Test 1: can a term be built from surjectivity alone, computably?

The standard entry point: "here is a family, and `FreeGroup.lift` of it is
surjective."  NONE just repackages the `Prop`.  SECTION must *manufacture a
choice* — one word per group element — and no algorithm is on offer, so the
elaborator demands `Classical.choice`. -/

/-! **NONE** -/

/- A plain `def`, no `noncomputable` — this is the live
`Group.Generators.ofLiftSurjective` (`Mathlib/GroupTheory/Generators.lean:63`). -/
def GensN.ofLiftSurjective (val : α → G)
    (h : Function.Surjective (FreeGroup.lift val)) : GensN G α :=
  ⟨val, by rw [← FreeGroup.range_lift_eq_closure, MonoidHom.range_eq_top.mpr h]⟩

/-! **SECTION** -/

/- The same constructor, refused.
EXPECTED ERROR: failed to compile definition, consider marking it as
'noncomputable' because it depends on 'Exists.choose', which is 'noncomputable' -/
def GensS.ofLiftSurjective (val : α → G)
    (h : Function.Surjective (FreeGroup.lift val)) : GensS G α where
  val := val
  sec g := (h g).choose
  lift_val_sec g := (h g).choose_spec

/-! **SECTION** escape hatch -/

/- Concede `noncomputable` and the definition goes through — this is verbatim
the strategy of `Algebra.Generators.ofSurjective`
(`Mathlib/RingTheory/Extension/Generators.lean:127`: `σ' x := (h x).choose`).
The price is not the keyword: it is that `sec` is now an *opaque* choice —
Test 5 shows nothing computes through it. -/
noncomputable def GensS.ofLiftSurjective' (val : α → G)
    (h : Function.Surjective (FreeGroup.lift val)) : GensS G α where
  val := val
  sec g := (h g).choose
  lift_val_sec g := (h g).choose_spec

/-! ## Test 2: do equal generating families give equal terms?

"Same `val`, same object" holds in NONE by proof irrelevance.  In SECTION it
is *false*: a term is a family *plus a dictionary of chosen words*, and the
dictionary is not determined by the family.  The demo group is the trivial
group `PUnit` — degenerate on purpose: `FreeGroup.lift` there is constant, so
*every* function `PUnit → FreeGroup Unit` is a section, and the multiplicity
of sections is maximal even though the group could not be simpler. -/

/-! **NONE** -/

/- Two NONE-terms with the same family are equal — `cases` + proof
irrelevance; no extra hypotheses needed. -/
example (P Q : GensN G α) (h : P.val = Q.val) : P = Q := by
  cases P; cases Q; simpa using h

/-! **SECTION** -/

/- The same proof, refused: after `simp` erases the proof fields, the goal
still demands the dictionaries agree.
EXPECTED ERROR: Type mismatch: After simplification, term
  h
 has type
  val✝¹ = val✝
but is expected to have type
  val✝¹ = val✝ ∧ sec✝¹ = sec✝ -/
example (P Q : GensS G α) (h : P.val = Q.val) : P = Q := by
  cases P; cases Q; simpa using h

/- ===== EXERCISE (temporary; delete freely) =====
The failed example above offered only the families (`h : P.val = Q.val`),
and the goal that survived `simp` demanded a second conjunct, `sec = sec`.
So supply that missing half as a hypothesis, and the equality becomes
provable.  Fill the `sorry`, reusing the failed example's tactic line with
`h` upgraded to the pair `⟨h1, h2⟩`.  Before running it: which `#check`
just below promises the pair has exactly two components? -/
example (P Q : GensS G α) (h1 : P.val = Q.val) (h2 : P.sec = Q.sec) :
    P = Q := by
  cases P; cases Q
  simpa using ⟨h1, h2⟩

/- And the missing conjunct is genuinely false: two SECTION-terms for the
trivial group, same `val`, different dictionaries.  `secOne` chooses the empty
word for the identity; `secOf` chooses the word `of ()`. -/

/-- Chooses the empty word `1` for every element. -/
def secOne : GensS PUnit Unit where
  val _ := 1
  sec _ := 1
  lift_val_sec _ := Subsingleton.elim _ _

/-- Chooses the length-one word `of ()` for every element. -/
def secOf : GensS PUnit Unit where
  val _ := 1
  sec _ := FreeGroup.of ()
  lift_val_sec _ := Subsingleton.elim _ _

/- Same generating family, provably different terms: their dictionaries
disagree on the reduced word (`toWord`) they assign. -/
example : secOne ≠ secOf := by
  intro h
  have h2 : secOne.sec 1 = secOf.sec 1 := by rw [h]
  simpa [secOne, secOf, FreeGroup.toWord_one, FreeGroup.toWord_of] using
    congrArg FreeGroup.toWord h2


/-! **Lean's own verdict** -/

/- Compare the auto-generated injectivity lemmas: NONE-terms are their
families (the `Prop` field is erased); SECTION-terms are families *and*
dictionaries. -/
#check @GensN.mk.injEq   /- … = (val = val_1) -/
#check @GensS.mk.injEq   /- … = (val = val_1 ∧ sec = sec_1) -/

/- Why it matters: mathlib carries the same cost, and never pays it.

No one in mathlib ever proves two `Algebra.Generators` terms equal.  The
structure has no `@[ext]`, and `grep -rn "Generators.ext" Mathlib/` returns
nothing.  When a result must not depend on which generators were picked,
mathlib builds a map between the two choices instead of an equality.  That map
is `Hom`, and it constrains only the generating family
(`Mathlib/RingTheory/Extension/Generators.lean:408-412`, `val`'s docstring
elided):

    @[ext]
    structure Hom where
      val : ι → P'.Ring
      aeval_val : ∀ i, aeval P'.val (val i) = algebraMap S S' (P.val i)

σ is absent.  Two generating families can be `Hom`-related while their
dictionaries disagree everywhere.  So the bundled σ costs nothing here: the
bill exists, but nothing in mathlib ever sends it.

A structure whose terms ARE compared gets no such shelter.  Every "these are
the same marked group" proof owes a second conjunct.  The example on line 215
is where that conjunct shows up: same family, and `simp` still demands
`sec = sec`.  `secOne ≠ secOf` above shows the demand is not empty. -/

/-! ## Test 3: constructions must thread the section

The union construction of `scratch_field_vs_parameter.lean`, in both styles.
NONE: new family, one closure proof.  SECTION: additionally, a *composite
dictionary* must be designed and verified — here the cheap embedding of `P`'s
dictionary; in the real `Algebra.Generators.comp` the composite σ is a genuine
construction
(`Mathlib/RingTheory/Extension/Generators.lean:234`:
`σ' x := (AddMonoidAlgebra.coeff <| Q.σ x).sum fun n r ↦ rename .inr (P.σ r) *
monomial (n.mapDomain .inl) 1` — plus a six-line proof that it is a section).
Every further construction pays again: `extendScalars`, `reindex`,
`ofAlgEquiv`, `localizationAway` each hand-build their σ. -/

/-! **NONE** -/

def GensN.union (P : GensN G α) (Q : GensN G β) : GensN G (α ⊕ β) where
  val := Sum.elim P.val Q.val
  closure_eq_top := top_le_iff.mp <| by
    rw [Set.Sum.elim_range]
    exact P.closure_eq_top.ge.trans (Subgroup.closure_mono Set.subset_union_left)

/-! **SECTION** -/

def GensS.union (P : GensS G α) (Q : GensS G β) : GensS G (α ⊕ β) where
  val := Sum.elim P.val Q.val
  sec := FreeGroup.map Sum.inl ∘ P.sec
  lift_val_sec g := by
    have key : (FreeGroup.lift (Sum.elim P.val Q.val)).comp (FreeGroup.map Sum.inl) =
        FreeGroup.lift P.val := by
      ext a
      simp
    simpa using (congrArg (fun f ↦ f (P.sec g)) key).trans (P.lift_val_sec g)

/-! ## Test 4: can the `Prop` layer tell the styles apart?

No — and this is the honest draw.  "`G` is finitely generated" phrased over
either structure gives the same proposition: inside an existential, `Nonempty`
erases the dictionary, and `Classical.choice` is free in proofs of `Prop`s.
Bundling a section buys nothing at this layer; omitting one loses nothing. -/

/-- FG phrased over NONE — the live
`Group.fg_iff_nonempty_finite_generators` shape. -/
def FGN (G : Type) [Group G] : Prop := ∃ n : ℕ, Nonempty (GensN G (Fin n))

/-- FG phrased over SECTION. -/
def FGS (G : Type) [Group G] : Prop := ∃ n : ℕ, Nonempty (GensS G (Fin n))

/- The bridge.  ← is the forgetful map; → uses choice — legitimately, since
the goal is a `Prop`.  Note the asymmetry of the two directions: it is the
Test 1 asymmetry, now invisible because `Nonempty` hides the data. -/
example : FGN G ↔ FGS G := by
  constructor
  · rintro ⟨n, ⟨P⟩⟩
    have hsurj : Function.Surjective (FreeGroup.lift P.val) :=
      MonoidHom.range_eq_top.mp
        (by rw [FreeGroup.range_lift_eq_closure, P.closure_eq_top])
    exact ⟨n, ⟨P.val, Function.surjInv hsurj, fun g ↦ Function.surjInv_eq hsurj g⟩⟩
  · rintro ⟨n, ⟨P⟩⟩
    exact ⟨n, ⟨P.toGensN⟩⟩

/-! ## Test 5: the one thing SECTION does better — definitional control

This is the reason `Algebra.Generators` bundles σ.  In review of PR #12518
Joël Riou proposed exactly the NONE design — "Could not this be replaced by
the assumption that the map `R[I] → S` is surjective? Then, `σ` could be
chosen afterwards." — and Andrew Yang declined for one reason: "I'd prefer
good definitional equalities when considering the canonical presentation
`R[S] → S`."  (Both quotes verbatim; URLs in `Context`.)

The point: *canonical terms have canonical sections*, and only a data field
can remember them.  For the group `G` generated by itself, the canonical
dictionary sends `g` to the one-letter word `of g` — and a downstream
definition that consumes the dictionary then *computes*. -/

/-! **SECTION** -/

/-- `G` generating itself, with the canonical dictionary `of` — the analogue
of `Algebra.Generators.self` (`σ' := X`) and `mvPolynomial` (`σ' f := f`). -/
def GensS.self (G : Type) [Group G] : GensS G G where
  val := id
  sec := FreeGroup.of
  lift_val_sec g := by simp

/- The dictionary is definitionally the canonical one: -/
example (g : G) : (GensS.self G).sec g = FreeGroup.of g := rfl

/-- The length of the word that `P.sec` chose for `g`.

This is a `def`, not a theorem.  The output is a number, and producing it
reads the dictionary.  That is the whole point: it is a consumer that takes
the section as input.  NONE can write the same definition, but only after
inventing a dictionary by choice (`GensN.sec`, just below), and then no
value of it is provable. -/
def GensS.wordLength [DecidableEq α] (P : GensS G α) (g : G) : ℕ :=
  (P.sec g).toWord.length

/- What this stands in for.  The real σ-consumer in mathlib is the
`S`-module structure on `Extension.Cotangent`.  Its scalar multiplication
also reads σ (`Mathlib/RingTheory/Extension/Basic.lean:369`:
`smul := fun r s ↦ .of (P.σ r • s.val)`).  Reading σ is what earns the
computation rule `Cotangent.val_smul … := rfl`
(`Mathlib/RingTheory/Extension/Basic.lean:403`, tagged `@[simp]`).

The same thing happens here on the canonical term.  `simp` computes the
number, and no choice appears anywhere: -/
example [DecidableEq G] (g : G) : (GensS.self G).wordLength g = 1 := by
  simp [GensS.wordLength, GensS.self, FreeGroup.toWord_of]

/- What `wordLength` is NOT: the word metric.  The word metric of a marked
group is the length of the SHORTEST word for `g`, minimised over every word
for `g`.  That number does not move when the dictionary moves, so it needs
only surjectivity, and NONE defines it fine.  `wordLength` does move.  The two
lines below measure the same element of the same group twice, through the two
dictionaries of Test 2, and get 0 and 1: -/

example : secOne.wordLength PUnit.unit = 0 := by
  simp [GensS.wordLength, secOne, FreeGroup.toWord_one]

example : secOf.wordLength PUnit.unit = 1 := by
  simp [GensS.wordLength, secOf, FreeGroup.toWord_of]

/- The mirror image.  Anything that pushes the chosen word back down to `G`
cannot see which word was chosen, because pushing it down is the one thing a
section promises.  Two sections, two different words, same value: -/

theorem GensS.lift_sec_eq (P Q : GensS G α) (g : G) :
    FreeGroup.lift P.val (P.sec g) = FreeGroup.lift Q.val (Q.sec g) := by
  rw [P.lift_val_sec, Q.lift_val_sec]

/- That two-rewrite proof is the group form of `Extension.Cotangent.val_smul'`
(`Mathlib/RingTheory/Extension/Basic.lean:407`), the lemma that makes the
`S`-action on `I/I²` section-blind.  Same shape, same length.

That is the asymmetry the whole sheet turns on.  Group theory wants the
metric, which ignores the dictionary.  `Algebra.Generators` wants
`Cotangent`'s `smul`, which reads it. -/

/-! **NONE** escape hatch, priced -/

/- NONE can build a dictionary after the fact, so nothing is out of reach at
the `Prop` level.  `Function.surjInv` builds it with one `Classical.choice`
(`Mathlib/Logic/Function/Basic.lean:571`:
`surjInv h b := Classical.choose (h b)`).  That is why this `def` is
`noncomputable`. -/
noncomputable def GensN.sec (P : GensN G α) : G → FreeGroup α :=
  Function.surjInv (f := FreeGroup.lift P.val)
    (MonoidHom.range_eq_top.mp
      (by rw [FreeGroup.range_lift_eq_closure, P.closure_eq_top]))

/- Reading that definition inside out.  `surjInv` asks for
`Surjective (FreeGroup.lift P.val)`.  NONE stores a fact about subgroups
instead.  Two named lemmas walk one into the other.

1. `MonoidHom.range_eq_top` (`Mathlib/Algebra/Group/Subgroup/Ker.lean:142`:
   `f.range = (⊤ : Subgroup N) ↔ Function.Surjective f`, `f` implicit).  Its
   `.mp` supplies the surjectivity, so the goal left for the `by` block is
   `(FreeGroup.lift P.val).range = ⊤`.
2. `FreeGroup.range_lift_eq_closure`
   (`Mathlib/GroupTheory/FreeGroup/Basic.lean:716`:
   `(lift f).range = Subgroup.closure (Set.range f)`).  That line shows no
   binders of its own.  It captures `{α : Type u} {β : Type v} [Group β]`
   and, from `variable {f}` at `:686`, an implicit `{f : α → β}`.  Rewriting
   with it turns the goal into `Subgroup.closure (Set.range P.val) = ⊤`.
3. That is `P.closure_eq_top`, so the second rewrite finishes the block.

The named argument `(f := FreeGroup.lift P.val)` is not required.  Drop it
and the goal at the `by` reads `MonoidHom.range ?m = ⊤`, with a hole where
the map should be.  Step 2 then back-solves the hole and splits into two
goals, `Subgroup.closure (Set.range ?m) = ⊤` and `α → G`, which step 3
closes together.  Both versions produce the same term.  The pin is here so
that the goal you read is the goal you prove. -/

/-- The self-generators, NONE style. -/
def GensN.self (G : Type) [Group G] : GensN G G :=
  ⟨id, by rw [Set.range_id, Subgroup.closure_univ]⟩

/- But the recovered dictionary is opaque.  The specification
`Function.surjInv_eq` — the lift of the chosen word is `g` — is its *only*
property; WHICH word was chosen is invisible, even on the canonical term.
EXPECTED ERROR: Type mismatch
  rfl
has type
  ?m.8 = ?m.8
but is expected to have type
  (GensN.self G).sec g = FreeGroup.of g -/
example (g : G) : (GensN.self G).sec g = FreeGroup.of g := rfl

/- Not a `rfl`-only gap: no proof exists.  `surjInv` grabs *some* preimage of
`g` under a map that is far from injective (`FreeGroup G → G`), and nothing
pins the grab to `of g`.  A NONE-style `wordLength` is therefore both
`noncomputable` and simp-lemma-free: the number exists, and nothing more can
be said about it.  Every downstream definition inherits the opacity — this is
what `Algebra.Generators` refused to accept for `Cotangent`'s module
structure, and what group theory has (so far) never needed to accept, because
no planned consumer of `Group.Generators` takes a dictionary as input. -/

/-! ## Test 6: the section as a NORMAL FORM — the real reason `Algebra` keeps σ

Tests 1–3 priced the section as an arbitrary choice.  Test 5 defended it as
definitional control.  Neither is quite the reason mathlib keeps σ.

The reason is plainer.  Commutative algebra has normal forms.  Every element of
a localization is `a / rⁿ`.  Every element of a quotient of a polynomial ring
is a polynomial.  A section is the sentence "here is how to write an element
down", and mathlib's real sections are written out, not chosen:

```
def localizationAway : Generators R S Unit where
  val _ := IsLocalization.Away.invSelf r
  σ' s :=
    letI a : R := (IsLocalization.Away.sec r s).1
    letI n : ℕ := (IsLocalization.Away.sec r s).2
    C a * X () ^ n
```
(`Mathlib/RingTheory/Extension/Generators.lean:208`.  That line shows no
binders of its own.  It captures `(R : Type u) (S : Type v) [CommRing R]
[CommRing S] [Algebra R S]` from the section header, plus `(r : R)` and the
instance `[IsLocalization.Away r S]` from the `variable` line at `:201`.)

Read σ′ in words.  Take `s`, read off its numerator `a` and its denominator
exponent `n`, hand back the polynomial `a · Xⁿ`.  Nothing is chosen.
`Generators.comp` (`:234`) tells the same story one level up: lift an element
of `T` to a polynomial over `S`, then lift each of that polynomial's
coefficients to a polynomial over `R`.

Groups show the same phenomenon whenever the group has a normal form.  The
infinite cyclic group has one: every element is `aᵏ` for exactly one `k`. -/

/-- `Multiplicative ℤ` on one generator, with its normal form as the section.
The mirror of `Generators.localizationAway`: `a / rⁿ` there, `aᵏ` here. -/
def GensS.intNF : GensS (Multiplicative ℤ) Unit where
  val _ := Multiplicative.ofAdd 1
  sec g := FreeGroup.of () ^ (Multiplicative.toAdd g)
  lift_val_sec g := by simp [← ofAdd_zsmul]

/- The section computes, and `rfl` sees it.  Contrast the third EXPECTED ERROR
just above, `(GensN.self G).sec g = FreeGroup.of g`, where the same question is
asked of a `surjInv` section and no proof exists at all. -/
example : GensS.intNF.sec (Multiplicative.ofAdd 3) = FreeGroup.of () ^ (3 : ℤ) := rfl

/-! ### Normal forms compose

`Algebra.Generators.comp` builds a presentation of `T` over `R` out of ones for
`T` over `S` and `S` over `R`, and its σ substitutes one section into the
other.  The group analogue that needs the least machinery is the direct
product: lay the two alphabets side by side, and concatenate the two normal
forms.  This is Test 3's `union` again, but now the composite dictionary is
content rather than a bill. -/

def GensS.prod {H : Type} [Group H] (P : GensS G α) (Q : GensS H β) :
    GensS (G × H) (α ⊕ β) where
  val := Sum.elim (fun a ↦ (P.val a, 1)) (fun b ↦ (1, Q.val b))
  sec g := FreeGroup.map Sum.inl (P.sec g.1) * FreeGroup.map Sum.inr (Q.sec g.2)
  lift_val_sec g := by
    have keyL : (FreeGroup.lift
        (Sum.elim (fun a ↦ (P.val a, (1 : H))) (fun b ↦ ((1 : G), Q.val b)))).comp
        (FreeGroup.map Sum.inl) = (MonoidHom.inl G H).comp (FreeGroup.lift P.val) := by
      ext a <;> simp
    have keyR : (FreeGroup.lift
        (Sum.elim (fun a ↦ (P.val a, (1 : H))) (fun b ↦ ((1 : G), Q.val b)))).comp
        (FreeGroup.map Sum.inr) = (MonoidHom.inr G H).comp (FreeGroup.lift Q.val) := by
      ext b <;> simp
    have hL := DFunLike.congr_fun keyL (P.sec g.1)
    have hR := DFunLike.congr_fun keyR (Q.sec g.2)
    simp only [MonoidHom.coe_comp, Function.comp_apply] at hL hR
    simp [hL, hR, P.lift_val_sec, Q.lift_val_sec]

/- The payoff, in practice.  Ask the composite for the normal form of the pair
`(a², b³)` in `ℤ × ℤ` and an actual word comes back.  `toWord` prints it as a
list of letters, each paired with `true` for the letter and `false` for its
inverse. -/

#eval (GensS.prod GensS.intNF GensS.intNF).sec
    (Multiplicative.ofAdd 2, Multiplicative.ofAdd 3) |>.toWord
/- [(Sum.inl (), true), (Sum.inl (), true),
    (Sum.inr (), true), (Sum.inr (), true), (Sum.inr (), true)] -/

/- Same fact, as a statement rather than a print-out: -/
example : (GensS.prod GensS.intNF GensS.intNF).sec
    (Multiplicative.ofAdd 2, Multiplicative.ofAdd 3) =
    FreeGroup.of (Sum.inl ()) ^ (2 : ℤ) * FreeGroup.of (Sum.inr ()) ^ (3 : ℤ) := by
  simp [GensS.prod, GensS.intNF]

/-! ### Why this does not transfer to `Group.Generators`

Compare the two ways a SECTION-term can come into existence.

* `GensS.ofLiftSurjective'` (Test 1): σ is `Exists.choose`.  Nothing about its
  value is provable, on any term.  Cost with no content.
* `GensS.intNF` here, and `Generators.localizationAway` in mathlib: σ is a
  formula, and the value computes.  Content.

`Algebra.Generators` lives in the second world for its standard constructions.
Localizations, quotients and polynomial rings all come with a way of writing
elements down, and every construction in the file (`comp`, `localizationAway`,
`extendScalars`, `reindex`, `ofAlgEquiv`) outputs one.  That is what the field
is for, and it is why `relation_comp_localizationAway_inl` can hypothesize
`P.σ (-1) = -1` at all: there is something there to constrain.

An arbitrary finitely generated group has no such formula.  The word problem is
undecidable in general (Novikov–Boone), so no construction on all groups can
output a computed section the way `localizationAway` does.  `GensS.intNF` above
is one special group, not a construction.  For a general `Group.Generators` the
only section available is Test 1's `Exists.choose`, which is the first bullet.

So the verdict of this sheet is not "sections are bad".  It is narrower.
Bundle a section when your objects have normal forms and your constructions
produce them.  `Algebra` does.  Groups, in the generality `Group.Generators` is
written for, do not. -/

/-! ## References: mathlib precedents for the SECTION vs NONE choice

All paths are files in this tree; quotes are verbatim; historical content is
pinned as `git show <commit>:<path>`.

### The case study: `Algebra.Generators` / `Algebra.Extension` (SECTION side)

* Introduced with σ from day one: PR #12518
  (https://github.com/leanprover-community/mathlib4/pull/12518, commit
  `913dc471aee`, 2024-06-10, A. Yang).  Review exchange quoted in `Context`
  above.  `ofSurjective` (the choice-based NONE→SECTION entry point) also
  day-one.
* `Algebra.Extension` — `Mathlib/RingTheory/Extension/Basic.lean:47`; field
  docstring `:54`: "A chosen (set-theoretic) section of an extension."
  Introduced PR #18684 (commit `6ae3e986f08`, 2024-11-15).
* σ survived the #25085 unbundling untouched; the further-unbundling
  experiment #25191 was closed unmerged ("horribly failed").
* σ's consumers: see `Context`.  Conversely `Hom` needs no σ-compatibility
  (`Mathlib/RingTheory/Extension/Generators.lean:408`,
  `Mathlib/RingTheory/Extension/Basic.lean:205`) and no `Generators.ext`
  exists — terms are never compared, only connected by homs.
* σ's fences, the two lemmas saying what it provably cannot affect:
  `Extension.Cotangent.val_smul'`
  (`Mathlib/RingTheory/Extension/Basic.lean:407`) for the action on `I/I²`,
  and `Extension.H1Cotangent.map_eq`
  (`Mathlib/RingTheory/Extension/Cotangent/Basic.lean:391`) for the induced
  map on `H¹`.  Both quoted in `Context`.
* σ as a normal form rather than a choice: `Generators.localizationAway`
  (`Mathlib/RingTheory/Extension/Generators.lean:208`, σ′ built from
  `IsLocalization.Away.sec`) and `Generators.comp` (`:234`).  Test 6.

### The three-layer pattern (DATA structure + `Nonempty` Prop + noncomputable accessor)

* `CategoryTheory.SplitEpi` — `Mathlib/CategoryTheory/EpiMono.lean:68`: "A split
  epimorphism is a morphism `f : X ⟶ Y` with a given section" — the datum is
  the *given* map.  `IsSplitEpi` (`:76`) is literally
  `Nonempty (SplitEpi f)`; the accessor `section_` (`:98`,
  `hf.exists_splitEpi.some.section_`) is `noncomputable`.  Plain `Epi`
  (`Mathlib/CategoryTheory/Category/Basic.lean:321`) is the witness-free
  bottom layer.  Verdict: mathlib keeps BOTH layers when both are needed, and
  names the data layer separately.
* `Encodable` (data) vs `Countable` (Prop) —
  `Mathlib/Logic/Encodable/Basic.lean:52` / `Mathlib/Data/Countable/Defs.lean:41`.
  The bridge `Encodable.ofCountable` (`Encodable/Basic.lean:395`) is
  `noncomputable` and its docstring says the recovered structure is
  "(non-canonical)".
* `Fintype` (data) vs `Finite` (Prop) — the written house policy,
  `Mathlib/Data/Finite/Defs.lean:96-100`: "Theorems should use `Finite`
  instead of `Fintype`, unless definitions in the theorem statement require
  `Fintype`.  Definitions should prefer `Finite` as well, unless it is
  important that the definitions are meant to be computable in the reduction
  or `#eval` sense."  Exactly this sheet's verdict: the data variant earns its
  keep only when a definition consumes it.
* Sharpest one-liner against bundling arbitrary choices as ambient data:
  `Fintype.toEncodable`, `Mathlib/Logic/Equiv/List.lean:119-120`: "It is not
  made into a global instance, since it involves an arbitrary choice."

### Group theory's own record on sections

* Transversals: `Subgroup.IsComplement` is a `Prop` on a `Set`
  (`Mathlib/GroupTheory/Complement.lean:48`); the representative-choosing
  function is *derived* and `noncomputable`
  (`IsComplement.toLeftFun`, `:495`: "A left transversal can be viewed as a
  function mapping each element of the group to the chosen representative
  from that left coset").  Schreier's lemma consumes Set + Prop, never
  bundled data (`Mathlib/GroupTheory/Schreier.lean:94`).
* The one group-theory structure that DOES bundle a set-theoretic section:
  `GroupExtension.Section` (`Mathlib/GroupTheory/GroupExtension/Defs.lean:241`:
  `toFun : G → E` + `rightInverse_rightHom`) — because there the sections
  *themselves* are the objects of study (splittings classified up to
  conjugacy, in bijection with `H¹`).  Bundle the section when the section is
  the mathematics; `Group.Generators`' mathematics is the marking, not a
  choice of words.  Note the surrounding `GroupExtension` structure itself
  keeps `rightHom_surjective` as a `Prop` field (`:80`).
* `FreeGroupBasis` (`Mathlib/GroupTheory/FreeGroup/IsFreeGroup.lean:55`)
  bundles `repr : G ≃* FreeGroup ι` — an inverse *direction*, but a canonical
  one: the inverse of an isomorphism involves no choice.  The section of a
  non-injective `FreeGroup α →* G` is the opposite case: maximal
  arbitrariness (Test 2).
* The third way — section as an ARGUMENT, neither bundled nor existential:
  `MonoidHom.liftOfRightInverse`
  (`Mathlib/Algebra/Group/Subgroup/Basic.lean:876`) takes `f_inv` as a plain
  parameter, with the `noncomputable abbrev liftOfSurjective` (`:892`) as
  choice-based fallback.  If a `Group.Generators` consumer ever needs a
  dictionary, it can take one as an argument at the use site.

### The NONE side, live

* `Group.Generators` — `Mathlib/GroupTheory/Generators.lean:44` (this branch):
  family + `closure_eq_top`; computable `ofLiftSurjective` (`:63`).
  House style agrees: `PresentedGroup.mk_surjective` keeps surjectivity as a
  theorem (`Mathlib/GroupTheory/PresentedGroup.lean:50`), `Group.FG` is a
  `Prop` (`Mathlib/GroupTheory/Finiteness.lean:395`).
* The choice-based escape hatch: `Function.surjInv` / `surjInv_eq` —
  `Mathlib/Logic/Function/Basic.lean:571` / `:574` (noncomputable,
  `Classical.choose`).
* Middle way not taken: `Trunc` (`Mathlib/Data/Quot.lean:467`, "unlike
  `Nonempty α`, `Trunc α` is data … can be used to maintain computability")
  could carry a section computably-but-canonically-anonymously; nothing in the
  planned group API would consume even that.
-/
