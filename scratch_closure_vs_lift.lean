import Mathlib.GroupTheory.Generators

/-!
# Scratch: the generating condition — CLOSURE equation vs LIFT surjectivity

Should the `Generators` field be `Subgroup.closure (Set.range val) = ⊤`
(CLOSURE) or `Function.Surjective (FreeGroup.lift val)` (LIFT)?

## What kind of call this is

A counts call. Nothing breaks on either side. Every test below compiles,
and the two designs differ by one application of
`FreeGroup.closure_range_eq_top_iff_surjective_lift`. Which side applies
it flips between Test 2 and Test 3. The tests therefore do not separate
the designs, and the counts below are the whole argument. A reader who
weighs those numbers differently is entitled to the other answer.

## The counts

Theorems concluding a closure equation, then lemmas taking one as an
argument:

    grep -rE "theorem .*closure.*= ⊤|lemma .*closure.*= ⊤" Mathlib --include="*.lean" | wc -l
    51
    grep -rE "\(h[a-zA-Z]* : (Subgroup\.)?closure [^)]*= ⊤\)" Mathlib --include="*.lean" | wc -l
    29

The same two patterns for the lift shape:

    grep -rE "theorem .*Surjective \(FreeGroup.lift|lemma .*Surjective \(FreeGroup.lift" Mathlib --include="*.lean"
    Mathlib/GroupTheory/Generators.lean:70
    grep -rE "\(h[a-zA-Z]* : Function.Surjective \(FreeGroup.lift" Mathlib --include="*.lean" | wc -l
    0

The one hit is this branch's own `Group.Generators.lift_val_surjective`,
so upstream mathlib has none of either. All four patterns match single
lines only, so every number here is a floor. Mathlib does state
generation as a surjection twice, quantifying over an unnamed `φ` where
none of these patterns can see it:
`Group.fg_iff_exists_freeGroup_hom_surjective` and its `_finite` variant
(`Mathlib/GroupTheory/Finiteness.lean:473`, `:484`).

Scratch material. Delete freely.
-/

/-- CLOSURE, as in `Group.Generators`
(`Mathlib/GroupTheory/Generators.lean:60`) and `AffineBasis.tot'`
(`Mathlib/LinearAlgebra/AffineSpace/Basis.lean:93`). -/
structure GensClos (G : Type) [Group G] (α : Type) where
  val : α → G
  closure_eq_top : Subgroup.closure (Set.range val) = ⊤

/-- LIFT. -/
structure GensLift (G : Type) [Group G] (α : Type) where
  val : α → G
  lift_surjective : Function.Surjective (FreeGroup.lift val)

variable {G H : Type} [Group G] [Group H] {α : Type}

/-! ## The one conversion

`FreeGroup.closure_range_eq_top_iff_surjective_lift`
(`Mathlib/GroupTheory/FreeGroup/Basic.lean:723`) turns either statement
into the other, with no side conditions. Both designs use it, in
opposite directions, and neither has to name it: the tests below apply
`.mp` and `.mpr` inline. Either design may name it anyway —
`Group.Generators` does, as the one-line
`lift_val_surjective` (`:70`) — but that is a choice about identifiers,
not a difference in what a user has to prove.
-/

/-! ## Test 1: build a term from a library generation fact

`h` stands for the 51 theorems counted above. -/

/- CLOSURE: the proof in hand is the field. -/
example (f : α → G) (h : Subgroup.closure (Set.range f) = ⊤) :
    GensClos G α :=
  ⟨f, h⟩

/- LIFT: the same proof, one `.mp`. -/
example (f : α → G) (h : Subgroup.closure (Set.range f) = ⊤) :
    GensLift G α :=
  ⟨f, FreeGroup.closure_range_eq_top_iff_surjective_lift.mp h⟩

/- The family reads back out by `rfl` on both sides, so neither design
needs a simp lemma for it. -/
example (f : α → G) (h : Subgroup.closure (Set.range f) = ⊤) :
    (GensLift.mk f
      (FreeGroup.closure_range_eq_top_iff_surjective_lift.mp h)).val = f :=
  rfl

/-! ## Test 2: homs agreeing on the generators agree everywhere

`MonoidHom.eq_of_eqOn_dense` (`Mathlib/Algebra/Group/Subgroup/Ker.lean:403`)
is one of the 29. Its first explicit argument is a closure equation. -/

/- CLOSURE: the field is the argument. -/
example (P : GensClos G α) (φ ψ : G →* H)
    (h : Set.EqOn φ ψ (Set.range P.val)) : φ = ψ :=
  MonoidHom.eq_of_eqOn_dense P.closure_eq_top h

/- LIFT: one `.mpr`. -/
example (P : GensLift G α) (φ ψ : G →* H)
    (h : Set.EqOn φ ψ (Set.range P.val)) : φ = ψ :=
  MonoidHom.eq_of_eqOn_dense
    (FreeGroup.closure_range_eq_top_iff_surjective_lift.mpr P.lift_surjective) h

/-! ## Test 3: the one thing LIFT does better

`Group.fg_of_surjective` (`Mathlib/GroupTheory/Finiteness.lean:459`) wants
a surjection, so here the conversion lands on CLOSURE.

The current API has no call site for this. `Group.Generators.fg`
(`Mathlib/GroupTheory/Generators.lean:83`) is the branch's only use of
surjectivity, and the third example below proves the same thing without
it. -/

/- LIFT: the field is the argument. -/
example [Finite α] (P : GensLift G α) : Group.FG G :=
  Group.fg_of_surjective P.lift_surjective

/- CLOSURE: one `.mp`, mirroring Test 2. -/
example [Finite α] (P : GensClos G α) : Group.FG G :=
  Group.fg_of_surjective
    (FreeGroup.closure_range_eq_top_iff_surjective_lift.mp P.closure_eq_top)

/- Or skip the conversion. `Group.fg_iff` (`:416`) states finite
generation as a closure equation. -/
example [Finite α] (P : GensClos G α) : Group.FG G :=
  Group.fg_iff.mpr ⟨_, P.closure_eq_top, Set.finite_range _⟩

/-! ## Live: the real API on this branch -/

/- The CLOSURE field (`Mathlib/GroupTheory/Generators.lean:64`) and the
named conversion (`:70`), which is `.mp` of the library iff. -/
#check @Group.Generators.closure_eq_top
#check @Group.Generators.lift_val_surjective
#check @FreeGroup.closure_range_eq_top_iff_surjective_lift

/-! ## Where this sheet is weaker than it looks

One lemma application, in opposite directions, is the whole measured
difference. Nothing here shows a proof that only one design can write. A
reader who finds one `.mp` unimportant should read this sheet as saying
the two designs are close to equivalent, and take the counts as the
argument.

Three claims earlier drafts made and got wrong:

* "51 to 0". The 0 came from a pattern that cannot match mathlib's
  `∃ (φ : FreeGroup α →* G), Function.Surjective φ`, and mathlib has two
  of those.
* Two `EXPECTED ERROR` examples. Each handed a proof of one field's
  statement to the other field's slot. That is a type mismatch in both
  directions whatever the design, so it measured nothing.
* "CLOSURE ships one helper lemma, LIFT would ship two." Both helpers
  were `.mp` and `.mpr` of the one iff above, and neither design has to
  name either one. Test 1 and Test 3 apply them inline.

Earlier drafts also cited three consumers in
`Mathlib/GroupTheory/Presentation.lean` and ran `#check` on
`Group.Generators.ofLiftSurjective`. Neither the file nor that
declaration exists in this checkout.

`Group.Generators.map` contains a `sorry` (`:80`). The warning does not
reach an importer, so this sheet compiles clean, but the branch it argues
about is not sorry-free.
-/

/-! ## References

* The conversion is one iff:
  `FreeGroup.closure_range_eq_top_iff_surjective_lift`,
  `Mathlib/GroupTheory/FreeGroup/Basic.lean:723`, built on
  `range_lift_eq_closure`, `:716`. Both were added by this branch.
  Free-module twin:
  `span_range_eq_top_iff_surjective_finsuppLinearCombination`,
  `Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean:139`.
* Group-side members of the 29: `Mathlib/GroupTheory/Schreier.lean:69`,
  `:98`, `:121`, `Mathlib/GroupTheory/Subgroup/Centralizer.lean:128`,
  `:133`, `Mathlib/GroupTheory/GroupAction/Quotient.lean:464`, `:470`.
* `Subgroup.FG` and `Group.FG` are closure-defined:
  `Mathlib/GroupTheory/Finiteness.lean:303`, `:395`.
* The lift shape where it is right: `FreeGroupBasis.repr : G ≃* FreeGroup ι`,
  `Mathlib/GroupTheory/FreeGroup/IsFreeGroup.lean:59`. That map is an
  isomorphism, so the field carries data. Surjectivity carries none.
-/
