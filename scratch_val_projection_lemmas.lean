import Mathlib.GroupTheory.Generators

/-!
# Scratch: do the `_val` projection lemmas earn their keep?

Three questions, three different answers.

1. Does `map_val` do anything `rfl` can't? (Yes — it moves `simp`.)
2. Should it be hand-written? (No — `@[simps]` on the def is the idiom.)
3. Does `ofSet` want one? (The sibling structure ships none.)
-/

open Function

namespace Group.Generators

variable {G H α : Type*} [Group G] [Group H]

/-! ## Test 1 — a `map` with NO projection lemma

The fact is true by `rfl`. The question is whether `simp` can find it. -/

/-- A transport with deliberately no `_val` lemma attached. -/
protected def mapBare (P : Group.Generators G α) (f : G →* H) (hf : Surjective f) :
    Group.Generators H α where
  val := f ∘ P.val
  closure_eq_top := by
    rw [Set.range_comp, ← MonoidHom.map_closure, P.closure_eq_top,
      Subgroup.map_top_of_surjective f hf]

/-- `rfl` closes it, so the equation is definitional. -/
example (P : Group.Generators G α) (f : G →* H) (hf : Surjective f) (a : α) :
    (P.mapBare f hf).val a = f (P.val a) := rfl

/-- `simp` does not, because `mapBare` is an ordinary `def` and `simp` will not
unfold one. EXPECTED ERROR. -/
example (P : Group.Generators G α) (f : G →* H) (hf : Surjective f) (a : α) :
    (P.mapBare f hf).val a = f (P.val a) := by simp

/-! ## Test 2 — the same def, with `@[simps]` instead of a hand-written lemma -/

/-- The attribute generates the projection lemma and tags it `@[simp]`. -/
@[simps]
protected def mapSimps (P : Group.Generators G α) (f : G →* H) (hf : Surjective f) :
    Group.Generators H α where
  val := f ∘ P.val
  closure_eq_top := by
    rw [Set.range_comp, ← MonoidHom.map_closure, P.closure_eq_top,
      Subgroup.map_top_of_surjective f hf]

/- What did it generate, and under what name? -/
#check @Group.Generators.mapSimps_val

/-- Now `simp` closes the goal that failed in Test 1. -/
example (P : Group.Generators G α) (f : G →* H) (hf : Surjective f) (a : α) :
    (P.mapSimps f hf).val a = f (P.val a) := by simp

/-! ## Test 3 — the default `@[simps]` form is pointwise, and that matters

`mapSimps_val` above is stated APPLIED: `(P.mapSimps f hf).val a = …`.
So it only fires where `.val` already has an argument. The field of this
structure is used UNAPPLIED all over — `closure_eq_top` is about
`Set.range val` — and there `.val` has no argument to match on.

EXPECTED ERROR: the pointwise lemma cannot see this goal. -/

example (P : Group.Generators G α) (f : G →* H) (hf : Surjective f) :
    Set.range (P.mapSimps f hf).val = f '' Set.range P.val := by
  simp [Set.range_comp]

/-- `-fullyApplied` generates the unapplied equation instead — the form
that was hand-written in the real file. -/
@[simps -fullyApplied val]
protected def mapUnapplied (P : Group.Generators G α) (f : G →* H) (hf : Surjective f) :
    Group.Generators H α where
  val := f ∘ P.val
  closure_eq_top := by
    rw [Set.range_comp, ← MonoidHom.map_closure, P.closure_eq_top,
      Subgroup.map_top_of_surjective f hf]

#check @Group.Generators.mapUnapplied_val

/-- Same goal, now closed: `.val` is rewritten to a composition, and the
ordinary simp set takes over from there. -/
example (P : Group.Generators G α) (f : G →* H) (hf : Surjective f) :
    Set.range (P.mapUnapplied f hf).val = f '' Set.range P.val := by
  simp [Set.range_comp]

/-! ## Test 4 — `ofSet`

`ofSet`'s `val` is `Subtype.val`, a leaf. A projection lemma here rewrites
one atom to another atom, so nothing downstream opens up. Compare the two
goals: Test 3 exposes a `∘` that the simp set knows lemmas about; this one
exposes a coercion that was already in normal form. -/

example {S : Set G} (h : Subgroup.closure S = ⊤) (s : S) :
    (Group.Generators.ofSet h).val s = (s : G) := rfl

/-! ## Test 5 — retesting `ofSet`, because the "leaf" story was too quick

The claim to check: is `ofSet` really different from `map`, or does it hit
the same wall? Goal picked to be the one a consumer would actually meet —
recovering the generating set from the family. -/

/-- No projection lemma for `ofSet` exists. EXPECTED ERROR: same wall as Test 1. -/
example {S : Set G} (h : Subgroup.closure S = ⊤) :
    Set.range (Group.Generators.ofSet h).val = S := by
  simp [Subtype.range_coe]

/-- `rfl`-adjacent: the fact itself is cheap once the construction is unfolded. -/
example {S : Set G} (h : Subgroup.closure S = ⊤) :
    Set.range (Group.Generators.ofSet h).val = S := by
  show Set.range (Subtype.val : S → G) = S
  exact Subtype.range_coe

/-- With the lemma in scope, `simp` gets through on its own. -/
theorem ofSet_val_scratch {S : Set G} (h : Subgroup.closure S = ⊤) :
    (Group.Generators.ofSet h).val = Subtype.val := rfl

attribute [simp] ofSet_val_scratch

example {S : Set G} (h : Subgroup.closure S = ⊤) :
    Set.range (Group.Generators.ofSet h).val = S := by simp

end Group.Generators
