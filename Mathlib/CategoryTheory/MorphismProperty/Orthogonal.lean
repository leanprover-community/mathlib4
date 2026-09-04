/-
Copyright (c) 2026 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.UniqueLimits
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Left and right orthogonals of a morphism property

Given a morphism property `T`, we define the classes of morphisms that are left
(resp. right) orthogonal to `T`, i.e. that have the *unique* left (resp. right)
lifting property with respect to every morphism in `T`.

This file mirrors `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`
(`llp`/`rlp`) with `HasLiftingProperty` replaced by `HasUniqueLiftingProperty`.

## Main declarations

* `CategoryTheory.MorphismProperty.leftOrthogonal`,
  `CategoryTheory.MorphismProperty.rightOrthogonal`: the two orthogonal classes.
* `CategoryTheory.MorphismProperty.IsOrthogonalPair`: the property that two
  classes are the orthogonals of each other.
* `CategoryTheory.MorphismProperty.gc_leftOrthogonal_rightOrthogonal`: the two
  operations form an antitone Galois connection, whence the triple identities
  `CategoryTheory.MorphismProperty.rightOrthogonal_leftOrthogonal_rightOrthogonal`
  and
  `CategoryTheory.MorphismProperty.leftOrthogonal_rightOrthogonal_leftOrthogonal`.
* `CategoryTheory.MorphismProperty.leftOrthogonal_le_llp`,
  `CategoryTheory.MorphismProperty.rightOrthogonal_le_rlp`: comparison with the
  ordinary lifting-property classes.
* `CategoryTheory.MorphismProperty.IsOrthogonalPair.inf_eq_isomorphisms`: the
  two classes of an orthogonal pair meet in the isomorphisms.

Both classes contain the isomorphisms and are closed under composition,
retracts, and the appropriate variance of base change and (co)limits; each such
closure property comes in a bare form for `leftOrthogonal`/`rightOrthogonal` and
in an instance form for the two classes of an `IsOrthogonalPair`. Cancellation
is discussed below. Finally, `op_leftOrthogonal` and its three companions
identify the orthogonals in `Cᵒᵖ`.

## Cancellation terminology and orientation

Cancellation properties of the orthogonal classes are expressed through mathlib's
relative predicates `MorphismProperty.HasOfPostcompProperty` and
`MorphismProperty.HasOfPrecompProperty`.

With mathlib's composition convention (`f ≫ g` means `g` after `f`), the
orientation dictionary is:

| cancellation | rule | mathlib predicate |
|---|---|---|
| right cancellation | `f ≫ g ∈ P`, `g ∈ P` ⟹ `f ∈ P` | `P.HasOfPostcompProperty P` |
| left cancellation | `f ≫ g ∈ P`, `f ∈ P` ⟹ `g ∈ P` | `P.HasOfPrecompProperty P` |

The two orthogonal classes satisfy **one each, not both**:

* `T.rightOrthogonal` — the *right* class — has the *of-postcomp* property
  (right cancellation);
* `T.leftOrthogonal` — the *left* class — has the *of-precomp* property
  (left cancellation).

Neither class has the other property in general, and neither has
`HasTwoOutOfThreeProperty`: `HasTwoOutOfThreeProperty` is a tempting but wrong
target here. Relative forms `B.HasOfPostcompProperty W'` for `W' ≤ B` are
obtained from `HasOfPostcompProperty.of_le`, not from bespoke instances.

Proposition 3 of [anel2009] uses the opposite cancellation vocabulary: it calls
the right class's of-postcomp rule above *left cancellation*, and calls the dual
rule *right cancellation*. The names in this file follow mathlib's composition
API and the orientation table above.

## References

* [M. Anel, *Grothendieck topologies from unique factorisation systems*][anel2009]

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (T : MorphismProperty C)

namespace MorphismProperty

/-- Given `T : MorphismProperty C`, this is the class of morphisms that are left
orthogonal to `T`, i.e. that have the *unique* left lifting property with respect
to `T`. -/
def leftOrthogonal : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasUniqueLiftingProperty f g

/-- Given `T : MorphismProperty C`, this is the class of morphisms that are right
orthogonal to `T`, i.e. that have the *unique* right lifting property with respect
to `T`. -/
def rightOrthogonal : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasUniqueLiftingProperty g f

lemma leftOrthogonal_of_isIso {A B : C} (i : A ⟶ B) [IsIso i] :
    T.leftOrthogonal i :=
  fun _ _ _ _ ↦ inferInstance

lemma rightOrthogonal_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    T.rightOrthogonal f :=
  fun _ _ _ _ ↦ inferInstance

/-- `T ≤ T'.leftOrthogonal` if and only if `T' ≤ T.rightOrthogonal`; both express
that every morphism in `T'` has the unique lifting property against every morphism
in `T`. -/
lemma le_leftOrthogonal_iff_le_rightOrthogonal (T' : MorphismProperty C) :
    T ≤ T'.leftOrthogonal ↔ T' ≤ T.rightOrthogonal :=
  ⟨fun h _ _ _ hp _ _ _ hi ↦ h _ hi _ hp,
    fun h _ _ _ hi _ _ _ hp ↦ h _ hp _ hi⟩

/-- `leftOrthogonal` and `rightOrthogonal` form a Galois connection between
`MorphismProperty C` and its order dual. -/
lemma gc_leftOrthogonal_rightOrthogonal :
    GaloisConnection (OrderDual.toDual (α := MorphismProperty C) ∘ leftOrthogonal)
      (rightOrthogonal ∘ OrderDual.ofDual) :=
  fun _ _ ↦ le_leftOrthogonal_iff_le_rightOrthogonal _ _

/-- Every morphism property is contained in the left orthogonal of its right
orthogonal. -/
lemma le_leftOrthogonal_rightOrthogonal : T ≤ T.rightOrthogonal.leftOrthogonal := by
  rw [le_leftOrthogonal_iff_le_rightOrthogonal]

/-- The triple orthogonal `T.rightOrthogonal.leftOrthogonal.rightOrthogonal`
collapses to `T.rightOrthogonal`. -/
@[simp]
lemma rightOrthogonal_leftOrthogonal_rightOrthogonal :
    T.rightOrthogonal.leftOrthogonal.rightOrthogonal = T.rightOrthogonal :=
  gc_leftOrthogonal_rightOrthogonal.u_l_u_eq_u T

/-- The triple orthogonal `T.leftOrthogonal.rightOrthogonal.leftOrthogonal`
collapses to `T.leftOrthogonal`. -/
@[simp]
lemma leftOrthogonal_rightOrthogonal_leftOrthogonal :
    T.leftOrthogonal.rightOrthogonal.leftOrthogonal = T.leftOrthogonal :=
  gc_leftOrthogonal_rightOrthogonal.l_u_l_eq_l T

lemma antitone_rightOrthogonal :
    Antitone (rightOrthogonal : MorphismProperty C → _) :=
  fun _ _ h ↦ gc_leftOrthogonal_rightOrthogonal.monotone_u h

lemma antitone_leftOrthogonal :
    Antitone (leftOrthogonal : MorphismProperty C → _) :=
  fun _ _ h ↦ gc_leftOrthogonal_rightOrthogonal.monotone_l h

/-- **Right orthogonals only see the left-saturation of a class.** If a class `Q`
sits between `P` and its left-saturation `P.rightOrthogonal.leftOrthogonal`, then
`P` and `Q` have the same right orthogonal.

This is the abstract generality behind "spreading out": any class obtained from `P`
by cobase changes, isomorphisms, retracts, (transfinite) composition, or coproducts
— all of which preserve membership in the *left* orthogonal — is automatically
`≤ P.rightOrthogonal.leftOrthogonal`, so enlarging `P` to it does not change the
right orthogonal. Concretely, if every `Q`-morphism is (up to isomorphism of arrows)
a cobase change of a `P`-morphism and `P ≤ Q`, the hypothesis holds and
`P.rightOrthogonal = Q.rightOrthogonal`.

The proof is pure order theory: `antitone_rightOrthogonal` gives one inclusion from
`P ≤ Q`, and the other follows from applying it to `hQ` together with the triple
collapse `rightOrthogonal_leftOrthogonal_rightOrthogonal`. -/
lemma rightOrthogonal_eq_of_le_of_le_leftOrthogonal_rightOrthogonal
    {P Q : MorphismProperty C} (hPQ : P ≤ Q)
    (hQ : Q ≤ P.rightOrthogonal.leftOrthogonal) :
    P.rightOrthogonal = Q.rightOrthogonal :=
  le_antisymm
    (by simpa using antitone_rightOrthogonal hQ)
    (antitone_rightOrthogonal hPQ)

/-- Dual of `rightOrthogonal_eq_of_le_of_le_leftOrthogonal_rightOrthogonal`: if `Q`
sits between `P` and its right-saturation `P.leftOrthogonal.rightOrthogonal`, then
`P` and `Q` have the same left orthogonal. -/
lemma leftOrthogonal_eq_of_le_of_le_rightOrthogonal_leftOrthogonal
    {P Q : MorphismProperty C} (hPQ : P ≤ Q)
    (hQ : Q ≤ P.leftOrthogonal.rightOrthogonal) :
    P.leftOrthogonal = Q.leftOrthogonal :=
  le_antisymm
    (by simpa using antitone_leftOrthogonal hQ)
    (antitone_leftOrthogonal hPQ)

/-- The left orthogonal in the opposite category is the opposite of the right
orthogonal: unique left lifting against `T.op` is unique right lifting against
`T`, read in `Cᵒᵖ`. -/
@[simp]
lemma op_leftOrthogonal : T.op.leftOrthogonal = T.rightOrthogonal.op := by
  ext X Y f
  exact ⟨fun hf _ _ g hg ↦ (hf g.op hg).unop, fun hf _ _ g hg ↦ (hf g.unop hg).op⟩

/-- The right orthogonal in the opposite category is the opposite of the left
orthogonal. -/
@[simp]
lemma op_rightOrthogonal : T.op.rightOrthogonal = T.leftOrthogonal.op := by
  ext X Y f
  exact ⟨fun hf _ _ g hg ↦ (hf g.op hg).unop, fun hf _ _ g hg ↦ (hf g.unop hg).op⟩

/-- Dual of `op_leftOrthogonal` for a property on an opposite category. -/
@[simp]
lemma unop_leftOrthogonal (T : MorphismProperty Cᵒᵖ) :
    T.unop.leftOrthogonal = T.rightOrthogonal.unop := by
  ext X Y f
  exact ⟨fun hf _ _ g hg ↦ (hf g.unop hg).op, fun hf _ _ g hg ↦ (hf g.op hg).unop⟩

/-- Dual of `op_rightOrthogonal` for a property on an opposite category. -/
@[simp]
lemma unop_rightOrthogonal (T : MorphismProperty Cᵒᵖ) :
    T.unop.rightOrthogonal = T.leftOrthogonal.unop := by
  ext X Y f
  exact ⟨fun hf _ _ g hg ↦ (hf g.unop hg).op, fun hf _ _ g hg ↦ (hf g.op hg).unop⟩

/-- Two morphism properties form an orthogonal pair if each is exactly the
corresponding unique orthogonal of the other. This is the notion of a unique
lifting system of [anel2009], Definition 1; it does not include a factorization
axiom. -/
class IsOrthogonalPair (A B : MorphismProperty C) : Prop where
  left_eq : B.leftOrthogonal = A
  right_eq : A.rightOrthogonal = B

-- `left_eq` and `right_eq` are not `simp` lemmas: in `B.leftOrthogonal = A` the class argument
-- `A` does not occur in the left-hand side, and dually for `right_eq`, so neither is usable by
-- `simp`. Use them through an explicit `rw [← IsOrthogonalPair.left_eq (A := A) (B := B)]`.

/-- The orthogonal pair generated by a morphism property `T`
([anel2009], Lemma 2). -/
instance rightOrthogonal_isOrthogonalPair :
    IsOrthogonalPair T.rightOrthogonal.leftOrthogonal T.rightOrthogonal where
  left_eq := rfl
  right_eq := rightOrthogonal_leftOrthogonal_rightOrthogonal T

/-- The dual orthogonal pair generated by a morphism property `T`. -/
instance leftOrthogonal_isOrthogonalPair :
    IsOrthogonalPair T.leftOrthogonal T.leftOrthogonal.rightOrthogonal where
  left_eq := leftOrthogonal_rightOrthogonal_leftOrthogonal T
  right_eq := rfl

/-- Membership in the right orthogonal of a family `MorphismProperty.ofHoms f` reduces to the
unique right lifting property against each generator `f i`. This has nothing to do with the
particular family; it is the defining unfolding of `rightOrthogonal` for a property generated by
an explicit family of morphisms. -/
lemma rightOrthogonal_ofHoms_iff {ι : Type*} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    {X Y : C} (p : X ⟶ Y) :
    (MorphismProperty.ofHoms f).rightOrthogonal p ↔
      ∀ i, HasUniqueLiftingProperty (f i) p :=
  ⟨fun h i => h _ ⟨i⟩, fun h _ _ g hg => by obtain ⟨i⟩ := hg; exact h i⟩

/-- Dual of `rightOrthogonal_ofHoms_iff`: membership in the left orthogonal of a family
`MorphismProperty.ofHoms f` reduces to the unique left lifting property against each generator. -/
lemma leftOrthogonal_ofHoms_iff {ι : Type*} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    {X Y : C} (p : X ⟶ Y) :
    (MorphismProperty.ofHoms f).leftOrthogonal p ↔
      ∀ i, HasUniqueLiftingProperty p (f i) :=
  ⟨fun h i => h _ ⟨i⟩, fun h _ _ g hg => by obtain ⟨i⟩ := hg; exact h i⟩

/-- The left orthogonal is contained in the (ordinary) left lifting property: a
morphism with the *unique* left lifting property in particular has the left lifting
property. -/
lemma leftOrthogonal_le_llp : T.leftOrthogonal ≤ T.llp :=
  fun _ _ _ hf _ _ g hg ↦ (hf g hg).toHasLiftingProperty

/-- The right orthogonal is contained in the (ordinary) right lifting property: a
morphism with the *unique* right lifting property in particular has the right
lifting property. -/
lemma rightOrthogonal_le_rlp : T.rightOrthogonal ≤ T.rlp :=
  fun _ _ _ hf _ _ g hg ↦ (hf g hg).toHasLiftingProperty

/-- The left orthogonal of `T` is multiplicative: it contains the identities and
is stable under composition. Identities are isomorphisms (`leftOrthogonal_of_isIso`)
and composition is `HasUniqueLiftingProperty.of_comp_left`. -/
instance leftOrthogonal_isMultiplicative : T.leftOrthogonal.IsMultiplicative where
  id_mem X _ _ p hp := by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance

/-- The right orthogonal of `T` is multiplicative: it contains the identities and
is stable under composition (`HasUniqueLiftingProperty.of_comp_right`). -/
instance rightOrthogonal_isMultiplicative : T.rightOrthogonal.IsMultiplicative where
  id_mem X _ _ p hp := by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance

/-- The left orthogonal of `T` respects isomorphisms: it is stable under composition
and contains the isomorphisms, which is all `respectsIso_of_isStableUnderComposition`
needs. -/
instance leftOrthogonal_respectsIso : T.leftOrthogonal.RespectsIso :=
  respectsIso_of_isStableUnderComposition fun _ _ f hf ↦
    haveI : IsIso f := hf
    T.leftOrthogonal_of_isIso f

/-- The right orthogonal of `T` respects isomorphisms: it is stable under composition
and contains the isomorphisms, which is all `respectsIso_of_isStableUnderComposition`
needs. -/
instance rightOrthogonal_respectsIso : T.rightOrthogonal.RespectsIso :=
  respectsIso_of_isStableUnderComposition fun _ _ f hf ↦
    haveI : IsIso f := hf
    T.rightOrthogonal_of_isIso f

set_option synthInstance.checkSynthOrder false in
/-- The left class of an orthogonal pair is multiplicative
([anel2009], Proposition 3(1)). -/
instance IsOrthogonalPair.left_isMultiplicative (A B : MorphismProperty C)
    [IsOrthogonalPair A B] : A.IsMultiplicative := by
  rw [← IsOrthogonalPair.left_eq (A := A) (B := B)]
  infer_instance

set_option synthInstance.checkSynthOrder false in
/-- The right class of an orthogonal pair is multiplicative
([anel2009], Proposition 3(1)). -/
instance IsOrthogonalPair.right_isMultiplicative (A B : MorphismProperty C)
    [IsOrthogonalPair A B] : B.IsMultiplicative := by
  rw [← IsOrthogonalPair.right_eq (A := A) (B := B)]
  infer_instance

/-- The left orthogonal of `T` is stable under retracts, via
`RetractArrow.leftUniqueLiftingProperty`. -/
instance leftOrthogonal_isStableUnderRetracts : T.leftOrthogonal.IsStableUnderRetracts where
  of_retract h hg _ _ f hf :=
    letI := hg _ hf
    h.leftUniqueLiftingProperty f

/-- The right orthogonal of `T` is stable under retracts, via
`RetractArrow.rightUniqueLiftingProperty`. -/
instance rightOrthogonal_isStableUnderRetracts : T.rightOrthogonal.IsStableUnderRetracts where
  of_retract h hf _ _ g hg :=
    letI := hf _ hg
    h.rightUniqueLiftingProperty g

/-- The left orthogonal of `T` is stable under cobase change, via
`IsPushout.hasUniqueLiftingProperty`. -/
instance leftOrthogonal_isStableUnderCobaseChange :
    T.leftOrthogonal.IsStableUnderCobaseChange where
  of_isPushout h hf _ _ g' hg' :=
    letI := hf _ hg'
    h.hasUniqueLiftingProperty g'

/-- The right orthogonal of `T` is stable under base change, via
`IsPullback.hasUniqueLiftingProperty`. -/
instance rightOrthogonal_isStableUnderBaseChange :
    T.rightOrthogonal.IsStableUnderBaseChange where
  of_isPullback h hf _ _ f' hf' :=
    letI := hf _ hf'
    h.hasUniqueLiftingProperty f'

/-- The right orthogonal of `T` has the of-postcomp property against itself: if
`f ≫ g` and `g` are both right orthogonal to `T`, then so is `f` (right
cancellation). See the module docstring for the orientation dictionary. -/
instance rightOrthogonal_hasOfPostcompProperty :
    T.rightOrthogonal.HasOfPostcompProperty T.rightOrthogonal where
  of_postcomp f g hg hfg _ _ i hi := by
    have := hfg i hi
    have := (hg i hi).toHasAtMostOneLiftingProperty
    exact .of_comp_right_cancel i f g

/-- The left orthogonal of `T` has the of-precomp property against itself: if
`f ≫ g` and `f` are both left orthogonal to `T`, then so is `g` (left
cancellation). See the module docstring for the orientation dictionary. -/
instance leftOrthogonal_hasOfPrecompProperty :
    T.leftOrthogonal.HasOfPrecompProperty T.leftOrthogonal where
  of_precomp f g hf hfg _ _ i hi := by
    have := hfg i hi
    have := (hf i hi).toHasAtMostOneLiftingProperty
    exact .of_comp_left_cancel i g f

set_option synthInstance.checkSynthOrder false in
/-- The left class of an orthogonal pair is stable under retracts
([anel2009], Proposition 3(3)). -/
instance IsOrthogonalPair.left_isStableUnderRetracts (A B : MorphismProperty C)
    [IsOrthogonalPair A B] : A.IsStableUnderRetracts := by
  rw [← IsOrthogonalPair.left_eq (A := A) (B := B)]
  infer_instance

set_option synthInstance.checkSynthOrder false in
/-- The right class of an orthogonal pair is stable under retracts
([anel2009], Proposition 3(3)). -/
instance IsOrthogonalPair.right_isStableUnderRetracts (A B : MorphismProperty C)
    [IsOrthogonalPair A B] : B.IsStableUnderRetracts := by
  rw [← IsOrthogonalPair.right_eq (A := A) (B := B)]
  infer_instance

set_option synthInstance.checkSynthOrder false in
/-- The left class of an orthogonal pair is stable under cobase change
([anel2009], Proposition 3(3)). -/
instance IsOrthogonalPair.left_isStableUnderCobaseChange (A B : MorphismProperty C)
    [IsOrthogonalPair A B] : A.IsStableUnderCobaseChange := by
  rw [← IsOrthogonalPair.left_eq (A := A) (B := B)]
  infer_instance

set_option synthInstance.checkSynthOrder false in
/-- The right class of an orthogonal pair is stable under base change
([anel2009], Proposition 3(3)). -/
instance IsOrthogonalPair.right_isStableUnderBaseChange (A B : MorphismProperty C)
    [IsOrthogonalPair A B] : B.IsStableUnderBaseChange := by
  rw [← IsOrthogonalPair.right_eq (A := A) (B := B)]
  infer_instance

set_option synthInstance.checkSynthOrder false in
/-- The right class of an orthogonal pair has of-postcomp cancellation (called
left cancellation in [anel2009], Proposition 3(3), and right cancellation in the
orientation table in this module). -/
instance IsOrthogonalPair.right_hasOfPostcompProperty (A B : MorphismProperty C)
    [IsOrthogonalPair A B] : B.HasOfPostcompProperty B := by
  rw [← IsOrthogonalPair.right_eq (A := A) (B := B)]
  infer_instance

set_option synthInstance.checkSynthOrder false in
/-- The left class of an orthogonal pair has of-precomp cancellation (the dual
of the rule called left cancellation in [anel2009], Proposition 3(3), and left
cancellation in the orientation table in this module). -/
instance IsOrthogonalPair.left_hasOfPrecompProperty (A B : MorphismProperty C)
    [IsOrthogonalPair A B] : A.HasOfPrecompProperty A := by
  rw [← IsOrthogonalPair.left_eq (A := A) (B := B)]
  infer_instance

/-- Thin wrapper over `MorphismProperty.of_postcomp` for the right orthogonal, so
downstream files need not name the `HasOfPostcompProperty` typeclass: if `g` and
`f ≫ g` are right orthogonal to `T`, then so is `f`. -/
lemma rightOrthogonal_of_postcomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : T.rightOrthogonal g) (hfg : T.rightOrthogonal (f ≫ g)) :
    T.rightOrthogonal f :=
  T.rightOrthogonal.of_postcomp f g hg hfg

/-- Right cancellation of a **monomorphism**, with no hypothesis on `T`: if `f ≫ g` is right
orthogonal to `T` and `g` is a monomorphism, then `f` is right orthogonal to `T`.

This strengthens `rightOrthogonal_of_postcomp`, which asks the cancelled factor `g` to lie in
the right class; here it only has to be monic. Both halves of unique lifting survive the
cancellation: a lift of a square against `f` is obtained from the lift against `f ≫ g` because
`g` is monic, and uniqueness is inherited because `g` being monic gives
`HasAtMostOneLiftingProperty i g` for free. -/
lemma rightOrthogonal_of_postcomp_mono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g]
    (hfg : T.rightOrthogonal (f ≫ g)) : T.rightOrthogonal f := fun _ _ i hi ↦ by
  have := hfg i hi
  exact .of_comp_right_cancel i f g

/-- Left cancellation of an **epimorphism**, the dual of `rightOrthogonal_of_postcomp_mono`: if
`f ≫ g` is left orthogonal to `T` and `f` is an epimorphism, then `g` is left orthogonal
to `T`. -/
lemma leftOrthogonal_of_precomp_epi {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f]
    (hfg : T.leftOrthogonal (f ≫ g)) : T.leftOrthogonal g := fun _ _ p hp ↦ by
  have := hfg p hp
  exact .of_comp_left_cancel p g f

/-- Thin wrapper over `MorphismProperty.of_precomp` for the left orthogonal: if
`f` and `f ≫ g` are left orthogonal to `T`, then so is `g`. -/
lemma leftOrthogonal_of_precomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : T.leftOrthogonal f) (hfg : T.leftOrthogonal (f ≫ g)) :
    T.leftOrthogonal g :=
  T.leftOrthogonal.of_precomp f g hf hfg

/-- A section of a morphism in the right orthogonal of `T` is itself right orthogonal
to `T`: if `f ≫ g = 𝟙` and `g` is right orthogonal to `T`, then so is `f` (one
of the section/retraction consequences of [anel2009], Proposition 3(3)). The composite
`f ≫ g` is an isomorphism, hence right orthogonal by `rightOrthogonal_of_isIso`,
and of-postcomp cancellation (`rightOrthogonal_of_postcomp`) then yields `f`.
Retractions of right-class maps follow from stability under retracts. -/
lemma rightOrthogonal_of_section {X Y : C} {f : X ⟶ Y} {g : Y ⟶ X}
    (hg : T.rightOrthogonal g) (h : f ≫ g = 𝟙 X) : T.rightOrthogonal f := by
  have hfg : T.rightOrthogonal (f ≫ g) := by
    rw [h]; exact T.rightOrthogonal_of_isIso _
  exact T.rightOrthogonal_of_postcomp f g hg hfg

/-- A retraction of a morphism in the left orthogonal of `T` is itself left orthogonal
to `T`: if `f ≫ g = 𝟙` and `f` is left orthogonal to `T`, then so is `g` (one
of the dual section/retraction consequences of [anel2009], Proposition 3(3)).
Sections
of left-class maps follow from stability under retracts. -/
lemma leftOrthogonal_of_retraction {X Y : C} {f : X ⟶ Y} {g : Y ⟶ X}
    (hf : T.leftOrthogonal f) (h : f ≫ g = 𝟙 X) : T.leftOrthogonal g := by
  have hfg : T.leftOrthogonal (f ≫ g) := by
    rw [h]; exact T.leftOrthogonal_of_isIso _
  exact T.leftOrthogonal_of_precomp f g hf hfg

/-- A morphism that is both left orthogonal to `T` and in `T` is an isomorphism:
it then has the unique lifting property against itself, hence the ordinary lifting
property against itself, so it is an isomorphism ([anel2009], Proposition 3(2),
one inclusion). Stated generically in `T`; no `IsOrthogonalPair` is needed. -/
lemma leftOrthogonal_inf_le_isomorphisms : T.leftOrthogonal ⊓ T ≤ isomorphisms C := by
  intro X Y f hf
  obtain ⟨hfl, hfT⟩ := hf
  have hlp : HasLiftingProperty f f := (hfl f hfT).toHasLiftingProperty
  exact isIso_of_hasLiftingProperty_self f

/-- A morphism that is both in `T` and right orthogonal to `T` is an isomorphism
([anel2009], Proposition 3(2), the dual inclusion). Stated generically in `T`. -/
lemma inf_rightOrthogonal_le_isomorphisms : T ⊓ T.rightOrthogonal ≤ isomorphisms C := by
  intro X Y f hf
  obtain ⟨hfT, hfr⟩ := hf
  have hlp : HasLiftingProperty f f := (hfr f hfT).toHasLiftingProperty
  exact isIso_of_hasLiftingProperty_self f

/-- The intersection of the two classes of an orthogonal pair is exactly the
isomorphisms ([anel2009], Proposition 3(2)). -/
lemma IsOrthogonalPair.inf_eq_isomorphisms (A B : MorphismProperty C)
    [IsOrthogonalPair A B] : A ⊓ B = isomorphisms C := by
  apply le_antisymm
  · rw [← IsOrthogonalPair.left_eq (A := A) (B := B)]
    exact B.leftOrthogonal_inf_le_isomorphisms
  · intro X Y f hf
    rw [isomorphisms.iff] at hf
    have : IsIso f := hf
    constructor
    · rw [← IsOrthogonalPair.left_eq (A := A) (B := B)]
      exact B.leftOrthogonal_of_isIso f
    · rw [← IsOrthogonalPair.right_eq (A := A) (B := B)]
      exact A.rightOrthogonal_of_isIso f

/-- The right orthogonal of `T` is stable under limits of any shape `J`: a morphism
of limit cones lying over a natural transformation whose every component is right
orthogonal to `T` is itself right orthogonal to `T` ([anel2009],
Proposition 3(4)).

This has no ordinary-lifting analogue for non-discrete `J`; see
`HasUniqueLiftingProperty.of_isLimit`. The discrete-`J` case recovers stability
under products.

**Which limit this is.** The limit here is taken in `Arrow C`, so for a diagram
of quotient maps `A j ⟶ A j ⧸ I j` in `CommRingCat` the conclusion is about the
arrow `lim A j ⟶ lim (A j ⧸ I j)`. That arrow is in general *not* the quotient
map of the limit pair, which is `lim A j ⟶ (lim A j) ⧸ (lim I j)`: the two
targets differ already for a tower of surjections, since a limit of quotients
need not be the quotient by the limit ideal. The statement about the limit
*pair* is a different theorem with a different proof — it comes from
reflectivity of the right class inside the arrows of a quotient-like class (the
Phase G.2 of `cellular_presentation_plan.md`, with Stacks 0EM6 as its
corollary).

Both statements are wanted, and this one is the right tool precisely when the
morphism at hand is not known to be a quotient — for instance when surjectivity
of the right factor of a factorization is itself the hard theorem. Do not
replace it by the pair statement. -/
instance rightOrthogonal_isStableUnderLimitsOfShape (J : Type*) [Category J] :
    T.rightOrthogonal.IsStableUnderLimitsOfShape J where
  condition _ _ _ _ h₁ h₂ f hf _ hφ _ _ i hi := by
    have : ∀ j, HasUniqueLiftingProperty i (f.app j) := fun j ↦ hf j i hi
    exact HasUniqueLiftingProperty.of_isLimit f h₁ h₂ hφ i

/-- The left orthogonal of `T` is stable under colimits of any shape `J`: a morphism
of colimit cocones lying over a natural transformation whose every component is left
orthogonal to `T` is itself left orthogonal to `T` ([anel2009],
Proposition 3(4), dual).

The discrete-`J` case recovers stability under coproducts. -/
instance leftOrthogonal_isStableUnderColimitsOfShape (J : Type*) [Category J] :
    T.leftOrthogonal.IsStableUnderColimitsOfShape J where
  condition _ _ _ _ h₁ h₂ f hf _ hφ _ _ p hp := by
    have : ∀ j, HasUniqueLiftingProperty (f.app j) p := fun j ↦ hf j p hp
    exact HasUniqueLiftingProperty.of_isColimit f h₁ h₂ hφ p

/-- The left orthogonal of `T` is stable under coproducts. The
`IsStableUnderCoproductsOfShape J` field is filled from
`leftOrthogonal_isStableUnderColimitsOfShape` (a coproduct is a colimit over a
discrete shape). -/
instance leftOrthogonal_isStableUnderCoproducts :
    IsStableUnderCoproducts.{w} T.leftOrthogonal where

set_option synthInstance.checkSynthOrder false in
/-- The right class of an orthogonal pair is stable under limits of any shape `J`
([anel2009], Proposition 3(4)). -/
instance IsOrthogonalPair.right_isStableUnderLimitsOfShape (A B : MorphismProperty C)
    [IsOrthogonalPair A B] (J : Type*) [Category J] : B.IsStableUnderLimitsOfShape J := by
  rw [← IsOrthogonalPair.right_eq (A := A) (B := B)]
  infer_instance

set_option synthInstance.checkSynthOrder false in
/-- The left class of an orthogonal pair is stable under colimits of any shape `J`
([anel2009], Proposition 3(4), dual). -/
instance IsOrthogonalPair.left_isStableUnderColimitsOfShape (A B : MorphismProperty C)
    [IsOrthogonalPair A B] (J : Type*) [Category J] : A.IsStableUnderColimitsOfShape J := by
  rw [← IsOrthogonalPair.left_eq (A := A) (B := B)]
  infer_instance

end MorphismProperty

end CategoryTheory
