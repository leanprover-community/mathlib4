/-
Copyright (c) 2023 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# A functor from a small category to a filtered category factors through a small filtered category

A consequence of this is that if `C` is filtered and finally small, then `C` is also
"finally filtered-small", i.e., there is a final functor from a small filtered category to `C`.
This is occasionally useful, for example in the proof of the recognition theorem for ind-objects
(Proposition 6.1.5 in [Kashiwara2006]).
-/

universe w v v₁ u u₁

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace IsFiltered

section filteredClosure

variable [IsFilteredOrEmpty C] {α : Type w} (f : α → C)

/-- The "filtered closure" of an `α`-indexed family of objects in `C` is the set of objects in `C`
    obtained by starting with the family and successively adding maxima and coequalizers. -/
inductive filteredClosure : ObjectProperty C
  | base : (x : α) → filteredClosure (f x)
  | max : {j j' : C} → filteredClosure j → filteredClosure j' → filteredClosure (max j j')
  | coeq : {j j' : C} → filteredClosure j → filteredClosure j' → (f f' : j ⟶ j') →
      filteredClosure (coeq f f')

@[deprecated (since := "2025-03-05")] alias FilteredClosure := filteredClosure

/-- The full subcategory induced by the filtered closure of a family of objects is filtered. -/
instance : IsFilteredOrEmpty (filteredClosure f).FullSubcategory where
  cocone_objs j j' :=
    ⟨⟨max j.1 j'.1, filteredClosure.max j.2 j'.2⟩, leftToMax _ _, rightToMax _ _, trivial⟩
  cocone_maps {j j'} f f' :=
    ⟨⟨coeq f f', filteredClosure.coeq j.2 j'.2 f f'⟩, coeqHom (C := C) f f', coeq_condition _ _⟩

namespace FilteredClosureSmall
/-! Our goal for this section is to show that the size of the filtered closure of an `α`-indexed
    family of objects in `C` only depends on the size of `α` and the morphism types of `C`, not on
    the size of the objects of `C`. More precisely, if `α` lives in `Type w`, the objects of `C`
    live in `Type u` and the morphisms of `C` live in `Type v`, then we want
    `Small.{max v w} (FullSubcategory (filteredClosure f))`.

    The strategy is to define a type `AbstractFilteredClosure` which should be an inductive type
    similar to `filteredClosure`, which lives in the correct universe and surjects onto the full
    subcategory. The difficulty with this is that we need to define it at the same time as the map
    `AbstractFilteredClosure → C`, as the coequalizer constructor depends on the actual morphisms
    in `C`. This would require some kind of inductive-recursive definition, which Lean does not
    allow. Our solution is to define a function `ℕ → Σ t : Type (max v w), t → C` by (strong)
    induction and then take the union over all natural numbers, mimicking what one would do in a
    set-theoretic setting. -/

/-- One step of the inductive procedure consists of adjoining all maxima and coequalizers of all
    objects and morphisms obtained so far. This is quite redundant, picking up many objects which we
    already hit in earlier iterations, but this is easier to work with later. -/
private inductive InductiveStep (n : ℕ) (X : ∀ (k : ℕ), k < n → Σ t : Type (max v w), t → C) :
    Type (max v w)
  | max : {k k' : ℕ} → (hk : k < n) → (hk' : k' < n) → (X _ hk).1 → (X _ hk').1 → InductiveStep n X
  | coeq : {k k' : ℕ} → (hk : k < n) → (hk' : k' < n) → (j : (X _ hk).1) → (j' : (X _ hk').1) →
      ((X _ hk).2 j ⟶ (X _ hk').2 j') → ((X _ hk).2 j ⟶ (X _ hk').2 j') → InductiveStep n X

/-- The realization function sends the abstract maxima and weak coequalizers to the corresponding
    objects in `C`. -/
private noncomputable def inductiveStepRealization (n : ℕ)
    (X : ∀ (k : ℕ), k < n → Σ t : Type (max v w), t → C) : InductiveStep.{w} n X → C
  | (InductiveStep.max hk hk' x y) => max ((X _ hk).2 x) ((X _ hk').2 y)
  | (InductiveStep.coeq _ _ _ _ f g) => coeq f g

/-- All steps of building the abstract filtered closure together with the realization function,
    as a function of `ℕ`.

   The function is defined by well-founded recursion, but we really want to use its
   definitional equalities in the proofs below, so lets make it semireducible. -/
@[semireducible] private noncomputable def bundledAbstractFilteredClosure :
    ℕ → Σ t : Type (max v w), t → C
  | 0 => ⟨ULift.{v} α, f ∘ ULift.down⟩
  | (n + 1) => ⟨_, inductiveStepRealization (n + 1) (fun m _ => bundledAbstractFilteredClosure m)⟩

/-- The small type modelling the filtered closure. -/
private noncomputable def AbstractFilteredClosure : Type (max v w) :=
  Σ n, (bundledAbstractFilteredClosure f n).1

/-- The surjection from the abstract filtered closure to the actual filtered closure in `C`. -/
private noncomputable def abstractFilteredClosureRealization : AbstractFilteredClosure f → C :=
  fun x => (bundledAbstractFilteredClosure f x.1).2 x.2

end FilteredClosureSmall

theorem small_fullSubcategory_filteredClosure :
    Small.{max v w} (filteredClosure f).FullSubcategory  := by
  refine small_of_injective_of_exists (FilteredClosureSmall.abstractFilteredClosureRealization f)
    (fun _ _ => ObjectProperty.FullSubcategory.ext) ?_
  rintro ⟨j, h⟩
  induction h with
  | base x => exact ⟨⟨0, ⟨x⟩⟩, rfl⟩
  | max hj₁ hj₂ ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, FilteredClosureSmall.InductiveStep.max ?_ ?_ x y⟩, rfl⟩
    all_goals apply Nat.lt_succ_of_le
    exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]
  | coeq hj₁ hj₂ g g' ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, FilteredClosureSmall.InductiveStep.coeq ?_ ?_ x y g g'⟩, rfl⟩
    all_goals apply Nat.lt_succ_of_le
    exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]

instance : EssentiallySmall.{max v w} (filteredClosure f).FullSubcategory :=
  have : LocallySmall.{max v w} (filteredClosure f).FullSubcategory := locallySmall_max.{w, v, u}
  have := small_fullSubcategory_filteredClosure f
  essentiallySmall_of_small_of_locallySmall _

end filteredClosure

section

variable [IsFilteredOrEmpty C] {D : Type u₁} [Category.{v₁} D] (F : D ⥤ C)

/-- Every functor from a small category to a filtered category factors fully faithfully through a
    small filtered category. This is that category. -/
def SmallFilteredIntermediate : Type (max u₁ v) :=
  SmallModel.{max u₁ v} (filteredClosure F.obj).FullSubcategory

noncomputable instance : SmallCategory (SmallFilteredIntermediate F) :=
  inferInstanceAs (SmallCategory (SmallModel (filteredClosure F.obj).FullSubcategory))

namespace SmallFilteredIntermediate

/-- The first part of a factoring of a functor from a small category to a filtered category through
    a small filtered category. -/
noncomputable def factoring : D ⥤ SmallFilteredIntermediate F :=
  ObjectProperty.lift _ F filteredClosure.base ⋙ (equivSmallModel _).functor

/-- The second, fully faithful part of a factoring of a functor from a small category to a filtered
    category through a small filtered category. -/
noncomputable def inclusion : SmallFilteredIntermediate F ⥤ C :=
  (equivSmallModel _).inverse ⋙ ObjectProperty.ι _

instance : (inclusion F).Faithful :=
  inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Faithful

noncomputable instance : (inclusion F).Full :=
  inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Full

/-- The factorization through a small filtered category is in fact a factorization, up to natural
    isomorphism. -/
noncomputable def factoringCompInclusion : factoring F ⋙ inclusion F ≅ F :=
  isoWhiskerLeft _ (isoWhiskerRight (Equivalence.unitIso _).symm _)

instance : IsFilteredOrEmpty (SmallFilteredIntermediate F) :=
  IsFilteredOrEmpty.of_equivalence (equivSmallModel _)

instance [Nonempty D] : IsFiltered (SmallFilteredIntermediate F) :=
  { (inferInstance : IsFilteredOrEmpty _) with
    nonempty := Nonempty.map (factoring F).obj inferInstance }

end SmallFilteredIntermediate

end

end IsFiltered

namespace IsCofiltered

section cofilteredClosure

variable [IsCofilteredOrEmpty C] {α : Type w} (f : α → C)

/-- The "cofiltered closure" of an `α`-indexed family of objects in `C` is the set of objects in `C`
    obtained by starting with the family and successively adding minima and equalizers. -/
inductive cofilteredClosure : ObjectProperty C
  | base : (x : α) → cofilteredClosure (f x)
  | min : {j j' : C} → cofilteredClosure j → cofilteredClosure j' → cofilteredClosure (min j j')
  | eq : {j j' : C} → cofilteredClosure j → cofilteredClosure j' → (f f' : j ⟶ j') →
      cofilteredClosure (eq f f')

@[deprecated (since := "2025-03-05")] alias CofilteredClosure := cofilteredClosure

/-- The full subcategory induced by the cofiltered closure of a family is cofiltered. -/
instance : IsCofilteredOrEmpty (cofilteredClosure f).FullSubcategory where
  cone_objs j j' :=
    ⟨⟨min j.1 j'.1, cofilteredClosure.min j.2 j'.2⟩, minToLeft _ _, minToRight _ _, trivial⟩
  cone_maps {j j'} f f' :=
    ⟨⟨eq f f', cofilteredClosure.eq j.2 j'.2 f f'⟩, eqHom (C := C) f f', eq_condition _ _⟩

namespace CofilteredClosureSmall

/-- Implementation detail for the instance
    `EssentiallySmall.{max v w} (FullSubcategory (cofilteredClosure f))`. -/
private inductive InductiveStep (n : ℕ) (X : ∀ (k : ℕ), k < n → Σ t : Type (max v w), t → C) :
    Type (max v w)
  | min : {k k' : ℕ} → (hk : k < n) → (hk' : k' < n) → (X _ hk).1 → (X _ hk').1 → InductiveStep n X
  | eq : {k k' : ℕ} → (hk : k < n) → (hk' : k' < n) → (j : (X _ hk).1) → (j' : (X _ hk').1) →
      ((X _ hk).2 j ⟶ (X _ hk').2 j') → ((X _ hk).2 j ⟶ (X _ hk').2 j') → InductiveStep n X

/-- Implementation detail for the instance
    `EssentiallySmall.{max v w} (FullSubcategory (cofilteredClosure f))`. -/
private noncomputable def inductiveStepRealization (n : ℕ)
    (X : ∀ (k : ℕ), k < n → Σ t : Type (max v w), t → C) : InductiveStep.{w} n X → C
  | (InductiveStep.min hk hk' x y) => min ((X _ hk).2 x) ((X _ hk').2 y)
  | (InductiveStep.eq _ _ _ _ f g) => eq f g

/-- Implementation detail for the instance
   `EssentiallySmall.{max v w} (FullSubcategory (cofilteredClosure f))`.

   The function is defined by well-founded recursion, but we really want to use its
   definitional equalities in the proofs below, so lets make it semireducible. -/
@[semireducible] private noncomputable def bundledAbstractCofilteredClosure :
    ℕ → Σ t : Type (max v w), t → C
  | 0 => ⟨ULift.{v} α, f ∘ ULift.down⟩
  | (n + 1) => ⟨_, inductiveStepRealization (n + 1) (fun m _ => bundledAbstractCofilteredClosure m)⟩

/-- Implementation detail for the instance
    `EssentiallySmall.{max v w} (FullSubcategory (cofilteredClosure f))`. -/
private noncomputable def AbstractCofilteredClosure : Type (max v w) :=
  Σ n, (bundledAbstractCofilteredClosure f n).1

/-- Implementation detail for the instance
    `EssentiallySmall.{max v w} (FullSubcategory (cofilteredClosure f))`. -/
private noncomputable def abstractCofilteredClosureRealization : AbstractCofilteredClosure f → C :=
  fun x => (bundledAbstractCofilteredClosure f x.1).2 x.2

end CofilteredClosureSmall

theorem small_fullSubcategory_cofilteredClosure :
    Small.{max v w} (cofilteredClosure f).FullSubcategory := by
  refine small_of_injective_of_exists
    (CofilteredClosureSmall.abstractCofilteredClosureRealization f)
    (fun _ _ => ObjectProperty.FullSubcategory.ext) ?_
  rintro ⟨j, h⟩
  induction h with
  | base x => exact ⟨⟨0, ⟨x⟩⟩, rfl⟩
  | min hj₁ hj₂ ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, CofilteredClosureSmall.InductiveStep.min ?_ ?_ x y⟩, rfl⟩
    all_goals apply Nat.lt_succ_of_le
    exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]
  | eq hj₁ hj₂ g g' ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, CofilteredClosureSmall.InductiveStep.eq ?_ ?_ x y g g'⟩, rfl⟩
    all_goals apply Nat.lt_succ_of_le
    exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]

instance : EssentiallySmall.{max v w} (cofilteredClosure f).FullSubcategory :=
  have : LocallySmall.{max v w} (cofilteredClosure f).FullSubcategory :=
    locallySmall_max.{w, v, u}
  have := small_fullSubcategory_cofilteredClosure f
  essentiallySmall_of_small_of_locallySmall _

end cofilteredClosure

section

variable [IsCofilteredOrEmpty C] {D : Type u₁} [Category.{v₁} D] (F : D ⥤ C)

/-- Every functor from a small category to a cofiltered category factors fully faithfully through a
    small cofiltered category. This is that category. -/
def SmallCofilteredIntermediate : Type (max u₁ v) :=
  SmallModel.{max u₁ v} (cofilteredClosure F.obj).FullSubcategory

noncomputable instance : SmallCategory (SmallCofilteredIntermediate F) :=
  inferInstanceAs (SmallCategory (SmallModel (cofilteredClosure F.obj).FullSubcategory))

namespace SmallCofilteredIntermediate

/-- The first part of a factoring of a functor from a small category to a cofiltered category
    through a small filtered category. -/
noncomputable def factoring : D ⥤ SmallCofilteredIntermediate F :=
  ObjectProperty.lift _ F cofilteredClosure.base ⋙ (equivSmallModel _).functor

/-- The second, fully faithful part of a factoring of a functor from a small category to a filtered
    category through a small filtered category. -/
noncomputable def inclusion : SmallCofilteredIntermediate F ⥤ C :=
  (equivSmallModel _).inverse ⋙ ObjectProperty.ι _

instance : (inclusion F).Faithful :=
  inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Faithful

noncomputable instance : (inclusion F).Full :=
  inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Full

/-- The factorization through a small filtered category is in fact a factorization, up to natural
    isomorphism. -/
noncomputable def factoringCompInclusion : factoring F ⋙ inclusion F ≅ F :=
  isoWhiskerLeft _ (isoWhiskerRight (Equivalence.unitIso _).symm _)

instance : IsCofilteredOrEmpty (SmallCofilteredIntermediate F) :=
  IsCofilteredOrEmpty.of_equivalence (equivSmallModel _)

instance [Nonempty D] : IsCofiltered (SmallCofilteredIntermediate F) :=
  { (inferInstance : IsCofilteredOrEmpty _) with
    nonempty := Nonempty.map (factoring F).obj inferInstance }

end SmallCofilteredIntermediate

end

end IsCofiltered

end CategoryTheory
