/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

import Mathlib.Data.Fin.VecNotation

/-!
# Filtered categories

A category is filtered if every finite diagram admits a cocone.
We give a simple characterisation of this condition as
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object.

An important example of filtered category is given by nonempty directed types;
actually, filtered categories may be considered as a generalization of nonempty directed types.
In the file `CategoryTheory.Presentable.Directed`, we show that "conversely"
if `C` is a filtered category, there exists a final functor `α ⥤ C` from
a nonempty directed type (`IsFiltered.isDirected`).

Filtered colimits are often better behaved than arbitrary colimits.
See `Mathlib/CategoryTheory/Limits/Types/` for some details.

Filtered categories are nice because colimits indexed by filtered categories tend to be
easier to describe than general colimits (and more often preserved by functors).

In this file we show that any functor from a finite category to a filtered category admits a cocone:
* `cocone_nonempty [FinCategory J] [IsFiltered C] (F : J ⥤ C) : Nonempty (Cocone F)`

More generally,
for any finite collection of objects and morphisms between them in a filtered category
(even if not closed under composition) there exists some object `Z` receiving maps from all of them,
so that all the triangles (one edge from the finite set, two from morphisms to `Z`) commute.
This formulation is often more useful in practice and is available via `sup_exists`,
which takes a finset of objects, and an indexed family (indexed by source and target)
of finsets of morphisms.

We also prove the converse of `cocone_nonempty` as `of_cocone_nonempty`.

Furthermore, we give special support for two diagram categories: The `bowtie` and the `tulip`.
This is because these shapes show up in the proofs that forgetful functors of algebraic categories
(e.g. `MonCat`, `CommRingCat`, ...) preserve filtered colimits.

All of the above API, except for the `bowtie` and the `tulip`, is also provided for cofiltered
categories.

## See also
In `Mathlib/CategoryTheory/Limits/FilteredColimitCommutesFiniteLimit.lean` we show that filtered
colimits commute with finite limits.

There is another characterization of filtered categories, namely that whenever `F : J ⥤ C` is a
functor from a finite category, there is `X : C` such that `Nonempty (limit (F.op ⋙ yoneda.obj X))`.
This is shown in `Mathlib/CategoryTheory/Limits/Filtered.lean`.
-/

public section


open Function

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory

attribute [local instance] uliftCategory

variable (C : Type u) [Category.{v} C]

to_dual_name_hint Coeq Eq, Left Right

/-- A category `IsFilteredOrEmpty` if
1. for every pair of objects there exists another object "to the right", and
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal.
-/
class IsFilteredOrEmpty : Prop where
  /-- for every pair of objects there exists another object "to the right" -/
  cocone_objs : ∀ X Y : C, ∃ (Z : _) (_ : X ⟶ Z) (_ : Y ⟶ Z), True
  /-- for every pair of parallel morphisms there exists a morphism to the right
  so the compositions are equal -/
  cocone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ (Z : _) (h : Y ⟶ Z), f ≫ h = g ≫ h

/--
A category `IsCofilteredOrEmpty` if
1. for every pair of objects there exists another object "to the left", and
2. for every pair of parallel morphisms there exists a morphism to the left so the compositions
   are equal.
-/
@[to_dual]
class IsCofilteredOrEmpty : Prop where
  /-- for every pair of objects there exists another object "to the left" -/
  cone_objs : ∀ X Y : C, ∃ (W : _) (_ : W ⟶ X) (_ : W ⟶ Y), True
  /-- for every pair of parallel morphisms there exists a morphism to the left
  so the compositions are equal -/
  cone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ (W : _) (h : W ⟶ X), h ≫ f = h ≫ g

/-- A category `IsFiltered` if
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object. -/
@[stacks 002V "They also define a diagram being filtered."]
class IsFiltered : Prop extends IsFilteredOrEmpty C where
  /-- a filtered category must be non-empty -/
  -- This should be an instance but it causes significant slowdown
  [nonempty : Nonempty C]

/-- A category `IsCofiltered` if
1. for every pair of objects there exists another object "to the left",
2. for every pair of parallel morphisms there exists a morphism to the left so the compositions
   are equal, and
3. there exists some object. -/
@[stacks 04AZ, to_dual]
class IsCofiltered : Prop extends IsCofilteredOrEmpty C where
  /-- a cofiltered category must be non-empty -/
  -- This should be an instance but it causes significant slowdown
  [nonempty : Nonempty C]

@[to_dual]
instance (priority := 100) isFilteredOrEmpty_of_semilatticeSup (α : Type u) [SemilatticeSup α] :
    IsFilteredOrEmpty α where
  cocone_objs X Y := ⟨X ⊔ Y, homOfLE le_sup_left, homOfLE le_sup_right, trivial⟩
  cocone_maps X Y f g := ⟨Y, 𝟙 _, by subsingleton⟩

@[to_dual]
instance (priority := 100) isFiltered_of_semilatticeSup_nonempty (α : Type u) [SemilatticeSup α]
    [Nonempty α] : IsFiltered α where

@[to_dual]
instance (priority := 100) (α : Type u) [Preorder α]
    [IsDirectedOrder α] : IsFilteredOrEmpty α where
  cocone_objs X Y :=
    let ⟨Z, h1, h2⟩ := exists_ge_ge X Y
    ⟨Z, homOfLE h1, homOfLE h2, trivial⟩
  cocone_maps X Y f g := ⟨Y, 𝟙 _, by subsingleton⟩

@[to_dual]
instance (priority := 100) (α : Type u) [Preorder α]
    [IsDirectedOrder α] [Nonempty α] : IsFiltered α where

-- Sanity checks
example (α : Type u) [SemilatticeSup α] [OrderBot α] : IsFiltered α := by infer_instance

example (α : Type u) [SemilatticeSup α] [OrderTop α] : IsFiltered α := by infer_instance

@[to_dual]
instance : IsFiltered (Discrete PUnit) where
  cocone_objs X Y := ⟨⟨PUnit.unit⟩, ⟨by trivial⟩, ⟨by subsingleton⟩, trivial⟩
  cocone_maps X Y f g := ⟨⟨PUnit.unit⟩, ⟨by trivial⟩, by subsingleton⟩

namespace IsFiltered

section AllowEmpty

variable {C}
variable [IsFilteredOrEmpty C]

/-- `max j j'` is an arbitrary choice of object to the right of both `j` and `j'`,
whose existence is ensured by `IsFiltered`.
-/
@[to_dual
/-- `min j j'` is an arbitrary choice of object to the left of both `j` and `j'`,
whose existence is ensured by `IsCofiltered`.
-/]
noncomputable def max (j j' : C) : C :=
  (IsFilteredOrEmpty.cocone_objs j j').choose

/-- `leftToMax j j'` is an arbitrary choice of morphism from `j` to `max j j'`,
whose existence is ensured by `IsFiltered`.
-/
@[to_dual minToLeft
/-- `minToLeft j j'` is an arbitrary choice of morphism from `min j j'` to `j`,
whose existence is ensured by `IsCofiltered`.
-/]
noncomputable def leftToMax (j j' : C) : j ⟶ max j j' :=
  (IsFilteredOrEmpty.cocone_objs j j').choose_spec.choose

/-- `rightToMax j j'` is an arbitrary choice of morphism from `j'` to `max j j'`,
whose existence is ensured by `IsFiltered`.
-/
@[to_dual minToRight
/-- `minToRight j j'` is an arbitrary choice of morphism from `min j j'` to `j'`,
whose existence is ensured by `IsCofiltered`.
-/]
noncomputable def rightToMax (j j' : C) : j' ⟶ max j j' :=
  (IsFilteredOrEmpty.cocone_objs j j').choose_spec.choose_spec.choose

/-- `coeq f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of object
which admits a morphism `coeqHom f f' : j' ⟶ coeq f f'` such that
`coeq_condition : f ≫ coeqHom f f' = f' ≫ coeqHom f f'`.
Its existence is ensured by `IsFiltered`.
-/
@[to_dual
/-- `eq f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of object
which admits a morphism `eqHom f f' : eq f f' ⟶ j` such that
`eq_condition : eqHom f f' ≫ f = eqHom f f' ≫ f'`.
Its existence is ensured by `IsCofiltered`.
-/]
noncomputable def coeq {j j' : C} (f f' : j ⟶ j') : C :=
  (IsFilteredOrEmpty.cocone_maps f f').choose

/-- `coeqHom f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of morphism
`coeqHom f f' : j' ⟶ coeq f f'` such that
`coeq_condition : f ≫ coeqHom f f' = f' ≫ coeqHom f f'`.
Its existence is ensured by `IsFiltered`.
-/
@[to_dual
/-- `eqHom f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of morphism
`eqHom f f' : eq f f' ⟶ j` such that
`eq_condition : eqHom f f' ≫ f = eqHom f f' ≫ f'`.
Its existence is ensured by `IsCofiltered`.
-/]
noncomputable def coeqHom {j j' : C} (f f' : j ⟶ j') : j' ⟶ coeq f f' :=
  (IsFilteredOrEmpty.cocone_maps f f').choose_spec.choose

/-- `coeq_condition f f'`, for morphisms `f f' : j ⟶ j'`, is the proof that
`f ≫ coeqHom f f' = f' ≫ coeqHom f f'`.
-/
-- Not `@[simp]` as it does not fire.
@[to_dual (attr := reassoc)
/-- `eq_condition f f'`, for morphisms `f f' : j ⟶ j'`, is the proof that
`eqHom f f' ≫ f = eqHom f f' ≫ f'`.
-/]
theorem coeq_condition {j j' : C} (f f' : j ⟶ j') : f ≫ coeqHom f f' = f' ≫ coeqHom f f' :=
  (IsFilteredOrEmpty.cocone_maps f f').choose_spec.choose_spec

end AllowEmpty

@[to_dual]
lemma isDirectedOrder (α : Type u) [Preorder α] [IsFiltered α] :
    IsDirectedOrder α where
  directed i j := ⟨max i j, leOfHom (leftToMax i j), leOfHom (rightToMax i j)⟩

end IsFiltered

namespace IsFilteredOrEmpty
open IsFiltered

variable {C}
variable [IsFilteredOrEmpty C]
variable {D : Type u₁} [Category.{v₁} D]

/-- If `C` is filtered or empty, and we have a functor `R : C ⥤ D` with a left adjoint, then `D` is
filtered or empty.
-/
@[to_dual
/-- If `C` is cofiltered or empty, and we have a functor `L : C ⥤ D` with a right adjoint,
then `D` is cofiltered or empty.
-/]
theorem of_right_adjoint {L : D ⥤ C} {R : C ⥤ D} (h : L ⊣ R) : IsFilteredOrEmpty D :=
  { cocone_objs := fun X Y =>
      ⟨R.obj (max (L.obj X) (L.obj Y)),
        h.homEquiv _ _ (leftToMax _ _), h.homEquiv _ _ (rightToMax _ _), ⟨⟩⟩
    cocone_maps := fun X Y f g =>
      ⟨R.obj (coeq (L.map f) (L.map g)), h.homEquiv _ _ (coeqHom _ _), by
        rw [← h.homEquiv_naturality_left, ← h.homEquiv_naturality_left, coeq_condition]⟩ }

/-- If `C` is filtered or empty, and we have a right adjoint functor `R : C ⥤ D`, then `D` is
filtered or empty. -/
@[to_dual
/-- If `C` is cofiltered or empty, and we have a left adjoint functor `L : C ⥤ D`, then `D` is
cofiltered or empty. -/]
theorem of_isRightAdjoint (R : C ⥤ D) [R.IsRightAdjoint] : IsFilteredOrEmpty D :=
  of_right_adjoint (Adjunction.ofIsRightAdjoint R)

/-- Being filtered or empty is preserved by equivalence of categories. -/
@[to_dual /-- Being cofiltered or empty is preserved by equivalence of categories. -/]
theorem of_equivalence (h : C ≌ D) : IsFilteredOrEmpty D :=
  of_right_adjoint h.symm.toAdjunction

end IsFilteredOrEmpty

namespace IsFiltered

section Nonempty

open CategoryTheory.Limits

variable {C}
variable [IsFiltered C]

/-- Any finite collection of objects in a filtered category has an object "to the right".
-/
@[to_dual
/-- Any finite collection of objects in a cofiltered category has an object "to the left".
-/]
theorem sup_objs_exists (O : Finset C) : ∃ S : C, ∀ {X}, X ∈ O → Nonempty (X ⟶ S) := by
  classical
  induction O using Finset.induction with
  | empty => exact ⟨Classical.choice IsFiltered.nonempty, by simp⟩
  | insert X O' nm h =>
    obtain ⟨S', w'⟩ := h
    use max X S'
    rintro Y mY
    obtain rfl | h := eq_or_ne Y X
    · exact ⟨leftToMax _ _⟩
    · exact ⟨(w' (Finset.mem_of_mem_insert_of_ne mY h)).some ≫ rightToMax _ _⟩

variable (O : Finset C) (H : Finset (Σ' (X Y : C) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y))

/-- Given any `Finset` of objects `{X, ...}` and
indexed collection of `Finset`s of morphisms `{f, ...}` in `C`,
there exists an object `S`, with a morphism `T X : X ⟶ S` from each `X`,
such that the triangles commute: `f ≫ T Y = T X`, for `f : X ⟶ Y` in the `Finset`.
-/
@[to_dual
/-- Given any `Finset` of objects `{X, ...}` and
indexed collection of `Finset`s of morphisms `{f, ...}` in `C`,
there exists an object `S`, with a morphism `T X : S ⟶ X` from each `X`,
such that the triangles commute: `T X ≫ f = T Y`, for `f : X ⟶ Y` in the `Finset`.
-/]
theorem sup_exists :
    ∃ (S : C) (T : ∀ {X : C}, X ∈ O → (X ⟶ S)),
      ∀ {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y},
        (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) ∈ H →
          f ≫ T mY = T mX := by
  classical
  induction H using Finset.induction with
  | empty =>
    obtain ⟨S, f⟩ := sup_objs_exists O
    exact ⟨S, fun mX => (f mX).some, by rintro - - - - - ⟨⟩⟩
  | insert h' H' nmf h'' =>
    obtain ⟨X, Y, mX, mY, f⟩ := h'
    obtain ⟨S', T', w'⟩ := h''
    refine ⟨coeq (f ≫ T' mY) (T' mX), fun mZ => T' mZ ≫ coeqHom (f ≫ T' mY) (T' mX), ?_⟩
    intro X' Y' mX' mY' f' mf'
    rw [← Category.assoc]
    by_cases h : X = X' ∧ Y = Y'
    · rcases h with ⟨rfl, rfl⟩
      grind [coeq_condition]
    · rw [@w' _ _ mX' mY' f' _]
      apply Finset.mem_of_mem_insert_of_ne mf'
      contrapose h
      obtain ⟨rfl, h⟩ := h
      trivial

/-- An arbitrary choice of object "to the right"
of a finite collection of objects `O` and morphisms `H`,
making all the triangles commute.
-/
@[to_dual
/-- An arbitrary choice of object "to the left"
of a finite collection of objects `O` and morphisms `H`,
making all the triangles commute.
-/]
noncomputable def sup : C :=
  (sup_exists O H).choose

/-- The morphisms to `sup O H`. -/
@[to_dual infTo /-- The morphisms from `inf O H`. -/]
noncomputable def toSup {X : C} (m : X ∈ O) : X ⟶ sup O H :=
  (sup_exists O H).choose_spec.choose m

/-- The triangles of consisting of a morphism in `H` and the maps to `sup O H` commute.
-/
@[to_dual infTo_commutes
/-- The triangles consisting of a morphism in `H` and the maps from `inf O H` commute.
-/]
theorem toSup_commutes {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y}
    (mf : (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) ∈ H) :
    f ≫ toSup O H mY = toSup O H mX :=
  (sup_exists O H).choose_spec.choose_spec mX mY mf

variable {J : Type w} [SmallCategory J] [FinCategory J]

/-- If we have `IsFiltered C`, then for any functor `F : J ⥤ C` with `FinCategory J`,
there exists a cocone over `F`.
-/
@[to_dual
/-- If we have `IsCofiltered C`, then for any functor `F : J ⥤ C` with `FinCategory J`,
there exists a cone over `F`.
-/]
theorem cocone_nonempty (F : J ⥤ C) : Nonempty (Cocone F) := by
  classical
  let O := Finset.univ.image F.obj
  let H : Finset (Σ' (X Y : C) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
    Finset.univ.biUnion fun X : J => Finset.univ.biUnion fun Y : J =>
      Finset.univ.image fun f : X ⟶ Y => ⟨F.obj X, F.obj Y, by simp [O], by simp [O], F.map f⟩
  obtain ⟨Z, f, w⟩ := sup_exists O H
  refine ⟨⟨Z, ⟨fun X => f (by simp [O]), ?_⟩⟩⟩
  intro j j' g
  dsimp
  simp only [Category.comp_id]
  apply w
  simp only [O, H, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, PSigma.mk.injEq,
    true_and, exists_and_left]
  exact ⟨j, rfl, j', g, by simp⟩

/-- An arbitrary choice of cocone over `F : J ⥤ C`, for `FinCategory J` and `IsFiltered C`.
-/
@[to_dual
/-- An arbitrary choice of cone over `F : J ⥤ C`, for `FinCategory J` and `IsCofiltered C`.
-/]
noncomputable def cocone (F : J ⥤ C) : Cocone F :=
  (cocone_nonempty F).some

variable {D : Type u₁} [Category.{v₁} D]

/-- If `C` is filtered, and we have a functor `R : C ⥤ D` with a left adjoint, then `D` is filtered.
-/
@[to_dual (rename := R ↔ L)
/-- If `C` is cofiltered, and we have a functor `L : C ⥤ D` with a right adjoint,
then `D` is cofiltered.
-/]
theorem of_right_adjoint {L : D ⥤ C} {R : C ⥤ D} (h : L ⊣ R) : IsFiltered D :=
  { IsFilteredOrEmpty.of_right_adjoint h with
    nonempty := IsFiltered.nonempty.map R.obj }

/-- If `C` is filtered, and we have a right adjoint functor `R : C ⥤ D`, then `D` is filtered. -/
@[to_dual (rename := R → L)
/-- If `C` is cofiltered, and we have a left adjoint functor `L : C ⥤ D`, then `D` is cofiltered. -/
]
theorem of_isRightAdjoint (R : C ⥤ D) [R.IsRightAdjoint] : IsFiltered D :=
  of_right_adjoint (Adjunction.ofIsRightAdjoint R)

/-- Being filtered is preserved by equivalence of categories. -/
@[to_dual /-- Being cofiltered is preserved by equivalence of categories. -/]
theorem of_equivalence (h : C ≌ D) : IsFiltered D :=
  of_right_adjoint h.symm.toAdjunction

omit [IsFiltered C] in
@[to_dual]
lemma iff_of_equivalence (e : C ≌ D) : IsFiltered C ↔ IsFiltered D :=
  ⟨fun _ ↦ .of_equivalence e, fun _ ↦ .of_equivalence e.symm⟩

end Nonempty

section OfCocone

open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
/-- If every finite diagram in `C` admits a cocone, then `C` is filtered. It is sufficient to verify
this for diagrams whose shape lives in any one fixed universe. -/
@[to_dual
/-- If every finite diagram in `C` admits a cone, then `C` is cofiltered. It is sufficient to
verify this for diagrams whose shape lives in any one fixed universe. -/]
theorem of_cocone_nonempty (h : ∀ {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
    Nonempty (Cocone F)) : IsFiltered C := by
  have : Nonempty C := by
    obtain ⟨c⟩ := h (Functor.empty _)
    exact ⟨c.pt⟩
  have : IsFilteredOrEmpty C := by
    refine ⟨?_, ?_⟩
    · intro X Y
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y)
      exact ⟨c.pt, c.ι.app ⟨⟨WalkingPair.left⟩⟩, c.ι.app ⟨⟨WalkingPair.right⟩⟩, trivial⟩
    · intro X Y f g
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      refine ⟨c.pt, c.ι.app ⟨WalkingParallelPair.one⟩, ?_⟩
      have h₁ := c.ι.naturality ⟨WalkingParallelPairHom.left⟩
      have h₂ := c.ι.naturality ⟨WalkingParallelPairHom.right⟩
      simp_all
  apply IsFiltered.mk

@[to_dual]
theorem of_hasFiniteColimits [HasFiniteColimits C] : IsFiltered C :=
  of_cocone_nonempty.{v} C fun F => ⟨colimit.cocone F⟩

@[to_dual]
theorem of_isTerminal {X : C} (h : IsTerminal X) : IsFiltered C :=
  of_cocone_nonempty.{v} _ fun {_} _ _ _ => ⟨⟨X, ⟨fun _ => h.from _, fun _ _ _ => h.hom_ext _ _⟩⟩⟩

@[to_dual]
instance (priority := 100) of_hasTerminal [HasTerminal C] : IsFiltered C :=
  of_isTerminal _ terminalIsTerminal

/-- For every universe `w`, `C` is filtered if and only if every finite diagram in `C` with shape
in `w` admits a cocone. -/
@[to_dual
/-- For every universe `w`, `C` is filtered if and only if every finite diagram in `C` with shape
in `w` admits a cocone. -/]
theorem iff_cocone_nonempty : IsFiltered C ↔
    ∀ {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C), Nonempty (Cocone F) :=
  ⟨fun _ _ _ _ F => cocone_nonempty F, of_cocone_nonempty C⟩

end OfCocone

section SpecialShapes

variable {C}
variable [IsFilteredOrEmpty C]

/-- `max₃ j₁ j₂ j₃` is an arbitrary choice of object to the right of `j₁`, `j₂` and `j₃`,
whose existence is ensured by `IsFiltered`.
-/
noncomputable def max₃ (j₁ j₂ j₃ : C) : C :=
  max (max j₁ j₂) j₃

/-- `firstToMax₃ j₁ j₂ j₃` is an arbitrary choice of morphism from `j₁` to `max₃ j₁ j₂ j₃`,
whose existence is ensured by `IsFiltered`.
-/
noncomputable def firstToMax₃ (j₁ j₂ j₃ : C) : j₁ ⟶ max₃ j₁ j₂ j₃ :=
  leftToMax j₁ j₂ ≫ leftToMax (max j₁ j₂) j₃

/-- `secondToMax₃ j₁ j₂ j₃` is an arbitrary choice of morphism from `j₂` to `max₃ j₁ j₂ j₃`,
whose existence is ensured by `IsFiltered`.
-/
noncomputable def secondToMax₃ (j₁ j₂ j₃ : C) : j₂ ⟶ max₃ j₁ j₂ j₃ :=
  rightToMax j₁ j₂ ≫ leftToMax (max j₁ j₂) j₃

/-- `thirdToMax₃ j₁ j₂ j₃` is an arbitrary choice of morphism from `j₃` to `max₃ j₁ j₂ j₃`,
whose existence is ensured by `IsFiltered`.
-/
noncomputable def thirdToMax₃ (j₁ j₂ j₃ : C) : j₃ ⟶ max₃ j₁ j₂ j₃ :=
  rightToMax (max j₁ j₂) j₃

/-- `coeq₃ f g h`, for morphisms `f g h : j₁ ⟶ j₂`, is an arbitrary choice of object
which admits a morphism `coeq₃Hom f g h : j₂ ⟶ coeq₃ f g h` such that
`coeq₃_condition₁`, `coeq₃_condition₂` and `coeq₃_condition₃` are satisfied.
Its existence is ensured by `IsFiltered`.
-/
noncomputable def coeq₃ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : C :=
  coeq (coeqHom f g ≫ leftToMax (coeq f g) (coeq g h))
    (coeqHom g h ≫ rightToMax (coeq f g) (coeq g h))

/-- `coeq₃Hom f g h`, for morphisms `f g h : j₁ ⟶ j₂`, is an arbitrary choice of morphism
`j₂ ⟶ coeq₃ f g h` such that `coeq₃_condition₁`, `coeq₃_condition₂` and `coeq₃_condition₃`
are satisfied. Its existence is ensured by `IsFiltered`.
-/
noncomputable def coeq₃Hom {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : j₂ ⟶ coeq₃ f g h :=
  coeqHom f g ≫
    leftToMax (coeq f g) (coeq g h) ≫
      coeqHom (coeqHom f g ≫ leftToMax (coeq f g) (coeq g h))
        (coeqHom g h ≫ rightToMax (coeq f g) (coeq g h))

theorem coeq₃_condition₁ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) :
    f ≫ coeq₃Hom f g h = g ≫ coeq₃Hom f g h := by
  simp only [coeq₃Hom, ← Category.assoc, coeq_condition f g]

set_option backward.isDefEq.respectTransparency false in
theorem coeq₃_condition₂ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) :
    g ≫ coeq₃Hom f g h = h ≫ coeq₃Hom f g h := by
  dsimp [coeq₃Hom]
  slice_lhs 2 4 => rw [← Category.assoc, coeq_condition _ _]
  slice_rhs 2 4 => rw [← Category.assoc, coeq_condition _ _]
  slice_lhs 1 3 => rw [← Category.assoc, coeq_condition _ _]
  simp only [Category.assoc]

theorem coeq₃_condition₃ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : f ≫ coeq₃Hom f g h = h ≫ coeq₃Hom f g h :=
  Eq.trans (coeq₃_condition₁ f g h) (coeq₃_condition₂ f g h)

/-- For every span `j ⟵ i ⟶ j'`, there exists a cocone `j ⟶ k ⟵ j'` such that the square
commutes. -/
@[to_dual
/-- For every cospan `j ⟶ i ⟵ j'`,
there exists a cone `j ⟵ k ⟶ j'` such that the square commutes. -/]
theorem span {i j j' : C} (f : i ⟶ j) (f' : i ⟶ j') :
    ∃ (k : C) (g : j ⟶ k) (g' : j' ⟶ k), f ≫ g = f' ≫ g' :=
  let ⟨K, G, G', _⟩ := IsFilteredOrEmpty.cocone_objs j j'
  let ⟨k, e, he⟩ := IsFilteredOrEmpty.cocone_maps (f ≫ G) (f' ≫ G')
  ⟨k, G ≫ e, G' ≫ e, by simpa only [← Category.assoc] ⟩

/-- Given a "bowtie" of morphisms
```
 j₁   j₂
 |\  /|
 | \/ |
 | /\ |
 |/  \∣
 vv  vv
 k₁  k₂
```
in a filtered category, we can construct an object `s` and two morphisms from `k₁` and `k₂` to `s`,
making the resulting squares commute.
-/
@[to_dual
/-- Given a "bowtie" of morphisms
```
 k₁   k₂
 |\  /|
 | \/ |
 | /\ |
 |/  \∣
 vv  vv
 j₁  j₂
```
in a cofiltered category, we can construct an object `s` and two morphisms
from `s` to `k₁` and `k₂`, making the resulting squares commute.
-/]
theorem bowtie {j₁ j₂ k₁ k₂ : C} (f₁ : j₁ ⟶ k₁) (g₁ : j₁ ⟶ k₂) (f₂ : j₂ ⟶ k₁) (g₂ : j₂ ⟶ k₂) :
    ∃ (s : C) (α : k₁ ⟶ s) (β : k₂ ⟶ s), f₁ ≫ α = g₁ ≫ β ∧ f₂ ≫ α = g₂ ≫ β := by
  obtain ⟨t, k₁t, k₂t, ht⟩ := span f₁ g₁
  obtain ⟨s, ts, hs⟩ := IsFilteredOrEmpty.cocone_maps (f₂ ≫ k₁t) (g₂ ≫ k₂t)
  simp_rw [Category.assoc] at hs
  exact ⟨s, k₁t ≫ ts, k₂t ≫ ts, by simp only [← Category.assoc, ht], hs⟩

/-- Given a "crown" of morphisms
```
  j₁   j₂   j₃  ... jₙ
 /  \  /\  /  \
|    \/  \/    |
|    /\  /\    |
|   |  \/  |   |
 \  |  /\  |  /
  \ | /  \ | /
   vvv    vvv
    k₁    k₂
```
in a filtered category, we can construct an object `s` and two morphisms from `k₁` and `k₂` to `s`,
making the resulting squares commute.
-/
theorem crown
    {ι : Type*} [Finite ι] (j : ι → C) {k₁ k₂ : C} (f : ∀ i, j i ⟶ k₁) (g : ∀ i, j i ⟶ k₂) :
    ∃ (s : C) (α : k₁ ⟶ s) (β : k₂ ⟶ s), ∀ i, f i ≫ α = g i ≫ β := by
  induction ι using Finite.induction_empty_option with
  | @of_equiv ι₁ ι₂ e IH =>
    obtain ⟨s, α, β, H⟩ := IH (j ∘ e) (f <| e ·) (g <| e ·)
    exact ⟨s, α, β, e.forall_congr_right.mp H⟩
  | h_empty => exact ⟨max k₁ k₂, leftToMax k₁ k₂, rightToMax k₁ k₂, by simp⟩
  | @h_option ι _ IH =>
    obtain ⟨s₁, α₁, β₁, H₁⟩ := IH (j ·) (f ·) (g ·)
    obtain ⟨s₂, α₂, β₂, H₂⟩ := span (f .none) (g .none)
    obtain ⟨t, α, β, h₁, h₂⟩ := bowtie α₁ α₂ β₁ β₂
    exact ⟨t, α₁ ≫ α, β₁ ≫ α, Option.rec (by grind) (by grind)⟩

/-- Given a "crown" of morphisms
```
  j₁   j₂   j₃
 /  \  /\  /  \
|    \/  \/    |
|    /\  /\    |
|   |  \/  |   |
 \  |  /\  |  /
  \ | /  \ | /
   vvv    vvv
    k₁    k₂
```
in a filtered category, we can construct an object `s` and two morphisms from `k₁` and `k₂` to `s`,
making the resulting squares commute.
-/
theorem crown₃
    {j₁ j₂ j₃ k₁ k₂ : C} (f₁ : j₁ ⟶ k₁) (g₁ : j₁ ⟶ k₂) (f₂ : j₂ ⟶ k₁)
    (g₂ : j₂ ⟶ k₂) (f₃ : j₃ ⟶ k₁) (g₃ : j₃ ⟶ k₂) :
    ∃ (s : C) (α : k₁ ⟶ s) (β : k₂ ⟶ s),
      f₁ ≫ α = g₁ ≫ β ∧ f₂ ≫ α = g₂ ≫ β ∧ f₃ ≫ α = g₃ ≫ β := by
  obtain ⟨s, α, β, H⟩ := crown ![j₁, j₂, j₃] (Fin.cons f₁ (Fin.cons f₂ (Fin.cons f₃ nofun)))
     (Fin.cons g₁ (Fin.cons g₂ (Fin.cons g₃ nofun)))
  exact ⟨s, α, β, H 0, H 1, H 2⟩

theorem crown₄
    {j₁ j₂ j₃ j₄ k₁ k₂ : C} (f₁ : j₁ ⟶ k₁) (g₁ : j₁ ⟶ k₂) (f₂ : j₂ ⟶ k₁)
    (g₂ : j₂ ⟶ k₂) (f₃ : j₃ ⟶ k₁) (g₃ : j₃ ⟶ k₂) (f₄ : j₄ ⟶ k₁) (g₄ : j₄ ⟶ k₂) :
    ∃ (s : C) (α : k₁ ⟶ s) (β : k₂ ⟶ s),
      f₁ ≫ α = g₁ ≫ β ∧ f₂ ≫ α = g₂ ≫ β ∧ f₃ ≫ α = g₃ ≫ β ∧ f₄ ≫ α = g₄ ≫ β := by
  obtain ⟨s, α, β, H⟩ := crown ![j₁, j₂, j₃, j₄]
      (Fin.cons f₁ (Fin.cons f₂ (Fin.cons f₃ (Fin.cons f₄ nofun))))
     (Fin.cons g₁ (Fin.cons g₂ (Fin.cons g₃ (Fin.cons g₄ nofun))))
  exact ⟨s, α, β, H 0, H 1, H 2, H 3⟩

/-- Given a "tulip" of morphisms
```
 j₁    j₂    j₃
 |\   / \   / |
 | \ /   \ /  |
 |  vv    vv  |
 \  k₁    k₂ /
  \         /
   \       /
    \     /
     \   /
      v v
       l
```
in a filtered category, we can construct an object `s` and three morphisms from `k₁`, `k₂` and `l`
to `s`, making the resulting squares commute.
-/
theorem tulip {j₁ j₂ j₃ k₁ k₂ l : C} (f₁ : j₁ ⟶ k₁) (f₂ : j₂ ⟶ k₁) (f₃ : j₂ ⟶ k₂) (f₄ : j₃ ⟶ k₂)
    (g₁ : j₁ ⟶ l) (g₂ : j₃ ⟶ l) :
    ∃ (s : C) (α : k₁ ⟶ s) (β : l ⟶ s) (γ : k₂ ⟶ s),
      f₁ ≫ α = g₁ ≫ β ∧ f₂ ≫ α = f₃ ≫ γ ∧ f₄ ≫ γ = g₂ ≫ β := by
  obtain ⟨l', k₁l, k₂l, hl⟩ := span f₂ f₃
  obtain ⟨s, ls, l's, hs₁, hs₂⟩ := bowtie g₁ (f₁ ≫ k₁l) g₂ (f₄ ≫ k₂l)
  refine ⟨s, k₁l ≫ l's, ls, k₂l ≫ l's, ?_, by simp only [← Category.assoc, hl], ?_⟩ <;>
    simp only [hs₁, hs₂, Category.assoc]

@[to_dual]
lemma wideSpan {I : Type*} [Finite I] {i : C} {j : I → C} (f : ∀ x, i ⟶ j x) :
    ∃ k fik, ∃ g : ∀ x, j x ⟶ k, ∀ x, f x ≫ g x = fik := by
  have : IsFiltered C := { nonempty := ⟨i⟩ }
  classical
  cases nonempty_fintype I
  obtain ⟨k, fk, hk⟩ := sup_exists (insert i (Finset.univ.image j))
    (Finset.univ.image fun x ↦ ⟨i, j x, by simp, by simp, f x⟩)
  exact ⟨k, _, _, fun x ↦ hk _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩

end SpecialShapes

end IsFiltered

namespace IsCofiltered

variable {C}
variable [IsCofilteredOrEmpty C]
theorem _root_.CategoryTheory.Functor.ranges_directed (F : C ⥤ Type*) (j : C) :
    Directed (· ⊇ ·) fun f : Σ' i, i ⟶ j => Set.range (F.map f.2) := fun ⟨i, ij⟩ ⟨k, kj⟩ => by
  let ⟨l, li, lk, e⟩ := cospan ij kj
  refine ⟨⟨l, lk ≫ kj⟩, e ▸ ?_, ?_⟩ <;>
    simp_rw [F.map_comp] <;>
    convert! Set.range_comp_subset_range _ _

end IsCofiltered

section Opposite

open Opposite

@[to_dual]
instance isCofilteredOrEmpty_op_of_isFilteredOrEmpty [IsFilteredOrEmpty C] :
    IsCofilteredOrEmpty Cᵒᵖ where
  cone_objs X Y :=
    ⟨op (IsFiltered.max X.unop Y.unop), (IsFiltered.leftToMax _ _).op,
      (IsFiltered.rightToMax _ _).op, trivial⟩
  cone_maps X Y f g :=
    ⟨op (IsFiltered.coeq f.unop g.unop), (IsFiltered.coeqHom _ _).op, by
      rw [show f = f.unop.op by simp, show g = g.unop.op by simp, ← op_comp, ← op_comp]
      congr 1
      exact IsFiltered.coeq_condition f.unop g.unop⟩

@[to_dual]
instance isCofiltered_op_of_isFiltered [IsFiltered C] : IsCofiltered Cᵒᵖ where
  nonempty := letI : Nonempty C := IsFiltered.nonempty; inferInstance

/-- If `Cᵒᵖ` is filtered or empty, then `C` is cofiltered or empty. -/
@[to_dual /-- If `Cᵒᵖ` is cofiltered or empty, then `C` is filtered or empty. -/]
lemma isCofilteredOrEmpty_of_isFilteredOrEmpty_op [IsFilteredOrEmpty Cᵒᵖ] : IsCofilteredOrEmpty C :=
  IsCofilteredOrEmpty.of_equivalence (opOpEquivalence _)

/-- If `Cᵒᵖ` is filtered, then `C` is cofiltered. -/
@[to_dual/-- If `Cᵒᵖ` is cofiltered, then `C` is filtered. -/]
lemma isCofiltered_of_isFiltered_op [IsFiltered Cᵒᵖ] : IsCofiltered C :=
  IsCofiltered.of_equivalence (opOpEquivalence _)

@[to_dual]
lemma isCofiltered_op_iff_isFiltered : IsCofiltered Cᵒᵖ ↔ IsFiltered C :=
  ⟨fun _ ↦ isFiltered_of_isCofiltered_op _, fun _ ↦ inferInstance⟩

end Opposite

section ULift

@[to_dual]
instance [IsFiltered C] : IsFiltered (ULift.{u₂} C) :=
  IsFiltered.of_equivalence ULift.equivalence

@[to_dual]
instance [IsFiltered C] : IsFiltered (ULiftHom C) :=
  IsFiltered.of_equivalence ULiftHom.equiv

@[to_dual]
instance [IsFiltered C] : IsFiltered (AsSmall C) :=
  IsFiltered.of_equivalence AsSmall.equiv

end ULift

section Pi

variable {α : Type w} {I : α → Type u₁} [∀ i, Category.{v₁} (I i)]

open IsFiltered in
@[to_dual]
instance [∀ i, IsFilteredOrEmpty (I i)] : IsFilteredOrEmpty (∀ i, I i) where
  cocone_objs k l := ⟨fun s => max (k s) (l s), fun s => leftToMax (k s) (l s),
    fun s => rightToMax (k s) (l s), trivial⟩
  cocone_maps k l f g := ⟨fun s => coeq (f s) (g s), fun s => coeqHom (f s) (g s),
    funext fun s => by simp [coeq_condition (f s) (g s)]⟩

attribute [local instance] IsFiltered.nonempty in
@[to_dual]
instance [∀ i, IsFiltered (I i)] : IsFiltered (∀ i, I i) where

end Pi

section Prod

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

set_option backward.isDefEq.respectTransparency false in
open IsFiltered in
@[to_dual]
instance [IsFilteredOrEmpty C] [IsFilteredOrEmpty D] : IsFilteredOrEmpty (C × D) where
  cocone_objs k l := ⟨(max k.1 l.1, max k.2 l.2), (leftToMax k.1 l.1, leftToMax k.2 l.2),
    (rightToMax k.1 l.1, rightToMax k.2 l.2), trivial⟩
  cocone_maps k l f g := ⟨(coeq f.1 g.1, coeq f.2 g.2), (coeqHom f.1 g.1, coeqHom f.2 g.2),
    by simp [coeq_condition]⟩

attribute [local instance] IsFiltered.nonempty in
@[to_dual]
instance [IsFiltered C] [IsFiltered D] : IsFiltered (C × D) where

end Prod

end CategoryTheory
