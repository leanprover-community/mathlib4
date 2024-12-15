/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Comma.CardinalArrow
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.HasCardinalLT
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # Presentable objects

If `κ` is a regular cardinal, we introduce the notion of `κ`-filtered
category, which generalizes the notion of filtered category.
Indeed, we obtain the equivalence
`IsCardinalFiltered J ℵ₀ ↔ IsFiltered J`.

A functor `F : C ⥤ D` is `κ`-accessible (`Functor.IsAccessible`)
if it commutes with colimits of shape `J` where `J` is any `κ`-filtered category.

An object `X` of a category is `κ`-presentable (`IsPresentable`)
if the functor `Hom(X, _)` (i.e. `coyoneda.obj (op X)`) is `κ`-accessible.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w w' v'' v' v u'' u' u

namespace CategoryTheory

open Limits Opposite

section

/-- A category `J` is `κ`-filtered (for a regular cardinal `κ`) if
any functor `F : A ⥤ J` from a category `A` such that `HasCardinalLT (Arrow A) κ`
admits a cocone. -/
class IsCardinalFiltered (J : Type u') [Category.{v'} J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  nonempty_cocone {A : Type w} [SmallCategory A] (F : A ⥤ J)
    (hA : HasCardinalLT (Arrow A) κ) : Nonempty (Cocone F)

namespace IsCardinalFiltered

variable {J : Type u'} [Category.{v'} J] {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
  [IsCardinalFiltered J κ]

/-- A choice of cocone for a functor `F : A ⥤ J` such that `HasCardinatLT (Arrow A) κ`
when `J` is a `κ`-filtered category. -/
noncomputable def cocone {A : Type v''} [Category.{u''} A]
    (F : A ⥤ J) (hA : HasCardinalLT (Arrow A) κ) :
    Cocone F := by
  have := hA.small
  have := small_of_small_arrow.{w} A
  have := locallySmall_of_small_arrow.{w} A
  let e := (Shrink.equivalence.{w} A).trans (ShrinkHoms.equivalence.{w} (Shrink.{w} A))
  exact (Cocones.equivalenceOfReindexing e.symm (Iso.refl _)).inverse.obj
    (nonempty_cocone (κ := κ) (e.inverse ⋙ F) (by simpa)).some

/-- If `S : K → J` is a family of objects of cardinality `< κ` in a `κ`-filtered category,
this is a  choice of object in `J` which is the target of a map from any of
the objects `S k`. -/
noncomputable def max {K : Type v''} (S : K → J) (hS : HasCardinalLT K κ) : J := by
  have : HasCardinalLT (Arrow (Discrete K)) κ := by simpa using hS
  exact (cocone (Discrete.functor S) this).pt

/-- If `S : K → J` is a family of objects of cardinality `< κ` in a `κ`-filtered category,
this is a choice of map `S k ⟶ max S hS` for any `k : K`. -/
noncomputable def toMax {K : Type v''} (S : K → J) (hS : HasCardinalLT K κ) (k : K) :
    S k ⟶ max S hS := by
  have : HasCardinalLT (Arrow (Discrete K)) κ := by simpa using hS
  exact (cocone (Discrete.functor S) this).ι.app ⟨k⟩

section

section

inductive ParallelMaps (T : Type u'') : Type
  | zero
  | one

namespace ParallelMaps

variable {T : Type u''}

inductive Hom : ParallelMaps T → ParallelMaps T → Type u''
  | id (X : ParallelMaps T) : Hom X X
  | map (t : T) : Hom zero one

def Hom.comp :
  ∀ {X Y Z : ParallelMaps T}, Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, id _, g => g
  | _, _, _, f, id _ => f

instance : Category (ParallelMaps T) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by rintro _ _ (_ | _); all_goals rfl
  comp_id := by rintro _ _ (_ | _); all_goals rfl
  assoc := by rintro _ _ _ _ (_ | _) (_ | _) (_ | _); all_goals rfl

@[simps]
def mkFunctor {C : Type u} [Category.{v} C] {X Y : C} (f : T → (X ⟶ Y)) :
    ParallelMaps T ⥤ C where
  obj a := match a with
    | zero => X
    | one => Y
  map φ := match φ with
    | .id _ => 𝟙 _
    | .map t => f t
  map_comp := by
    rintro _ _ _ (_ | _) (_ | _) <;> simp <;> rfl

variable (T) in
def arrowEquiv : Arrow (ParallelMaps T) ≃ Option (Option T) where
  toFun f := match f.left, f.right, f.hom with
    | zero, _, .id _ => none
    | one, _, .id _ => some none
    | zero, one, .map t => some (some t)
  invFun x := match x with
    | none => Arrow.mk (𝟙 zero)
    | some none => Arrow.mk (𝟙 one)
    | some (some t) => Arrow.mk (.map t)
  left_inv := by rintro ⟨(_ | _), _, (_ | _)⟩ <;> rfl
  right_inv := by rintro (_ | (_ | _)) <;> rfl

lemma _root_.hasCardinalLT_option_iff (X : Type u) (κ' : Cardinal.{w})
    (hκ' : Cardinal.aleph0 ≤ κ') :
    HasCardinalLT (Option X) κ' ↔ HasCardinalLT X κ' := by
  constructor
  · intro h
    exact h.of_injective _ (Option.some_injective _)
  · intro h
    dsimp [HasCardinalLT] at h ⊢
    simp only [Cardinal.mk_option, Cardinal.lift_add, Cardinal.lift_one]
    exact Cardinal.add_lt_of_lt (by simpa using hκ') h
      (lt_of_lt_of_le Cardinal.one_lt_aleph0 (by simpa using hκ'))

lemma hasCardinalLT {κ' : Cardinal.{w}} (hT : HasCardinalLT T κ') (hκ' : Cardinal.aleph0 ≤ κ') :
    HasCardinalLT (Arrow (ParallelMaps T)) κ' := by
  simpa only [hasCardinalLT_iff_of_equiv (arrowEquiv T),
    hasCardinalLT_option_iff _ _ hκ'] using hT

end ParallelMaps

end

variable {K : Type u''} {j j' : J} (f : K → (j ⟶ j')) (hK : HasCardinalLT K κ)

noncomputable def coeq : J :=
  (cocone (ParallelMaps.mkFunctor f) (ParallelMaps.hasCardinalLT hK hκ.out.aleph0_le)).pt

noncomputable def coeqHom : j' ⟶ coeq f hK :=
  (cocone (ParallelMaps.mkFunctor f) (ParallelMaps.hasCardinalLT hK hκ.out.aleph0_le)).ι.app .one

noncomputable def toCoeq : j ⟶ coeq f hK :=
  (cocone (ParallelMaps.mkFunctor f) (ParallelMaps.hasCardinalLT hK hκ.out.aleph0_le)).ι.app .zero

@[reassoc]
lemma coeq_condition (k : K) : f k ≫ coeqHom f hK = toCoeq f hK :=
  (cocone (ParallelMaps.mkFunctor f) (ParallelMaps.hasCardinalLT hK hκ.out.aleph0_le)).w
    (ParallelMaps.Hom.map k)

end

variable (J)

lemma of_le {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ' ≤ κ) :
    IsCardinalFiltered J κ' where
  nonempty_cocone F hA := ⟨cocone F (hA.of_le h)⟩

end IsCardinalFiltered

open IsCardinalFiltered in
lemma isFiltered_of_isCardinalDirected (J : Type u') [Category.{v'} J]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]:
    IsFiltered J := by
  rw [IsFiltered.iff_cocone_nonempty.{w}]
  intro A _ _ F
  have hA : HasCardinalLT (Arrow A) κ := by
    refine HasCardinalLT.of_le ?_ hκ.out.aleph0_le
    simp only [hasCardinalLT_aleph0]
    infer_instance
  exact ⟨cocone F hA⟩

instance : Fact Cardinal.aleph0.IsRegular where
  out := Cardinal.isRegular_aleph0

lemma isCardinalFiltered_aleph0_iff (J : Type u') [Category.{v'} J] :
    IsCardinalFiltered J Cardinal.aleph0 ↔ IsFiltered J := by
  constructor
  · intro
    exact isFiltered_of_isCardinalDirected J Cardinal.aleph0
  · intro
    constructor
    intro A _ F hA
    rw [hasCardinalLT_aleph0] at hA
    have := ((Arrow.finite_iff A).1 hA).some
    exact ⟨IsFiltered.cocone F⟩

lemma isCardinalFiltered_preorder (J : Type w) [Preorder J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (h : ∀ ⦃K : Type w⦄ (s : K → J) (_ : Cardinal.mk K < κ),
      ∃ (j : J), ∀ (k : K), s k ≤ j) :
    IsCardinalFiltered J κ where
  nonempty_cocone {A _ F hA} := by
    obtain ⟨j, hj⟩ := h F.obj (by simpa only [hasCardinalLT_iff_cardinal_mk_lt] using
        hasCardinalLT_of_hasCardinalLT_arrow hA)
    exact ⟨Cocone.mk j
      { app a := homOfLE (hj a)
        naturality _ _ _ := rfl }⟩

end

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Functor

variable (F : C ⥤ D) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- A functor is `κ`-accessible (with `κ` a regular cardinal)
if it preserves colimits of shape `J` where `J` is any `κ`-filtered category. -/
class IsAccessible : Prop where
  preservesColimitOfShape {J : Type w} [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F

lemma preservesColimitsOfShape_of_isAccessible [F.IsAccessible κ]
    (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F :=
  IsAccessible.preservesColimitOfShape κ

variable {κ} in
lemma isAccessible_of_le
    [F.IsAccessible κ] {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ ≤ κ') :
    F.IsAccessible κ' where
  preservesColimitOfShape {J _ _} := by
    have := IsCardinalFiltered.of_le J h
    exact F.preservesColimitsOfShape_of_isAccessible κ J

end Functor

variable (X : C) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- An object `X` in a category is `κ`-presentable (for `κ` a regular cardinal)
when the functor `Hom(X, _)` preserves colimits indexed by
`κ`-filtered categories. -/
abbrev IsPresentable : Prop := (coyoneda.obj (op X)).IsAccessible κ

lemma preservesColimitsOfShape_of_isPresentable [IsPresentable X κ]
    (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J (coyoneda.obj (op X)) :=
  (coyoneda.obj (op X)).preservesColimitsOfShape_of_isAccessible κ J

variable {κ} in
lemma isPresentable_of_le [IsPresentable X κ]
    {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ ≤ κ') :
    IsPresentable X κ' :=
  (coyoneda.obj (op X)).isAccessible_of_le h

end CategoryTheory
