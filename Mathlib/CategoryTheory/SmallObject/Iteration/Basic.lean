/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.MorphismProperty.IsSmall
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.SuccPred.Limit

/-! # Transfinite iterations of a construction

In this file, we introduce the structure `SuccStruct` on a category `C`.
It consists of the data of an object `X₀ : C`, a successor map `succ : C → C`
and a morphism `toSucc : X ⟶ succ X` for any `X : C`. The map `toSucc`
does not have to be natural in `X`. For any element `j : J` in
well-ordered type `J`, we would like to define
the iteration of `Φ : SuccStruct C`, as a functor `F : J ⥤ C`
such that `F.obj ⊥ = X₀`, `F.obj j ⟶ F.obj (Order.succ j)` is `toSucc (F.obj j)`
when `j` is not maximal, and when `j` is limit, `F.obj j` should be the
colimit of the `F.obj k` for `k < j`.

In the small object argument, we shall apply this to the iteration of
a functor `F : C ⥤ C` equipped with a natural transformation `ε : 𝟭 C ⟶ F`:
this will correspond to the case of
`SuccStruct.ofTrans ε : SuccStruct (C ⥤ C)`, for which `X₀ := 𝟭 C`,
`succ G := G ⋙ F` and `toSucc G : G ⟶ G ⋙ F` is given by `whiskerLeft G ε`.

The construction of the iteration of `Φ : SuccStruct C` is done
by transfinite induction, under an assumption `HasIterationOfShape C J`.
However, for a limit element `j : J`, the definition of `F.obj j`
does not involve only the objects `F.obj i` for `i < j`, but it also
involves the maps `F.obj i₁ ⟶ F.obj i₂` for `i₁ ≤ i₂ < j`.
Then, this is a straightforward application of definitions by
transfinite induction. In order to solve this technical difficulty,
we introduce a structure `Φ.Iteration j` for any `j : J`. This
structure contains all the expected data and properties for
all the indices that are `≤ j`. In this file, we show that
`Φ.Iteration j` is a subsingleton. The uniqueness shall ne
obtained in the file `SmallObject.Iteration.Nonempty`, and
the construction of the functor `Φ.iterationFunctor J : J ⥤ C`
and of its colimit `Φ.iteration J : C` is done in the
file `SmallObject.Iteration.Iteration`.

The map `Φ.toSucc X : X ⟶ Φ.succ X` does not have to be natural
(and it is not in certain applications). Then, two isomorphic
objects `X` and `Y` may have non isomorphic successors. This is
the reason why we make an extensive use of equalities of objects
in the definitions.

In the file `SmallObject.TransfiniteIteration`, we consider
the colimit over all `j : J` of the `j`th iteration of `Φ`.

-/

universe w v v' u u'

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {J : Type w}

section

variable {D : Type u'} [Category.{v'} D]

namespace Arrow

lemma functor_ext {F G : C ⥤ D} (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    F.mapArrow.obj (Arrow.mk f) = G.mapArrow.obj (Arrow.mk f)) :
    F = G :=
  Functor.ext (fun X ↦ congr_arg Comma.left (h (𝟙 X))) (fun X Y f ↦ by
    have := (eqToIso (h f)).hom.w
    dsimp at this
    rw [Comma.eqToHom_left, Comma.eqToHom_right] at this
    rw [reassoc_of% this, eqToHom_trans, eqToHom_refl, comp_id])

lemma congr_mk_id {X Y : C} (h : X = Y) :
    Arrow.mk (𝟙 X) = Arrow.mk (𝟙 Y) := by rw [h]

lemma mk_eq_mk_iff {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') :
    Arrow.mk f = Arrow.mk f' ↔
      ∃ (hX : X = X') (hY : Y = Y'), f = eqToHom hX ≫ f' ≫ eqToHom hY.symm := by
  constructor
  · intro h
    refine ⟨congr_arg Comma.left h, congr_arg Comma.right h, ?_⟩
    have := (eqToIso h).hom.w
    dsimp at this
    rw [Comma.eqToHom_left, Comma.eqToHom_right] at this
    rw [reassoc_of% this, eqToHom_trans, eqToHom_refl, comp_id]
  · rintro ⟨rfl, rfl, h⟩
    simp only [eqToHom_refl, comp_id, id_comp] at h
    rw [h]

end Arrow

namespace Functor

--@[simp]
--lemma mapArrow_obj_mk (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
--    F.mapArrow.obj (Arrow.mk f) = Arrow.mk (F.map f) := rfl

end Functor

end
namespace SmallObject

section

variable [Preorder J] {j : J} (F : Set.Iic j ⥤ C) {i : J} (hi : i ≤ j)

/-- The functor `Set.Iio i ⥤ C` obtained by "restriction" of `F : Set.Iic j ⥤ C`
when `i ≤ j`. -/
def restrictionLT : Set.Iio i ⥤ C :=
  (monotone_inclusion_lt_le_of_le hi).functor ⋙ F

@[simp]
lemma restrictionLT_obj (k : J) (hk : k < i) :
    (restrictionLT F hi).obj ⟨k, hk⟩ = F.obj ⟨k, hk.le.trans hi⟩ := rfl

@[simp]
lemma restrictionLT_map {k₁ k₂ : Set.Iio i} (φ : k₁ ⟶ k₂) :
    (restrictionLT F hi).map φ = F.map (homOfLE (by simpa using leOfHom φ)) := rfl

/-- Given `F : Set.Iic j ⥤ C`, `i : J` such that `hi : i ≤ j`, this is the
cocone consisting of all maps `F.obj ⟨k, hk⟩ ⟶ F.obj ⟨i, hi⟩` for `k : J` such that `k < i`. -/
@[simps]
def coconeOfLE : Cocone (restrictionLT F hi) where
  pt := F.obj ⟨i, hi⟩
  ι :=
    { app := fun ⟨k, hk⟩ => F.map (homOfLE (by simpa using hk.le))
      naturality := fun ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ _ => by
        simp [comp_id, ← Functor.map_comp, homOfLE_comp] }

/-- The functor `Set.Iic i ⥤ C` obtained by "restriction" of `F : Set.Iic j ⥤ C`
when `i ≤ j`. -/
def restrictionLE : Set.Iic i ⥤ C :=
  (monotone_inclusion_le_le_of_le hi).functor ⋙ F

@[simp]
lemma restrictionLE_obj (k : J) (hk : k ≤ i) :
    (restrictionLE F hi).obj ⟨k, hk⟩ = F.obj ⟨k, hk.trans hi⟩ := rfl

@[simp]
lemma restrictionLE_map {k₁ k₂ : Set.Iic i} (φ : k₁ ⟶ k₂) :
    (restrictionLE F hi).map φ = F.map (homOfLE (by simpa using leOfHom φ)) := rfl

end

section

variable [Preorder J]

variable (C J) in
/-- A category `C` has iterations of shape `J` when certain shapes
of colimits exists. When `J` is well ordered, this assumption is used in
order to show that the category `Iteration ε j` is nonempty for any `j : J`,
see the file `CategoryTheory.SmallObject.Iteration.Nonempty`. The API is developed
further in `CategoryTheory.SmallObject.TransfiniteIteration`. -/
class HasIterationOfShape : Prop where
  hasColimitsOfShape_of_isSuccLimit (j : J) (hj : Order.IsSuccLimit j) :
    HasColimitsOfShape (Set.Iio j) C := by infer_instance
  hasColimitsOfShape : HasColimitsOfShape J C := by infer_instance

attribute [instance] HasIterationOfShape.hasColimitsOfShape

variable (C) in
lemma hasColimitsOfShape_of_isSuccLimit [HasIterationOfShape C J] (j : J)
    (hj : Order.IsSuccLimit j) :
    HasColimitsOfShape (Set.Iio j) C :=
  HasIterationOfShape.hasColimitsOfShape_of_isSuccLimit j hj

instance [HasIterationOfShape C J] :
    HasIterationOfShape (Arrow C) J where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

instance [HasIterationOfShape C J] {K : Type u'} [Category.{v'} K]:
    HasIterationOfShape (K ⥤ C) J where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

instance [HasIterationOfShape C J] (K : Type*) [Category K] (X : K) :
    PreservesWellOrderContinuousOfShape J ((evaluation K C).obj X) where
  preservesColimitsOfShape j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

instance [HasIterationOfShape C J] :
    PreservesWellOrderContinuousOfShape J (Arrow.leftFunc : _ ⥤ C) where
  preservesColimitsOfShape j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

instance [HasIterationOfShape C J] :
    PreservesWellOrderContinuousOfShape J (Arrow.rightFunc : _ ⥤ C) where
  preservesColimitsOfShape j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

end

variable (C) in
/-- A successor structure () on a category consists of the
data of an object `succ X` for any `X : C`, a map `toSucc X : X ⟶ toSucc X`
(which does not need to be natural), and a zeroth object `X₀`.
-/
structure SuccStruct where
  /-- the zeroth object -/
  X₀ : C
  /-- the successor of an object -/
  succ (X : C) : C
  /-- the map to the successor -/
  toSucc (X : C) : X ⟶ succ X

namespace SuccStruct

/-- Given a functor `Φ : C ⥤ C`, a natural transformation of the form `𝟭 C ⟶ Φ`
induces a successor structure. -/
@[simps]
def ofNatTrans {F : C ⥤ C} (ε : 𝟭 C ⟶ F) : SuccStruct (C ⥤ C) where
  succ G := G ⋙ F
  toSucc G := whiskerLeft G ε
  X₀ := 𝟭 C

--lemma congr_toSucc (Φ : SuccStruct C) {X Y : C} (h : X = Y) :
--    Φ.toSucc X = eqToHom (by rw [h]) ≫ Φ.toSucc Y ≫ eqToHom (by rw [h]) := by
--  subst h
--  simp

variable (Φ : SuccStruct C)

/-- The map `Φ.toSucc X : X ⟶ Φ.Succ X`, as an element in `Arrow C`. -/
def toSuccArrow (X : C) : Arrow C := Arrow.mk (Φ.toSucc X)

/-- The class of morphisms that are of the morphism `toSucc X : X ⟶ succ X`. -/
def prop : MorphismProperty C := .ofHoms (fun (X : C) ↦ Φ.toSucc X)

lemma prop_toSucc (X : C) : Φ.prop (Φ.toSucc X) := ⟨_⟩

lemma prop_iff {X Y : C} (f : X ⟶ Y) :
    Φ.prop f ↔ Arrow.mk f = Φ.toSuccArrow X := by
  constructor
  · rintro ⟨_⟩
    rfl
  · intro h
    rw [← Φ.prop.arrow_mk_mem_toSet_iff, h]
    apply prop_toSucc

variable [LinearOrder J] [OrderBot J] [SuccOrder J]
    [HasIterationOfShape C J]

/-- Given a functor `F : Set.Iic ⥤ C`, this is the morphism in `C`, as an element
in `Arrow C`, that is obtained by applying `F.map` to an inequality, -/
def arrowMap {j : J} (F : Set.Iic j ⥤ C) (i₁ i₂ : J) (h₁₂ : i₁ ≤ i₂)
    (h₂ : i₂ ≤ j) : Arrow C :=
  Arrow.mk (F.map (homOfLE h₁₂ : ⟨i₁, h₁₂.trans h₂⟩ ⟶ ⟨i₂, h₂⟩))

/-- Given a functor `F : Set.Iic j ⥤ C` and `i : J` such that `i < j`,
this is the arrow `F.obj ⟨i, _⟩ ⟶ F.obj ⟨Order.succ i, _⟩`. -/
def arrowSucc {j : J} (F : Set.Iic j ⥤ C) (i : J) (hi : i < j) : Arrow C :=
    arrowMap F i (Order.succ i) (Order.le_succ i) (Order.succ_le_of_lt hi)

omit [OrderBot J] [HasIterationOfShape C J] in
lemma arrowSucc_def {j : J} (F : Set.Iic j ⥤ C) (i : J) (hi : i < j) :
    arrowSucc F i hi = arrowMap F i (Order.succ i) (Order.le_succ i) (Order.succ_le_of_lt hi) :=
  rfl

omit [OrderBot J] [SuccOrder J] [HasIterationOfShape C J] in
@[simp]
lemma arrowMap_refl {j : J} (F : Set.Iic j ⥤ C) (i : J) (hi : i ≤ j) :
    arrowMap F i i (by simp) hi = Arrow.mk (𝟙 (F.obj ⟨i, hi⟩)) := by
  simp [arrowMap]

omit [OrderBot J] [SuccOrder J] [HasIterationOfShape C J] in
lemma arrowMap_restrictionLE {j : J} (F : Set.Iic j ⥤ C) {j' : J} (hj' : j' ≤ j)
    (i₁ i₂ : J) (h₁₂ : i₁ ≤ i₂) (h₂ : i₂ ≤ j') :
    arrowMap (restrictionLE F hj') i₁ i₂ h₁₂ h₂ =
      arrowMap F i₁ i₂ h₁₂ (h₂.trans hj') := rfl

/-- Given `F : Set.Iio i ⥤ C`, with `i` a limit element, and `k` such that `hk : k < i`,
this is the map `colimit.ι F ⟨k, hk⟩`, as an element in `Arrow C`. -/
noncomputable def arrowι {i : J} (F : Set.Iio i ⥤ C) (hi : Order.IsSuccLimit i)
    (k : J) (hk : k < i) : Arrow C :=
  letI := hasColimitsOfShape_of_isSuccLimit C i hi
  Arrow.mk (colimit.ι F ⟨k, hk⟩)

/-- The category of `j`th iterations of a succesor structure `Φ : SuccStruct C`.
An object consists of the data of all iterations of `Φ` for `i : J` such
that `i ≤ j` (this is the field `F`). Such objects are
equipped with data and properties which characterizes uniquely the iterations
on three types of elements: `⊥`, successors, limit elements. -/
@[ext]
structure Iteration [WellFoundedLT J] (j : J) where
  /-- The data of all `i`th iterations for `i : J` such that `i ≤ j`. -/
  F : Set.Iic j ⥤ C
  /-- The zeroth iteration is the zeroth object . -/
  obj_bot : F.obj ⟨⊥, bot_le⟩ = Φ.X₀
  /-- The iteration on a successor element identifies to the successor. -/
  arrowSucc_eq (i : J) (hi : i < j) : arrowSucc F i hi = Φ.toSuccArrow (F.obj ⟨i, hi.le⟩)
  arrowMap_limit (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) (k : J) (hk : k < i) :
    arrowMap F k i hk.le hij = arrowι (restrictionLT F hij) hi k hk
  --/-- The natural map from an iteration to its successor is induced by `toSucc`. -/
  --map_succ (i : J) (hi : i < j) :
  --  F.map (homOfLE (Order.le_succ i) : ⟨i, hi.le⟩ ⟶ ⟨Order.succ i, Order.succ_le_of_lt hi⟩) =
  --    Φ.toSucc _ ≫ eqToHom (by rw [obj_succ _ hi])
  --/-- If `i` is a limit element, the `i`th iteration is the colimit
  --of `k`th iterations for `k < i`. -/
  --map_eq_ι (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j)
  --    (k : J) (hk : k < i) :
  --  letI := hasColimitsOfShape_of_isSuccLimit C i hi
  --  F.map (homOfLE hk.le : ⟨k, hk.le.trans hij⟩ ⟶ ⟨i, hij⟩) =
  --    colimit.ι (restrictionLT F hij) ⟨k, hk⟩ ≫
  --      eqToHom (by rw [obj_limit i hi])

variable [WellFoundedLT J]

namespace Iteration

variable {Φ}
variable {j : J}

attribute [simp] obj_bot

section

variable (iter : Φ.Iteration j)

/-- The isomorphism `iter.F.obj ⟨⊥, bot_le⟩ ≅ Φ.X₀`. -/
def isoBot : iter.F.obj ⟨⊥, bot_le⟩ ≅ Φ.X₀ :=
  eqToIso (by rw [obj_bot])

lemma obj_succ (i : J) (hi : i < j) :
    iter.F.obj ⟨Order.succ i, Order.succ_le_of_lt hi⟩ = Φ.succ (iter.F.obj ⟨i, hi.le⟩) :=
  congr_arg Comma.right (iter.arrowSucc_eq i hi)

lemma obj_limit (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
    letI := hasColimitsOfShape_of_isSuccLimit C i hi
    iter.F.obj ⟨i, hij⟩ = colimit (restrictionLT iter.F hij) :=
  congr_arg Comma.right (iter.arrowMap_limit i hi hij ⊥ (Order.IsSuccLimit.bot_lt hi))

/-
/-- The object `iter.F.obj ⟨Order.succ i, _⟩` identifies to
the successor of `iter.F.obj ⟨i, _⟩` when `i < j`. -/
def isoSucc (i : J) (hi : i < j) :
    iter.F.obj ⟨Order.succ i, Order.succ_le_of_lt hi⟩ ≅
      Φ.succ (iter.F.obj ⟨i, hi.le⟩) :=
  eqToIso (by rw [obj_succ _ i hi])

/-- Variant of `map_succ'` involving the isomorphism `isoSucc`. -/
lemma map_succ' (i : J) (hi : i < j) :
    iter.F.map (homOfLE (Order.le_succ i) :
        ⟨i, hi.le⟩ ⟶ ⟨Order.succ i, Order.succ_le_of_lt hi⟩) =
      Φ.toSucc _ ≫ (iter.isoSucc i hi).inv :=
  iter.map_succ i hi

lemma arrow_mk_map_succ (i : J) (hi : i < j) :
    Arrow.mk (iter.F.map (homOfLE (Order.le_succ i) :
      ⟨i, hi.le⟩ ⟶ ⟨Order.succ i, Order.succ_le_of_lt hi⟩)) =
        Φ.toSuccArrow (iter.F.obj ⟨i, hi.le⟩) :=
  Arrow.ext rfl (iter.obj_succ i hi)
    (by simp [iter.map_succ' i hi, toSuccArrow, isoSucc])

lemma prop_map_succ (i : J) (hi : i < j) :
    Φ.prop (iter.F.map (homOfLE (Order.le_succ i) :
      ⟨i, hi.le⟩ ⟶ ⟨Order.succ i, Order.succ_le_of_lt hi⟩)) := by
  rw [prop_iff, iter.arrow_mk_map_succ _ hi]

/-- When `i : J` is limit, `iter.F.obj ⟨i, _⟩` identifies
to the colimit of the restriction of `iter.F` to `Set.Iio i`. -/
noncomputable def isColimit (i : J)
    (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
    IsColimit (coconeOfLE iter.F hij) := by
  have := hasColimitsOfShape_of_isSuccLimit C i hi
  exact IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocones.ext (eqToIso (iter.obj_limit i hi hij).symm)
    (fun ⟨k, hk⟩ ↦ (iter.map_eq_ι i hi hij k hk).symm))
    -/

/-- The element in `Φ.Iteration i` that is deduced from an element
in `Φ.Iteration j` when `i ≤ j`. -/
@[simps F]
def trunc (iter : Φ.Iteration j) {j' : J} (hj' : j' ≤ j) : Φ.Iteration j' where
  F := restrictionLE iter.F hj'
  obj_bot := iter.obj_bot
  arrowSucc_eq i hi := iter.arrowSucc_eq i (lt_of_lt_of_le hi hj')
  arrowMap_limit i hi hij k hk := iter.arrowMap_limit i hi (hij.trans hj') k hk

end

--omit [OrderBot J] [SuccOrder J] [WellFoundedLT J] in
--lemma congr_colimit_ι {F G : Set.Iio j ⥤ C} (h : F = G) (hj : Order.IsSuccLimit j)
--    (i : Set.Iio j) :
--    letI := hasColimitsOfShape_of_isSuccLimit C j hj
--    colimit.ι F i = by
--      refine eqToHom (by rw [h]) ≫ colimit.ι G i ≫ eqToHom (by rw [h]) := by
--  subst h
--  simp

namespace subsingleton

end subsingleton

namespace subsingleton

omit [OrderBot J] [SuccOrder J] [HasIterationOfShape C J] [WellFoundedLT J]

variable (F G : Set.Iic j ⥤ C)

section

variable (k₁ k₂ : J) (h₁₂ : k₁ ≤ k₂) (h₂ : k₂ ≤ j)

/-- Auxiliary definition for the proof of `Subsingleton (Φ.Iteration j)`. -/
def MapEq : Prop := arrowMap F k₁ k₂ h₁₂ h₂ = arrowMap G k₁ k₂ h₁₂ h₂

namespace MapEq

variable {k₁ k₂ h₁₂ h₂} (h : MapEq F G k₁ k₂ h₁₂ h₂)

include h

lemma src : F.obj ⟨k₁, h₁₂.trans h₂⟩ = G.obj ⟨k₁, h₁₂.trans h₂⟩ :=
  congr_arg Comma.left h

lemma tgt : F.obj ⟨k₂, h₂⟩ = G.obj ⟨k₂, h₂⟩ :=
  congr_arg Comma.right h

lemma w :
    F.map (homOfLE h₁₂ : ⟨k₁, h₁₂.trans h₂⟩ ⟶ ⟨k₂, h₂⟩) =
      eqToHom (by rw [h.src]) ≫ G.map (homOfLE h₁₂ : ⟨k₁, h₁₂.trans h₂⟩ ⟶ ⟨k₂, h₂⟩) ≫
        eqToHom (by rw [h.tgt]) := by
  have := (eqToIso h).hom.w
  dsimp [arrowMap] at this
  rw [Comma.eqToHom_left, Comma.eqToHom_right] at this
  simp [reassoc_of% this]

end MapEq

end

variable {F G}


lemma mapEq_refl (k : J) (hk : k ≤ j) (h : F.obj ⟨k, hk⟩ = G.obj ⟨k, hk⟩) :
    MapEq F G k k (by simp) hk := by
  rw [MapEq, arrowMap_refl, arrowMap_refl, h]

-- there is a more general lemma in `Arrow C`
lemma mapEq_trans {i₁ i₂ i₃ : J} (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃) {h₃ : i₃ ≤ j}
    (m₁₂ : MapEq F G i₁ i₂ h₁₂ (h₂₃.trans h₃)) (m₂₃ : MapEq F G i₂ i₃ h₂₃ h₃) :
    MapEq F G i₁ i₃ (h₁₂.trans h₂₃) h₃ := by
  simp only [MapEq, arrowMap, Arrow.mk_eq_mk_iff]
  refine ⟨m₁₂.src, m₂₃.tgt, ?_⟩
  rw [← homOfLE_comp (y := ⟨i₂, h₂₃.trans h₃⟩) h₁₂ h₂₃]
  simp [-homOfLE_comp, m₁₂.w, m₂₃.w]

lemma ext (h : ∀ (k₁ k₂ : J) (h₁₂ : k₁ ≤ k₂) (h₂ : k₂ ≤ j),
    MapEq F G k₁ k₂ h₁₂ h₂) :
    F = G := by
  apply Arrow.functor_ext
  rintro ⟨k₁, _⟩ ⟨k₂, h₂⟩ f
  apply h

end subsingleton

open subsingleton in
instance subsingleton : Subsingleton (Φ.Iteration j) where
  allEq iter₁ iter₂ := by
    suffices iter₁.F = iter₂.F by aesop
    revert iter₁ iter₂
    induction j using SuccOrder.limitRecOn with
    | hm j h =>
        obtain rfl := h.eq_bot
        intro iter₁ iter₂
        refine ext (fun k₁ k₂ h₁₂ h₂ ↦ ?_)
        obtain rfl : k₂ = ⊥ := by simpa using h₂
        obtain rfl : k₁ = ⊥ := by simpa using h₁₂
        apply mapEq_refl _ _ (by simp)
    | hs j hj₁ hj₂ =>
        intro iter₁ iter₂
        refine ext (fun k₁ k₂ h₁₂ h₂ ↦ ?_)
        have h₀ := Order.le_succ j
        replace hj₂ := hj₂ (iter₁.trunc h₀) (iter₂.trunc h₀)
        have hsucc := Functor.congr_obj hj₂ ⟨j, by simp⟩
        dsimp at hj₂ hsucc
        wlog h : k₂ ≤ j generalizing k₁ k₂
        · obtain h₂ | rfl := h₂.lt_or_eq
          · exact this _ _ _ _ ((Order.lt_succ_iff_of_not_isMax hj₁).1 h₂)
          · by_cases h' : k₁ ≤ j
            · apply mapEq_trans _ h₀ (this k₁ j h' h₀ (by simp))
              simp only [MapEq, ← arrowSucc_def _ _ (Order.lt_succ_of_not_isMax hj₁),
                arrowSucc_eq, hsucc]
            · simp only [not_le] at h'
              obtain rfl : k₁ = Order.succ j := le_antisymm h₁₂
                ((Order.succ_le_iff_of_not_isMax hj₁).2 h')
              rw [MapEq, arrowMap_refl, arrowMap_refl,
                obj_succ _ _ h', obj_succ _ _ h', hsucc]
        simp only [MapEq, ← arrowMap_restrictionLE _ (Order.le_succ j) _ _ _ h, hj₂]
    | hl j h₁ h₂ =>
        intro iter₁ iter₂
        refine ext (fun k₁ k₂ h₁₂ h₃ ↦ ?_)
        wlog h₄ : k₂ < j generalizing k₁ k₂; swap
        · have := h₂ k₂ h₄ (iter₁.trunc h₄.le) (iter₂.trunc h₄.le)
          simp at this
          simp only [MapEq, ← arrowMap_restrictionLE _ h₄.le _ _ _ (by rfl), this]
        · obtain rfl : j = k₂ := le_antisymm (by simpa using h₄) h₃
          have : restrictionLT iter₁.F le_rfl = restrictionLT iter₂.F le_rfl :=
            Arrow.functor_ext (fun _ l _ ↦ this _ _ _ _ l.2)
          by_cases h₅ : k₁ < j
          · dsimp [MapEq]
            simp_rw [arrowMap_limit _ _ h₁ _ _ h₅, this]
          · obtain rfl : k₁ = j := le_antisymm h₁₂ (by simpa using h₅)
            apply mapEq_refl
            simp only [obj_limit _ _ h₁, this]


end Iteration

end SuccStruct

end SmallObject

end CategoryTheory
