/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.HasIterationOfShape
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.PrincipalSeg
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.SuccPred.Limit
public import Mathlib.Order.Interval.Set.InitialSeg

/-! # Transfinite iterations of a successor structure

In this file, we introduce the structure `SuccStruct` on a category `C`.
It consists of the data of an object `X₀ : C`, a successor map `succ : C → C`
and a morphism `toSucc : X ⟶ succ X` for any `X : C`. The map `toSucc`
does not have to be natural in `X`. For any element `j : J` in a
well-ordered type `J`, we would like to define
the iteration of `Φ : SuccStruct C`, as a functor `F : J ⥤ C`
such that `F.obj ⊥ = X₀`, `F.obj j ⟶ F.obj (Order.succ j)` is `toSucc (F.obj j)`
when `j` is not maximal, and when `j` is limit, `F.obj j` should be the
colimit of the `F.obj k` for `k < j`.

In the small object argument, we shall apply this to the iteration of
a functor `F : C ⥤ C` equipped with a natural transformation `ε : 𝟭 C ⟶ F`:
this will correspond to the case of
`SuccStruct.ofNatTrans ε : SuccStruct (C ⥤ C)`, for which `X₀ := 𝟭 C`,
`succ G := G ⋙ F` and `toSucc G : G ⟶ G ⋙ F` is given by `whiskerLeft G ε`.

The construction of the iteration of `Φ : SuccStruct C` is done
by transfinite induction, under an assumption `HasIterationOfShape C J`.
However, for a limit element `j : J`, the definition of `F.obj j`
does not involve only the objects `F.obj i` for `i < j`, but it also
involves the maps `F.obj i₁ ⟶ F.obj i₂` for `i₁ ≤ i₂ < j`.
Then, this is not a straightforward application of definitions by
transfinite induction. In order to solve this technical difficulty,
we introduce a structure `Φ.Iteration j` for any `j : J`. This
structure contains all the expected data and properties for
all the indices that are `≤ j`. In this file, we show that
`Φ.Iteration j` is a subsingleton. The existence shall be
obtained in the file `Mathlib/CategoryTheory/SmallObject/Iteration/Nonempty.lean`, and
the construction of the functor `Φ.iterationFunctor J : J ⥤ C`
and of its colimit `Φ.iteration J : C` will be done in the
file `Mathlib/CategoryTheory/SmallObject/TransfiniteIteration.lean`.

The map `Φ.toSucc X : X ⟶ Φ.succ X` does not have to be natural
(and it is not in certain applications). Then, two isomorphic
objects `X` and `Y` may have non-isomorphic successors. This is
the reason why we make an extensive use of equalities in
`C` and in `Arrow C` in the definitions.

## Note

The iteration was first introduced in mathlib by Joël Riou, using
a different approach as the one described above. After refactoring
his code, he found that the approach described above had already
been used in the pioneering formalization work in Lean 3 by
Reid Barton in 2018 towards the model category structure on
topological spaces.

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Category Limits

namespace SmallObject

variable {C : Type u} [Category.{v} C] {J : Type w}

section

variable [PartialOrder J] {j : J} (F : Set.Iic j ⥤ C) {i : J} (hi : i ≤ j)

/-- The functor `Set.Iio i ⥤ C` obtained by "restriction" of `F : Set.Iic j ⥤ C`
when `i ≤ j`. -/
def restrictionLT : Set.Iio i ⥤ C :=
  (Set.principalSegIioIicOfLE hi).monotone.functor ⋙ F


@[simp]
lemma restrictionLT_obj (k : J) (hk : k < i) :
    (restrictionLT F hi).obj ⟨k, hk⟩ = F.obj ⟨k, hk.le.trans hi⟩ := rfl

@[simp]
lemma restrictionLT_map {k₁ k₂ : Set.Iio i} (φ : k₁ ⟶ k₂) :
    (restrictionLT F hi).map φ = F.map (homOfLE (by simpa using leOfHom φ)) := rfl

/-- Given `F : Set.Iic j ⥤ C`, `i : J` such that `hi : i ≤ j`, this is the
cocone consisting of all maps `F.obj ⟨k, hk⟩ ⟶ F.obj ⟨i, hi⟩` for `k : J` such that `k < i`. -/
@[simps!]
def coconeOfLE : Cocone (restrictionLT F hi) :=
  (Set.principalSegIioIicOfLE hi).cocone F

/-- The functor `Set.Iic i ⥤ C` obtained by "restriction" of `F : Set.Iic j ⥤ C`
when `i ≤ j`. -/
def restrictionLE : Set.Iic i ⥤ C :=
  (Set.initialSegIicIicOfLE hi).monotone.functor ⋙ F

@[simp]
lemma restrictionLE_obj (k : J) (hk : k ≤ i) :
    (restrictionLE F hi).obj ⟨k, hk⟩ = F.obj ⟨k, hk.trans hi⟩ := rfl

@[simp]
lemma restrictionLE_map {k₁ k₂ : Set.Iic i} (φ : k₁ ⟶ k₂) :
    (restrictionLE F hi).map φ = F.map (homOfLE (by simpa using leOfHom φ)) := rfl

end

variable (C) in
/-- A successor structure on a category consists of the
data of an object `succ X` for any `X : C`, a map `toSucc X : X ⟶ succ X`
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
induces a successor structure on `C ⥤ C`. -/
@[simps]
def ofNatTrans {F : C ⥤ C} (ε : 𝟭 C ⟶ F) : SuccStruct (C ⥤ C) where
  succ G := G ⋙ F
  toSucc G := Functor.whiskerLeft G ε
  X₀ := 𝟭 C

variable (Φ : SuccStruct C)

/-- The class of morphisms that are of the form `toSucc X : X ⟶ succ X`. -/
def prop : MorphismProperty C := .ofHoms (fun (X : C) ↦ Φ.toSucc X)

lemma prop_toSucc (X : C) : Φ.prop (Φ.toSucc X) := ⟨_⟩

/-- The map `Φ.toSucc X : X ⟶ Φ.Succ X`, as an element in `Arrow C`. -/
@[simps!]
def toSuccArrow (X : C) : Arrow C := Arrow.mk (Φ.toSucc X)

lemma prop_iff {X Y : C} (f : X ⟶ Y) :
    Φ.prop f ↔ Arrow.mk f = Φ.toSuccArrow X := by
  constructor
  · rintro ⟨_⟩
    rfl
  · intro h
    rw [← Φ.prop.arrow_mk_mem_toSet_iff, h]
    apply prop_toSucc

variable {Φ}

lemma prop.succ_eq {X Y : C} {f : X ⟶ Y} (hf : Φ.prop f) :
    Φ.succ X = Y := by
  cases hf
  rfl

@[reassoc]
lemma prop.fac {X Y : C} {f : X ⟶ Y} (hf : Φ.prop f) :
    f = Φ.toSucc X ≫ eqToHom hf.succ_eq := by
  cases hf
  simp

set_option backward.defeqAttrib.useBackward true in
/-- If `Φ : SuccStruct C` and `f` is a morphism in `C` which
satisfies `Φ.prop f`, then this is the isomorphism of arrows
between `f` and `Φ.toSuccArrow X`. -/
@[simps!]
def prop.arrowIso {X Y : C} {f : X ⟶ Y} (hf : Φ.prop f) :
    Arrow.mk f ≅ Φ.toSuccArrow X :=
  Arrow.isoMk (Iso.refl _) (eqToIso hf.succ_eq.symm) (by simp [hf.fac])

variable (Φ)
variable [LinearOrder J]

/-- Given a functor `F : Set.Iic ⥤ C`, this is the morphism in `C`, as an element
in `Arrow C`, that is obtained by applying `F.map` to an inequality. -/
def arrowMap {j : J} (F : Set.Iic j ⥤ C) (i₁ i₂ : J) (h₁₂ : i₁ ≤ i₂) (h₂ : i₂ ≤ j) :
    Arrow C :=
  Arrow.mk (F.map (homOfLE h₁₂ : ⟨i₁, h₁₂.trans h₂⟩ ⟶ ⟨i₂, h₂⟩))

@[simp]
lemma arrowMap_refl {j : J} (F : Set.Iic j ⥤ C) (i : J) (hi : i ≤ j) :
    arrowMap F i i (by simp) hi = Arrow.mk (𝟙 (F.obj ⟨i, hi⟩)) := by
  simp [arrowMap]

lemma arrowMap_restrictionLE {j : J} (F : Set.Iic j ⥤ C) {j' : J} (hj' : j' ≤ j)
    (i₁ i₂ : J) (h₁₂ : i₁ ≤ i₂) (h₂ : i₂ ≤ j') :
    arrowMap (restrictionLE F hj') i₁ i₂ h₁₂ h₂ =
      arrowMap F i₁ i₂ h₁₂ (h₂.trans hj') := rfl

section

variable [SuccOrder J] {j : J} (F : Set.Iic j ⥤ C) (i : J) (hi : i < j)

/-- Given a functor `F : Set.Iic j ⥤ C` and `i : J` such that `i < j`,
this is the arrow `F.obj ⟨i, _⟩ ⟶ F.obj ⟨Order.succ i, _⟩`. -/
def arrowSucc : Arrow C :=
    arrowMap F i (Order.succ i) (Order.le_succ i) (Order.succ_le_of_lt hi)

lemma arrowSucc_def :
    arrowSucc F i hi = arrowMap F i (Order.succ i) (Order.le_succ i) (Order.succ_le_of_lt hi) :=
  rfl

end

section

variable [HasIterationOfShape J C]
  {i : J} (F : Set.Iio i ⥤ C) (hi : Order.IsSuccLimit i) (k : J) (hk : k < i)

/-- Given `F : Set.Iio i ⥤ C`, with `i` a limit element, and `k` such that `hk : k < i`,
this is the map `colimit.ι F ⟨k, hk⟩`, as an element in `Arrow C`. -/
noncomputable def arrowι : Arrow C :=
  letI := hasColimitsOfShape_of_isSuccLimit C i hi
  Arrow.mk (colimit.ι F ⟨k, hk⟩)

lemma arrowι_def :
    letI := hasColimitsOfShape_of_isSuccLimit C i hi
    arrowι F hi k hk = Arrow.mk (colimit.ι F ⟨k, hk⟩) := rfl

end

variable [SuccOrder J] [OrderBot J] [HasIterationOfShape J C]

/-- The category of `j`th iterations of a successor structure `Φ : SuccStruct C`.
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
  /-- The iteration on a successor element is the successor. -/
  arrowSucc_eq (i : J) (hi : i < j) : arrowSucc F i hi = Φ.toSuccArrow (F.obj ⟨i, hi.le⟩)
  /-- The iteration on a limit element identifies to the colimit of the
  value on smaller elements, see `Iteration.isColimit`. -/
  arrowMap_limit (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) (k : J) (hk : k < i) :
    arrowMap F k i hk.le hij = arrowι (restrictionLT F hij) hi k hk

variable [WellFoundedLT J]

namespace Iteration

variable {Φ}
variable {j : J}

section

variable (iter : Φ.Iteration j)

lemma obj_succ (i : J) (hi : i < j) :
    iter.F.obj ⟨Order.succ i, Order.succ_le_of_lt hi⟩ = Φ.succ (iter.F.obj ⟨i, hi.le⟩) :=
  congr_arg Comma.right (iter.arrowSucc_eq i hi)

lemma prop_map_succ (i : J) (hi : i < j) :
    Φ.prop (iter.F.map (homOfLE (Order.le_succ i) :
      ⟨i, hi.le⟩ ⟶ ⟨Order.succ i, Order.succ_le_of_lt hi⟩)) := by
  rw [prop_iff, ← arrowMap, ← arrowSucc_def _ _ hi, iter.arrowSucc_eq]

lemma obj_limit (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
    letI := hasColimitsOfShape_of_isSuccLimit C i hi
    iter.F.obj ⟨i, hij⟩ = colimit (restrictionLT iter.F hij) :=
  congr_arg Comma.right (iter.arrowMap_limit i hi hij ⊥ (Order.IsSuccLimit.bot_lt hi))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The iteration on a limit element identifies to the colimit of the
value on smaller elements. -/
noncomputable def isColimit (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
    IsColimit (coconeOfLE iter.F hij) := by
  letI := hasColimitsOfShape_of_isSuccLimit C i hi
  refine IsColimit.ofIsoColimit (colimit.isColimit (restrictionLT iter.F hij))
    (Cocone.ext (eqToIso (iter.obj_limit i hi hij).symm) ?_)
  rintro ⟨k, hk⟩
  apply Arrow.mk_injective
  dsimp
  rw [← arrowMap]
  simp [iter.arrowMap_limit i hi hij k hk, arrowι_def]

/-- The element in `Φ.Iteration i` that is deduced from an element
in `Φ.Iteration j` when `i ≤ j`. -/
@[simps F]
def trunc (iter : Φ.Iteration j) {j' : J} (hj' : j' ≤ j) : Φ.Iteration j' where
  F := restrictionLE iter.F hj'
  obj_bot := iter.obj_bot
  arrowSucc_eq i hi := iter.arrowSucc_eq i (lt_of_lt_of_le hi hj')
  arrowMap_limit i hi hij k hk := iter.arrowMap_limit i hi (hij.trans hj') k hk

end

namespace subsingleton

variable {K : Type w} [LinearOrder K] {x : K} (F G : Set.Iic x ⥤ C)

section

variable (k₁ k₂ : K) (h₁₂ : k₁ ≤ k₂) (h₂ : k₂ ≤ x)

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
  have := (Arrow.mk_eq_mk_iff _ _).1 h
  tauto

end MapEq

end

variable {F G}

lemma mapEq_refl (k : K) (hk : k ≤ x) (h : F.obj ⟨k, hk⟩ = G.obj ⟨k, hk⟩) :
    MapEq F G k k (by simp) hk := by
  rw [MapEq, arrowMap_refl, arrowMap_refl, h]

lemma mapEq_trans {i₁ i₂ i₃ : K} (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃) {h₃ : i₃ ≤ x}
    (m₁₂ : MapEq F G i₁ i₂ h₁₂ (h₂₃.trans h₃)) (m₂₃ : MapEq F G i₂ i₃ h₂₃ h₃) :
    MapEq F G i₁ i₃ (h₁₂.trans h₂₃) h₃ := by
  simp only [MapEq, arrowMap, Arrow.mk_eq_mk_iff]
  refine ⟨m₁₂.src, m₂₃.tgt, ?_⟩
  rw [← homOfLE_comp (y := ⟨i₂, h₂₃.trans h₃⟩) h₁₂ h₂₃]
  simp [-homOfLE_comp, m₁₂.w, m₂₃.w]

lemma ext (h : ∀ (k₁ k₂ : K) (h₁₂ : k₁ ≤ k₂) (h₂ : k₂ ≤ x),
    MapEq F G k₁ k₂ h₁₂ h₂) :
    F = G := by
  apply Arrow.functor_ext
  rintro ⟨k₁, _⟩ ⟨k₂, h₂⟩ f
  apply h

end subsingleton

set_option backward.defeqAttrib.useBackward true in
open subsingleton in
instance subsingleton : Subsingleton (Φ.Iteration j) where
  allEq iter₁ iter₂ := by
    suffices iter₁.F = iter₂.F by aesop
    revert iter₁ iter₂
    induction j using SuccOrder.limitRecOn with
    | isMin j h =>
      obtain rfl := h.eq_bot
      intro iter₁ iter₂
      refine ext (fun k₁ k₂ h₁₂ h₂ ↦ ?_)
      obtain rfl : k₂ = ⊥ := by simpa using h₂
      obtain rfl : k₁ = ⊥ := by simpa using h₁₂
      apply mapEq_refl _ _ (by simp only [obj_bot])
    | succ j hj₁ hj₂ =>
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
    | isSuccLimit j h₁ h₂ =>
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

set_option backward.defeqAttrib.useBackward true in
lemma congr_obj {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    (k : J) (h₁ : k ≤ j₁) (h₂ : k ≤ j₂) :
    iter₁.F.obj ⟨k, h₁⟩ = iter₂.F.obj ⟨k, h₂⟩ := by
  wlog h : j₁ ≤ j₂ generalizing j₁ j₂
  · exact (this iter₂ iter₁ h₂ h₁ (le_of_lt (by simpa using h))).symm
  rw [Subsingleton.elim iter₁ (iter₂.trunc h)]
  dsimp

lemma congr_arrowMap {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    {k₁ k₂ : J} (h : k₁ ≤ k₂) (h₁ : k₂ ≤ j₁) (h₂ : k₂ ≤ j₂) :
    arrowMap iter₁.F k₁ k₂ h h₁ = arrowMap iter₂.F k₁ k₂ h h₂ := by
  wlog hj : j₁ ≤ j₂ generalizing j₁ j₂
  · simp [this iter₂ iter₁ h₂ h₁ ((not_le.1 hj).le)]
  rw [Subsingleton.elim iter₁ (iter₂.trunc hj)]
  rfl

lemma congr_map {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    {k₁ k₂ : J} (h : k₁ ≤ k₂) (h₁ : k₂ ≤ j₁) (h₂ : k₂ ≤ j₂) :
    iter₁.F.map (homOfLE h : ⟨k₁, h.trans h₁⟩ ⟶ ⟨k₂, h₁⟩) =
      eqToHom (congr_obj iter₁ iter₂ k₁ (h.trans h₁) (h.trans h₂)) ≫
        iter₂.F.map (homOfLE h) ≫
        eqToHom (congr_obj iter₁ iter₂ k₂ h₁ h₂).symm := by
  have := (Arrow.mk_eq_mk_iff _ _).1 (congr_arrowMap iter₁ iter₂ h h₁ h₂)
  tauto

/-- Given `iter₁ : Φ.Iteration j₁` and `iter₂ : Φ.Iteration j₂`, with `j₁ ≤ j₂`,
if `k₁ ≤ k₂` are elements such that `k₁ ≤ j₁` and `k₂ ≤ k₂`, then this
is the canonical map `iter₁.F.obj ⟨k₁, h₁⟩ ⟶ iter₂.F.obj ⟨k₂, h₂⟩`. -/
def mapObj {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    {k₁ k₂ : J} (h₁₂ : k₁ ≤ k₂) (h₁ : k₁ ≤ j₁) (h₂ : k₂ ≤ j₂) (hj : j₁ ≤ j₂) :
    iter₁.F.obj ⟨k₁, h₁⟩ ⟶ iter₂.F.obj ⟨k₂, h₂⟩ :=
  eqToHom (congr_obj iter₁ iter₂ k₁ h₁ (h₁.trans hj)) ≫
    iter₂.F.map (homOfLE h₁₂)

lemma arrow_mk_mapObj {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    {k₁ k₂ : J} (h₁₂ : k₁ ≤ k₂) (h₁ : k₁ ≤ j₁) (h₂ : k₂ ≤ j₂) (hj : j₁ ≤ j₂) :
    Arrow.mk (mapObj iter₁ iter₂ h₁₂ h₁ h₂ hj) =
      arrowMap iter₂.F k₁ k₂ h₁₂ h₂ := by
  simp [mapObj, arrowMap]

@[simp]
lemma mapObj_refl {j : J} (iter : Φ.Iteration j)
    {k l : J} (h : k ≤ l) (h' : l ≤ j) :
    mapObj iter iter h (h.trans h') h' (by rfl) = iter.F.map (homOfLE h) := by
  simp [mapObj]

@[reassoc (attr := simp)]
lemma mapObj_trans {j₁ j₂ j₃ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    (iter₃ : Φ.Iteration j₃) {k₁ k₂ k₃ : J} (h₁₂ : k₁ ≤ k₂) (h₂₃ : k₂ ≤ k₃)
    (h₁ : k₁ ≤ j₁) (h₂ : k₂ ≤ j₂) (h₃ : k₃ ≤ j₃) (h₁₂' : j₁ ≤ j₂) (h₂₃' : j₂ ≤ j₃) :
    mapObj iter₁ iter₂ h₁₂ h₁ h₂ h₁₂' ≫ mapObj iter₂ iter₃ h₂₃ h₂ h₃ h₂₃' =
      mapObj iter₁ iter₃ (h₁₂.trans h₂₃) h₁ h₃ (h₁₂'.trans h₂₃') := by
  simp [mapObj, congr_map iter₂ iter₃ h₁₂ h₂ (h₂.trans h₂₃'), ← Functor.map_comp]

end Iteration

end SuccStruct

end SmallObject

end CategoryTheory
