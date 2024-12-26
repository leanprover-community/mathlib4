/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
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
by transfinite induction. However, for a limit element `j : J`,
the definition of `F.obj j` does not involve only
the objects `F.obj i` for `i < j`, but it also
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

-/

universe w v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {J : Type w}

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
see the file `CategoryTheory.SmallObject.Nonempty`. -/
class HasIterationOfShape : Prop where
  hasColimitsOfShape_of_isSuccLimit (j : J) (hj : Order.IsSuccLimit j) :
    HasColimitsOfShape (Set.Iio j) C := by infer_instance
  hasColimitsOfShape : HasColimitsOfShape J C := by infer_instance

attribute [instance] HasIterationOfShape.hasColimitsOfShape

variable (C) in
lemma hasColimitOfShape_of_isSuccLimit [HasIterationOfShape C J] (j : J)
    (hj : Order.IsSuccLimit j) :
    HasColimitsOfShape (Set.Iio j) C :=
  HasIterationOfShape.hasColimitsOfShape_of_isSuccLimit j hj

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

lemma congr_toSucc (Φ : SuccStruct C) {X Y : C} (h : X = Y) :
    Φ.toSucc X = eqToHom (by rw [h]) ≫ Φ.toSucc Y ≫ eqToHom (by rw [h]) := by
  subst h
  simp

variable (Φ : SuccStruct C) [LinearOrder J] [OrderBot J] [SuccOrder J]
    [HasIterationOfShape C J]

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
  obj_succ (i : J) (hi : i < j) :
    F.obj ⟨Order.succ i, Order.succ_le_of_lt hi⟩ = Φ.succ (F.obj ⟨i, hi.le⟩)
  /-- The natural map from an iteration to its successor is induced by `toSucc`. -/
  map_succ (i : J) (hi : i < j) :
    F.map (homOfLE (Order.le_succ i) : ⟨i, hi.le⟩ ⟶ ⟨Order.succ i, Order.succ_le_of_lt hi⟩) =
      Φ.toSucc _ ≫ eqToHom (by rw [obj_succ _ hi])
  /-- If `i` is a limit element, the `i`th iteration is the colimit
  of `k`th iterations for `k < i`. -/
  obj_limit (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
    letI := hasColimitOfShape_of_isSuccLimit C i hi
    F.obj ⟨i, hij⟩ = colimit (restrictionLT F hij)
  map_eq_ι (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j)
      (k : J) (hk : k < i) :
    letI := hasColimitOfShape_of_isSuccLimit C i hi
    F.map (homOfLE hk.le : ⟨k, hk.le.trans hij⟩ ⟶ ⟨i, hij⟩) =
      colimit.ι (restrictionLT F hij) ⟨k, hk⟩ ≫
        eqToHom (by rw [obj_limit i hi])

variable [WellFoundedLT J]

namespace Iteration

variable {Φ}
variable {j : J}

section

variable (iter : Φ.Iteration j)

/-- The isomorphism `iter.F.obj ⟨⊥, bot_le⟩ ≅ Φ.X₀`. -/
def isoBot : iter.F.obj ⟨⊥, bot_le⟩ ≅ Φ.X₀ :=
  eqToIso (by rw [obj_bot])

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

/-- When `i : J` is limit, `iter.F.obj ⟨i, _⟩` identifies
to the colimit of the restriction of `iter.F` to `Set.Iio i`. -/
noncomputable def isColimit (i : J)
    (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
    IsColimit (coconeOfLE iter.F hij) := by
  have := hasColimitOfShape_of_isSuccLimit C i hi
  exact IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocones.ext (eqToIso (iter.obj_limit i hi hij).symm)
    (fun ⟨k, hk⟩ ↦ (iter.map_eq_ι i hi hij k hk).symm))

/-- The element in `Φ.Iteration i` that is deduced from an element
in `Φ.Iteration j` when `i ≤ j`. -/
@[simps F]
def trunc (iter : Φ.Iteration j) {i : J} (hi : i ≤ j) : Φ.Iteration i where
  F := restrictionLE iter.F hi
  obj_bot := iter.obj_bot
  obj_succ k hk := iter.obj_succ k (lt_of_lt_of_le hk hi)
  obj_limit k hk hk' := iter.obj_limit k hk (hk'.trans hi)
  map_succ k hk := iter.map_succ k (lt_of_lt_of_le hk hi)
  map_eq_ι k hk hki l hl := iter.map_eq_ι k hk (hki.trans hi) l hl

end

omit [OrderBot J] [SuccOrder J] [WellFoundedLT J] in
lemma congr_colimit_ι {F G : Set.Iio j ⥤ C} (h : F = G) (hj : Order.IsSuccLimit j)
    (i : Set.Iio j) :
    letI := hasColimitOfShape_of_isSuccLimit C j hj
    colimit.ι F i = by
      refine eqToHom (by rw [h]) ≫ colimit.ι G i ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-! Auxiliary definitions for the proof of `Subsingleton (Φ.Iteration j)`. -/

namespace subsingleton

variable {F G : Set.Iic j ⥤ C} (hobj : F.obj = G.obj)

omit [OrderBot J] [SuccOrder J] [WellFoundedLT J]

def MapEq (i₁ i₂ : J) (h₁₂ : i₁ ≤ i₂) (h₂ : i₂ ≤ j) : Prop :=
  F.map (homOfLE h₁₂ : ⟨i₁, h₁₂.trans h₂⟩ ⟶ ⟨i₂, h₂⟩) =
    eqToHom (by rw [hobj]) ≫
      G.map (homOfLE h₁₂ : ⟨i₁, _⟩ ⟶ ⟨i₂, _⟩) ≫ eqToHom (by rw [hobj])

omit [HasIterationOfShape C J] in
lemma mapEq_of_eq {k : J} (hkj : k ≤ j) (h : restrictionLE F hkj = restrictionLE G hkj)
    (i₁ i₂ : J) (h₁₂ : i₁ ≤ i₂) (h₂ : i₂ ≤ k) :
    MapEq hobj i₁ i₂ h₁₂ (h₂.trans hkj) := by
  exact Functor.congr_hom h (homOfLE h₁₂ : ⟨i₁, h₁₂.trans h₂⟩ ⟶ ⟨i₂, h₂⟩)

omit [HasIterationOfShape C J]

lemma mapEq_rfl (i : J) (h : i ≤ j) : MapEq hobj i i (by simp) h := by
  simp [MapEq]

variable {hobj} in
lemma mapEq_trans {i₁ i₂ i₃ : J} (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃) {h₃ : i₃ ≤ j}
    (m₁₂ : MapEq hobj i₁ i₂ h₁₂ (h₂₃.trans h₃)) (m₂₃ : MapEq hobj i₂ i₃ h₂₃ h₃) :
    MapEq hobj i₁ i₃ (h₁₂.trans h₂₃) h₃ := by
  dsimp [MapEq] at m₁₂ m₂₃ ⊢
  rw [← homOfLE_comp (X := Set.Iic j) (x := ⟨i₁, _⟩)
    (y := ⟨i₂, h₂₃.trans h₃⟩) (z := ⟨i₃, _⟩) h₁₂ h₂₃, Functor.map_comp,
    Functor.map_comp, m₁₂, m₂₃]
  simp

lemma functor_eq (hmap : ∀ (i₁ i₂ : J) (h₁₂ : i₁ ≤ i₂) (h₂ : i₂ ≤ j), MapEq hobj i₁ i₂ h₁₂ h₂) :
    F = G :=
  Functor.ext (by simp [hobj]) (by
    rintro ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ f
    exact hmap i₁ i₂ (leOfHom f) h₂)

end subsingleton

open subsingleton in
instance subsingleton : Subsingleton (Φ.Iteration j) where
  allEq iter₁ iter₂ := by
    suffices iter₁.F = iter₂.F by aesop
    revert iter₁ iter₂
    induction j using SuccOrder.limitRecOn with
    | hm j h =>
        intro iter₁ iter₂
        obtain rfl := h.eq_bot
        fapply Functor.ext
        · rintro ⟨i, hi⟩
          obtain rfl : i = ⊥ := by simpa using hi
          simp only [obj_bot]
        · rintro ⟨i, hi⟩ ⟨i', hi'⟩ f
          obtain rfl : i = ⊥ := by simpa using hi
          obtain rfl : i' = ⊥ := by simpa using hi'
          obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
          simp
    | hs j hj₁ hj₂ =>
        intro iter₁ iter₂
        have hobj : iter₁.F.obj = iter₂.F.obj := by
          ext ⟨i, hi⟩
          wlog h : i ≤ j generalizing i
          · obtain hi | rfl := hi.lt_or_eq
            · exact this _ _ ((Order.lt_succ_iff_of_not_isMax hj₁).mp hi)
            · simp only [obj_succ _ _ (Order.lt_succ_of_not_isMax hj₁), this _ _ (by rfl)]
          exact Functor.congr_obj (hj₂ (iter₁.trunc (Order.le_succ _))
            (iter₂.trunc (Order.le_succ _))) ⟨i, h⟩
        have hsucc : MapEq hobj _ _ (Order.le_succ j) (by simp) := by
          simp only [MapEq, map_succ _ _ (Order.lt_succ_of_not_isMax hj₁),
            Φ.congr_toSucc (congr_fun hobj ⟨j, _⟩), assoc, eqToHom_trans]
        apply functor_eq hobj
        intro i₁ i₂
        wlog hi₂ : i₂ ≤ j generalizing i₂
        · intro h₁₂ h₂
          obtain h₂ | rfl := h₂.lt_or_eq
          · exact (hi₂ ((Order.lt_succ_iff_of_not_isMax hj₁).mp h₂)).elim
          · by_cases hi₁ : i₁ ≤ j
            · exact mapEq_trans _ _ (this j (by simp) hi₁ (Order.le_succ j)) hsucc
            · obtain rfl : i₁ = Order.succ j :=
                le_antisymm h₁₂ ((Order.succ_le_iff_of_not_isMax hj₁).mpr (by simpa using hi₁))
              apply mapEq_rfl
        intro h₁₂ h₂
        exact mapEq_of_eq hobj (Order.le_succ j)
          (hj₂ (iter₁.trunc (Order.le_succ j)) (iter₂.trunc (Order.le_succ j))) _ _ _ hi₂
    | hl j h₁ h₂ =>
        intro iter₁ iter₂
        have hobj : iter₁.F.obj = iter₂.F.obj := by
          ext ⟨i, hi⟩
          wlog h : i < j generalizing i
          · obtain rfl : j = i := le_antisymm (by simpa using h) hi
            simp only [obj_limit _ _ h₁]
            congr 1
            fapply Functor.ext
            · rintro ⟨i, hi⟩
              exact this _ _ hi
            · rintro ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩ f
              exact Functor.congr_hom (h₂ i₂ hi₂ (iter₁.trunc hi₂.le) (iter₂.trunc hi₂.le))
                (homOfLE (leOfHom f) : ⟨i₁, leOfHom f⟩ ⟶ ⟨i₂, by simp⟩)
          exact Functor.congr_obj (h₂ i h (iter₁.trunc h.le) (iter₂.trunc h.le)) ⟨i, by simp⟩
        apply functor_eq hobj
        intro i₁ i₂ h₁₂ hi₂
        by_cases h₃ : i₂ < j
        · exact mapEq_of_eq hobj hi₂
            (h₂ _ h₃ (iter₁.trunc h₃.le) (iter₂.trunc h₃.le)) _ _ _ (by rfl)
        · obtain rfl : j = i₂ := le_antisymm (by simpa using h₃) hi₂
          by_cases h₄ : i₁ < j
          · dsimp [MapEq]
            have : restrictionLT iter₁.F hi₂ = restrictionLT iter₂.F hi₂ :=
              Functor.ext (fun k ↦ congr_fun hobj ⟨k.1, k.2.le⟩) (by
                rintro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ f
                exact Functor.congr_hom (h₂ k₂ hk₂ (iter₁.trunc hk₂.le) (iter₂.trunc hk₂.le))
                  (homOfLE (leOfHom f) : ⟨k₁, leOfHom f⟩ ⟶ ⟨k₂, by simp⟩))
            simp only [map_eq_ι _ _ h₁ _ _ h₄, assoc, eqToHom_trans,
              congr_colimit_ι this h₁]
          · obtain rfl : i₁ = j := le_antisymm h₁₂ (by simpa using h₄)
            exact mapEq_rfl hobj i₁ hi₂

end Iteration

end SuccStruct

end SmallObject

end CategoryTheory
