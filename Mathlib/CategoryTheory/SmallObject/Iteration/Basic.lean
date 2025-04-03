/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.SuccPred.Limit

/-! # Transfinite iterations of a functor

In this file, given a functor `Φ : C ⥤ C` and a natural transformation
`ε : 𝟭 C ⟶ Φ`, we shall define the transfinite iterations of `Φ` (TODO).

Given `j : J` where `J` is a well ordered set, we first introduce
a category `Iteration ε j`. An object in this category consists of
a functor `F : Set.Iic j ⥤ C ⥤ C` equipped with the data
which makes it the `i`th-iteration of `Φ` for all `i` such that `i ≤ j`.
Under suitable assumptions on `C`, we shall show that this category
`Iteration ε j` is equivalent to the punctual category (TODO).
We shall study morphisms in this category, showing first that
there is at most one morphism between two morphisms (done), and secondly,
that there does always exist a unique morphism between
two objects (TODO). Then, we shall show the existence of
an object (TODO). In these proofs, which are all done using
transfinite induction, we have to treat three cases separately:
* the case `j = ⊥`;
* the case `j` is a successor;
* the case `j` is a limit element.

-/

universe u

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C] {Φ : C ⥤ C} (ε : 𝟭 C ⟶ Φ) {J : Type u}

namespace Functor

namespace Iteration

variable [Preorder J] {j : J} (F : Set.Iic j ⥤ C)

/-- The map `F.obj ⟨i, _⟩ ⟶ F.obj ⟨Order.succ i, _⟩` when `F : Set.Iic j ⥤ C`
and `i : J` is such that `i < j`. -/
noncomputable abbrev mapSucc' [SuccOrder J] (i : J) (hi : i < j) :
    F.obj ⟨i, hi.le⟩ ⟶ F.obj ⟨Order.succ i, Order.succ_le_of_lt hi⟩ :=
  F.map <| homOfLE <| Subtype.mk_le_mk.2 <| Order.le_succ i

variable {i : J} (hi : i ≤ j)

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

end Iteration

/-- The category of `j`th iterations of a functor `Φ` equipped with a natural
transformation `ε : 𝟭 C ⟶ Φ`. An object consists of the data of all iterations
of `Φ` for `i : J` such that `i ≤ j` (this is the field `F`). Such objects are
equipped with data and properties which characterizes the iterations up to a unique
isomorphism for the three types of elements: `⊥`, successors, limit elements. -/
structure Iteration [Preorder J] [OrderBot J] [SuccOrder J] (j : J) where
  /-- The data of all `i`th iterations for `i : J` such that `i ≤ j`. -/
  F : Set.Iic j ⥤ C ⥤ C
  /-- The zeroth iteration is the identity functor. -/
  isoZero : F.obj ⟨⊥, bot_le⟩ ≅ 𝟭 C
  /-- The iteration on a successor element is obtained by composition of
  the previous iteration with `Φ`. -/
  isoSucc (i : J) (hi : i < j) : F.obj ⟨Order.succ i, Order.succ_le_of_lt hi⟩ ≅ F.obj ⟨i, hi.le⟩ ⋙ Φ
  /-- The natural map from an iteration to its successor is induced by `ε`. -/
  mapSucc'_eq (i : J) (hi : i < j) :
    Iteration.mapSucc' F i hi = whiskerLeft _ ε ≫ (isoSucc i hi).inv
  /-- If `i` is a limit element, the `i`th iteration is the colimit
  of `k`th iterations for `k < i`. -/
  isColimit (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
    IsColimit (Iteration.coconeOfLE F hij)

namespace Iteration

variable {ε}
variable {j : J}

section

variable [Preorder J] [OrderBot J] [SuccOrder J] (iter : Φ.Iteration ε j)

/-- For `iter : Φ.Iteration.ε j`, this is the map
`iter.F.obj ⟨i, _⟩ ⟶ iter.F.obj ⟨Order.succ i, _⟩` if `i : J` is such that `i < j`. -/
noncomputable abbrev mapSucc (i : J) (hi : i < j) :
    iter.F.obj ⟨i, hi.le⟩ ⟶ iter.F.obj ⟨Order.succ i, Order.succ_le_of_lt hi⟩ :=
  mapSucc' iter.F i hi

lemma mapSucc_eq (i : J) (hi : i < j) :
    iter.mapSucc i hi = whiskerLeft _ ε ≫ (iter.isoSucc i hi).inv :=
  iter.mapSucc'_eq _ hi

end

section

variable [Preorder J] [OrderBot J] [SuccOrder J] (iter₁ iter₂ : Φ.Iteration ε j)

/-- A morphism between two objects `iter₁` and `iter₂` in the
category `Φ.Iteration ε j` of `j`th iterations of a functor `Φ`
equipped with a natural transformation `ε : 𝟭 C ⟶ Φ` consists of a natural
transformation `natTrans : iter₁.F ⟶ iter₂.F` which is compatible with the
isomorphisms `isoZero` and `isoSucc`. -/
structure Hom where
  /-- A natural transformation `iter₁.F ⟶ iter₂.F` -/
  natTrans : iter₁.F ⟶ iter₂.F
  natTrans_app_zero :
    natTrans.app ⟨⊥, bot_le⟩ = iter₁.isoZero.hom ≫ iter₂.isoZero.inv := by aesop_cat
  natTrans_app_succ (i : J) (hi : i < j) :
    natTrans.app ⟨Order.succ i, Order.succ_le_of_lt hi⟩ = (iter₁.isoSucc i hi).hom ≫
      whiskerRight (natTrans.app ⟨i, hi.le⟩) _ ≫ (iter₂.isoSucc i hi).inv := by aesop_cat

namespace Hom

attribute [simp, reassoc] natTrans_app_zero

/-- The identity morphism in the category `Φ.Iteration ε j`. -/
@[simps]
def id : Hom iter₁ iter₁ where
  natTrans := 𝟙 _

variable {iter₁ iter₂}

-- Note: this is not made a global ext lemma because it is shown below
-- that the type of morphisms is a subsingleton.
lemma ext' {f g : Hom iter₁ iter₂} (h : f.natTrans = g.natTrans) : f = g := by
  cases f
  cases g
  subst h
  rfl

attribute [local ext] ext'

/-- The composition of morphisms in the category `Φ.Iteration ε j`. -/
@[simps]
def comp {iter₃ : Iteration ε j} (f : Hom iter₁ iter₂) (g : Hom iter₂ iter₃) :
    Hom iter₁ iter₃ where
  natTrans := f.natTrans ≫ g.natTrans
  natTrans_app_succ i hi := by simp [natTrans_app_succ _ _ hi]

instance : Category (Iteration ε j) where
  Hom := Hom
  id := id
  comp := comp

instance {J} {j : J} [PartialOrder J] [OrderBot J] [WellFoundedLT J] [SuccOrder J]
    {iter₁ iter₂ : Iteration ε j} :
    Subsingleton (iter₁ ⟶ iter₂) where
  allEq f g := by
    apply ext'
    suffices ∀ i hi, f.natTrans.app ⟨i, hi⟩ = g.natTrans.app ⟨i, hi⟩ by
      ext ⟨i, hi⟩ : 2
      apply this
    intro i
    induction i using SuccOrder.limitRecOn with
    | hm j H =>
      obtain rfl := H.eq_bot
      simp [natTrans_app_zero]
    | hs j H IH =>
      intro hj
      simp [Hom.natTrans_app_succ, IH, (Order.lt_succ_of_not_isMax H).trans_le hj]
    | hl j H IH =>
      refine fun hj ↦ (iter₁.isColimit j H hj).hom_ext ?_
      rintro ⟨k, hk⟩
      simp [IH k hk]

end Hom

@[simp]
lemma natTrans_id : Hom.natTrans (𝟙 iter₁) = 𝟙 _ := rfl

variable {iter₁ iter₂}

@[simp, reassoc]
lemma natTrans_comp {iter₃ : Iteration ε j} (φ : iter₁ ⟶ iter₂) (ψ : iter₂ ⟶ iter₃) :
    (φ ≫ ψ).natTrans = φ.natTrans ≫ ψ.natTrans := rfl

@[reassoc]
lemma natTrans_naturality (φ : iter₁ ⟶ iter₂) (i₁ i₂ : J) (h : i₁ ≤ i₂) (h' : i₂ ≤ j) :
    iter₁.F.map (by exact homOfLE h) ≫ φ.natTrans.app ⟨i₂, h'⟩ =
      φ.natTrans.app ⟨i₁, h.trans h'⟩ ≫ iter₂.F.map (by exact homOfLE h) := by
  apply φ.natTrans.naturality

variable (ε) in
/-- The evaluation functor `Iteration ε j ⥤ C ⥤ C` at `i : J` when `i ≤ j`. -/
@[simps]
def eval {i : J} (hi : i ≤ j) : Iteration ε j ⥤ C ⥤ C where
  obj iter := iter.F.obj ⟨i, hi⟩
  map φ := φ.natTrans.app _

/-- Given `iter : Iteration ε j` and `i : J` such that `i ≤ j`, this is the
induced element in `Iteration ε i`. -/
@[simps F isoZero isoSucc]
def trunc (iter : Iteration ε j) {i : J} (hi : i ≤ j) : Iteration ε i where
  F := restrictionLE (iter.F) hi
  isoZero := iter.isoZero
  isoSucc k hk := iter.isoSucc k (lt_of_lt_of_le hk hi)
  mapSucc'_eq k hk := iter.mapSucc'_eq k (lt_of_lt_of_le hk hi)
  isColimit k hk' hk := iter.isColimit k hk' (hk.trans hi)

variable (ε) in
/-- The truncation functor `Iteration ε j ⥤ Iteration ε i` when `i ≤ j`. -/
@[simps obj]
def truncFunctor {i : J} (hi : i ≤ j) : Iteration ε j ⥤ Iteration ε i where
  obj iter := iter.trunc hi
  map {iter₁ iter₂} φ :=
    { natTrans := whiskerLeft _ φ.natTrans
      natTrans_app_succ := fun k hk => φ.natTrans_app_succ k (lt_of_lt_of_le hk hi) }

@[simp]
lemma truncFunctor_map_natTrans_app
    (φ : iter₁ ⟶ iter₂) {i : J} (hi : i ≤ j) (k : J) (hk : k ≤ i) :
    ((truncFunctor ε hi).map φ).natTrans.app ⟨k, hk⟩ =
      φ.natTrans.app ⟨k, hk.trans hi⟩ := rfl

end

namespace Hom

variable [PartialOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  (iter₁ iter₂ : Φ.Iteration ε j)

lemma congr_app (φ φ' : iter₁ ⟶ iter₂) (i : J) (hi : i ≤ j) :
    φ.natTrans.app ⟨i, hi⟩ = φ'.natTrans.app ⟨i, hi⟩ := by
  obtain rfl := Subsingleton.elim φ φ'
  rfl

end Hom

end Iteration

end Functor

end CategoryTheory
