/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.Order.IsWellOrderLimitElement

/-! # Transfinite iterations of a functor

In this file, given a functor `Φ : C ⥤ C` and a natural transformation
`ε : 𝟭 C ⟶ Φ`, we shall define the transfinite iterations of `Φ` (TODO).

Given `j : J` where `J` is a well ordered set, we first introduce
a category `Iteration ε j`. An object in this category consists of
a functor `F : { i // i ≤ j } ⥤ C ⥤ C` equipped with the data
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

variable {C : Type*} [Category C] {Φ : C ⥤ C} (ε : 𝟭 C ⟶ Φ)
  {J : Type u} [LinearOrder J] [IsWellOrder J (· < ·)] [OrderBot J]

namespace Functor

namespace Iteration

variable {j : J} (F : { i // i ≤ j } ⥤ C)

/-- The map `F.obj ⟨i, _⟩ ⟶ F.obj ⟨wellOrderSucc i, _⟩` when `F : { i // i ≤ j } ⥤ C`
and `i : J` is such that `i < j`. -/
noncomputable abbrev mapSucc' (i : J) (hi : i < j) :
    F.obj ⟨i, hi.le⟩ ⟶ F.obj ⟨wellOrderSucc i, wellOrderSucc_le hi⟩ :=
  F.map (homOfLE (by simpa only [Subtype.mk_le_mk] using self_le_wellOrderSucc i))

variable {i : J} (hi : i ≤ j)

/-- The functor `{ k // k < i } ⥤ C` obtained by "restriction" of `F : { i // i ≤ j } ⥤ C`
when `i ≤ j`. -/
def restrictionLT : { k // k < i } ⥤ C :=
  (monotone_inclusion_lt_le_of_le hi).functor ⋙ F

@[simp]
lemma restrictionLT_obj (k : J) (hk : k < i) :
    (restrictionLT F hi).obj ⟨k, hk⟩ = F.obj ⟨k, hk.le.trans hi⟩ := rfl

@[simp]
lemma restrictionLT_map {k₁ k₂ : { k // k < i }} (φ : k₁ ⟶ k₂) :
    (restrictionLT F hi).map φ = F.map (homOfLE (by simpa using leOfHom φ)) := rfl

/-- Given `F : { i // i ≤ j } ⥤ C`, `i : J` such that `hi : i ≤ j`, this is the
cocone consisting of all maps `F.obj ⟨k, hk⟩ ⟶ F.obj ⟨i, hi⟩` for `k : J` such that `k < i`. -/
@[simps]
def coconeOfLE : Cocone (restrictionLT F hi) where
  pt := F.obj ⟨i, hi⟩
  ι :=
    { app := fun ⟨k, hk⟩ => F.map (homOfLE (by simpa using hk.le))
      naturality := fun ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ _ => by
        simp [comp_id, ← Functor.map_comp, homOfLE_comp] }

end Iteration

/-- The category of `j`th iterations of a functor `Φ` equipped with a natural
transformation `ε : 𝟭 C ⟶ Φ`. An object consists of the data of all iterations
of `Φ` for `i : J` such that `i ≤ j` (this is the field `F`). Such objects are
equipped with data and properties which characterizes the iterations up to a unique
isomorphism for the three types of elements: `⊥`, successors, limit elements. -/
structure Iteration (j : J) where
  /-- The data of all `i`th iterations for `i : J` such that `i ≤ j`. -/
  F : { i // i ≤ j } ⥤ C ⥤ C
  /-- The zeroth iteration is the identity functor. -/
  isoZero : F.obj ⟨⊥, bot_le⟩ ≅ 𝟭 C
  /-- The iteration on a successor element is obtained by composition of
  the previous iteration with `Φ`. -/
  isoSucc (i : J) (hi : i < j) :
    F.obj ⟨wellOrderSucc i, wellOrderSucc_le hi⟩ ≅ F.obj ⟨i, hi.le⟩ ⋙ Φ
  /-- The natural map from an iteration to its successor is induced by `ε`. -/
  mapSucc'_eq (i : J) (hi : i < j) :
    Iteration.mapSucc' F i hi = whiskerLeft _ ε ≫ (isoSucc i hi).inv
  /-- If `i` is a limit element, the `i`th iteration is the colimit
  of `k`th iterations for `k < i`. -/
  isColimit (i : J) [IsWellOrderLimitElement i] (hi : i ≤ j) :
    IsColimit (Iteration.coconeOfLE F hi)

namespace Iteration

variable {ε}
variable {j : J}

section

variable (iter : Φ.Iteration ε j)

/-- For `iter : Φ.Iteration.ε j`, this is the map
`iter.F.obj ⟨i, _⟩ ⟶ iter.F.obj ⟨wellOrderSucc i, _⟩` if `i : J` is such that `i < j`. -/
noncomputable abbrev mapSucc (i : J) (hi : i < j) :
    iter.F.obj ⟨i, hi.le⟩ ⟶ iter.F.obj ⟨wellOrderSucc i, wellOrderSucc_le hi⟩ :=
  mapSucc' iter.F i hi

lemma mapSucc_eq (i : J) (hi : i < j) :
    iter.mapSucc i hi = whiskerLeft _ ε ≫ (iter.isoSucc i hi).inv :=
  iter.mapSucc'_eq _ hi

end

variable (iter₁ iter₂ iter₃ : Φ.Iteration ε j)

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
    natTrans.app ⟨wellOrderSucc i, wellOrderSucc_le hi⟩ = (iter₁.isoSucc i hi).hom ≫
      whiskerRight (natTrans.app ⟨i, hi.le⟩) _ ≫ (iter₂.isoSucc i hi).inv := by aesop_cat

namespace Hom

attribute [simp, reassoc] natTrans_app_zero

/-- The identity morphism in the category `Φ.Iteration ε j`. -/
@[simps]
def id : Hom iter₁ iter₁ where
  natTrans := 𝟙 _

variable {iter₁ iter₂ iter₃}

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

instance : Subsingleton (iter₁ ⟶ iter₂) where
  allEq f g := ext' (by
    let P := fun (i : J) => ∀ (hi : i ≤ j), f.natTrans.app ⟨i, hi⟩ = g.natTrans.app ⟨i, hi⟩
    suffices ∀ (i : J), P i by
      ext ⟨i, hi⟩ : 2
      apply this
    refine fun _ => WellFoundedLT.induction _ (fun i hi hi' => ?_)
    obtain rfl|⟨i, rfl, hi''⟩|_ := eq_bot_or_eq_succ_or_isWellOrderLimitElement i
    · simp only [natTrans_app_zero]
    · simp only [Hom.natTrans_app_succ _ i (lt_of_lt_of_le hi'' hi'), hi i hi'']
    · exact (iter₁.isColimit i hi').hom_ext (fun ⟨k, hk⟩ => by simp [hi k hk]))

end Hom

end Iteration

end Functor

end CategoryTheory
