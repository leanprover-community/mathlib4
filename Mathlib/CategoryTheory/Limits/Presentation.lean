/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# (Co)limit presentations

Let `J` and `C` be categories and `X : C`. We define type `ColimitPresentation J X` that contains
the data of objects `Dⱼ` and natural maps `sⱼ : Dⱼ ⟶ X` that make `X` the colimit of the `Dⱼ`.

(See `Mathlib/CategoryTheory/Presentable/ColimitPresentation.lean` for the construction of a
presentation of a colimit of objects that are equipped with presentations.)

## Main definitions:

- `CategoryTheory.Limits.ColimitPresentation`: A colimit presentation of `X` over `J` is a diagram
  `{Dᵢ}` in `C` and natural maps `sᵢ : Dᵢ ⟶ X` making `X` into the colimit of the `Dᵢ`.
- `CategoryTheory.Limits.LimitPresentation`: A limit presentation of `X` over `J` is a diagram
  `{Dᵢ}` in `C` and natural maps `sᵢ : X ⟶ Dᵢ` making `X` into the limit of the `Dᵢ`.

## TODOs:

- Refactor `TransfiniteCompositionOfShape` so that it extends `ColimitPresentation`.
-/

@[expose] public section

universe s t w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- A colimit presentation of `X` over `J` is a diagram `{Dᵢ}` in `C` and natural maps
`sᵢ : Dᵢ ⟶ X` making `X` into the colimit of the `Dᵢ`. -/
structure ColimitPresentation (J : Type w) [Category.{t} J] (X : C) where
  /-- The diagram `{Dᵢ}`. -/
  diag : J ⥤ C
  /-- The natural maps `sᵢ : Dᵢ ⟶ X`. -/
  ι : diag ⟶ (Functor.const J).obj X
  /-- `X` is the colimit of the `Dᵢ` via `sᵢ`. -/
  isColimit : IsColimit (Cocone.mk _ ι)

variable {J : Type w} [Category.{t} J] {X : C}

namespace ColimitPresentation

initialize_simps_projections ColimitPresentation (-isColimit)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma w (pres : ColimitPresentation J X) {i j : J} (f : i ⟶ j) :
    pres.diag.map f ≫ pres.ι.app j = pres.ι.app i := by
  simp

/-- The cocone associated to a colimit presentation. -/
abbrev cocone (pres : ColimitPresentation J X) : Cocone pres.diag :=
  Cocone.mk _ pres.ι

lemma hasColimit (pres : ColimitPresentation J X) : HasColimit pres.diag :=
  ⟨_, pres.isColimit⟩

/-- The canonical colimit presentation of any object over a point. -/
@[simps]
noncomputable
def self (X : C) : ColimitPresentation PUnit.{s + 1} X where
  diag := (Functor.const _).obj X
  ι := 𝟙 _
  isColimit := isColimitConstCocone _ _

/-- If `F : J ⥤ C` is a functor that has a colimit, then this is the obvious
colimit presentation of `colimit F`. -/
noncomputable def colimit (F : J ⥤ C) [HasColimit F] :
    ColimitPresentation J (colimit F) where
  diag := F
  ι := _
  isColimit := colimit.isColimit _

/-- If `F` preserves colimits of shape `J`, it maps colimit presentations of `X` to
colimit presentations of `F(X)`. -/
@[simps]
noncomputable
def map (P : ColimitPresentation J X) {D : Type*} [Category* D] (F : C ⥤ D)
    [PreservesColimitsOfShape J F] : ColimitPresentation J (F.obj X) where
  diag := P.diag ⋙ F
  ι := Functor.whiskerRight P.ι F ≫ (F.constComp _ _).hom
  isColimit := (isColimitOfPreserves F P.isColimit).ofIsoColimit (Cocone.ext (.refl _) (by simp))

/-- If `P` is a colimit presentation of `X`, it is possible to define another
colimit presentation of `X` where `P.diag` is replaced by an isomorphic functor. -/
@[simps]
def changeDiag (P : ColimitPresentation J X) {F : J ⥤ C} (e : F ≅ P.diag) :
    ColimitPresentation J X where
  diag := F
  ι := e.hom ≫ P.ι
  isColimit := (IsColimit.precomposeHomEquiv e _).2 P.isColimit

/-- Map a colimit presentation under an isomorphism. -/
@[simps]
def ofIso (P : ColimitPresentation J X) {Y : C} (e : X ≅ Y) : ColimitPresentation J Y where
  diag := P.diag
  ι := P.ι ≫ (Functor.const J).map e.hom
  isColimit := P.isColimit.ofIsoColimit (Cocone.ext e fun _ ↦ rfl)

/-- Change the index category of a colimit presentation. -/
@[simps]
noncomputable
def reindex (P : ColimitPresentation J X) {J' : Type*} [Category* J'] (F : J' ⥤ J) [F.Final] :
    ColimitPresentation J' X where
  diag := F ⋙ P.diag
  ι := F.whiskerLeft P.ι
  isColimit := (Functor.Final.isColimitWhiskerEquiv F _).symm P.isColimit

end ColimitPresentation

/-- A limit presentation of `X` over `J` is a diagram `{Dᵢ}` in `C` and natural maps
`sᵢ : X ⟶ Dᵢ` making `X` into the limit of the `Dᵢ`. -/
structure LimitPresentation (J : Type w) [Category.{t} J] (X : C) where
  /-- The diagram `{Dᵢ}`. -/
  diag : J ⥤ C
  /-- The natural maps `sᵢ : X ⟶ Dᵢ`. -/
  π : (Functor.const J).obj X ⟶ diag
  /-- `X` is the limit of the `Dᵢ` via `sᵢ`. -/
  isLimit : IsLimit (Cone.mk _ π)

variable {J : Type w} [Category.{t} J] {X : C}

namespace LimitPresentation

initialize_simps_projections LimitPresentation (-isLimit)

@[reassoc]
lemma w (pres : LimitPresentation J X) {i j : J} (f : i ⟶ j) :
    pres.π.app i ≫ pres.diag.map f = pres.π.app j := by
  simpa using (pres.π.naturality f).symm

/-- The cone associated to a limit presentation. -/
abbrev cone (pres : LimitPresentation J X) : Cone pres.diag :=
  Cone.mk _ pres.π

lemma hasLimit (pres : LimitPresentation J X) : HasLimit pres.diag :=
  ⟨_, pres.isLimit⟩

/-- The canonical limit presentation of any object over a point. -/
@[simps]
noncomputable
def self (X : C) : LimitPresentation PUnit.{s + 1} X where
  diag := (Functor.const _).obj X
  π := 𝟙 _
  isLimit := isLimitConstCone _ _

/-- If `F : J ⥤ C` is a functor that has a limit, then this is the obvious
limit presentation of `limit F`. -/
noncomputable def limit (F : J ⥤ C) [HasLimit F] :
    LimitPresentation J (limit F) where
  diag := F
  π := _
  isLimit := limit.isLimit _

/-- If `F` preserves limits of shape `J`, it maps limit presentations of `X` to
limit presentations of `F(X)`. -/
@[simps]
noncomputable
def map (P : LimitPresentation J X) {D : Type*} [Category* D] (F : C ⥤ D)
    [PreservesLimitsOfShape J F] : LimitPresentation J (F.obj X) where
  diag := P.diag ⋙ F
  π := (F.constComp _ _).inv ≫ Functor.whiskerRight P.π F
  isLimit := (isLimitOfPreserves F P.isLimit).ofIsoLimit (Cone.ext (.refl _) (by simp))

/-- If `P` is a limit presentation of `X`, it is possible to define another
limit presentation of `X` where `P.diag` is replaced by an isomorphic functor. -/
@[simps]
def changeDiag (P : LimitPresentation J X) {F : J ⥤ C} (e : F ≅ P.diag) :
    LimitPresentation J X where
  diag := F
  π := P.π ≫ e.inv
  isLimit := (IsLimit.postcomposeHomEquiv e.symm _).2 P.isLimit

/-- Map a limit presentation under an isomorphism. -/
@[simps]
def ofIso (P : LimitPresentation J X) {Y : C} (e : X ≅ Y) : LimitPresentation J Y where
  diag := P.diag
  π := (Functor.const J).map e.inv ≫ P.π
  isLimit := P.isLimit.ofIsoLimit (Cone.ext e)

/-- Change the index category of a limit presentation. -/
@[simps]
noncomputable
def reindex (P : LimitPresentation J X) {J' : Type*} [Category* J'] (F : J' ⥤ J) [F.Initial] :
    LimitPresentation J' X where
  diag := F ⋙ P.diag
  π := F.whiskerLeft P.π
  isLimit := (Functor.Initial.isLimitWhiskerEquiv F _).symm P.isLimit

end LimitPresentation

end CategoryTheory.Limits
