/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence

/-!
# Limits and the category of (co)cones

This files contains results that stem from the limit API. For the definition and the category
instance of `Cone`, please refer to `CategoryTheory/Limits/Cones.lean`.

## Main results
* The category of cones on `F : J ⥤ C` is equivalent to the category
  `CostructuredArrow (const J) F`.
* A cone is limiting iff it is terminal in the category of cones. As a corollary, an equivalence of
  categories of cones preserves limiting properties.

-/


namespace CategoryTheory.Limits

open CategoryTheory CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

/-- Given a cone `c` over `F`, we can interpret the legs of `c` as structured arrows
    `c.pt ⟶ F.obj -`. -/
@[simps]
def Cone.toStructuredArrow {F : J ⥤ C} (c : Cone F) : J ⥤ StructuredArrow c.pt F where
  obj j := StructuredArrow.mk (c.π.app j)
  map f := StructuredArrow.homMk f

/-- If `F` has a limit, then the limit projections can be interpreted as structured arrows
    `limit F ⟶ F.obj -`. -/
@[simps]
noncomputable def limit.toStructuredArrow (F : J ⥤ C) [HasLimit F] :
    J ⥤ StructuredArrow (limit F) F where
  obj j := StructuredArrow.mk (limit.π F j)
  map f := StructuredArrow.homMk f

/-- `Cone.toStructuredArrow` can be expressed in terms of `Functor.toStructuredArrow`. -/
def Cone.toStructuredArrowIsoToStructuredArrow {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ≅ (𝟭 J).toStructuredArrow c.pt F c.π.app (by simp) :=
  Iso.refl _

/-- `Functor.toStructuredArrow` can be expressed in terms of `Cone.toStructuredArrow`. -/
def _root_.CategoryTheory.Functor.toStructuredArrowIsoToStructuredArrow (G : J ⥤ K) (X : C)
    (F : K ⥤ C) (f : (Y : J) → X ⟶ F.obj (G.obj Y))
    (h : ∀ {Y Z : J} (g : Y ⟶ Z), f Y ≫ F.map (G.map g) = f Z) :
    G.toStructuredArrow X F f h ≅
      (Cone.mk X ⟨f, by simp [h]⟩).toStructuredArrow ⋙ StructuredArrow.pre _ _ _ :=
  Iso.refl _

/-- Interpreting the legs of a cone as a structured arrow and then forgetting the arrow again does
    nothing. -/
@[simps!]
def Cone.toStructuredArrowCompProj {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.proj _ _ ≅ 𝟭 J :=
  Iso.refl _

@[simp]
lemma Cone.toStructuredArrow_comp_proj {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.proj _ _ = 𝟭 J :=
  rfl

/-- Interpreting the legs of a cone as a structured arrow, interpreting this arrow as an arrow over
    the cone point, and finally forgetting the arrow is the same as just applying the functor the
    cone was over. -/
@[simps!]
def Cone.toStructuredArrowCompToUnderCompForget {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.toUnder _ _ ⋙ Under.forget _ ≅ F :=
  Iso.refl _

@[simp]
lemma Cone.toStructuredArrow_comp_toUnder_comp_forget {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.toUnder _ _ ⋙ Under.forget _ = F :=
  rfl

/-- A cone `c` on `F : J ⥤ C` lifts to a cone in `Over c.pt` with cone point `𝟙 c.pt`. -/
@[simps]
def Cone.toUnder {F : J ⥤ C} (c : Cone F) :
    Cone (c.toStructuredArrow ⋙ StructuredArrow.toUnder _ _) where
  pt := Under.mk (𝟙 c.pt)
  π := { app := fun j ↦ Under.homMk (c.π.app j) (by simp) }

/-- The limit cone for `F : J ⥤ C` lifts to a cocone in `Under (limit F)` with cone point
    `𝟙 (limit F)`. This is automatically also a limit cone. -/
noncomputable def limit.toUnder (F : J ⥤ C) [HasLimit F] :
    Cone (limit.toStructuredArrow F ⋙ StructuredArrow.toUnder _ _) where
  pt := Under.mk (𝟙 (limit F))
  π := { app := fun j ↦ Under.homMk (limit.π F j) (by simp) }

/-- `c.toUnder` is a lift of `c` under the forgetful functor. -/
@[simps!]
def Cone.mapConeToUnder {F : J ⥤ C} (c : Cone F) : (Under.forget c.pt).mapCone c.toUnder ≅ c :=
  Iso.refl _

/-- Given a diagram of `StructuredArrow X F`s, we may obtain a cone with cone point `X`. -/
@[simps!]
def Cone.fromStructuredArrow (F : C ⥤ D) {X : D} (G : J ⥤ StructuredArrow X F) :
    Cone (G ⋙ StructuredArrow.proj X F ⋙ F) where
  pt := X
  π := { app := fun j ↦ (G.obj j).hom }

/-- Given a cone `c : Cone K` and a map `f : X ⟶ F.obj c.X`, we can construct a cone of structured
arrows over `X` with `f` as the cone point.
-/
@[simps]
def Cone.toStructuredArrowCone {K : J ⥤ C} (c : Cone K) (F : C ⥤ D) {X : D} (f : X ⟶ F.obj c.pt) :
    Cone ((F.mapCone c).toStructuredArrow ⋙ StructuredArrow.map f ⋙ StructuredArrow.pre _ K F) where
  pt := StructuredArrow.mk f
  π := { app := fun j ↦ StructuredArrow.homMk (c.π.app j) rfl }

/-- Construct an object of the category `(Δ ↓ F)` from a cone on `F`. This is part of an
    equivalence, see `Cone.equivCostructuredArrow`. -/
@[simps]
def Cone.toCostructuredArrow (F : J ⥤ C) : Cone F ⥤ CostructuredArrow (const J) F where
  obj c := CostructuredArrow.mk c.π
  map f := CostructuredArrow.homMk f.hom

/-- Construct a cone on `F` from an object of the category `(Δ ↓ F)`. This is part of an
    equivalence, see `Cone.equivCostructuredArrow`. -/
@[simps]
def Cone.fromCostructuredArrow (F : J ⥤ C) : CostructuredArrow (const J) F ⥤ Cone F where
  obj c := ⟨c.left, c.hom⟩
  map f :=
    { hom := f.left
      w := fun j ↦ by
        convert congr_fun (congr_arg NatTrans.app f.w) j
        simp }

/-- The category of cones on `F` is just the comma category `(Δ ↓ F)`, where `Δ` is the constant
    functor. -/
@[simps]
def Cone.equivCostructuredArrow (F : J ⥤ C) : Cone F ≌ CostructuredArrow (const J) F where
  functor := Cone.toCostructuredArrow F
  inverse := Cone.fromCostructuredArrow F
  unitIso := NatIso.ofComponents Cones.eta
  counitIso := NatIso.ofComponents fun _ ↦ (CostructuredArrow.eta _).symm

/-- A cone is a limit cone iff it is terminal. -/
def Cone.isLimitEquivIsTerminal {F : J ⥤ C} (c : Cone F) : IsLimit c ≃ IsTerminal c :=
  IsLimit.isoUniqueConeMorphism.toEquiv.trans
    { toFun := fun _ ↦ IsTerminal.ofUnique _
      invFun := fun h s ↦ ⟨⟨IsTerminal.from h s⟩, fun a ↦ IsTerminal.hom_ext h a _⟩
      left_inv := by cat_disch
      right_inv := by cat_disch }

theorem hasLimit_iff_hasTerminal_cone (F : J ⥤ C) : HasLimit F ↔ HasTerminal (Cone F) :=
  ⟨fun _ ↦ (Cone.isLimitEquivIsTerminal _ (limit.isLimit F)).hasTerminal, fun h ↦
    haveI : HasTerminal (Cone F) := h
    ⟨⟨⟨⊤_ _, (Cone.isLimitEquivIsTerminal _).symm terminalIsTerminal⟩⟩⟩⟩

theorem hasLimitsOfShape_iff_isLeftAdjoint_const :
    HasLimitsOfShape J C ↔ IsLeftAdjoint (const J : C ⥤ _) :=
  calc
    HasLimitsOfShape J C ↔ ∀ F : J ⥤ C, HasLimit F :=
      ⟨fun h ↦ h.has_limit, fun h ↦ HasLimitsOfShape.mk⟩
    _ ↔ ∀ F : J ⥤ C, HasTerminal (Cone F) := forall_congr' hasLimit_iff_hasTerminal_cone
    _ ↔ ∀ F : J ⥤ C, HasTerminal (CostructuredArrow (const J) F) :=
      (forall_congr' fun F ↦ (Cone.equivCostructuredArrow F).hasTerminal_iff)
    _ ↔ (IsLeftAdjoint (const J : C ⥤ _)) :=
      isLeftAdjoint_iff_hasTerminal_costructuredArrow.symm

theorem IsLimit.liftConeMorphism_eq_isTerminal_from {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
    (s : Cone F) : hc.liftConeMorphism s = IsTerminal.from (Cone.isLimitEquivIsTerminal _ hc) _ :=
  rfl

theorem IsTerminal.from_eq_liftConeMorphism {F : J ⥤ C} {c : Cone F} (hc : IsTerminal c)
    (s : Cone F) :
    IsTerminal.from hc s = ((Cone.isLimitEquivIsTerminal _).symm hc).liftConeMorphism s :=
  (IsLimit.liftConeMorphism_eq_isTerminal_from (c.isLimitEquivIsTerminal.symm hc) s).symm

/-- If `G : Cone F ⥤ Cone F'` preserves terminal objects, it preserves limit cones. -/
noncomputable def IsLimit.ofPreservesConeTerminal {F : J ⥤ C} {F' : K ⥤ D} (G : Cone F ⥤ Cone F')
    [PreservesLimit (Functor.empty.{0} _) G] {c : Cone F} (hc : IsLimit c) : IsLimit (G.obj c) :=
  (Cone.isLimitEquivIsTerminal _).symm <| (Cone.isLimitEquivIsTerminal _ hc).isTerminalObj _ _

/-- If `G : Cone F ⥤ Cone F'` reflects terminal objects, it reflects limit cones. -/
noncomputable def IsLimit.ofReflectsConeTerminal {F : J ⥤ C} {F' : K ⥤ D} (G : Cone F ⥤ Cone F')
    [ReflectsLimit (Functor.empty.{0} _) G] {c : Cone F} (hc : IsLimit (G.obj c)) : IsLimit c :=
  (Cone.isLimitEquivIsTerminal _).symm <| (Cone.isLimitEquivIsTerminal _ hc).isTerminalOfObj _ _

/-- Given a cocone `c` over `F`, we can interpret the legs of `c` as costructured arrows
    `F.obj - ⟶ c.pt`. -/
@[simps]
def Cocone.toCostructuredArrow {F : J ⥤ C} (c : Cocone F) : J ⥤ CostructuredArrow F c.pt where
  obj j := CostructuredArrow.mk (c.ι.app j)
  map f := CostructuredArrow.homMk f

/-- If `F` has a colimit, then the colimit inclusions can be interpreted as costructured arrows
    `F.obj - ⟶ colimit F`. -/
@[simps]
noncomputable def colimit.toCostructuredArrow (F : J ⥤ C) [HasColimit F] :
    J ⥤ CostructuredArrow F (colimit F) where
  obj j := CostructuredArrow.mk (colimit.ι F j)
  map f := CostructuredArrow.homMk f

/-- `Cocone.toCostructuredArrow` can be expressed in terms of `Functor.toCostructuredArrow`. -/
def Cocone.toCostructuredArrowIsoToCostructuredArrow {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ≅ (𝟭 J).toCostructuredArrow F c.pt c.ι.app (by simp) :=
  Iso.refl _

/-- `Functor.toCostructuredArrow` can be expressed in terms of `Cocone.toCostructuredArrow`. -/
def _root_.CategoryTheory.Functor.toCostructuredArrowIsoToCostructuredArrow (G : J ⥤ K)
    (F : K ⥤ C) (X : C) (f : (Y : J) → F.obj (G.obj Y) ⟶ X)
    (h : ∀ {Y Z : J} (g : Y ⟶ Z), F.map (G.map g) ≫ f Z = f Y) :
    G.toCostructuredArrow F X f h ≅
      (Cocone.mk X ⟨f, by simp [h]⟩).toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _ :=
  Iso.refl _

/-- Interpreting the legs of a cocone as a costructured arrow and then forgetting the arrow again
    does nothing. -/
@[simps!]
def Cocone.toCostructuredArrowCompProj {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.proj _ _ ≅ 𝟭 J :=
  Iso.refl _

@[simp]
lemma Cocone.toCostructuredArrow_comp_proj {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.proj _ _ = 𝟭 J :=
  rfl

/-- Interpreting the legs of a cocone as a costructured arrow, interpreting this arrow as an arrow
    over the cocone point, and finally forgetting the arrow is the same as just applying the
    functor the cocone was over. -/
@[simps!]
def Cocone.toCostructuredArrowCompToOverCompForget {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙ Over.forget _ ≅ F :=
  Iso.refl _

@[simp]
lemma Cocone.toCostructuredArrow_comp_toOver_comp_forget {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙ Over.forget _ = F :=
  rfl

/-- A cocone `c` on `F : J ⥤ C` lifts to a cocone in `Over c.pt` with cone point `𝟙 c.pt`. -/
@[simps]
def Cocone.toOver {F : J ⥤ C} (c : Cocone F) :
    Cocone (c.toCostructuredArrow ⋙ CostructuredArrow.toOver _ _) where
  pt := Over.mk (𝟙 c.pt)
  ι := { app := fun j ↦ Over.homMk (c.ι.app j) (by simp) }

/-- The colimit cocone for `F : J ⥤ C` lifts to a cocone in `Over (colimit F)` with cone point
    `𝟙 (colimit F)`. This is automatically also a colimit cocone. -/
@[simps]
noncomputable def colimit.toOver (F : J ⥤ C) [HasColimit F] :
    Cocone (colimit.toCostructuredArrow F ⋙ CostructuredArrow.toOver _ _) where
  pt := Over.mk (𝟙 (colimit F))
  ι := { app := fun j ↦ Over.homMk (colimit.ι F j) (by simp) }

/-- `c.toOver` is a lift of `c` under the forgetful functor. -/
@[simps!]
def Cocone.mapCoconeToOver {F : J ⥤ C} (c : Cocone F) : (Over.forget c.pt).mapCocone c.toOver ≅ c :=
  Iso.refl _

/-- Given a diagram `CostructuredArrow F X`s, we may obtain a cocone with cone point `X`. -/
@[simps!]
def Cocone.fromCostructuredArrow (F : C ⥤ D) {X : D} (G : J ⥤ CostructuredArrow F X) :
    Cocone (G ⋙ CostructuredArrow.proj F X ⋙ F) where
  pt := X
  ι := { app := fun j ↦ (G.obj j).hom }

/-- Given a cocone `c : Cocone K` and a map `f : F.obj c.X ⟶ X`, we can construct a cocone of
    costructured arrows over `X` with `f` as the cone point. -/
@[simps]
def Cocone.toCostructuredArrowCocone {K : J ⥤ C} (c : Cocone K) (F : C ⥤ D) {X : D}
    (f : F.obj c.pt ⟶ X) : Cocone ((F.mapCocone c).toCostructuredArrow ⋙
      CostructuredArrow.map f ⋙ CostructuredArrow.pre _ _ _) where
  pt := CostructuredArrow.mk f
  ι := { app := fun j ↦ CostructuredArrow.homMk (c.ι.app j) rfl }

/-- Construct an object of the category `(F ↓ Δ)` from a cocone on `F`. This is part of an
    equivalence, see `Cocone.equivStructuredArrow`. -/
@[simps]
def Cocone.toStructuredArrow (F : J ⥤ C) : Cocone F ⥤ StructuredArrow F (const J) where
  obj c := StructuredArrow.mk c.ι
  map f := StructuredArrow.homMk f.hom

/-- Construct a cocone on `F` from an object of the category `(F ↓ Δ)`. This is part of an
    equivalence, see `Cocone.equivStructuredArrow`. -/
@[simps]
def Cocone.fromStructuredArrow (F : J ⥤ C) : StructuredArrow F (const J) ⥤ Cocone F where
  obj c := ⟨c.right, c.hom⟩
  map f :=
    { hom := f.right
      w := fun j ↦ by
        convert (congr_fun (congr_arg NatTrans.app f.w) j).symm
        simp }

/-- The category of cocones on `F` is just the comma category `(F ↓ Δ)`, where `Δ` is the constant
    functor. -/
@[simps]
def Cocone.equivStructuredArrow (F : J ⥤ C) : Cocone F ≌ StructuredArrow F (const J) where
  functor := Cocone.toStructuredArrow F
  inverse := Cocone.fromStructuredArrow F
  unitIso := NatIso.ofComponents Cocones.eta
  counitIso := NatIso.ofComponents fun _ ↦ (StructuredArrow.eta _).symm

/-- A cocone is a colimit cocone iff it is initial. -/
def Cocone.isColimitEquivIsInitial {F : J ⥤ C} (c : Cocone F) : IsColimit c ≃ IsInitial c :=
  IsColimit.isoUniqueCoconeMorphism.toEquiv.trans
    { toFun := fun _ ↦ IsInitial.ofUnique _
      invFun := fun h s ↦ ⟨⟨IsInitial.to h s⟩, fun a ↦ IsInitial.hom_ext h a _⟩
      left_inv := by cat_disch
      right_inv := by cat_disch }

theorem hasColimit_iff_hasInitial_cocone (F : J ⥤ C) : HasColimit F ↔ HasInitial (Cocone F) :=
  ⟨fun _ ↦ (Cocone.isColimitEquivIsInitial _ (colimit.isColimit F)).hasInitial, fun h ↦
    haveI : HasInitial (Cocone F) := h
    ⟨⟨⟨⊥_ _, (Cocone.isColimitEquivIsInitial _).symm initialIsInitial⟩⟩⟩⟩

theorem hasColimitsOfShape_iff_isRightAdjoint_const :
    HasColimitsOfShape J C ↔ IsRightAdjoint (const J : C ⥤ _) :=
  calc
    HasColimitsOfShape J C ↔ ∀ F : J ⥤ C, HasColimit F :=
      ⟨fun h ↦ h.has_colimit, fun h ↦ HasColimitsOfShape.mk⟩
    _ ↔ ∀ F : J ⥤ C, HasInitial (Cocone F) := forall_congr' hasColimit_iff_hasInitial_cocone
    _ ↔ ∀ F : J ⥤ C, HasInitial (StructuredArrow F (const J)) :=
      (forall_congr' fun F ↦ (Cocone.equivStructuredArrow F).hasInitial_iff)
    _ ↔ (IsRightAdjoint (const J : C ⥤ _)) :=
      isRightAdjoint_iff_hasInitial_structuredArrow.symm

theorem IsColimit.descCoconeMorphism_eq_isInitial_to {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
    (s : Cocone F) :
    hc.descCoconeMorphism s = IsInitial.to (Cocone.isColimitEquivIsInitial _ hc) _ :=
  rfl

theorem IsInitial.to_eq_descCoconeMorphism {F : J ⥤ C} {c : Cocone F} (hc : IsInitial c)
    (s : Cocone F) :
    IsInitial.to hc s = ((Cocone.isColimitEquivIsInitial _).symm hc).descCoconeMorphism s :=
  (IsColimit.descCoconeMorphism_eq_isInitial_to (c.isColimitEquivIsInitial.symm hc) s).symm

/-- If `G : Cocone F ⥤ Cocone F'` preserves initial objects, it preserves colimit cocones. -/
noncomputable def IsColimit.ofPreservesCoconeInitial {F : J ⥤ C} {F' : K ⥤ D}
    (G : Cocone F ⥤ Cocone F')
    [PreservesColimit (Functor.empty.{0} _) G] {c : Cocone F} (hc : IsColimit c) :
    IsColimit (G.obj c) :=
  (Cocone.isColimitEquivIsInitial _).symm <| (Cocone.isColimitEquivIsInitial _ hc).isInitialObj _ _

/-- If `G : Cocone F ⥤ Cocone F'` reflects initial objects, it reflects colimit cocones. -/
noncomputable def IsColimit.ofReflectsCoconeInitial {F : J ⥤ C} {F' : K ⥤ D}
    (G : Cocone F ⥤ Cocone F')
    [ReflectsColimit (Functor.empty.{0} _) G] {c : Cocone F} (hc : IsColimit (G.obj c)) :
    IsColimit c :=
  (Cocone.isColimitEquivIsInitial _).symm <|
    (Cocone.isColimitEquivIsInitial _ hc).isInitialOfObj _ _

end CategoryTheory.Limits
