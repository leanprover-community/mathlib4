/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sina Hazratpour
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Comma.Over

/-!
# The Grothendieck construction

Given a functor `F : C ⥤ Cat`, the objects of `Grothendieck F`
consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj c`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and
`φ : (F.map β).obj f ⟶ f'`

`Grothendieck.functor` makes the Grothendieck construction into a functor from the functor category
`C ⥤ Cat` to the over category `Over C` in the category of categories.

Categories such as `PresheafedSpace` are in fact examples of this construction,
and it may be interesting to try to generalize some of the development there.

## Implementation notes

Really we should treat `Cat` as a 2-category, and allow `F` to be a 2-functor.

There is also a closely related construction starting with `G : Cᵒᵖ ⥤ Cat`,
where morphisms consists again of `β : b ⟶ b'` and `φ : f ⟶ (F.map (op β)).obj f'`.

## References

See also `CategoryTheory.Functor.Elements` for the category of elements of functor `F : C ⥤ Type`.

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

-/


universe u

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]
variable (F : C ⥤ Cat)

/--
The Grothendieck construction (often written as `∫ F` in mathematics) for a functor `F : C ⥤ Cat`
gives a category whose
* objects `X` consist of `X.base : C` and `X.fiber : F.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`
-/
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/5171): no such linter yet
-- @[nolint has_nonempty_instance]
structure Grothendieck where
  /-- The underlying object in `C` -/
  base : C
  /-- The object in the fiber of the base object. -/
  fiber : F.obj base

namespace Grothendieck

variable {F}

/-- A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
-/
structure Hom (X Y : Grothendieck F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism from the pushforward to the source fiber object to the target fiber object. -/
  fiber : (F.map base).obj X.fiber ⟶ Y.fiber

@[ext (iff := false)]
theorem ext {X Y : Grothendieck F} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g.fiber) : f = g := by
  cases f; cases g
  congr
  dsimp at w_base
  aesop_cat

/-- The identity morphism in the Grothendieck category.
-/
def id (X : Grothendieck F) : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (by erw [CategoryTheory.Functor.map_id, Functor.id_obj X.fiber])

instance (X : Grothendieck F) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms in the Grothendieck category.
-/
def comp {X Y Z : Grothendieck F} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber :=
    eqToHom (by erw [Functor.map_comp, Functor.comp_obj]) ≫ (F.map g.base).map f.fiber ≫ g.fiber

attribute [local simp] eqToHom_map

instance : Category (Grothendieck F) where
  Hom X Y := Grothendieck.Hom X Y
  id X := Grothendieck.id X
  comp := @fun _ _ _ f g => Grothendieck.comp f g
  comp_id := @fun X Y f => by
    dsimp; ext
    · simp [comp, id]
    · dsimp [comp, id]
      rw [← NatIso.naturality_2 (eqToIso (F.map_id Y.base)) f.fiber]
      simp
  id_comp := @fun X Y f => by dsimp; ext <;> simp [comp, id]
  assoc := @fun W X Y Z f g h => by
    dsimp; ext
    · simp [comp, id]
    · dsimp [comp, id]
      rw [← NatIso.naturality_2 (eqToIso (F.map_comp _ _)) f.fiber]
      simp

@[simp]
theorem id_base (X : Grothendieck F) :
    Hom.base (𝟙 X) = 𝟙 X.base := by
  rfl

@[simp]
theorem id_fiber (X : Grothendieck F) :
    Hom.fiber (𝟙 X) = eqToHom (by erw [CategoryTheory.Functor.map_id, Functor.id_obj X.fiber]) :=
  rfl

@[simp]
theorem comp_base {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
theorem comp_fiber {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.fiber (f ≫ g) =
    eqToHom (by erw [Functor.map_comp, Functor.comp_obj]) ≫
    (F.map g.base).map f.fiber ≫ g.fiber :=
  rfl


theorem congr {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  dsimp
  simp

lemma eqToHom_eq {X Y : Grothendieck F} (hF : X = Y) :
    eqToHom hF = { base := eqToHom (by subst hF; rfl), fiber := eqToHom (by subst hF; simp) } := by
  subst hF
  rfl
section

variable (F)

/-- The forgetful functor from `Grothendieck F` to the source category. -/
@[simps!]
def forget : Grothendieck F ⥤ C where
  obj X := X.1
  map := @fun _ _ f => f.1

end

section

variable {G : C ⥤ Cat}

/-- The Grothendieck construction is functorial: a natural transformation `α : F ⟶ G` induces
a functor `Grothendieck.map : Grothendieck F ⥤ Grothendieck G`.
-/
@[simps!]
def map (α : F ⟶ G) : Grothendieck F ⥤ Grothendieck G where
  obj X :=
  { base := X.base
    fiber := (α.app X.base).obj X.fiber }
  map {X Y} f :=
  { base := f.base
    fiber := (eqToHom (α.naturality f.base).symm).app X.fiber ≫ (α.app Y.base).map f.fiber }
  map_id X := by simp only [Cat.eqToHom_app, id_fiber, eqToHom_map, eqToHom_trans]; rfl
  map_comp {X Y Z} f g := by
    dsimp
    congr 1
    simp only [comp_fiber f g, ← Category.assoc, Functor.map_comp, eqToHom_map]
    congr 1
    simp only [Cat.eqToHom_app, Cat.comp_obj, eqToHom_trans, eqToHom_map, Category.assoc]
    erw [Functor.congr_hom (α.naturality g.base).symm f.fiber]
    simp

theorem map_obj {α : F ⟶ G} (X : Grothendieck F) :
    (Grothendieck.map α).obj X = ⟨X.base, (α.app X.base).obj X.fiber⟩ := rfl

theorem map_map {α : F ⟶ G} {X Y : Grothendieck F} {f : X ⟶ Y} :
    (Grothendieck.map α).map f =
    ⟨f.base, (eqToHom (α.naturality f.base).symm).app X.fiber ≫ (α.app Y.base).map f.fiber⟩ := rfl

/-- The functor `Grothendieck.map α : Grothendieck F ⥤ Grothendieck G` lies over `C`.-/
theorem functor_comp_forget {α : F ⟶ G} :
    Grothendieck.map α ⋙ Grothendieck.forget G = Grothendieck.forget F := rfl

theorem map_id_eq : map (𝟙 F) = 𝟙 (Cat.of <| Grothendieck <| F) := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp [map_map]
    rfl

/-- Making the equality of functors into an isomorphism. Note: we should avoid equality of functors
if possible, and we should prefer `map_id_iso` to `map_id_eq` whenever we can. -/
def mapIdIso : map (𝟙 F) ≅ 𝟙 (Cat.of <| Grothendieck <| F) := eqToIso map_id_eq

variable {H : C ⥤ Cat}
theorem map_comp_eq (α : F ⟶ G) (β : G ⟶ H) :
    map (α ≫ β) = map α ⋙ map β := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp only [map_map, map_obj_base, NatTrans.comp_app, Cat.comp_obj, Cat.comp_map,
      eqToHom_refl, Functor.comp_map, Functor.map_comp, Category.comp_id, Category.id_comp]
    fapply Grothendieck.ext
    · rfl
    · simp

theorem map_comp_eq_assoc (α : F ⟶ G) (β : G ⟶ H) (I : Grothendieck H ⥤ D) :
    map (α ≫ β) ⋙ I = map α ⋙ map β ⋙ I := by rw [map_comp_eq, Functor.assoc]

/-- Making the equality of functors into an isomorphism. Note: we should avoid equality of functors
if possible, and we should prefer `map_comp_iso` to `map_comp_eq` whenever we can. -/
def mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β := eqToIso (map_comp_eq α β)

def map_iso (α : F ≅ G) : Grothendieck F ≌ Grothendieck G where
  functor := map α.hom
  inverse := map α.inv
  unitIso := by
    apply eqToIso
    rw [← map_comp_eq, Iso.hom_inv_id, map_id_eq]
    rfl
  counitIso := by
    apply eqToIso
    rw [← map_comp_eq, Iso.inv_hom_id, map_id_eq]
    rfl

instance IsEquivalence_map (α : F ⟶ G) [IsIso α] : (map α).IsEquivalence := by
  suffices map_iso (asIso α) |>.functor |>.IsEquivalence by simpa
  infer_instance

end

universe v

/-- The Grothendieck construction as a functor from the functor category `E ⥤ Cat` to the
over category `Over E`. -/
def functor {E : Cat.{v,u}} : (E ⥤ Cat.{v,u}) ⥤ Over (T := Cat.{v,u}) E where
  obj F := Over.mk (X := E) (Y := Cat.of (Grothendieck F)) (Grothendieck.forget F)
  map {_ _} α := Over.homMk (X:= E) (Grothendieck.map α) Grothendieck.functor_comp_forget
  map_id F := by
    ext
    exact Grothendieck.map_id_eq (F := F)
  map_comp α β := by
    simp [Grothendieck.map_comp_eq α β]
    rfl

universe w

variable (G : C ⥤ Type w)

/-- Auxiliary definition for `grothendieckTypeToCat`, to speed up elaboration. -/
@[simps!]
def grothendieckTypeToCatFunctor : Grothendieck (G ⋙ typeToCat) ⥤ G.Elements where
  obj X := ⟨X.1, X.2.as⟩
  map f := ⟨f.1, f.2.1.1⟩

/-- Auxiliary definition for `grothendieckTypeToCat`, to speed up elaboration. -/
-- Porting note:
-- `simps` is incorrectly producing Prop-valued projections here,
-- so we manually specify which ones to produce.
-- See https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/!4.233204.20simps.20bug.20.28Grothendieck.20construction.29
@[simps! obj_base obj_fiber_as map_base]
def grothendieckTypeToCatInverse : G.Elements ⥤ Grothendieck (G ⋙ typeToCat) where
  obj X := ⟨X.1, ⟨X.2⟩⟩
  map f := ⟨f.1, ⟨⟨f.2⟩⟩⟩

/-- The Grothendieck construction applied to a functor to `Type`
(thought of as a functor to `Cat` by realising a type as a discrete category)
is the same as the 'category of elements' construction.
-/
-- See porting note on grothendieckTypeToCatInverse.
-- We just want to turn off grothendieckTypeToCat_inverse_map_fiber_down_down,
-- so have to list the complement here for `@[simps]`.
@[simps! functor_obj_fst functor_obj_snd functor_map_coe inverse_obj_base inverse_obj_fiber_as
  inverse_map_base unitIso_hom_app_base unitIso_hom_app_fiber unitIso_inv_app_base
  unitIso_inv_app_fiber counitIso_hom_app_coe counitIso_inv_app_coe]
def grothendieckTypeToCat : Grothendieck (G ⋙ typeToCat) ≌ G.Elements where
  functor := grothendieckTypeToCatFunctor G
  inverse := grothendieckTypeToCatInverse G
  unitIso :=
    NatIso.ofComponents
      (fun X => by
        rcases X with ⟨_, ⟨⟩⟩
        exact Iso.refl _)
      (by
        rintro ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ ⟨base, ⟨⟨f⟩⟩⟩
        dsimp at *
        simp
        rfl)
  counitIso :=
    NatIso.ofComponents
      (fun X => by
        cases X
        exact Iso.refl _)
      (by
        rintro ⟨⟩ ⟨⟩ ⟨f, e⟩
        dsimp at *
        simp
        rfl)
  functor_unitIso_comp := by
    rintro ⟨_, ⟨⟩⟩
    dsimp
    simp
    rfl

-- TODO: Grothendieck F = pre identity F
variable (F) in
/-- Applying a functor `G : D ⥤ C` to the base of the Grothendieck construction induces a functor
`Grothendieck (G ⋙ F) ⥤ Grothendieck F`. -/
@[simps]
def pre (G : D ⥤ C) : Grothendieck (G ⋙ F) ⥤ Grothendieck F where
  obj X := ⟨G.obj X.base, X.fiber⟩
  map f := ⟨G.map f.base, f.fiber⟩
  map_id X := Grothendieck.ext _ _ (G.map_id _) (by simp)
  map_comp f g := Grothendieck.ext _ _ (G.map_comp _ _) (by simp)

variable (F) in
@[simp]
-- TODO: Why does this type check?
theorem pre_id : pre F (𝟭 C) = 𝟭 _ := by
  simp only [pre, Functor.id_obj, Functor.id_map, map, Functor.comp_obj, NatTrans.id_app,
    Cat.id_obj, Functor.comp_map, Cat.comp_obj, eqToHom_refl, Cat.id_app, Cat.id_map,
    Category.id_comp]
  rfl

variable (F) in
def preNatTrans {G H : D ⥤ C} (α : G ⟶ H) :
    pre F G ⟶ (map (whiskerRight α F)) ⋙ (pre F H) := by
  refine ⟨fun X => ⟨α.app X.base, eqToHom rfl⟩, ?_⟩
  intros
  apply Grothendieck.ext <;> simp

/-!
This is a variant of `preNatTrans` for which the type and the implementation depend on
transformations `α` and `β` that may not be definitionally equal, even though `α = β`.
This can be helpful to avoid dependent type theory hell when rewriting α.
-/
variable (F) in
def preNatTrans' {G H : D ⥤ C} (α : G ⟶ H) {β : G ⟶ H} (h : α = β) :
    pre F G ⟶ (map (whiskerRight β F)) ⋙ (pre F H) := by
  refine ⟨fun X => ⟨α.app X.base, eqToHom (by rw [h]; rfl)⟩, ?_⟩
  cases h
  intros
  apply Grothendieck.ext <;> simp

lemma preNatTrans'_rfl_eq {G H : D ⥤ C} (α : G ⟶ H) :
    preNatTrans' F α rfl = preNatTrans F α := rfl

lemma preNatTrans_app {G H : D ⥤ C} (α : G ⟶ H) (x : Grothendieck (G ⋙ F)) :
    (preNatTrans F α).app x = ⟨α.app x.base, eqToHom rfl⟩ := rfl

@[simp]
lemma base_eqToHom {x y : Grothendieck F} (h : x = y) : (eqToHom h).base = eqToHom (by congr) := by
  cases h ; rfl

@[simp]
lemma fiber_eqToHom {x y : Grothendieck F} (h : x = y) :
    (eqToHom h).fiber = (eqToHom (by cases h ; simp)) := by cases h ; rfl

lemma preNatTrans'_id {G : D ⥤ C} {β : G ⟶ G} (h : 𝟙 G = β) :
    preNatTrans' F (𝟙 G) h = eqToHom (by
      cases h
      simp only [whiskerRight_id', map_id_eq]
      simp only [CategoryStruct.id]
      simp only [Cat.of_α]
      rw [Functor.id_comp]) := by
  cases h
  simp only [preNatTrans', Functor.comp_obj, NatTrans.id_app, pre_obj_base, map_obj_base,
    pre_obj_fiber, map_obj_fiber, whiskerRight_app, eqToHom_refl]
  ext X
  simp only [Functor.comp_obj, eqToHom_app]
  fapply Grothendieck.ext
  · simp only [base_eqToHom] ; rfl
  · simp only [fiber_eqToHom]
    simp only [pre_obj_base, map_obj_base, id_eq, Cat.of_α, eq_mpr_eq_cast, cast_eq, pre_obj_fiber,
      map_obj_fiber, Functor.comp_obj, whiskerRight_app, NatTrans.id_app, Category.comp_id]

variable (F) in
lemma preNatTrans_comp {G H I : D ⥤ C} (α : G ⟶ H) (β : H ⟶ I) :
    preNatTrans F (α ≫ β) = preNatTrans F α ≫ whiskerLeft (map (whiskerRight α F)) (preNatTrans F β)
      ≫ eqToHom (by simp [map_comp_eq_assoc]) := by
  ext x
  simp only [NatTrans.comp_app, eqToHom_app, whiskerLeft_app, preNatTrans_app]
  fapply Grothendieck.ext
  · simp only [pre_obj_base, Functor.comp_obj, map_obj_base, pre_obj_fiber, map_obj_fiber,
    whiskerRight_app, eqToHom_refl, comp_base, base_eqToHom, Category.comp_id]
  · simp only [Functor.comp_obj, pre_obj_base, map_obj_base, pre_obj_fiber, map_obj_fiber,
    whiskerRight_app, eqToHom_refl, comp_base, NatTrans.comp_app, Category.comp_id, comp_fiber,
    Functor.map_id, fiber_eqToHom, base_eqToHom, Cat.id_obj, Functor.map_comp, Cat.comp_obj,
    eqToHom_naturality, eqToHom_trans]

variable (F) in
@[reassoc]
lemma preNatTrans_comp2 {G H I : D ⥤ C} (α : G ⟶ H) (β : H ⟶ I) :
    preNatTrans F (α ≫ β) ≫ eqToHom (by simp [map_comp_eq_assoc]) = preNatTrans F α ≫
      whiskerLeft (map (whiskerRight α F)) (preNatTrans F β) := by
  simp only [preNatTrans_comp, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

variable (F) in
def invPreNatTrans {G H : D ⥤ C} (α : G ≅ H) :
    map (whiskerRight α.hom F) ⋙ pre F H ⟶ pre F G := by
  refine whiskerLeft (map (whiskerRight α.hom F)) (preNatTrans F α.inv) ≫ eqToHom ?_
  rw [← map_comp_eq_assoc, ← whiskerRight_comp, α.hom_inv_id, whiskerRight_id', map_id_eq]
  apply Functor.id_comp

@[simp]
def preNatTrans_comp_invPreNatTrans_eq {G H : D ⥤ C} (α : G ≅ H) :
    preNatTrans F α.hom ≫ invPreNatTrans F α = 𝟙 (pre F G) := by
  rw [invPreNatTrans, ← preNatTrans_comp2_assoc, ← preNatTrans'_rfl_eq, eqToHom_trans]
  -- Iso.hom_inv_id is a nice example where simp works but rw doesn't
  simp only [Iso.hom_inv_id, preNatTrans'_id, eqToHom_trans, eqToHom_refl]

@[simp]
def invPreNatTrans_comp_preNatTrans_eq {G H : D ⥤ C} (α : G ≅ H) :
    invPreNatTrans F α ≫ preNatTrans F α.hom = 𝟙 _ := by
  simp only [invPreNatTrans]

  ext X
  simp only [Functor.comp_obj, NatTrans.comp_app, whiskerLeft_app, preNatTrans_app, eqToHom_app,
    map_obj_base]
  fapply Grothendieck.ext
  · simp only [pre_obj_base, map_obj_base, pre_obj_fiber, map_obj_fiber, Functor.comp_obj,
    whiskerRight_app, eqToHom_refl, Category.assoc, comp_base, base_eqToHom, Category.id_comp,
    Iso.inv_hom_id_app, NatTrans.id_app, id_base]
  · simp only [comp_fiber, fiber_eqToHom, eqToHom_trans, eqToHom_map]
    simp only [NatTrans.id_app, id_fiber]

-- TODO: implement calcSymm tactic?
-- TODO: move to Bicategory
def isoCancelRight'' {C : Type*} [Bicategory C] {c d e : C} {f : d ⟶ e} {finv : e ⟶ d}
    {g₁ g₂ : c ⟶ d} (η : 𝟙 _ ≅ f ≫ finv) (α : g₁ ≫ f ≅ g₂ ≫ f) : g₁ ≅ g₂ := by
  calc
    g₁ ≅ g₁ ≫ 𝟙 _ := Bicategory.rightUnitor _ |>.symm
    _ ≅ g₁ ≫ f ≫ finv := Bicategory.whiskerLeftIso _ η
    _ ≅ (g₁ ≫ f) ≫ finv := Bicategory.associator _ _ _ |>.symm
    _ ≅ (g₂ ≫ f) ≫ finv := Bicategory.whiskerRightIso α _
    _ ≅ g₂ ≫ f ≫ finv := Bicategory.associator _ _ _
    _ ≅ _ := Bicategory.whiskerLeftIso _ η.symm
    _ ≅ g₂ := Bicategory.rightUnitor _

-- TODO: Can we reduce this *nicely* to bicategories?
def isoCancelRight' {E : Type*} [Category E]
    {F : D ⥤ E} {Finv : E ⥤ D} {G₁ G₂ : C ⥤ D} (η : 𝟭 _ ≅ F ⋙ Finv)
    (α : G₁ ⋙ F ≅ G₂ ⋙ F) : (G₁ ≅ G₂) := by
  calc
    G₁ ⋙ 𝟭 _ ≅ G₁ ⋙ F ⋙ Finv := isoWhiskerLeft _ η
    _ ≅ G₂ ⋙ F ⋙ Finv := isoWhiskerRight α _
    _ ≅ G₂ ⋙ 𝟭 _ := isoWhiskerLeft _ η.symm

def isoCancelRight {E : Type*} [Category E] {G₁ G₂ : E ⥤ D} (F : D ≌ C)
    (α : G₁ ⋙ F.functor ≅ G₂ ⋙ F.functor) : (G₁ ≅ G₂) := isoCancelRight' F.unitIso α

variable (F) in
def preNatIso {G H : D ⥤ C} (α : G ≅ H) :
    pre F G ≅ (map (whiskerRight α.hom F)) ⋙ (pre F H) :=
  ⟨preNatTrans F α.hom, invPreNatTrans F α, by simp, by simp⟩

instance isEquivalence_pre_id : Functor.IsEquivalence <| pre F <| 𝟭 C := by
  simp only [pre_id]
  infer_instance

variable (F) in
def preInv (G : D ≌ C) : Grothendieck F ⥤ Grothendieck (G.functor ⋙ F) := by
  refine map ?_ ⋙ Grothendieck.pre (G.functor ⋙ F) G.inverse
  rw [← Functor.assoc]
  exact eqToHom (Functor.id_comp F) ≫ (whiskerRight G.counitInv F)

lemma pre_comp_map (G: D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H) :
    pre F G ⋙ map α = map (whiskerLeft G α) ⋙ pre H G := rfl

variable (F) {E : Type*} [Category E] in
@[simp]
lemma pre_comp (G : D ⥤ C) (H : E ⥤ D) : pre F (H ⋙ G) = pre (G ⋙ F) H ⋙ pre F G := rfl

variable (F) in
protected def preUnitIso (G : D ≌ C) :
    map (whiskerRight G.unitInv _) ≅ pre (G.functor ⋙ F) (G.functor ⋙ G.inverse) :=
  preNatIso _ G.unitIso.symm |>.symm

variable (F) in
def preEquivalence (G : D ≌ C) : Grothendieck (G.functor ⋙ F) ≌ Grothendieck F := by
  refine Equivalence.mk (pre F G.functor) (preInv F G) ?_ ?_
  · simp only [preInv, eqToHom_refl, Category.id_comp, eq_mpr_eq_cast, cast_eq]
    erw [← Functor.assoc, pre_comp_map, Functor.assoc]
    simp only [Functor.assoc, ← pre_comp]
    calc
      _ = map (𝟙 _) := map_id_eq.symm
      _ = map _ := ?_
      _ = map _ ⋙ map _ := map_comp_eq _ _
      _ ≅ _ := (Grothendieck.preUnitIso F G |> isoWhiskerLeft _)
    congr
    ext X
    simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, Functor.id_obj,
      Functor.map_id, NatTrans.comp_app, NatTrans.id_app, whiskerLeft_app, whiskerRight_app,
      Equivalence.counitInv_functor_comp]
  · simp only [preInv, eqToHom_refl, Category.id_comp, eq_mpr_eq_cast, cast_eq, Functor.assoc,
    ← pre_comp]
    exact preNatIso F G.counitIso.symm |>.symm

def mapWhiskerLeftIsoConjPreMap (F : C ⥤ Cat) (G : D ≌ C) (α : F ⟶ F) :
    map (whiskerLeft G.functor α) ≅
      (preEquivalence F G).functor ⋙ map α ⋙ (preEquivalence F G).inverse := by
  apply Iso.symm
  apply isoCancelRight (preEquivalence F G)
  exact isoWhiskerLeft ((preEquivalence F G).functor ⋙ map α) (preEquivalence F G).counitIso

-- TODO: currently unused, where to put?
section Transport

def transport (x : Grothendieck F) {c : C} (t : x.base ⟶ c) :
    Grothendieck F := by
  exact ⟨c, (F.map t).obj x.fiber⟩

def transport_hom (x : Grothendieck F) {c : C} (t : x.base ⟶ c) :
    x ⟶ x.transport t := ⟨_, CategoryStruct.id _⟩

-- theorem transport_hom_comp (x : Grothendieck F) {c c' : C} (t : x.base ⟶ c) (t' : c ⟶ c') :
--     x.transport_hom (t ≫ t') = (x.transport_hom t) ≫ (x.transport t).transport_hom t' := sorry

noncomputable def transport.iso (x : Grothendieck F) {c : C} (t : x.base ⟶ c) [IsIso t] :
    x.transport t ≅ x := by
  refine ⟨?_, x.transport_hom t, ?_, ?_⟩
  · refine ⟨inv t, eqToHom ?_⟩
    simp only [transport]
    rw [← Functor.comp_obj, Functor.map_inv]
    show (F.map t ≫ inv (F.map t)).obj x.fiber = x.fiber
    rw [comp_inv_eq_id _ |>.mpr rfl]
    simp only [Cat.id_obj]
  · apply Grothendieck.ext <;> simp [transport_hom]
  · apply Grothendieck.ext <;> simp [transport_hom]

end Transport

section FunctorFrom

variable {E : Type*} [Category E]

variable (F) in
/-- The inclusion of a fiber `F.obj c` of a functor `F : C ⥤ Cat` into its Grothendieck
construction.-/
@[simps obj map]
def ι (c : C) : F.obj c ⥤ Grothendieck F where
  obj d := ⟨c, d⟩
  map f := ⟨𝟙 _, eqToHom (by simp) ≫ f⟩
  map_id d := by
    dsimp
    congr
    simp only [Category.comp_id]
  map_comp f g := by
    apply Grothendieck.ext _ _ (by simp)
    simp only [comp_base, ← Category.assoc, eqToHom_trans, comp_fiber, Functor.map_comp,
      eqToHom_map]
    congr 1
    simp only [eqToHom_comp_iff, Category.assoc, eqToHom_trans_assoc]
    apply Functor.congr_hom (F.map_id _).symm

instance faithful_ι (c : C) : (ι F c).Faithful where
  map_injective f := by
    injection f with _ f
    rwa [cancel_epi] at f

/-- Every morphism `f : X ⟶ Y` in the base category induces a natural transformation from the fiber
inclusion `ι F X` to the composition `F.map f ⋙ ι F Y`. -/
@[simps]
def ιNatTrans {X Y : C} (f : X ⟶ Y) : ι F X ⟶ F.map f ⋙ ι F Y where
  app d := ⟨f, 𝟙 _⟩
  naturality _ _ _ := by
    simp only [ι, Functor.comp_obj, Functor.comp_map]
    exact Grothendieck.ext _ _ (by simp) (by simp [eqToHom_map])

variable (fib : ∀ c, F.obj c ⥤ E) (hom : ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ F.map f ⋙ fib c')
variable (hom_id : ∀ c, hom (𝟙 c) = eqToHom (by simp only [Functor.map_id]; rfl))
variable (hom_comp : ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
  hom f ≫ whiskerLeft (F.map f) (hom g) ≫ eqToHom (by simp only [Functor.map_comp]; rfl))

/-- Construct a functor from `Grothendieck F` to another category `E` by providing a family of
functors on the fibers of `Grothendieck F`, a family of natural transformations on morphisms in the
base of `Grothendieck F` and coherence data for this family of natural transformations. -/
@[simps]
def functorFrom : Grothendieck F ⥤ E where
  obj X := (fib X.base).obj X.fiber
  map {X Y} f := (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber
  map_id X := by simp [hom_id]
  map_comp f g := by simp [hom_comp]

/-- `Grothendieck.ι F c` composed with `Grothendieck.functorFrom` is isomorphic a functor on a fiber
on `F` supplied as the first argument to `Grothendieck.functorFrom`. -/
def ιCompFunctorFrom (c : C) : ι F c ⋙ (functorFrom fib hom hom_id hom_comp) ≅ fib c :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [hom_id])

end FunctorFrom

end Grothendieck

end CategoryTheory
