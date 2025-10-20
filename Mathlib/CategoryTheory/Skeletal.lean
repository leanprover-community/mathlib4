/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Thin

/-!
# Skeleton of a category

Define skeletal categories as categories in which any two isomorphic objects are equal.

Construct the skeleton of an arbitrary category by taking isomorphism classes, and show it is a
skeleton of the original category.

In addition, construct the skeleton of a thin category as a partial ordering, and (noncomputably)
show it is a skeleton of the original category. The advantage of this special case being handled
separately is that lemmas and definitions about orderings can be used directly, for example for the
subobject lattice. In addition, some of the commutative diagrams about the functors commute
definitionally on the nose which is convenient in practice.
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-- A category is skeletal if isomorphic objects are equal. -/
def Skeletal : Prop :=
  ∀ ⦃X Y : C⦄, IsIsomorphic X Y → X = Y

/-- `IsSkeletonOf C D F` says that `F : D ⥤ C` exhibits `D` as a skeletal full subcategory of `C`,
in particular `F` is a (strong) equivalence and `D` is skeletal.
-/
structure IsSkeletonOf (F : D ⥤ C) : Prop where
  /-- The category `D` has isomorphic objects equal -/
  skel : Skeletal D
  /-- The functor `F` is an equivalence -/
  eqv : F.IsEquivalence := by infer_instance

attribute [local instance] isIsomorphicSetoid

variable {C D}

/-- If `C` is thin and skeletal, then any naturally isomorphic functors to `C` are equal. -/
theorem Functor.eq_of_iso {F₁ F₂ : D ⥤ C} [Quiver.IsThin C] (hC : Skeletal C) (hF : F₁ ≅ F₂) :
    F₁ = F₂ :=
  Functor.ext (fun X => hC ⟨hF.app X⟩) fun _ _ _ => Subsingleton.elim _ _

/-- If `C` is thin and skeletal, `D ⥤ C` is skeletal.
`CategoryTheory.functor_thin` shows it is thin also.
-/
theorem functor_skeletal [Quiver.IsThin C] (hC : Skeletal C) : Skeletal (D ⥤ C) := fun _ _ h =>
  h.elim (Functor.eq_of_iso hC)

variable (C D)

noncomputable section

/-- Construct the skeleton category as the induced category on the isomorphism classes, and derive
its category structure.
-/
def Skeleton : Type u₁ := InducedCategory (C := Quotient (isIsomorphicSetoid C)) C Quotient.out
deriving
  Category,
  [Inhabited C] → Inhabited _,
  (α : Sort _) → [CoeSort C α] → CoeSort _ α

end

/-- The functor from the skeleton of `C` to `C`. -/
@[simps!]
noncomputable def fromSkeleton : Skeleton C ⥤ C :=
  inducedFunctor _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380
-- Note(kmill): `derive Functor.Full, Functor.Faithful` does not create instances
-- that are in terms of `Skeleton`, but rather `InducedCategory`, which can't be applied.
-- With `deriving @Functor.Full (Skeleton C)`, the instance can't be derived, for a similar reason.

noncomputable instance : (fromSkeleton C).Full := by
  apply InducedCategory.full
noncomputable instance : (fromSkeleton C).Faithful := by
  apply InducedCategory.faithful

instance : (fromSkeleton C).EssSurj where mem_essImage X := ⟨Quotient.mk' X, Quotient.mk_out X⟩

noncomputable instance fromSkeleton.isEquivalence : (fromSkeleton C).IsEquivalence where

variable {C}

/-- The class of an object in the skeleton. -/
abbrev toSkeleton (X : C) : Skeleton C := ⟦X⟧

/-- The isomorphism between `⟦X⟧.out` and `X`. -/
noncomputable def preCounitIso (X : C) : (fromSkeleton C).obj (toSkeleton X) ≅ X :=
  Nonempty.some (Quotient.mk_out X)

alias fromSkeletonToSkeletonIso := preCounitIso

variable (C)

/-- An inverse to `fromSkeleton C` that forms an equivalence with it. -/
@[simps] noncomputable def toSkeletonFunctor : C ⥤ Skeleton C where
  obj := toSkeleton
  map {X Y} f := by apply (preCounitIso X).hom ≫ f ≫ (preCounitIso Y).inv
  map_id _ := by aesop
  map_comp _ _ := by change _ = CategoryStruct.comp (obj := C) _ _; simp

/-- The equivalence between the skeleton and the category itself. -/
@[simps] noncomputable def skeletonEquivalence : Skeleton C ≌ C where
  functor := fromSkeleton C
  inverse := toSkeletonFunctor C
  unitIso := NatIso.ofComponents
    (fun X ↦ InducedCategory.isoMk (Nonempty.some <| Quotient.mk_out X.out).symm)
    fun _ ↦ .symm <| Iso.inv_hom_id_assoc _ _
  counitIso := NatIso.ofComponents preCounitIso
  functor_unitIso_comp _ := Iso.inv_hom_id _

theorem skeleton_skeletal : Skeletal (Skeleton C) := by
  rintro X Y ⟨h⟩
  have : X.out ≈ Y.out := ⟨(fromSkeleton C).mapIso h⟩
  simpa using Quotient.sound this

/-- The `skeleton` of `C` given by choice is a skeleton of `C`. -/
lemma skeleton_isSkeleton : IsSkeletonOf C (Skeleton C) (fromSkeleton C) where
  skel := skeleton_skeletal C
  eqv := fromSkeleton.isEquivalence C

variable {C D}

lemma toSkeleton_fromSkeleton_obj (X : Skeleton C) : toSkeleton ((fromSkeleton C).obj X) = X :=
  Quotient.out_eq _

lemma toSkeleton_eq_toSkeleton_iff {X Y : C} : toSkeleton X = toSkeleton Y ↔ Nonempty (X ≅ Y) :=
  Quotient.eq

lemma congr_toSkeleton_of_iso {X Y : C} (e : X ≅ Y) : toSkeleton X = toSkeleton Y :=
  Quotient.sound ⟨e⟩

/-- Provides a (noncomputable) isomorphism `X ≅ Y` given that `toSkeleton X = toSkeleton Y`. -/
noncomputable def Skeleton.isoOfEq {X Y : C} (h : toSkeleton X = toSkeleton Y) :
    X ≅ Y :=
  Quotient.exact h |>.some

lemma toSkeleton_eq_iff {X : C} {Y : Skeleton C} :
    toSkeleton X = Y ↔ Nonempty (X ≅ (fromSkeleton C).obj Y) :=
  Quotient.mk_eq_iff_out

namespace Functor

/-- From a functor `C ⥤ D`, construct a map of skeletons `Skeleton C → Skeleton D`. -/
noncomputable def mapSkeleton (F : C ⥤ D) : Skeleton C ⥤ Skeleton D :=
  (skeletonEquivalence C).functor ⋙ F ⋙ (skeletonEquivalence D).inverse

variable (F : C ⥤ D)

lemma mapSkeleton_obj_toSkeleton (X : C) :
    F.mapSkeleton.obj (toSkeleton X) = toSkeleton (F.obj X) :=
  congr_toSkeleton_of_iso <| F.mapIso <| preCounitIso X

instance [F.Full] : F.mapSkeleton.Full := by unfold mapSkeleton; infer_instance

instance [F.Faithful] : F.mapSkeleton.Faithful := by unfold mapSkeleton; infer_instance

instance [F.EssSurj] : F.mapSkeleton.EssSurj := by unfold mapSkeleton; infer_instance

/-- A natural isomorphism between `X ↦ ⟦X⟧ ↦ ⟦FX⟧` and `X ↦ FX ↦ ⟦FX⟧`. On the level of
categories, these are `C ⥤ Skeleton C ⥤ Skeleton D` and `C ⥤ D ⥤ Skeleton D`. So this says that
the square formed by these 4 objects and 4 functors commutes. -/
noncomputable def toSkeletonFunctorCompMapSkeletonIso :
    toSkeletonFunctor C ⋙ F.mapSkeleton ≅ F ⋙ toSkeletonFunctor D :=
  NatIso.ofComponents (fun X ↦ (toSkeletonFunctor D).mapIso <| F.mapIso <| preCounitIso X)
    (fun {X Y} f ↦ show (_ ≫ _) ≫ _ = _ ≫ _ by simp [assoc])

lemma mapSkeleton_injective [F.Full] [F.Faithful] : Function.Injective F.mapSkeleton.obj :=
  fun _ _ h ↦ skeleton_skeletal C ⟨F.mapSkeleton.preimageIso <| eqToIso h⟩

lemma mapSkeleton_surjective [F.EssSurj] : Function.Surjective F.mapSkeleton.obj :=
  fun Y ↦ let ⟨X, h⟩ := EssSurj.mem_essImage Y; ⟨X, skeleton_skeletal D h⟩

end Functor

/-- Two categories which are categorically equivalent have skeletons with equivalent objects.
-/
noncomputable def Equivalence.skeletonEquiv (e : C ≌ D) : Skeleton C ≃ Skeleton D :=
  let f := ((skeletonEquivalence C).trans e).trans (skeletonEquivalence D).symm
  { toFun := f.functor.obj
    invFun := f.inverse.obj
    left_inv := fun X => skeleton_skeletal C ⟨(f.unitIso.app X).symm⟩
    right_inv := fun Y => skeleton_skeletal D ⟨f.counitIso.app Y⟩ }

variable (C D)

/-- Construct the skeleton category by taking the quotient of objects. This construction gives a
preorder with nice definitional properties, but is only really appropriate for thin categories.
If your original category is not thin, you probably want to be using `Skeleton` instead of this.
-/
def ThinSkeleton : Type u₁ :=
  Quotient (isIsomorphicSetoid C)

variable {C} in
/-- Convenience constructor for `ThinSkeleton`. -/
abbrev ThinSkeleton.mk (c : C) : ThinSkeleton C := Quotient.mk' c

instance inhabitedThinSkeleton [Inhabited C] : Inhabited (ThinSkeleton C) :=
  ⟨ThinSkeleton.mk default⟩

instance ThinSkeleton.preorder : Preorder (ThinSkeleton C) where
  le :=
    @Quotient.lift₂ C C _ (isIsomorphicSetoid C) (isIsomorphicSetoid C)
      (fun X Y => Nonempty (X ⟶ Y))
        (by
          rintro _ _ _ _ ⟨i₁⟩ ⟨i₂⟩
          exact
            propext
              ⟨Nonempty.map fun f => i₁.inv ≫ f ≫ i₂.hom,
                Nonempty.map fun f => i₁.hom ≫ f ≫ i₂.inv⟩)
  le_refl := by
    refine Quotient.ind fun a => ?_
    exact ⟨𝟙 _⟩
  le_trans a b c := Quotient.inductionOn₃ a b c fun _ _ _ => Nonempty.map2 (· ≫ ·)

/-- The functor from a category to its thin skeleton. -/
@[simps]
def toThinSkeleton : C ⥤ ThinSkeleton C where
  obj := ThinSkeleton.mk
  map f := homOfLE (Nonempty.intro f)

/-!
The constructions here are intended to be used when the category `C` is thin, even though
some of the statements can be shown without this assumption.
-/


namespace ThinSkeleton

/-- The thin skeleton is thin. -/
instance thin : Quiver.IsThin (ThinSkeleton C) := fun _ _ =>
  ⟨by
    rintro ⟨⟨f₁⟩⟩ ⟨⟨_⟩⟩
    rfl⟩

variable {C} {D}

/-- A functor `C ⥤ D` computably lowers to a functor `ThinSkeleton C ⥤ ThinSkeleton D`. -/
@[simps]
def map (F : C ⥤ D) : ThinSkeleton C ⥤ ThinSkeleton D where
  obj := Quotient.map F.obj fun _ _ ⟨hX⟩ => ⟨F.mapIso hX⟩
  map {X} {Y} := Quotient.recOnSubsingleton₂ X Y fun _ _ k => homOfLE (k.le.elim fun t => ⟨F.map t⟩)

theorem comp_toThinSkeleton (F : C ⥤ D) : F ⋙ toThinSkeleton D = toThinSkeleton C ⋙ map F :=
  rfl

/-- Given a natural transformation `F₁ ⟶ F₂`, induce a natural transformation `map F₁ ⟶ map F₂`. -/
def mapNatTrans {F₁ F₂ : C ⥤ D} (k : F₁ ⟶ F₂) : map F₁ ⟶ map F₂ where
  app X := Quotient.recOnSubsingleton X fun x => ⟨⟨⟨k.app x⟩⟩⟩

/- Porting note: `map₂ObjMap`, `map₂Functor`, and `map₂NatTrans` were all extracted
from the original `map₂` proof. Lean needed an extensive amount explicit type
annotations to figure things out. This also translated into repeated deterministic
timeouts. The extracted defs allow for explicit motives for the multiple
descents to the quotients.

It would be better to prove that
`ThinSkeleton (C × D) ≌ ThinSkeleton C × ThinSkeleton D`
which is more immediate from comparing the preorders. Then one could get
`map₂` by currying.
-/
/-- Given a bifunctor, we descend to a function on objects of `ThinSkeleton` -/
def map₂ObjMap (F : C ⥤ D ⥤ E) : ThinSkeleton C → ThinSkeleton D → ThinSkeleton E :=
  fun x y =>
    @Quotient.map₂ C D (isIsomorphicSetoid C) (isIsomorphicSetoid D) E (isIsomorphicSetoid E)
      (fun X Y => (F.obj X).obj Y)
          (fun X₁ _ ⟨hX⟩ _ Y₂ ⟨hY⟩ => ⟨(F.obj X₁).mapIso hY ≪≫ (F.mapIso hX).app Y₂⟩) x y

/-- For each `x : ThinSkeleton C`, we promote `map₂ObjMap F x` to a functor -/
def map₂Functor (F : C ⥤ D ⥤ E) : ThinSkeleton C → ThinSkeleton D ⥤ ThinSkeleton E :=
  fun x =>
    { obj := fun y => map₂ObjMap F x y
      map := fun {y₁} {y₂} => @Quotient.recOnSubsingleton C (isIsomorphicSetoid C)
        (fun x => (y₁ ⟶ y₂) → (map₂ObjMap F x y₁ ⟶ map₂ObjMap F x y₂)) _ x fun X
          => Quotient.recOnSubsingleton₂ y₁ y₂ fun _ _ hY =>
            homOfLE (hY.le.elim fun g => ⟨(F.obj X).map g⟩) }

/-- This provides natural transformations `map₂Functor F x₁ ⟶ map₂Functor F x₂` given
`x₁ ⟶ x₂` -/
def map₂NatTrans (F : C ⥤ D ⥤ E) : {x₁ x₂ : ThinSkeleton C} → (x₁ ⟶ x₂) →
    (map₂Functor F x₁ ⟶ map₂Functor F x₂) := fun {x₁} {x₂} =>
  @Quotient.recOnSubsingleton₂ C C (isIsomorphicSetoid C) (isIsomorphicSetoid C)
    (fun x x' : ThinSkeleton C => (x ⟶ x') → (map₂Functor F x ⟶ map₂Functor F x')) _ x₁ x₂
    (fun X₁ X₂ f => { app := fun y =>
      Quotient.recOnSubsingleton y fun Y => homOfLE (f.le.elim fun f' => ⟨(F.map f').app Y⟩) })

-- TODO: state the lemmas about what happens when you compose with `toThinSkeleton`
/-- A functor `C ⥤ D ⥤ E` computably lowers to a functor
`ThinSkeleton C ⥤ ThinSkeleton D ⥤ ThinSkeleton E` -/
@[simps]
def map₂ (F : C ⥤ D ⥤ E) : ThinSkeleton C ⥤ ThinSkeleton D ⥤ ThinSkeleton E where
  obj := map₂Functor F
  map := map₂NatTrans F

variable (C)

section

variable [Quiver.IsThin C]

instance toThinSkeleton_faithful : (toThinSkeleton C).Faithful where

/-- Use `Quotient.out` to create a functor out of the thin skeleton. -/
@[simps]
noncomputable def fromThinSkeleton : ThinSkeleton C ⥤ C where
  obj := Quotient.out
  map {x} {y} :=
    Quotient.recOnSubsingleton₂ x y fun X Y f =>
      (Nonempty.some (Quotient.mk_out X)).hom ≫ f.le.some ≫ (Nonempty.some (Quotient.mk_out Y)).inv

/-- The equivalence between the thin skeleton and the category itself. -/
noncomputable def equivalence : ThinSkeleton C ≌ C where
  functor := fromThinSkeleton C
  inverse := toThinSkeleton C
  counitIso := NatIso.ofComponents fun X => Nonempty.some (Quotient.mk_out X)
  unitIso := NatIso.ofComponents fun x => Quotient.recOnSubsingleton x fun X =>
    eqToIso (Quotient.sound ⟨(Nonempty.some (Quotient.mk_out X)).symm⟩)

noncomputable instance fromThinSkeleton_isEquivalence : (fromThinSkeleton C).IsEquivalence :=
  (equivalence C).isEquivalence_functor

variable {C}

theorem equiv_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≈ Y :=
  ⟨iso_of_both_ways f g⟩

instance thinSkeletonPartialOrder : PartialOrder (ThinSkeleton C) :=
  { CategoryTheory.ThinSkeleton.preorder C with
    le_antisymm :=
      Quotient.ind₂
        (by
          rintro _ _ ⟨f⟩ ⟨g⟩
          apply Quotient.sound (equiv_of_both_ways f g)) }

theorem skeletal : Skeletal (ThinSkeleton C) := fun X Y =>
  Quotient.inductionOn₂ X Y fun _ _ h => h.elim fun i => i.1.le.antisymm i.2.le

theorem map_comp_eq (F : E ⥤ D) (G : D ⥤ C) : map (F ⋙ G) = map F ⋙ map G :=
  Functor.eq_of_iso skeletal <|
    NatIso.ofComponents fun X => Quotient.recOnSubsingleton X fun _ => Iso.refl _

theorem map_id_eq : map (𝟭 C) = 𝟭 (ThinSkeleton C) :=
  Functor.eq_of_iso skeletal <|
    NatIso.ofComponents fun X => Quotient.recOnSubsingleton X fun _ => Iso.refl _

theorem map_iso_eq {F₁ F₂ : D ⥤ C} (h : F₁ ≅ F₂) : map F₁ = map F₂ :=
  Functor.eq_of_iso skeletal
    { hom := mapNatTrans h.hom
      inv := mapNatTrans h.inv }

/--
Applying `fromThinSkeleton`, `F` and then `toThinSkeleton` is isomorphic to applying `map F`.
-/
noncomputable def fromThinSkeletonCompToThinSkeletonIso (F : C ⥤ D) :
    fromThinSkeleton C ⋙ F ⋙ toThinSkeleton D ≅ map F :=
  Functor.isoWhiskerLeft (fromThinSkeleton C) (Iso.refl _) ≪≫
    Functor.isoWhiskerRight (equivalence C).unitIso.symm (map F) ≪≫
    Functor.leftUnitor (map F)

/--
Applying `map F` and then `fromThinSkeleton` is isomorphic to first applying `fromThinSkeleton`
and then applying `F`.
-/
noncomputable def mapCompFromThinSkeletonIso [Quiver.IsThin D] (F : C ⥤ D) :
    map F ⋙ fromThinSkeleton D ≅ fromThinSkeleton C ⋙ F  :=
  Functor.isoWhiskerRight (fromThinSkeletonCompToThinSkeletonIso F).symm _ ≪≫
    Functor.isoWhiskerLeft (fromThinSkeleton C ⋙ F) (equivalence D).counitIso ≪≫
    Functor.rightUnitor (fromThinSkeleton C ⋙ F)

/-- `fromThinSkeleton C` exhibits the thin skeleton as a skeleton. -/
lemma thinSkeleton_isSkeleton : IsSkeletonOf C (ThinSkeleton C) (fromThinSkeleton C) where
  skel := skeletal

instance isSkeletonOfInhabited :
    Inhabited (IsSkeletonOf C (ThinSkeleton C) (fromThinSkeleton C)) :=
  ⟨thinSkeleton_isSkeleton⟩

end

variable {C}

/-- An adjunction between thin categories gives an adjunction between their thin skeletons. -/
def lowerAdjunction (R : D ⥤ C) (L : C ⥤ D) (h : L ⊣ R) :
    ThinSkeleton.map L ⊣ ThinSkeleton.map R where
  unit :=
    { app := fun X => by
        letI := isIsomorphicSetoid C
        exact Quotient.recOnSubsingleton X fun x => homOfLE ⟨h.unit.app x⟩ }
      -- TODO: make quotient.rec_on_subsingleton' so the letI isn't needed
  counit :=
    { app := fun X => by
        letI := isIsomorphicSetoid D
        exact Quotient.recOnSubsingleton X fun x => homOfLE ⟨h.counit.app x⟩ }

end ThinSkeleton

open ThinSkeleton

section

variable {C} {α : Type*} [PartialOrder α]

/--
When `e : C ≌ α` is a categorical equivalence from a thin category `C` to some partial order `α`,
the `ThinSkeleton C` is order isomorphic to `α`.
-/
noncomputable def Equivalence.thinSkeletonOrderIso [Quiver.IsThin C] (e : C ≌ α) :
    ThinSkeleton C ≃o α :=
  ((ThinSkeleton.equivalence C).trans e).toOrderIso

end

end CategoryTheory
