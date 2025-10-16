/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Products.Basic

/-!
# Joins of categories

Given categories `C, D`, this file constructs a category `C ⋆ D`. Its objects are either
objects of `C` or objects of `D`, morphisms between objects of `C` are morphisms in `C`,
morphisms between objects of `D` are morphisms in `D`, and finally, given `c : C` and `d : D`,
there is a unique morphism `c ⟶ d` in `C ⋆ D`.

## Main constructions

* `Join.edge c d`: the unique map from `c` to `d`.
* `Join.inclLeft : C ⥤ C ⋆ D`, the left inclusion. Its action on morphisms is the main entry point
  to construct maps in `C ⋆ D` between objects coming from `C`.
* `Join.inclRight : D ⥤ C ⋆ D`, the right inclusion. Its action on morphisms is the main entry point
  to construct maps in `C ⋆ D` between objects coming from `D`.
* `Join.mkFunctor`, A constructor for functors out of a join of categories.
* `Join.mkNatTrans`, A constructor for natural transformations between functors out of a join
  of categories.
* `Join.mkNatIso`, A constructor for natural isomorphisms between functors out of a join
  of categories.

## References

* [Kerodon: section 1.4.3.2](https://kerodon.net/tag/0160)

-/

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

open Functor

/-- Elements of `Join C D` are either elements of `C` or elements of `D`. -/
-- Impl. : We are not defining it as a type alias for `C ⊕ D` so that we can have
-- aesop to call cases on `Join C D`
inductive Join (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] : Type (max u₁ u₂)
  | left : C → Join C D
  | right : D → Join C D

attribute [aesop safe cases (rule_sets := [CategoryTheory])] Join

namespace Join

@[inherit_doc] scoped infixr:30 " ⋆ " => Join

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

section CategoryStructure

variable {C D}

/-- Morphisms in `C ⋆ D` are those of `C` and `D`, plus a unique
morphism `(left c ⟶ right d)` for every `c : C` and `d : D`. -/
def Hom : C ⋆ D → C ⋆ D → Type (max v₁ v₂)
  | .left x, .left y => ULift (x ⟶ y)
  | .right x, .right y => ULift (x ⟶ y)
  | .left _, .right _ => PUnit
  | .right _, .left _ => PEmpty

/-- Identity morphisms in `C ⋆ D` are inherited from those in `C` and `D`. -/
def id : ∀ X : C ⋆ D, Hom X X
  | .left x => ULift.up (𝟙 x)
  | .right x => ULift.up (𝟙 x)

/-- Composition in `C ⋆ D` is inherited from the compositions in `C` and `D`. -/
def comp : ∀ {x y z : C ⋆ D}, Hom x y → Hom y z → Hom x z
  | .left _x, .left _y, .left _z, f, g => ULift.up (ULift.down f ≫ ULift.down g)
  | .left _x, .left _y, .right _z, _, _ => PUnit.unit
  | .left _x, .right _y, .right _z, _, _ =>  PUnit.unit
  | .right _x, .right _y, .right _z, f, g => ULift.up (ULift.down f ≫ ULift.down g)

instance : Category.{max v₁ v₂} (C ⋆ D) where
  Hom X Y := Hom X Y
  id _ := id _
  comp := comp
  assoc {a b c d} f g h := by
    cases a <;>
    cases b <;>
    cases c <;>
    cases d <;>
    simp only [Hom, comp, Category.assoc] <;>
    tauto
  id_comp {x y} f := by
    cases x <;> cases y <;> simp only [Hom, id, comp, Category.id_comp] <;> tauto
  comp_id {x y} f := by
    cases x <;> cases y <;> simp only [Hom, id, comp, Category.comp_id] <;> tauto

@[aesop safe destruct (rule_sets := [CategoryTheory])]
lemma false_of_right_to_left {X : D} {Y : C} (f : right X ⟶ left Y) : False := (f : PEmpty).elim

instance {X : C} {Y : D} : Unique (left X ⟶ right Y) := inferInstanceAs (Unique PUnit)

/-- Join.edge c d is the unique morphism from c to d. -/
def edge (c : C) (d : D) : left c ⟶ right d := default

end CategoryStructure

section Inclusions

/-- The canonical inclusion from C to `C ⋆ D`.
Terms of the form `(inclLeft C D).map f` should be treated as primitive when working with joins
and one should avoid trying to reduce them. For this reason, there is no `inclLeft_map` simp
lemma. -/
@[simps! obj]
def inclLeft : C ⥤ C ⋆ D where
  obj := left
  map := ULift.up

/-- The canonical inclusion from D to `C ⋆ D`.
Terms of the form `(inclRight C D).map f` should be treated as primitive when working with joins
and one should avoid trying to reduce them. For this reason, there is no `inclRight_map` simp
lemma. -/
@[simps! obj]
def inclRight : D ⥤ C ⋆ D where
  obj := right
  map := ULift.up

variable {C D}

/-- An induction principle for morphisms in a join of categories: a morphism is either of the form
`(inclLeft _ _).map _`, `(inclRight _ _).map _`, or is `edge _ _`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def homInduction {P : {x y : C ⋆ D} → (x ⟶ y) → Sort*}
    (left : ∀ x y : C, (f : x ⟶ y) → P ((inclLeft C D).map f))
    (right : ∀ x y : D, (f : x ⟶ y) → P ((inclRight C D).map f))
    (edge : ∀ (c : C) (d : D), P (edge c d))
    {x y : C ⋆ D} (f : x ⟶ y) : P f :=
  match x, y, f with
  | .left x, .left y, .up f => left x y f
  | .right x, .right y, .up f => right x y f
  | .left x, .right y, _ => edge x y

@[simp]
lemma homInduction_left {P : {x y : C ⋆ D} → (x ⟶ y) → Sort*}
    (left : ∀ x y : C, (f : x ⟶ y) → P ((inclLeft C D).map f))
    (right : ∀ x y : D, (f : x ⟶ y) → P ((inclRight C D).map f))
    (edge : ∀ (c : C) (d : D), P (edge c d))
    {x y : C} (f : x ⟶ y) : homInduction left right edge ((inclLeft C D).map f) = left x y f :=
  rfl

@[simp]
lemma homInduction_right {P : {x y : C ⋆ D} → (x ⟶ y) → Sort*}
    (left : ∀ x y : C, (f : x ⟶ y) → P ((inclLeft C D).map f))
    (right : ∀ x y : D, (f : x ⟶ y) → P ((inclRight C D).map f))
    (edge : ∀ (c : C) (d : D), P (edge c d))
    {x y : D} (f : x ⟶ y) : homInduction left right edge ((inclRight C D).map f) = right x y f :=
  rfl

@[simp]
lemma homInduction_edge {P : {x y : C ⋆ D} → (x ⟶ y) → Sort*}
    (left : ∀ x y : C, (f : x ⟶ y) → P ((inclLeft C D).map f))
    (right : ∀ x y : D, (f : x ⟶ y) → P ((inclRight C D).map f))
    (edge : ∀ (c : C) (d : D), P (edge c d))
    {c : C} {d : D} : homInduction left right edge (Join.edge c d) = edge c d :=
  rfl

variable (C D)

/-- The left inclusion is fully faithful. -/
def inclLeftFullyFaithful : (inclLeft C D).FullyFaithful where
  preimage f := f.down

/-- The right inclusion is fully faithful. -/
def inclRightFullyFaithful : (inclRight C D).FullyFaithful where
  preimage f := f.down

instance inclLeftFull : (inclLeft C D).Full := inclLeftFullyFaithful C D |>.full

instance inclRightFull : (inclRight C D).Full := inclRightFullyFaithful C D |>.full

instance inclLeftFaithful : (inclLeft C D).Faithful := inclLeftFullyFaithful C D |>.faithful

instance inclRightFaithful : (inclRight C D).Faithful := inclRightFullyFaithful C D |>.faithful

variable {C} in
/-- A situational lemma to help putting identities in the form `(inclLeft _ _).map _` when using
`homInduction`. -/
lemma id_left (c : C) : 𝟙 (left c) = (inclLeft C D).map (𝟙 c) := rfl

variable {D} in
/-- A situational lemma to help putting identities in the form `(inclRight _ _).map _` when using
`homInduction`. -/
lemma id_right (d : D) : 𝟙 (right d) = (inclRight C D).map (𝟙 d) := rfl

/-- The "canonical" natural transformation from `(Prod.fst C D) ⋙ inclLeft C D` to
`(Prod.snd C D) ⋙ inclRight C D`. This is bundling together all the edge morphisms
into the data of a natural transformation. -/
@[simps!]
def edgeTransform :
    Prod.fst C D ⋙ inclLeft C D ⟶ Prod.snd C D ⋙ inclRight C D where
  app := fun (c, d) ↦ edge c d

end Inclusions

section Functoriality

variable {C D} {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

/-- A pair of functors `F : C ⥤ E, G : D ⥤ E` as well as a natural transformation
`α : (Prod.fst C D) ⋙ F ⟶ (Prod.snd C D) ⋙ G` defines a functor out of `C ⋆ D`.
This is the main entry point to define functors out of a join of categories. -/
def mkFunctor (F : C ⥤ E) (G : D ⥤ E) (α : Prod.fst C D ⋙ F ⟶ Prod.snd C D ⋙ G) :
    C ⋆ D ⥤ E where
  obj X :=
    match X with
    | .left x => F.obj x
    | .right x => G.obj x
  map f :=
    homInduction
      (left := fun _ _ f ↦ F.map f)
      (right := fun _ _ g ↦ G.map g)
      (edge := fun c d ↦ α.app (c,d))
      f
  map_id x := by
    cases x
    · dsimp only [id_left, homInduction_left]
      simp
    · dsimp only [id_right, homInduction_right]
      simp
  map_comp {x y z} f g := by
    cases f <;> cases g
    · simp [← Functor.map_comp]
    · case left.edge f d => simpa using (α.naturality <| (Prod.sectL _ d).map f).symm
    · simp [← Functor.map_comp]
    · case edge.right c _ _ f => simpa using α.naturality <| (Prod.sectR c _).map f

section

variable (F : C ⥤ E) (G : D ⥤ E) (α : Prod.fst C D ⋙ F ⟶ Prod.snd C D ⋙ G)

-- As these equalities of objects are definitional, they should be fine.
@[simp]
lemma mkFunctor_obj_left (c : C) : (mkFunctor F G α).obj (left c) = F.obj c := rfl

@[simp]
lemma mkFunctor_obj_right (d : D) : (mkFunctor F G α).obj (right d) = G.obj d := rfl

@[simp]
lemma mkFunctor_map_inclLeft {c c' : C} (f : c ⟶ c') :
    (mkFunctor F G α).map ((inclLeft C D).map f) = F.map f :=
  rfl

/-- Precomposing `mkFunctor F G α` with the left inclusion gives back `F`. -/
@[simps!]
def mkFunctorLeft : inclLeft C D ⋙ mkFunctor F G α ≅ F := Iso.refl _

/-- Precomposing `mkFunctor F G α` with the right inclusion gives back `G`. -/
@[simps!]
def mkFunctorRight : inclRight C D ⋙ mkFunctor F G α ≅ G := Iso.refl _

@[simp]
lemma mkFunctor_map_inclRight {d d' : D} (f : d ⟶ d') :
    (mkFunctor F G α).map ((inclRight C D).map f) = G.map f :=
  rfl

/-- Whiskering `mkFunctor F G α` with the universal transformation gives back `α`. -/
@[simp]
lemma mkFunctor_edgeTransform :
    whiskerRight (edgeTransform C D) (mkFunctor F G α) = α := by
  ext x
  simp [mkFunctor]

@[simp]
lemma mkFunctor_map_edge (c : C) (d : D) :
    (mkFunctor F G α).map (edge c d) = α.app (c, d) :=
  rfl

end

/-- Construct a natural transformation between functors out of a join from
the data of natural transformations between each side that are compatible with the
action on edge maps. -/
def mkNatTrans {F : C ⋆ D ⥤ E} {F' : C ⋆ D ⥤ E}
    (αₗ : inclLeft C D ⋙ F ⟶ inclLeft C D ⋙ F') (αᵣ : inclRight C D ⋙ F ⟶ inclRight C D ⋙ F')
    (h : whiskerRight (edgeTransform C D) F ≫ whiskerLeft (Prod.snd C D) αᵣ =
      whiskerLeft (Prod.fst C D) αₗ ≫ whiskerRight (edgeTransform C D) F' :=
      by cat_disch) :
    F ⟶ F' where
  app x := match x with
    | left x => αₗ.app x
    | right x => αᵣ.app x
  naturality {x y} f := by
    cases f with
    | @left x y f => simpa using αₗ.naturality f
    | @right x y f => simpa using αᵣ.naturality f
    | @edge c d => exact funext_iff.mp (NatTrans.ext_iff.mp h) (c, d)

section

variable {F : C ⋆ D ⥤ E} {F' : C ⋆ D ⥤ E}
    (αₗ : inclLeft C D ⋙ F ⟶ inclLeft C D ⋙ F') (αᵣ : inclRight C D ⋙ F ⟶ inclRight C D ⋙ F')
    (h : whiskerRight (edgeTransform C D) F ≫ whiskerLeft (Prod.snd C D) αᵣ =
      whiskerLeft (Prod.fst C D) αₗ ≫ whiskerRight (edgeTransform C D) F' :=
      by cat_disch)

@[simp]
lemma mkNatTrans_app_left (c : C) : (mkNatTrans αₗ αᵣ h).app (left c) = αₗ.app c := rfl

@[simp]
lemma mkNatTrans_app_right (d : D) : (mkNatTrans αₗ αᵣ h).app (right d) = αᵣ.app d := rfl

@[simp]
lemma whiskerLeft_inclLeft_mkNatTrans : whiskerLeft (inclLeft C D) (mkNatTrans αₗ αᵣ h) = αₗ := rfl

@[simp]
lemma whiskerLeft_inclRight_mkNatTrans :
    whiskerLeft (inclRight C D) (mkNatTrans αₗ αᵣ h) = αᵣ := rfl

end

/-- Two natural transformations between functors out of a join are equal if they are so
after whiskering with the inclusions. -/
lemma natTrans_ext {F F' : C ⋆ D ⥤ E} {α β : F ⟶ F'}
    (h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β)
    (h₂ : whiskerLeft (inclRight C D) α = whiskerLeft (inclRight C D) β) :
    α = β := by
  ext t
  cases t with
  | left t => exact congrArg (fun x ↦ x.app t) h₁
  | right t => exact congrArg (fun x ↦ x.app t) h₂

lemma eq_mkNatTrans {F F' : C ⋆ D ⥤ E} (α : F ⟶ F') :
    mkNatTrans (whiskerLeft (inclLeft C D) α) (whiskerLeft (inclRight C D) α) = α := by
  apply natTrans_ext <;> simp

section

/-- `mkNatTrans` respects vertical composition. -/
lemma mkNatTransComp
    {F F' F'' : C ⋆ D ⥤ E}
    (αₗ : inclLeft C D ⋙ F ⟶ inclLeft C D ⋙ F')
    (αᵣ : inclRight C D ⋙ F ⟶ inclRight C D ⋙ F')
    (βₗ : inclLeft C D ⋙ F' ⟶ inclLeft C D ⋙ F'')
    (βᵣ : inclRight C D ⋙ F' ⟶ inclRight C D ⋙ F'')
    (h : whiskerRight (edgeTransform C D) F ≫ whiskerLeft (Prod.snd C D) αᵣ =
      whiskerLeft (Prod.fst C D) αₗ ≫ whiskerRight (edgeTransform C D) F' :=
      by cat_disch)
    (h' : whiskerRight (edgeTransform C D) F' ≫ whiskerLeft (Prod.snd C D) βᵣ =
      whiskerLeft (Prod.fst C D) βₗ ≫ whiskerRight (edgeTransform C D) F'' := by cat_disch) :
    mkNatTrans (αₗ ≫ βₗ) (αᵣ ≫ βᵣ) (by simp [← h', reassoc_of% h]) =
    mkNatTrans αₗ αᵣ h ≫ mkNatTrans βₗ βᵣ h' := by
  apply natTrans_ext <;> cat_disch

end

/-- Two functors out of a join of categories are naturally isomorphic if their
compositions with the inclusions are isomorphic and the whiskering with the canonical
transformation is respected through these isomorphisms. -/
@[simps]
def mkNatIso {F : C ⋆ D ⥤ E} {G : C ⋆ D ⥤ E}
    (eₗ : inclLeft C D ⋙ F ≅ inclLeft C D ⋙ G)
    (eᵣ : inclRight C D ⋙ F ≅ inclRight C D ⋙ G)
    (h : whiskerRight (edgeTransform C D) F ≫ (isoWhiskerLeft (Prod.snd C D) eᵣ).hom =
      (isoWhiskerLeft (Prod.fst C D) eₗ).hom ≫ whiskerRight (edgeTransform C D) G := by cat_disch) :
    F ≅ G where
  hom := mkNatTrans eₗ.hom eᵣ.hom (by simpa using h)
  inv := mkNatTrans eₗ.inv eᵣ.inv (by rw [Eq.comm, ← isoWhiskerLeft_inv, ← isoWhiskerLeft_inv,
    Iso.inv_comp_eq, ← Category.assoc, Eq.comm, Iso.comp_inv_eq, h])

/-- A pair of functors ((C ⥤ E), (D ⥤ E')) induces a functor `C ⋆ D ⥤ E ⋆ E'`. -/
def mapPair (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') : C ⋆ D ⥤ E ⋆ E' :=
  mkFunctor (Fₗ ⋙ inclLeft _ _) (Fᵣ ⋙ inclRight _ _) { app := fun _ ↦ edge _ _ }

section mapPair

variable (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E')

@[simp]
lemma mapPair_obj_left (c : C) : (mapPair Fₗ Fᵣ).obj (left c) = left (Fₗ.obj c) := rfl

@[simp]
lemma mapPair_obj_right (d : D) : (mapPair Fₗ Fᵣ).obj (right d) = right (Fᵣ.obj d) := rfl

@[simp]
lemma mapPair_map_inclLeft {c c' : C} (f : c ⟶ c') :
    (mapPair Fₗ Fᵣ).map ((inclLeft C D).map f) = (inclLeft E E').map (Fₗ.map f) := rfl

@[simp]
lemma mapPair_map_inclRight {d d' : D} (f : d ⟶ d') :
    (mapPair Fₗ Fᵣ).map ((inclRight C D).map f) = (inclRight E E').map (Fᵣ.map f) := rfl

/-- Characterizing `mapPair` on left morphisms. -/
@[simps! hom_app inv_app]
def mapPairLeft : inclLeft _ _ ⋙ mapPair Fₗ Fᵣ ≅ Fₗ ⋙ inclLeft _ _ := mkFunctorLeft _ _ _

/-- Characterizing `mapPair` on right morphisms. -/
@[simps! hom_app inv_app]
def mapPairRight : inclRight _ _ ⋙ mapPair Fₗ Fᵣ ≅ Fᵣ ⋙ inclRight _ _ := mkFunctorRight _ _ _

end mapPair

/-- Any functor out of a join is naturally isomorphic to a functor of the form `mkFunctor F G α`. -/
@[simps!]
def isoMkFunctor (F : C ⋆ D ⥤ E) :
    F ≅ mkFunctor (inclLeft C D ⋙ F) (inclRight C D ⋙ F) (whiskerRight (edgeTransform C D) F) :=
  mkNatIso (mkFunctorLeft _ _ _).symm (mkFunctorRight _ _ _).symm

/-- `mapPair` respects identities -/
@[simps!]
def mapPairId : mapPair (𝟭 C) (𝟭 D) ≅ 𝟭 (C ⋆ D) :=
  mkNatIso
    (mapPairLeft _ _ ≪≫ Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)
    (mapPairRight _ _ ≪≫ Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)

variable {J : Type u₅} [Category.{v₅} J]
  {K : Type u₆} [Category.{v₆} K]

-- @[simps!] times out here
/-- `mapPair` respects composition -/
def mapPairComp (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gₗ : E ⥤ J) (Gᵣ : E' ⥤ K) :
    mapPair (Fₗ ⋙ Gₗ) (Fᵣ ⋙ Gᵣ) ≅ mapPair Fₗ Fᵣ ⋙ mapPair Gₗ Gᵣ :=
  mkNatIso
    (mapPairLeft (Fₗ ⋙ Gₗ) (Fᵣ ⋙ Gᵣ) ≪≫
      Functor.associator Fₗ Gₗ (inclLeft J K) ≪≫
      (isoWhiskerLeft Fₗ (mapPairLeft Gₗ Gᵣ).symm) ≪≫
      (Functor.associator Fₗ (inclLeft E E') (mapPair Gₗ Gᵣ)).symm ≪≫
      isoWhiskerRight (mapPairLeft Fₗ Fᵣ).symm (mapPair Gₗ Gᵣ))
    (mapPairRight (Fₗ ⋙ Gₗ) (Fᵣ ⋙ Gᵣ) ≪≫
      Functor.associator Fᵣ Gᵣ (inclRight J K) ≪≫
      (isoWhiskerLeft Fᵣ (mapPairRight Gₗ Gᵣ).symm) ≪≫
      (Functor.associator Fᵣ (inclRight E E') (mapPair Gₗ Gᵣ)).symm ≪≫
      isoWhiskerRight (mapPairRight Fₗ Fᵣ).symm (mapPair Gₗ Gᵣ))

section mapPairComp

variable (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gₗ : E ⥤ J) (Gᵣ : E' ⥤ K)

@[simp]
lemma mapPairComp_hom_app_left (c : C) :
    (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c))) := by
  dsimp [mapPairComp]
  simp

@[simp]
lemma mapPairComp_hom_app_right (d : D) :
    (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.obj d))) := by
  dsimp [mapPairComp]
  simp

@[simp]
lemma mapPairComp_inv_app_left (c : C) :
    (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c))) := by
  dsimp [mapPairComp]
  simp

@[simp]
lemma mapPairComp_inv_app_right (d : D) :
    (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.obj d))) := by
  dsimp [mapPairComp]
  simp

end mapPairComp

end Functoriality

section NaturalTransforms

variable {E : Type u₃} [Category.{v₃} E]
  {E' : Type u₄} [Category.{v₄} E']

variable {C D}

/-- A natural transformation `Fₗ ⟶ Gₗ` induces a natural transformation
  `mapPair Fₗ H ⟶ mapPair Gₗ H` for every `H : D ⥤ E'`. -/
@[simps!]
def mapWhiskerRight {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ⟶ Gₗ) (H : D ⥤ E') :
    mapPair Fₗ H ⟶ mapPair Gₗ H :=
  mkNatTrans
    ((mapPairLeft Fₗ H).hom ≫ whiskerRight α (inclLeft E E') ≫ (mapPairLeft Gₗ H).inv)
    ((mapPairRight Fₗ H).hom ≫ whiskerRight (𝟙 H) (inclRight E E') ≫ (mapPairRight Gₗ H).inv)

@[simp]
lemma mapWhiskerRight_comp {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} {Hₗ : C ⥤ E}
    (α : Fₗ ⟶ Gₗ) (β : Gₗ ⟶ Hₗ) (H : D ⥤ E') :
    mapWhiskerRight (α ≫ β) H = mapWhiskerRight α H ≫ mapWhiskerRight β H := by
  cat_disch

@[simp]
lemma mapWhiskerRight_id (Fₗ : C ⥤ E) (H : D ⥤ E') :
    mapWhiskerRight (𝟙 Fₗ) H = 𝟙 _ := by
  cat_disch

/-- A natural transformation `Fᵣ ⟶ Gᵣ` induces a natural transformation
  `mapPair H Fᵣ ⟶ mapPair H Gᵣ` for every `H : C ⥤ E`. -/
@[simps!]
def mapWhiskerLeft (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ⟶ Gᵣ) :
    mapPair H Fᵣ ⟶ mapPair H Gᵣ :=
  mkNatTrans
    ((mapPairLeft H Fᵣ).hom ≫ whiskerRight (𝟙 H) (inclLeft E E') ≫ (mapPairLeft H Gᵣ).inv)
    ((mapPairRight H Fᵣ).hom ≫ whiskerRight α (inclRight E E') ≫ (mapPairRight H Gᵣ).inv)

@[simp]
lemma mapWhiskerLeft_comp {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} {Hᵣ : D ⥤ E'}
    (H : C ⥤ E) (α : Fᵣ ⟶ Gᵣ) (β : Gᵣ ⟶ Hᵣ) :
    mapWhiskerLeft H (α ≫ β) = mapWhiskerLeft H α ≫ mapWhiskerLeft H β := by
  cat_disch

@[simp]
lemma mapWhiskerLeft_id (H : C ⥤ E) (Fᵣ : D ⥤ E') :
    mapWhiskerLeft H (𝟙 Fᵣ) = 𝟙 _ := by
  cat_disch

/-- One can exchange `mapWhiskerLeft` and `mapWhiskerRight`. -/
lemma mapWhisker_exchange (Fₗ : C ⥤ E) (Gₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gᵣ : D ⥤ E')
    (αₗ : Fₗ ⟶ Gₗ) (αᵣ : Fᵣ ⟶ Gᵣ) :
    mapWhiskerLeft Fₗ αᵣ ≫ mapWhiskerRight αₗ Gᵣ =
      mapWhiskerRight αₗ Fᵣ ≫ mapWhiskerLeft Gₗ αᵣ := by
  ext
  cat_disch

/-- A natural isomorphism `Fᵣ ≅ Gᵣ` induces a natural isomorphism
  `mapPair H Fᵣ ≅ mapPair H Gᵣ` for every `H : C ⥤ E`. -/
@[simps!]
def mapIsoWhiskerLeft (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ) :
    mapPair H Fᵣ ≅ mapPair H Gᵣ :=
  mkNatIso
    (mapPairLeft H Fᵣ ≪≫ isoWhiskerRight (Iso.refl H) (inclLeft _ _) ≪≫ (mapPairLeft H Gᵣ).symm)
    (mapPairRight H Fᵣ ≪≫ isoWhiskerRight α (inclRight E E') ≪≫ (mapPairRight H Gᵣ).symm)

/-- A natural isomorphism `Fᵣ ≅ Gᵣ` induces a natural isomorphism
  `mapPair Fₗ H ≅ mapPair Gₗ H` for every `H : C ⥤ E`. -/
@[simps!]
def mapIsoWhiskerRight {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E') :
    mapPair Fₗ H ≅ mapPair Gₗ H :=
  mkNatIso
    (mapPairLeft Fₗ H ≪≫ isoWhiskerRight α (inclLeft E E') ≪≫ (mapPairLeft Gₗ H).symm)
    (mapPairRight Fₗ H ≪≫ isoWhiskerRight (Iso.refl H) (inclRight E E') ≪≫ (mapPairRight Gₗ H).symm)

lemma mapIsoWhiskerRight_hom {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E') :
    (mapIsoWhiskerRight α H).hom = mapWhiskerRight α.hom H := rfl

lemma mapIsoWhiskerRight_inv {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E') :
    (mapIsoWhiskerRight α H).inv = mapWhiskerRight α.inv H := by
  ext x
  cases x <;> simp [mapIsoWhiskerRight]

lemma mapIsoWhiskerLeft_hom (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ) :
    (mapIsoWhiskerLeft H α).hom = mapWhiskerLeft H α.hom := rfl

lemma mapIsoWhiskerLeft_inv (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ) :
    (mapIsoWhiskerLeft H α).inv = mapWhiskerLeft H α.inv := by
  ext x
  cases x <;> simp [mapIsoWhiskerLeft]

end NaturalTransforms

section mapPairEquiv

variable {C' : Type u₃} [Category.{v₃} C']
  {D' : Type u₄} [Category.{v₄} D']

variable {C D}

/-- Equivalent categories have equivalent joins. -/
@[simps]
def mapPairEquiv (e : C ≌ C') (e' : D ≌ D') : C ⋆ D ≌ C' ⋆ D' where
  functor := mapPair e.functor e'.functor
  inverse := mapPair e.inverse e'.inverse
  unitIso :=
    mapPairId.symm ≪≫
      mapIsoWhiskerRight e.unitIso _ ≪≫
      mapIsoWhiskerLeft _ e'.unitIso ≪≫
      mapPairComp _ _ _ _
  counitIso :=
    (mapPairComp _ _ _ _).symm ≪≫
      mapIsoWhiskerRight e.counitIso _ ≪≫
      mapIsoWhiskerLeft _ e'.counitIso ≪≫
      mapPairId
  functor_unitIso_comp x := by
    cases x <;>
    simp [← (inclLeft C' D').map_comp, ← (inclRight C' D').map_comp]

instance isEquivalenceMapPair {F : C ⥤ C'} {F' : D ⥤ D'} [F.IsEquivalence] [F'.IsEquivalence] :
    (mapPair F F').IsEquivalence :=
  inferInstanceAs (mapPairEquiv F.asEquivalence F'.asEquivalence).functor.IsEquivalence

end mapPairEquiv

end Join

end CategoryTheory
