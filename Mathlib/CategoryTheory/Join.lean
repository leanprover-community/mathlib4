/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/

import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# Joins of category

Given categories `C, D`, this file constructs a category `C ⋆ D`. Its objects are either
objects of `C` or objects of `D`, morphisms between objects of `C` are morphisms in `C`,
morphisms between object of `D` are morphisms in `D`, and finally, given `c : C` and `d : D`,
there is a unique morphism `c ⟶ d` in `C ⋆ D`.

## Main constructions
- `Join.edge c d`: the unique map from `c` to `d`.
- `Join.inclLeft : C ⥤ C ⋆ D`, the left inclusion. Its action on morphism is the main entry point
to constructs maps in `C ⋆ D` between objects coming from `C`.
- `Join.inclRight : D ⥤ C ⋆ D`, the left inclusion. Its action on morphism is the main entry point
to constructs maps in `C ⋆ D` between object coming from `D`.
- `Join.mkFunctor`, A constructor for functors out of a join of categories.
- `Join.mkNatTrans`, A constructor for natural transformations between functors out of a join
  of categories.

# TODOs
- Cofinality of the right inclusion, finality of the left inclusion.
-/

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

/-- Elements of `Join C D` are either elements of `C` or elements of `D`. -/
-- Impl. : We are not defining it as a type alias for `C ⊕ D` so that we can have
-- aesop to call cases on `Join C D`
inductive Join (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] : Type (max u₁ u₂)
  | left : C → Join C D
  | right : D → Join C D

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Join

@[inherit_doc] infixr:30 " ⋆ " => Join

namespace Join

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

section CategoryStructure

variable {C D}

/-- Morphisms in `C ⋆ D` are those of `C` and `D`, plus an unique
morphism `(left c ⟶ right d)` for every `c : C` and `d : D`. -/
def Hom : C ⋆ D → C ⋆ D → Type (max v₁ v₂)
  | .left x, .left y => ULift (x ⟶ y)
  | .right x, .right y => ULift (x ⟶ y)
  | .left _, .right _ => PUnit
  | .right _, .left _ => PEmpty

/-- Identity morphisms in `C ⋆ D` are inherited from those in `C` and `D`. -/
def id : ∀ (X : C ⋆ D), Hom X X
  | .left x => ULift.up (𝟙 x)
  | .right x => ULift.up (𝟙 x)

/-- Composition in `C ⋆ D` is inherited from the compositions in `C` and `D`. -/
def comp : ∀ {x y z : C ⋆ D}, Hom x y → Hom y z → Hom x z
  | .left _x, .left _y, .left _z => fun f g ↦ ULift.up (ULift.down f ≫ ULift.down g)
  | .left _x, .left _y, .right _z => fun _ _ ↦ PUnit.unit
  | .left _x, .right _y, .left _z => fun _ g ↦ PEmpty.elim g
  | .left _x, .right _y, .right _z => fun _ _ ↦ PUnit.unit
  | .right _x, .left _y, .left _z => fun f _ ↦ PEmpty.elim f
  | .right _x, .left _y, .right _z => fun f _ ↦ PEmpty.elim f
  | .right _x, .right _y, .left _z => fun _ g ↦ PEmpty.elim g
  | .right _x, .right _y, .right _z => fun f g ↦ ULift.up (ULift.down f ≫ ULift.down g)

instance : Category.{max v₁ v₂} (C ⋆ D) where
  Hom X Y := Hom X Y
  id _ := id _
  comp := comp
  assoc {a b c d} f g h := by
    cases a <;>
    cases b <;>
    cases c <;>
    cases d <;>
    simp only [Hom, id, comp, Category.assoc] <;>
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

@[simp]
lemma eq_edge {c : C} {d : D} (f : left c ⟶ right d) : f = edge c d := rfl

end CategoryStructure

section Inclusions

/-- The canonical inclusion from C to `C ⋆ D`. -/
@[simps! obj]
def inclLeft : C ⥤ C ⋆ D where
  obj := left
  map := ULift.up

/-- The canonical inclusion from D to `C ⋆ D`. -/
@[simps! obj]
def inclRight : D ⥤ C ⋆ D where
  obj := right
  map := ULift.up

variable {C D}

/-- An induction principle for morphisms in a join of category: a morphism is either of the form
`(inclLeft _ _).map _`, `(inclRight _ _).map _)`, or is `edge _ _`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def homInduction {P : {x y : C ⋆ D} → (x ⟶ y) → Sort*}
    (left : ∀ x y : C, (f : x ⟶ y) → P ((inclLeft C D).map f))
    (right : ∀ x y : D, (f : x ⟶ y) → P ((inclRight C D).map f))
    (edge : ∀ (c : C) (d : D), P (edge c d))
    {x y : C ⋆ D} (f : x ⟶ y) : P f :=
  match x, y, f with
  | .left x, .left y, f => left x y f.down
  | .right x, .right y, f => right x y f.down
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

instance inclLeftFull: (inclLeft C D).Full where
  map_surjective f := by
    cases f
    use (by assumption)

instance inclRightFull: (inclRight C D).Full where
  map_surjective f := by
    cases f
    use (by assumption)

instance inclLeftFaithFull: (inclLeft C D).Faithful where
  map_injective {_ _} _ _ h := by injection h

instance inclRightFaithfull: (inclRight C D).Faithful where
  map_injective {_ _} _ _ h := by injection h

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
@[simps]
def edgeTransform :
    (Prod.fst C D) ⋙ inclLeft C D ⟶ (Prod.snd C D) ⋙ inclRight C D where
  app := fun (c, d) ↦ edge c d

end Inclusions

section Functoriality

variable {C D} {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

/-- A pair of functor `F : C ⥤ E, G : D ⥤ E` as well as a natural transformation
`α : (Prod.fst C D) ⋙ F ⟶ (Prod.snd C D) ⋙ G`. defines a functor out of `C ⋆ D`.
This is the main entry point to define functors out of a join of categories. -/
def mkFunctor (F : C ⥤ E) (G : D ⥤ E) (α : (Prod.fst C D) ⋙ F ⟶ (Prod.snd C D) ⋙ G) :
    C ⋆ D ⥤ E where
  obj X :=
    match X with
    | .left x => (F.obj x)
    | .right x => (G.obj x)
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
    · rename_i f d
      simpa using (α.naturality <| (Prod.sectL _ d).map f).symm
    · simp [← Functor.map_comp]
    · rename_i c c' d f
      simpa using α.naturality <| (Prod.sectR c _).map f

section

variable (F : C ⥤ E) (G : D ⥤ E) (α : (Prod.fst C D) ⋙ F ⟶ (Prod.snd C D) ⋙ G)

/-- Precomposing `mkFunctor F G α` with the left inclusion gives back `F`. -/
def mkFunctorLeft : inclLeft C D ⋙ (mkFunctor F G α) ≅ F := Iso.refl _

@[simp]
lemma mkFunctor_map_inclLeft {c c' : C} (f : c ⟶ c') :
    (mkFunctor F G α).map ((inclLeft C D).map f) = F.map f :=
  rfl

/-- Precomposing `mkFunctor F G α` with the right inclusion gives back `G`. -/
def mkFunctorRight : inclRight C D ⋙ (mkFunctor F G α) ≅ G := Iso.refl _

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
/-- Two functors out of a join of category are naturally isomorphic if their
compositions with the inclusions are isomorphic and the whiskering with the canonical
transformation is respected through these isomorphisms. -/
def functorIsoExt {F : C ⋆ D ⥤ E} {G : C ⋆ D ⥤ E}
    (eₗ : inclLeft C D ⋙ F ≅ inclLeft C D ⋙ G)
    (eᵣ : inclRight C D ⋙ F ≅ inclRight C D ⋙ G)
    (h : (isoWhiskerLeft (Prod.fst C D) eₗ).hom ≫ whiskerRight (edgeTransform C D) G =
      whiskerRight (edgeTransform C D) F ≫ (isoWhiskerLeft (Prod.snd C D) eᵣ).hom :=
      by aesop_cat) :
    F ≅ G :=
  NatIso.ofComponents
    (fun x ↦ match x with
      | left x => eₗ.app x
      | right x => eᵣ.app x)
    (fun f ↦ by
      cases f with
      | @left x y f => simpa using eₗ.hom.naturality f
      | @right x y f => simpa using eᵣ.hom.naturality f
      | edge c d => simpa using (congrArg (fun α ↦ α.app (c,d)) h).symm)

/-- A version of `functorIsoExt` in which the hypothesis on the universal transform is supplied
extensionnaly, rather than as an equality of natural transformations. -/
def functorIsoExt' {F : C ⋆ D ⥤ E} {G : C ⋆ D ⥤ E}
    (eₗ : inclLeft C D ⋙ F ≅ inclLeft C D ⋙ G)
    (eᵣ : inclRight C D ⋙ F ≅ inclRight C D ⋙ G)
    (h : ∀ (c : C) (d : D), eₗ.hom.app c ≫ G.map (edge c d) = F.map (edge c d) ≫ eᵣ.hom.app d :=
      by aesop_cat) :
    F ≅ G := functorIsoExt eₗ eᵣ

/-- A pair of functors ((C ⥤ E), (D ⥤ E')) induces a functor (C ⋆ D ⥤ E ⋆ E'). -/
def mapPair (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') : (C ⋆ D) ⥤ (E ⋆ E') :=
  mkFunctor (Fₗ ⋙ inclLeft _ _) (Fᵣ ⋙ inclRight _ _) { app := fun _ ↦ edge _ _ }

/-- Any functor out of a join is naturally isomorphic to a functor of the form `mkFunctor F G α`. -/
@[simps!]
def isoMkFunctor (F : C ⋆ D ⥤ E) :
    F ≅ mkFunctor (inclLeft C D ⋙ F) (inclRight C D ⋙ F) (whiskerRight (edgeTransform C D) F) :=
  functorIsoExt (Iso.refl _) (Iso.refl _)

section

variable (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E')

/-- Characterizing `mapPair` on left morphisms. -/
@[simps!]
def mapPairLeft : inclLeft _ _ ⋙ (mapPair Fₗ Fᵣ) ≅ (Fₗ ⋙ inclLeft _ _) := mkFunctorLeft _ _ _

/-- Characterizing `mapPair` on right morphisms. -/
@[simps!]
def mapPairRight : inclRight _ _ ⋙ (mapPair Fₗ Fᵣ) ≅ (Fᵣ ⋙ inclRight _ _) := mkFunctorRight _ _ _

/-- Characterizing the action of map_pair on edges. -/
@[simp]
def mapPairEdge (c : C) (d : D):
    (mapPair Fₗ Fᵣ).map (edge c d) = edge (Fₗ.obj c) (Fᵣ.obj d) :=
  rfl

end

/-- `mapPair` respects identities -/
@[simps!]
def mapPairId : mapPair (𝟭 C) (𝟭 D) ≅ 𝟭 (C ⋆ D) := functorIsoExt (Iso.refl _) (Iso.refl _)

variable {J : Type u₅} [Category.{v₅} J]
  {K : Type u₆} [Category.{v₆} K]

/-- `mapPair` respects composition -/
@[simps!]
def mapPairComp (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gₗ : E ⥤ J) (Gᵣ : E' ⥤ K) :
    mapPair (Fₗ ⋙ Gₗ) (Fᵣ ⋙ Gᵣ) ≅ mapPair Fₗ Fᵣ ⋙ mapPair Gₗ Gᵣ :=
  functorIsoExt (Iso.refl _) (Iso.refl _)

end Functoriality

section NaturalTransforms

variable {E : Type u₃} [Category.{v₃} E]
  {E' : Type u₄} [Category.{v₄} E']

variable {C D}

/-- Construct a natural transformation between functors from a join from
the data of natural transformations between each side that are compatible with the
action on edge maps. -/
@[simps!]
def mkNatTrans (F : C ⋆ D ⥤ E) (F' : C ⋆ D ⥤ E)
    (αₗ : inclLeft C D ⋙ F ⟶ inclLeft C D ⋙ F') (αᵣ : inclRight C D ⋙ F ⟶ inclRight C D ⋙ F')
    (h : whiskerRight (edgeTransform C D) F ≫ whiskerLeft (Prod.snd C D) αᵣ =
      whiskerLeft (Prod.fst C D) αₗ ≫ whiskerRight (edgeTransform C D) F' :=
      by aesop_cat) :
    F ⟶ F' where
  app x := match x with
    | left x => αₗ.app x
    | right x => αᵣ.app x
  naturality {x y} f := by
    cases f with
    | @left x y f => simpa using αₗ.naturality f
    | @right x y f => simpa using αᵣ.naturality f
    | @edge c d => exact funext_iff.mp (NatTrans.ext_iff.mp h) (c, d)

/-- A natural transformation `Fₗ ⟶ Gₗ` induces a natural transformation
  `mapPair Fₗ H ⟶ mapPair Gₗ H` for every `H : D ⥤ E'`. -/
@[simps!]
def mapWhiskerRight {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ⟶ Gₗ) (H : D ⥤ E') :
    mapPair Fₗ H ⟶ mapPair Gₗ H :=
  mkNatTrans _ _
    ((mapPairLeft Fₗ H).inv ≫ (whiskerRight α (inclLeft E E')) ≫ (mapPairLeft Gₗ H).hom)
    (𝟙 _)

/-- A natural transformation `Fᵣ ⟶ Gᵣ` induces a natural transformation
  `mapPair H Fᵣ ⟶ mapPair H Gᵣ` for every `H : C ⥤ E`. -/
@[simps!]
def mapWhiskerLeft (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ⟶ Gᵣ) :
    mapPair H Fᵣ ⟶ mapPair H Gᵣ :=
  mkNatTrans _ _
    (𝟙 _)
    ((mapPairRight H Fᵣ).inv ≫ (whiskerRight α (inclRight E E')) ≫ (mapPairRight H Gᵣ).hom)

/-- One can exchange `mapWhiskerLeft` and `mapWhiskerRight`. -/
lemma mapWhisker_exchange (Fₗ : C ⥤ E) (Gₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gᵣ : D ⥤ E')
    (αₗ : Fₗ ⟶ Gₗ) (αᵣ : Fᵣ ⟶ Gᵣ) :
    mapWhiskerLeft Fₗ αᵣ ≫ mapWhiskerRight αₗ Gᵣ =
      mapWhiskerRight αₗ Fᵣ ≫ mapWhiskerLeft Gₗ αᵣ := by
  aesop_cat

end NaturalTransforms

end Join

end CategoryTheory
