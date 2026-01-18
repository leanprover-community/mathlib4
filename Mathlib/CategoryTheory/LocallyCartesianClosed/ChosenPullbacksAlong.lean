/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Chosen pullbacks along a morphism

## Main declarations

- `ChosenPullbacksAlong` : For a morphism `f : Y ⟶ X` in `C`, the type class
  `ChosenPullbacksAlong f` provides the data of a pullback functor `Over X ⥤ Over Y`
  as a right adjoint to `Over.map f`.

## Main results

- We prove that `ChosenPullbacksAlong` has good closure properties: isos have chosen pullbacks,
  and composition of morphisms with chosen pullbacks have chosen pullbacks.

-  We prove that chosen pullbacks yields usual pullbacks: `ChosenPullbacksAlong.isPullback`
  proves that for morphisms `f` and `g` with the same codomain, the object
  `ChosenPullbacksAlong.pullbackObj f g` together with morphisms
  `ChosenPullbacksAlong.fst f g` and `ChosenPullbacksAlong.snd f g` form a pullback square
  over `f` and `g`.

- We prove that in cartesian monoidal categories, morphisms to the terminal tensor unit and
  the product projections have chosen pullbacks.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits CartesianMonoidalCategory MonoidalCategory Over

variable {C : Type u₁} [Category.{v₁} C]

/-- A functorial choice of pullbacks along a morphism `f : Y ⟶ X` in `C` given by a functor
`Over X ⥤ Over Y` which is a right adjoint to the functor `Over.map f`. -/
class ChosenPullbacksAlong {Y X : C} (f : Y ⟶ X) where
  /-- The pullback functor along `f`. -/
  pullback : Over X ⥤ Over Y
  /-- The adjunction between `Over.map f` and `pullback f`. -/
  mapPullbackAdj (f) : Over.map f ⊣ pullback

variable (C) in
/-- A category has chosen pullbacks if every morphism has a chosen pullback. -/
abbrev ChosenPullbacks := Π {X Y : C} (f : Y ⟶ X), ChosenPullbacksAlong f

namespace ChosenPullbacksAlong

/-- Relating the existing noncomputable `HasPullbacksAlong` typeclass to `ChosenPullbacksAlong`. -/
@[simps]
noncomputable def ofHasPullbacksAlong {Y X : C} (f : Y ⟶ X) [HasPullbacksAlong f] :
    ChosenPullbacksAlong f where
  pullback := Over.pullback f
  mapPullbackAdj := Over.mapPullbackAdj f

/-- The identity morphism has a functorial choice of pullbacks. -/
def id (X : C) : ChosenPullbacksAlong (𝟙 X) where
  pullback := 𝟭 _
  mapPullbackAdj := (Adjunction.id).ofNatIsoLeft (Over.mapId _).symm

/-- Any chosen pullback functor of the identity morphism is naturally isomorphic to the identity
functor. -/
def pullbackId (X : C) [ChosenPullbacksAlong (𝟙 X)] :
    pullback (𝟙 X) ≅ 𝟭 (Over X) :=
  (mapPullbackAdj (𝟙 X)).rightAdjointUniq (id X).mapPullbackAdj

@[reassoc (attr := simp)]
theorem unit_pullbackId_hom_app (X : C) [ChosenPullbacksAlong (𝟙 X)] (Y : Over X) :
  (mapPullbackAdj (𝟙 X)).unit.app Y ≫ (pullbackId X).hom.app ((Over.map (𝟙 X)).obj Y) =
    (id X).mapPullbackAdj.unit.app Y := by
  rw [pullbackId, Adjunction.unit_rightAdjointUniq_hom_app]

@[reassoc (attr := simp)]
theorem unit_pullbackId_hom (X : C) [ChosenPullbacksAlong (𝟙 X)] :
  (mapPullbackAdj (𝟙 X)).unit ≫ (Over.map (𝟙 X)).whiskerLeft (pullbackId X).hom =
    (id X).mapPullbackAdj.unit := by
  rw [pullbackId, Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]
theorem pullbackId_hom_counit (X : C) [ChosenPullbacksAlong (𝟙 X)] :
  Functor.whiskerRight (pullbackId X).hom (Over.map (𝟙 X)) ≫ (id X).mapPullbackAdj.counit =
    (mapPullbackAdj (𝟙 X)).counit := by
  have := Adjunction.rightAdjointUniq_hom_counit (mapPullbackAdj (𝟙 X)) (id X).mapPullbackAdj
  rw [pullbackId, Adjunction.rightAdjointUniq_hom_counit]

/-- Every isomorphism has a functorial choice of pullbacks. -/
@[simps]
def iso {Y X : C} (f : Y ≅ X) : ChosenPullbacksAlong f.hom where
  pullback.obj Z := Over.mk (Z.hom ≫ f.inv)
  pullback.map {Y Z} g := Over.homMk (g.left)
  mapPullbackAdj.unit.app T := Over.homMk (𝟙 T.left)
  mapPullbackAdj.counit.app U := Over.homMk (𝟙 _)

/-- The inverse of an isomorphism has a functorial choice of pullbacks. -/
@[simps!]
def isoInv {Y X : C} (f : Y ≅ X) : ChosenPullbacksAlong f.inv := iso f.symm

/-- The composition of morphisms with chosen pullbacks has a chosen pullback. -/
def comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] : ChosenPullbacksAlong (f ≫ g) where
  pullback := pullback g ⋙ pullback f
  mapPullbackAdj := ((mapPullbackAdj f).comp (mapPullbackAdj g)).ofNatIsoLeft
    (Over.mapComp f g).symm

/-- Any chosen pullback of a composite of morphisms is naturally isomorphic to the composition of
chosen pullback functors. -/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  Adjunction.rightAdjointUniq (mapPullbackAdj (f ≫ g)) ((comp f g).mapPullbackAdj)

@[reassoc (attr := simp)]
theorem unit_pullbackComp_hom {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] :
    (mapPullbackAdj (f ≫ g)).unit ≫ (Over.map (f ≫ g)).whiskerLeft (pullbackComp f g).hom =
      (comp f g).mapPullbackAdj.unit := by
  rw [pullbackComp, Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]
theorem pullbackComp_hom_counit {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] :
    Functor.whiskerRight (pullbackComp f g).hom (Over.map (f ≫ g)) ≫
      (comp f g).mapPullbackAdj.counit =
      (mapPullbackAdj (f ≫ g)).counit := by
  rw [pullbackComp, Adjunction.rightAdjointUniq_hom_counit]

/-- In cartesian monoidal categories, any morphism to the terminal tensor unit has a functorial
choice of pullbacks. -/
@[simps]
def cartesianMonoidalCategoryToUnit [CartesianMonoidalCategory C] {X : C} (f : X ⟶ 𝟙_ C) :
    ChosenPullbacksAlong f where
  pullback.obj Y := Over.mk (snd Y.left X)
  pullback.map {Y Z} g := Over.homMk (g.left ▷ X)
  mapPullbackAdj.unit.app T := Over.homMk (lift (𝟙 _) (T.hom))
  mapPullbackAdj.counit.app U := Over.homMk (fst _ _)

/-- In cartesian monoidal categories, the first product projections `fst` have a functorial choice
of pullbacks. -/
@[simps]
def cartesianMonoidalCategoryFst [CartesianMonoidalCategory C] (X Y : C) :
    ChosenPullbacksAlong (fst X Y : X ⊗ Y ⟶ X) where
  pullback.obj Z := Over.mk (Z.hom ▷ Y)
  pullback.map g := Over.homMk (g.left ▷ Y)
  mapPullbackAdj.unit.app T := Over.homMk (lift (𝟙 _) (T.hom ≫ snd _ _))
  mapPullbackAdj.counit.app U := Over.homMk (fst _ _)

/-- In cartesian monoidal categories, the second product projections `snd` have a functorial choice
of pullbacks. -/
@[simps]
def cartesianMonoidalCategorySnd [CartesianMonoidalCategory C] (X Y : C) :
    ChosenPullbacksAlong (snd X Y : X ⊗ Y ⟶ Y) where
  pullback.obj Z := Over.mk (X ◁ Z.hom)
  pullback.map g := Over.homMk (X ◁ g.left)
  mapPullbackAdj.unit.app T := Over.homMk (lift (T.hom ≫ fst _ _) (𝟙 _))
  mapPullbackAdj.counit.app U := Over.homMk (snd _ _)

section PullbackFromChosenPullbacksAlongs

variable {Y Z X : C} (f : Y ⟶ X) (g : Z ⟶ X) [ChosenPullbacksAlong g]

/-- The underlying object of the chosen pullback along `g` of `f`. -/
abbrev pullbackObj : C := ((pullback g).obj (Over.mk f)).left

/-- A morphism in `Over X` from the chosen pullback along `g` of `f` to `Over.mk f`. -/
abbrev fst' : (Over.map g).obj ((pullback g).obj (Over.mk f)) ⟶ Over.mk f :=
  (mapPullbackAdj g).counit.app <| Over.mk f

/-- The first projection from the chosen pullback along `g` of `f` to the domain of `f`. -/
abbrev fst : pullbackObj f g ⟶ Y := fst' f g |>.left

theorem fst'_left : (fst' f g).left = fst f g := rfl

/-- The second projection from the chosen pullback along `g` of `f` to the domain of `g`. -/
abbrev snd : pullbackObj f g ⟶ Z := (pullback g).obj (Over.mk f) |>.hom

/-- A morphism in `Over X` from the chosen pullback along `g` of `f` to `Over.mk g`. -/
abbrev snd' : (Over.map g).obj ((pullback g).obj (Over.mk f)) ⟶ (Over.mk g) :=
  Over.homMk (snd f g)

theorem snd'_left : (snd' f g).left = snd f g := rfl

variable {f g}

@[reassoc]
theorem condition : fst f g ≫ f = snd f g ≫ g :=
  Over.w (fst' f g)

variable (f g) in
@[ext]
theorem hom_ext {W : C} {φ₁ φ₂ : W ⟶ pullbackObj f g} (h₁ : φ₁ ≫ fst _ _ = φ₂ ≫ fst _ _)
    (h₂ : φ₁ ≫ snd _ _ = φ₂ ≫ snd _ _) :
    φ₁ = φ₂ := by
  let adj := mapPullbackAdj g
  let U : Over Z := Over.mk (φ₁ ≫ snd f g)
  let φ₁' : U ⟶ (pullback g).obj (Over.mk f) := Over.homMk φ₁
  let φ₂' : U ⟶ (pullback g).obj (Over.mk f) := Over.homMk φ₂ (by simpa using h₂.symm)
  have : φ₁' = φ₂' := by
    apply (adj.homEquiv U _).symm.injective
    apply (Over.forget X).map_injective
    simpa using h₁
  exact congr_arg CommaMorphism.left this

section Lift

variable {W : C} (a : W ⟶ Y) (b : W ⟶ Z) (h : a ≫ f = b ≫ g := by cat_disch)

set_option backward.privateInPublic true in
/-- Given morphisms `a : W ⟶ Y` and `b : W ⟶ Z` satisfying `a ≫ f = b ≫ g`,
constructs the unique morphism `W ⟶ pullbackObj f g` which lifts `a` and `b`. -/
def lift : W ⟶ pullbackObj f g :=
  (((mapPullbackAdj g).homEquiv (Over.mk b) (Over.mk f)) (Over.homMk a)).left

set_option backward.privateInPublic true in
@[reassoc (attr := simp)]
theorem lift_fst : lift a b h ≫ fst f g = a := by
  let adj := mapPullbackAdj g
  let a' : (Over.map g).obj (Over.mk b) ⟶ Over.mk f := Over.homMk a h
  have : (Over.map g).map (adj.homEquiv (.mk b) (.mk f) (Over.homMk a)) ≫ fst' f g = a' := by
    simp only [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply, adj, a']
  exact congr_arg CommaMorphism.left this

set_option backward.privateInPublic true in
@[reassoc (attr := simp)]
theorem lift_snd : lift a b h ≫ snd f g = b := by
  simp [lift]

end Lift

section PullbackMap

variable (f g)

/-- The functoriality of `pullbackObj f g` in both arguments: Given a map from the pullback cospans
of `f' : Y' ⟶ X'` and `g' : Z' ⟶ X'` to the pullback cospan of `f : Y ⟶ X` and `g : Z ⟶ X`
as in the diagram below
```
Y' ⟶ Y
  ↘   ↘
  X' ⟶ X
  ↗   ↗
Z' ⟶ Z
```
if the morphisms `g'` and `g` both have chosen pullbacks, then we get an induced morphism
`pullbackMap f g f' g' comm₁ comm₂` from the chosen pullback of
`f' : Y' ⟶ X'` along `g'` to the chosen pullback of `f : Y ⟶ X` along `g`.
Here `comm₁` and `comm₂` are the commutativity conditions of the squares in the diagram above.
-/
def pullbackMap {Y' Z' X' : C} (f' : Y' ⟶ X') (g' : Z' ⟶ X') [ChosenPullbacksAlong g']
    (γ₁ : Y' ⟶ Y) (γ₂ : Z' ⟶ Z) (γ₃ : X' ⟶ X)
    (comm₁ : f' ≫ γ₃ = γ₁ ≫ f := by cat_disch) (comm₂ : g' ≫ γ₃ = γ₂ ≫ g := by cat_disch) :
    pullbackObj f' g' ⟶ pullbackObj f g :=
  lift (fst f' g' ≫ γ₁) (snd f' g' ≫ γ₂)
    (by rw [assoc, ← comm₁, ← assoc, condition, assoc, comm₂, assoc])

variable {f g}

@[reassoc (attr := simp)]
theorem pullbackMap_fst {Y' Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullbacksAlong g']
    {γ₁ : Y' ⟶ Y} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X} (comm₁ comm₂ := by cat_disch) :
    pullbackMap f g f' g' γ₁ γ₂ γ₃ comm₁ comm₂ ≫ fst f g = fst f' g' ≫ γ₁ := by
  simp only [pullbackMap, lift_fst]

@[reassoc (attr := simp)]
theorem pullbackMap_snd {Y' Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullbacksAlong g']
    {γ₁ : Y' ⟶ Y} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X} (comm₁ comm₂ := by cat_disch) :
    pullbackMap f g f' g' γ₁ γ₂ γ₃ comm₁ comm₂ ≫ snd f g = snd f' g' ≫ γ₂ := by
  simp only [pullbackMap, lift_snd]

@[simp]
theorem pullbackMap_id : pullbackMap f g f g (𝟙 Y) (𝟙 Z) (𝟙 X) = 𝟙 _ := by
  cat_disch

@[reassoc (attr := simp)]
theorem pullbackMap_comp {Y' Z' X' Y'' Z'' X'' : C}
    {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} {f'' : Y'' ⟶ X''} {g'' : Z'' ⟶ X''}
    [ChosenPullbacksAlong g'] [ChosenPullbacksAlong g'']
    {γ₁ : Y' ⟶ Y} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X}
    {δ₁ : Y'' ⟶ Y'} {δ₂ : Z'' ⟶ Z'} {δ₃ : X'' ⟶ X'}
    (comm₁ comm₂ comm₁' comm₂' := by cat_disch) :
    pullbackMap f' g' f'' g'' δ₁ δ₂ δ₃ comm₁' comm₂' ≫
      pullbackMap f g f' g' γ₁ γ₂ γ₃ comm₁ comm₂ =
    pullbackMap f g f'' g'' (δ₁ ≫ γ₁) (δ₂ ≫ γ₂) (δ₃ ≫ γ₃)
      (by rw [reassoc_of% comm₁', comm₁, assoc]) (by rw [reassoc_of% comm₂', comm₂, assoc]) := by
  cat_disch

end PullbackMap

variable (f g)

/-- The canonical pullback cone from the data of a chosen pullback of `f` along `g`. -/
def pullbackCone : PullbackCone f g :=
  PullbackCone.mk (fst f g) (snd f g) (by rw [condition])

@[simp] lemma pullbackCone_fst : (pullbackCone f g).fst = fst f g := rfl

@[simp] lemma pullbackCone_snd : (pullbackCone f g).snd = snd f g := rfl

/-- The canonical pullback cone is a limit cone.
Note: this limit cone is computable as lifts are constructed from the data contained in the
`ChosenPullbackAlong` instance, contrary to `IsPullback.isLimit`, which constructs lifting data from
`CategoryTheory.Square.IsPullback` (a `Prop`). -/
def isLimitPullbackCone :
    IsLimit (pullbackCone f g) :=
  PullbackCone.IsLimit.mk condition (fun s ↦ lift s.fst s.snd s.condition)
    (by cat_disch) (by cat_disch) (by cat_disch)

theorem isPullback : IsPullback (fst f g) (snd f g) f g where
  w := condition
  isLimit' := ⟨isLimitPullbackCone f g⟩

attribute [local simp] condition in
/-- If `g` has a chosen pullback, then `Over.ChosenPullbacksAlong.fst f g` has a chosen pullback. -/
def chosenPullbacksAlongFst : ChosenPullbacksAlong (fst f g) where
  pullback.obj W := Over.mk (pullbackMap _ _ _ _ W.hom (𝟙 _) (𝟙 _))
  pullback.map {W' W} k := Over.homMk (lift (fst _ g ≫ k.left) (snd _ g)) _
  mapPullbackAdj.unit.app Q := Over.homMk (lift (𝟙 _) (Q.hom ≫ snd _ _))
  mapPullbackAdj.counit.app W := Over.homMk (fst _ g)

instance hasPullbackAlong : HasPullbacksAlong g := fun f => (isPullback f g).hasPullback

instance hasPullbacks [ChosenPullbacks C] : HasPullbacks C :=
  hasPullbacks_of_hasLimit_cospan _

/-- The computable `ChosenPullbacksAlong.pullback g` is naturally isomorphic to the noncomputable
`Over.pullback g`. -/
noncomputable def pullbackIsoOverPullback : ChosenPullbacksAlong.pullback g ≅ Over.pullback g :=
  (ChosenPullbacksAlong.mapPullbackAdj g).rightAdjointUniq (Over.mapPullbackAdj g)

@[reassoc (attr := simp)]
theorem pullbackIsoOverPullback_hom_app_comp_fst (T : Over X) :
    ((pullbackIsoOverPullback g).hom.app T).left ≫ pullback.fst _ _ = fst _ _ := by
  simpa using (Over.forget _).congr_map
    ((ChosenPullbacksAlong.mapPullbackAdj g).rightAdjointUniq_hom_app_counit
      (Over.mapPullbackAdj g) T)

@[reassoc (attr := simp)]
theorem pullbackIsoOverPullback_hom_app_comp_snd (T : Over X) :
    ((pullbackIsoOverPullback g).hom.app T).left ≫ pullback.snd _ _ = snd _ _ :=
  Over.w ((pullbackIsoOverPullback g).hom.app T)

@[reassoc (attr := simp)]
theorem pullbackIsoOverPullback_inv_app_comp_fst (T : Over X) :
    ((pullbackIsoOverPullback g).inv.app T).left ≫ fst _ _ = pullback.fst _ _ := by
  simp [← pullbackIsoOverPullback_hom_app_comp_fst, ← Over.comp_left_assoc]

@[reassoc (attr := simp)]
theorem pullbackIsoOverPullback_inv_app_comp_snd (T : Over X) :
    ((pullbackIsoOverPullback g).inv.app T).left ≫ snd _ _ = pullback.snd _ _ :=
  Over.w ((pullbackIsoOverPullback g).inv.app T)

end PullbackFromChosenPullbacksAlongs

end ChosenPullbacksAlong

end CategoryTheory
