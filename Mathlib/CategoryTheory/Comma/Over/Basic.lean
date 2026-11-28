/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Over and under categories

Over (and under) categories are special cases of comma categories.
* If `L` is the identity functor and `R` is a constant functor, then `Comma L R` is the "slice" or
  "over" category over the object `R` maps to.
* Conversely, if `L` is a constant functor and `R` is the identity functor, then `Comma L R` is the
  "coslice" or "under" category under the object `L` maps to.

## Tags

Comma, Slice, Coslice, Over, Under
-/

@[expose] public section


namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

to_dual_name_hint Over Under, Left Right, Epi Mono

-- morphism levels before object levels. See note [category theory universes].
variable {T : Type u₁} [Category.{v₁} T]
variable {D : Type u₂} [Category.{v₂} D]

/-- The over category has as objects arrows in `T` with codomain `X` and as morphisms commutative
triangles. -/
@[stacks 001G, to_dual (attr := implicit_reducible)]
def Over (X : T) :=
  CostructuredArrow (𝟭 T) X

/-- The type of morphisms in the category `Over`. -/
@[to_dual (attr := implicit_reducible) (reorder := f g)
/-- The type of morphisms in the category `Under`. -/]
protected def Over.Hom {X : T} (f g : Over X) := CommaMorphism f g

@[to_dual]
instance {X : T} : Category (Over X) where
  Hom := Over.Hom
  __ := (inferInstance : Category (Comma _ _))

-- Satisfying the inhabited linter
@[to_dual]
instance Over.inhabited [Inhabited T] : Inhabited (Over (default : T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 _ }

namespace Over

variable {X : T}

/-- The underlying object of an object in `Over X`. -/
@[to_dual /-- The underlying object of an object in `Under X`. -/]
abbrev left (f : Over X) : T := Comma.left f

/-- The morphism that is part of an object in `Over X`. -/
@[to_dual /-- The morphism that is part of an object in `Under X`. -/]
abbrev hom (f : Over X) : f.left ⟶ X := Comma.hom f

variable {f g : Over X} (φ : f ⟶ g)

/-- The morphism that is part of a morphism in `Over X`. -/
@[to_dual /-- The morphism that is part of a morphism in `Under X`. -/]
abbrev Hom.left : f.left ⟶ g.left := CommaMorphism.left φ

@[to_dual (attr := reassoc (attr := simp))]
theorem w : φ.left ≫ g.hom = f.hom :=
  CostructuredArrow.w φ

@[to_dual (attr := reassoc)]
lemma Hom.w : φ.left ≫ g.hom = f.hom := Over.w φ

@[to_dual (attr := ext) UnderMorphism.ext]
theorem OverMorphism.ext {X : T} {U V : Over X} {f g : U ⟶ V} (h : f.left = g.left) : f = g :=
  CostructuredArrow.ext f g h

@[to_dual (attr := simp)]
theorem over_right (U : Over X) : U.right = ⟨⟨⟩⟩ := by simp only

@[to_dual (attr := simp)]
theorem id_left (U : Over X) : Hom.left (𝟙 U) = 𝟙 U.left :=
  rfl

@[to_dual (attr := simp, reassoc)]
theorem comp_left (a b c : Over X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).left = f.left ≫ g.left :=
  rfl

/-- To give an object in the over category, it suffices to give a morphism with codomain `X`. -/
@[to_dual
/-- To give an object in the under category, it suffices to give an arrow with domain `X`. -/]
abbrev mk {X Y : T} (f : Y ⟶ X) : Over X :=
  CostructuredArrow.mk f

/-- We can set up a coercion from arrows with codomain `X` to `over X`. This most likely should not
be a global instance, but it is sometimes useful. -/
@[to_dual (attr := instance_reducible)]
def coeFromHom {X Y : T} : CoeOut (Y ⟶ X) (Over X) where coe := mk

section

attribute [local instance] coeFromHom

@[to_dual]
theorem coe_hom {X Y : T} (f : Y ⟶ X) : (f : Over X).hom = f :=
  rfl

end

/-- To give a morphism in the over category, it suffices to give an arrow fitting in a commutative
triangle. -/
@[to_dual
/-- To give a morphism in the under category, it suffices to give a morphism fitting in a
commutative triangle. -/]
abbrev homMk {U V : Over X} (f : U.left ⟶ V.left) (w : f ≫ V.hom = U.hom := by cat_disch) : U ⟶ V :=
  CostructuredArrow.homMk f w

@[to_dual (attr := simp)]
lemma homMk_eta {U V : Over X} (f : U ⟶ V) (h) :
    homMk f.left h = f :=
  rfl

/-- This is useful when `homMk (· ≫ ·)` appears under `Functor.map` or a natural equivalence. -/
@[to_dual
/-- This is useful when `homMk (· ≫ ·)` appears under `Functor.map` or a natural equivalence. -/]
lemma homMk_comp {U V W : Over X} (f : U.left ⟶ V.left) (g : V.left ⟶ W.left) (w_f w_g) :
    homMk (f ≫ g) (by simp_all) = homMk f w_f ≫ homMk g w_g := by
  ext
  simp

/-- Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
@[simps! hom_left inv_left]
def isoMk {f g : Over X} (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom := by cat_disch) :
    f ≅ g :=
  CostructuredArrow.isoMk hl hw

/-- Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
@[simps! hom_right inv_right]
def _root_.CategoryTheory.Under.isoMk {f g : Under X} (hr : f.right ≅ g.right)
    (hw : f.hom ≫ hr.hom = g.hom := by cat_disch) : f ≅ g :=
  StructuredArrow.isoMk hr hw

to_dual_for isoMk := Under.isoMk hl (by rw [← Iso.eq_comp_inv, hw])
to_dual_for Under.isoMk := isoMk hr (by rw [← Iso.eq_inv_comp, hw])
attribute [to_dual none] isoMk_hom_left isoMk_inv_left Under.isoMk_hom_right Under.isoMk_inv_right

@[to_dual (attr := simp)]
lemma eqToHom_left {f g : Over X} (h : f = g) :
    (eqToHom h).left = eqToHom (by rw [h]) := by
  subst h
  rfl

@[to_dual (attr := reassoc (attr := simp))]
lemma hom_left_inv_left {f g : Over X} (e : f ≅ g) :
    e.hom.left ≫ e.inv.left = 𝟙 f.left := by
  simp [← Over.comp_left]

@[to_dual (attr := reassoc (attr := simp))]
lemma inv_left_hom_left {f g : Over X} (e : f ≅ g) :
    e.inv.left ≫ e.hom.left = 𝟙 g.left := by
  simp [← Over.comp_left]

@[to_dual]
lemma forall_iff (P : Over X → Prop) :
    (∀ Y, P Y) ↔ (∀ (Y) (f : Y ⟶ X), P (.mk f)) := by
  aesop

@[to_dual]
lemma mk_surjective {S : T} (X : Over S) :
    ∃ (Y : T) (f : Y ⟶ S), Over.mk f = X :=
  ⟨_, X.hom, rfl⟩

@[to_dual]
lemma homMk_surjective
    {S : T} {X Y : Over S} (f : X ⟶ Y) :
    ∃ (g : X.left ⟶ Y.left) (hg : g ≫ Y.hom = X.hom), f = Over.homMk g :=
  ⟨f.left, by simp⟩

variable (X) in
/-- The forgetful functor mapping an arrow to its domain. -/
@[stacks 001G, to_dual (attr := implicit_reducible)
/-- The forgetful functor mapping an arrow to its domain. -/]
def forget : Over X ⥤ T :=
  Comma.fst _ _

@[to_dual (attr := simp)]
theorem forget_obj {U : Over X} : (forget X).obj U = U.left :=
  rfl

@[to_dual (attr := simp)]
theorem forget_map {U V : Over X} {f : U ⟶ V} : (forget X).map f = f.left :=
  rfl

/-- The natural cocone over the forgetful functor `Over X ⥤ T` with cocone point `X`. -/
@[to_dual (attr := simps)
/-- The natural cone over the forgetful functor `Under X ⥤ T` with cone point `X`. -/]
def forgetCocone (X : T) : Limits.Cocone (forget X) :=
  { pt := X
    ι := { app := Comma.hom } }

/-- A morphism `f : X ⟶ Y` induces a functor `Over X ⥤ Over Y` in the obvious way. -/
@[stacks 001G, to_dual (attr := implicit_reducible)
/-- A morphism `X ⟶ Y` induces a functor `Under Y ⥤ Under X` in the obvious way. -/]
def map {Y : T} (f : X ⟶ Y) : Over X ⥤ Over Y :=
  Comma.mapRight _ <| Discrete.natTrans fun _ => f

section

variable {Y : T} {f : X ⟶ Y} {U V : Over X} {g : U ⟶ V}

@[to_dual (attr := simp)]
theorem map_obj_left : ((map f).obj U).left = U.left :=
  rfl

@[to_dual (attr := simp)]
theorem map_obj_hom : ((map f).obj U).hom = U.hom ≫ f :=
  rfl

@[to_dual (attr := simp)]
theorem map_map_left : ((map f).map g).left = g.left :=
  rfl

/-- If `f` is an isomorphism, `map f` is an equivalence of categories. -/
@[to_dual]
def mapIso (f : X ≅ Y) : Over X ≌ Over Y :=
  Comma.mapRightIso _ <| Discrete.natIso fun _ ↦ f

@[to_dual (attr := simp)] lemma mapIso_functor (f : X ≅ Y) : (mapIso f).functor = map f.hom := rfl
@[to_dual (attr := simp)] lemma mapIso_inverse (f : X ≅ Y) : (mapIso f).inverse = map f.inv := rfl

@[to_dual]
instance [IsIso f] : (Over.map f).IsEquivalence := (Over.mapIso <| asIso f).isEquivalence_functor

end

section coherences
/-!
This section proves various equalities between functors that
demonstrate, for instance, that over categories assemble into a
functor `mapFunctor : T ⥤ Cat`.

These equalities between functors are then converted to natural
isomorphisms using `eqToIso`. Such natural isomorphisms could be
obtained directly using `Iso.refl` but this method will have
better computational properties, when used, for instance, in
developing the theory of Beck-Chevalley transformations.
-/

/-- The natural isomorphism arising from `mapForget_eq`. -/
@[to_dual (attr := simps!) /-- Mapping by the identity morphism is just the identity functor. -/]
def mapId (Y : T) : map (𝟙 Y) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ ↦ isoMk (Iso.refl _))

/-- Mapping by the identity morphism is just the identity functor. -/
@[to_dual /-- Mapping by the identity morphism is just the identity functor. -/]
theorem mapId_eq (Y : T) : map (𝟙 Y) = 𝟭 _ :=
  Functor.ext_of_iso (mapId Y) (fun _ ↦ by simp [map, Comma.mapRight]; rfl)
    (fun _ ↦ by ext; simp [eqToHom_left])

/-- Mapping by `f` and then forgetting is the same as forgetting. -/
@[to_dual /-- Mapping by `f` and then forgetting is the same as forgetting. -/]
theorem mapForget_eq {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget Y) = (forget X) := rfl

/-- The natural isomorphism arising from `mapForget_eq`. -/
@[to_dual /-- The natural isomorphism arising from `mapForget_eq`. -/]
def mapForget {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget Y) ≅ (forget X) := eqToIso (mapForget_eq f)

/-- The natural isomorphism arising from `mapComp_eq`. -/
@[to_dual (attr := simps!) (reorder := f g)
/-- The natural isomorphism arising from `mapComp_eq`. -/]
def mapComp {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) ≅ map f ⋙ map g :=
  NatIso.ofComponents (fun _ ↦ isoMk (Iso.refl _))

/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/
@[to_dual (reorder := f g)
/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/]
theorem mapComp_eq {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = (map f) ⋙ (map g) :=
  Functor.ext_of_iso (mapComp f g)
    (fun _ ↦ by simp [map, Comma.mapRight])
    (fun _ ↦ by ext; simp [eqToHom_left])

/-- If `f = g`, then `map f` is naturally isomorphic to `map g`. -/
@[to_dual (attr := simps!) /-- If `f = g`, then `map f` is naturally isomorphic to `map g`. -/]
def mapCongr {X Y : T} (f g : X ⟶ Y) (h : f = g) :
    map f ≅ map g :=
  NatIso.ofComponents (fun _ ↦ isoMk (Iso.refl _))

@[to_dual (attr := simp)]
lemma mapCongr_rfl {X Y : T} (f : X ⟶ Y) :
    mapCongr f f rfl = Iso.refl _ := rfl

variable (T) in
/-- The functor defined by the over categories -/
@[simps] def mapFunctor : T ⥤ Cat where
  obj X := ↧(Over X)
  map f := (map f).toCatHom
  map_id X := congr($(mapId_eq X).toCatHom)
  map_comp f g := congr($(mapComp_eq f g).toCatHom)

open Under in
variable (T) in
/-- The functor defined by the under categories -/
@[simps] def _root_.CategoryTheory.Under.mapFunctor : Tᵒᵖ ⥤ Cat where
  obj X := ↧(Under X.unop)
  map f := (Under.map f.unop).toCatHom
  map_id X := congr($(Under.mapId_eq X.unop).toCatHom)
  map_comp f g := congr($(Under.mapComp_eq (g.unop) (f.unop)).toCatHom)

end coherences

@[to_dual]
instance forget_reflects_iso : (forget X).ReflectsIsomorphisms where
  reflects f _ := ⟨Over.homMk (inv ((forget X).map f) :), by cat_disch⟩

/-- The identity over `X` is terminal. -/
@[to_dual /-- The identity under `X` is initial. -/]
noncomputable def mkIdTerminal : Limits.IsTerminal (mk (𝟙 X)) :=
  CostructuredArrow.mkIdTerminal

-- We could make this defeq if we care.
@[to_dual (attr := simp) mkIdInitial_to_right]
lemma mkIdTerminal_from_left (Y : Over X) : (mkIdTerminal.from Y).left = Y.hom := by
  rw [mkIdTerminal.hom_ext (mkIdTerminal.from Y) (homMk Y.hom)]
  rfl

@[to_dual]
instance forget_faithful : (forget X).Faithful where

-- TODO: Show the converse holds if `T` has binary products.
/--
If `k.left` is an epimorphism, then `k` is an epimorphism. In other words, `Over.forget X` reflects
epimorphisms.
The converse does not hold without additional assumptions on the underlying category, see
`CategoryTheory.Over.epi_left_of_epi`.
-/
@[to_dual
/-- If `k.right` is a monomorphism, then `k` is a monomorphism. In other words, `Under.forget X`
reflects epimorphisms.
The converse does not hold without additional assumptions on the underlying category, see
`CategoryTheory.Under.mono_right_of_mono`.
-/]
theorem epi_of_epi_left {f g : Over X} (k : f ⟶ g) [hk : Epi k.left] : Epi k :=
  (forget X).epi_of_epi_map hk

@[to_dual]
instance epi_homMk {U V : Over X} {f : U.left ⟶ V.left} [Epi f] (w) : Epi (homMk f w) :=
  (forget X).epi_of_epi_map ‹_›

/--
If `k.left` is a monomorphism, then `k` is a monomorphism. In other words, `Over.forget X` reflects
monomorphisms.
The converse of `CategoryTheory.Over.mono_left_of_mono`.

This lemma is not an instance, to avoid loops in type class inference.
-/
@[to_dual
/--
If `k.right` is an epimorphism, then `k` is an epimorphism. In other words, `Under.forget X`
reflects epimorphisms.
The converse of `CategoryTheory.Under.epi_right_of_epi`.

This lemma is not an instance, to avoid loops in type class inference.
-/]
theorem mono_of_mono_left {f g : Over X} (k : f ⟶ g) [hk : Mono k.left] : Mono k :=
  (forget X).mono_of_mono_map hk

@[to_dual]
instance mono_homMk {U V : Over X} {f : U.left ⟶ V.left} [Mono f] (w) : Mono (homMk f w) :=
  (forget X).mono_of_mono_map ‹_›

/--
If `k` is a monomorphism, then `k.left` is a monomorphism. In other words, `Over.forget X` preserves
monomorphisms.
The converse of `CategoryTheory.Over.mono_of_mono_left`.
-/
@[to_dual
/--
If `k` is an epimorphism, then `k.right` is an epimorphism. In other words, `Under.forget X`
preserves epimorphisms.
The converse of `CategoryTheory.under.epi_of_epi_right`.
-/]
instance mono_left_of_mono {f g : Over X} (k : f ⟶ g) [Mono k] : Mono k.left := by
  refine ⟨fun {Y : T} l m a => ?_⟩
  let l' : mk (m ≫ f.hom) ⟶ f := homMk l (by
        dsimp; rw [← Over.w k, ← Category.assoc, congrArg (· ≫ g.hom) a, Category.assoc])
  suffices l' = (homMk m : mk (m ≫ f.hom) ⟶ f) by apply congrArg CommaMorphism.left this
  rw [← cancel_mono k]
  ext
  apply a

section IteratedSlice

variable (f : Over X)

/-- Given f : Y ⟶ X, this is the obvious functor from (T/X)/f to T/Y -/
@[simps]
def iteratedSliceForward : Over f ⥤ Over f.left where
  obj α := Over.mk α.hom.left
  map κ := Over.homMk κ.left.left (by dsimp; rw [← Over.w κ]; rfl)

/-- Given f : Y ⟶ X, this is the obvious functor from T/Y to (T/X)/f -/
@[simps]
def iteratedSliceBackward : Over f.left ⥤ Over f where
  obj g := mk (homMk g.hom : mk (g.hom ≫ f.hom) ⟶ f)
  map α := homMk (homMk α.left (w_assoc α f.hom)) (OverMorphism.ext (w α))

theorem iteratedSliceBackward_forget (f : Over X) :
    iteratedSliceBackward f ⋙ Over.forget f = Over.map f.hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given f : Y ⟶ X, we have an equivalence between (T/X)/f and T/Y -/
@[simps]
def iteratedSliceEquiv : Over f ≌ Over f.left where
  functor := iteratedSliceForward f
  inverse := iteratedSliceBackward f
  unitIso := NatIso.ofComponents (fun g => Over.isoMk (Over.isoMk (Iso.refl _)))
  counitIso := NatIso.ofComponents (fun g => Over.isoMk (Iso.refl _))

theorem iteratedSliceForward_forget :
    iteratedSliceForward f ⋙ forget f.left = forget f ⋙ forget X :=
  rfl

theorem iteratedSliceBackward_forget_forget :
    iteratedSliceBackward f ⋙ forget f ⋙ forget X = forget f.left :=
  rfl

variable {f}

/-- The naturality of the iterated slice equivalence up to isomorphism. -/
@[simps! hom_app inv_app]
def iteratedSliceForwardNaturalityIso {g : Over X} (p : f ⟶ g) :
    iteratedSliceForward f ⋙ Over.map p.left ≅ Over.map p ⋙ iteratedSliceForward g :=
  Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism relating the functor `Over.map p` to the functor `Over.map p.left`,
mediated by the underlying functor of the iterated slice equivalence.
Note that `iteratedSliceForward` can in fact be considered as a natural transformation from the
2-functor `Over (C := Over X) : Over X ⥤ Cat` to the composite 2-functor
`forget X ⋙ Over : Over X ⥤ Cat`, and the naturality isomorphism is then given by
`iteratedSliceEquivOverMapIso`.
-/
@[simps! hom_app_left_left inv_app_left_left]
def iteratedSliceEquivOverMapIso {f g : Over X} (p : f ⟶ g) :
    f.iteratedSliceForward ⋙ Over.map p.left ⋙ g.iteratedSliceBackward ≅ Over.map p :=
  NatIso.ofComponents (fun h => Over.isoMk (Over.isoMk (Iso.refl _)))

end IteratedSlice

/-- A functor `F : T ⥤ D` induces a functor `Over X ⥤ Over (F.obj X)` in the obvious way. -/
@[to_dual (attr := implicit_reducible, simps)
/-- A functor `F : T ⥤ D` induces a functor `Under X ⥤ Under (F.obj X)` in the obvious way. -/]
def post (F : T ⥤ D) : Over X ⥤ Over (F.obj X) where
  obj Y := mk <| F.map Y.hom
  map f := Over.homMk (F.map f.left) (by simp [← F.map_comp])

@[to_dual]
lemma post_comp {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) = post (X := X) F ⋙ post G :=
  rfl

@[to_dual]
lemma post_forget_eq_forget_comp (F : T ⥤ D) (X : T) :
    post F ⋙ forget (F.obj X) = forget X ⋙ F :=
  rfl

/-- `post (F ⋙ G)` is isomorphic (actually equal) to `post F ⋙ post G`. -/
@[to_dual (attr := simps!)
/-- `post (F ⋙ G)` is isomorphic (actually equal) to `post F ⋙ post G`. -/]
def postComp {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) ≅ post F ⋙ post G :=
  NatIso.ofComponents (fun X ↦ Iso.refl _) (fun f ↦ by
    ext
    dsimp only [Iso.refl_hom, Over.comp_left, Over.id_left]
    simp)

/-- A natural transformation `F ⟶ G` induces a natural transformation on
`Over X` up to `Over.map`. -/
@[to_dual (attr := simps)
/-- A natural transformation `F ⟶ G` induces a natural transformation on
`Under X` up to `Under.map`. -/]
def postMap {F G : T ⥤ D} (e : F ⟶ G) : post F ⋙ map (e.app X) ⟶ post G where
  app Y := Over.homMk (e.app Y.left)

/-- If `F` and `G` are naturally isomorphic, then `Over.post F` and `Over.post G` are also naturally
isomorphic up to `Over.map` -/
@[to_dual (attr := simps!)
/-- If `F` and `G` are naturally isomorphic, then `Under.post F` and `Under.post G` are also
naturally isomorphic up to `Under.map` -/]
def postCongr {F G : T ⥤ D} (e : F ≅ G) : post F ⋙ map (e.hom.app X) ≅ post G :=
  NatIso.ofComponents (fun A ↦ Over.isoMk (e.app A.left))

variable (X) (F : T ⥤ D)

@[to_dual]
instance [F.Faithful] : (Over.post (X := X) F).Faithful where
  map_injective {A B} f g h := by
    ext
    exact F.map_injective (congrArg CommaMorphism.left h)

@[to_dual]
instance [F.Faithful] [F.Full] : (Over.post (X := X) F).Full where
  map_surjective {A B} f := by
    obtain ⟨a, ha⟩ := F.map_surjective f.left
    exact ⟨Over.homMk a (F.map_injective (by simp [ha, dsimp% f.w])), by cat_disch⟩

@[to_dual]
instance [F.Full] [F.EssSurj] : (Over.post (X := X) F).EssSurj where
  mem_essImage B := by
    obtain ⟨A', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) B.left
    obtain ⟨f, hf⟩ := F.map_surjective (e.hom ≫ B.hom)
    exact ⟨Over.mk f, ⟨Over.isoMk e⟩⟩

@[to_dual]
instance [F.IsEquivalence] : (Over.post (X := X) F).IsEquivalence where

/-- If `F` is fully faithful, then so is `Over.post F`. -/
@[to_dual /-- If `F` is fully faithful, then so is `Under.post F`. -/]
def _root_.CategoryTheory.Functor.FullyFaithful.over (h : F.FullyFaithful) :
    (post (X := X) F).FullyFaithful where
  preimage {A B} f := Over.homMk (h.preimage f.left) <| h.map_injective (by simpa using Over.w f)

/-- If `G` is a right adjoint, then so is `post G : Over Y ⥤ Over (G Y)`.

If the left adjoint of `G` is `F`, then the left adjoint of `post G` is given by
`(X ⟶ G Y) ↦ (F X ⟶ F G Y ⟶ Y)`. -/
@[to_dual (attr := simps)
/-- If `F` is a left adjoint, then so is `post F : Under X ⥤ Under (F X)`.

If the right adjoint of `F` is `G`, then the right adjoint of `post F` is given by
`(F X ⟶ Y) ↦ (X ⟶ G F X ⟶ G Y)`. -/]
def postAdjunctionRight {Y : D} {F : T ⥤ D} {G : D ⥤ T} (a : F ⊣ G) :
    post F ⋙ map (a.counit.app Y) ⊣ post G where
  unit.app A := homMk <| a.unit.app A.left
  counit.app A := homMk <| a.counit.app A.left
  counit.naturality _ _ f := by
    ext
    exact a.counit_naturality f.left
  left_triangle_components A := by
    ext
    simp [-Functor.id_obj]

@[to_dual]
instance isRightAdjoint_post {Y : D} {G : D ⥤ T} [G.IsRightAdjoint] :
    (post (X := Y) G).IsRightAdjoint :=
  ⟨_, ⟨postAdjunctionRight (Adjunction.ofIsRightAdjoint G)⟩⟩

/-- An equivalence of categories induces an equivalence on over categories. -/
@[to_dual (attr := simps)
/-- An equivalence of categories induces an equivalence on under categories. -/]
def postEquiv (F : T ≌ D) : Over X ≌ Over (F.functor.obj X) where
  functor := Over.post F.functor
  inverse := Over.post (X := F.functor.obj X) F.inverse ⋙ Over.map (F.unitIso.inv.app X)
  unitIso := NatIso.ofComponents (fun A ↦ Over.isoMk (F.unitIso.app A.left))
  counitIso := NatIso.ofComponents (fun A ↦ Over.isoMk (F.counitIso.app A.left))

/-- `post (Over.forget X) : Over f ⥤ Over (forget.obj f)` is naturally isomorphic to the
functor `Over.iteratedSliceForward : Over f ⥤ Over f.left`. -/
@[simps! hom_app inv_app]
def iteratedSliceForwardIsoPost (f : Over X) :
    post (Over.forget X) ≅ Over.iteratedSliceForward f :=
  Iso.refl _

open Limits

variable {X} in
/-- If `X : T` is terminal, then the over category of `X` is equivalent to `T`. -/
@[to_dual (attr := simps)
/-- If `X : T` is initial, then the under category of `X` is equivalent to `T`. -/]
def equivalenceOfIsTerminal (hX : IsTerminal X) : Over X ≌ T where
  functor := forget X
  inverse := { obj Y := mk (hX.from Y), map f := homMk f }
  unitIso := NatIso.ofComponents fun Y ↦ isoMk (.refl _) (hX.hom_ext _ _)
  counitIso := NatIso.ofComponents fun _ ↦ .refl _

/-- The induced functor to `Over X` from a functor `J ⥤ C` and natural maps `sᵢ : X ⟶ Dᵢ`.
For the converse direction see `CategoryTheory.WithTerminal.commaFromOver`. -/
@[to_dual (attr := simps)
/-- The induced functor to `Under X` from a functor `J ⥤ C` and natural maps `sᵢ : X ⟶ Dᵢ`. -/]
protected def lift {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : D ⟶ (Functor.const J).obj X) :
    J ⥤ Over X where
  obj j := mk (s.app j)
  map f := homMk (D.map f) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The induced cone on `Over X` on the lifted functor. -/
@[to_dual (attr := simps) /-- The induced cocone on `Under X` from on the lifted functor. -/]
def liftCone {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : D ⟶ (Functor.const J).obj X)
    (c : Cone D) (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ s.app j = p) :
    Cone (Over.lift D s) where
  pt := mk p
  π.app j := homMk (c.π.app j)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The lifted cone on `Over X` is a limit cone if the original cone was limiting
and `J` is nonempty. -/
@[to_dual
/-- The lifted cocone on `Under X` is a colimit cocone if the original cocone was colimiting
and `J` is nonempty. -/]
def isLimitLiftCone {J : Type*} [Category* J] [Nonempty J]
    (D : J ⥤ T) {X : T} (s : D ⟶ (Functor.const J).obj X)
    (c : Cone D) (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ s.app j = p)
    (hc : IsLimit c) :
    IsLimit (Over.liftCone D s c p hp) where
  lift t := homMk (hc.lift ((forget _).mapCone t)) (by
    let j : J := Classical.arbitrary _
    simp [← hp j, dsimp% (t.π.app j).w, dsimp% hc.fac_assoc ((forget X).mapCone t) j])
  fac t j := by
    ext
    simp [dsimp% hc.fac ((forget X).mapCone t) j]
  uniq t _ hm := by
    ext
    refine hc.hom_ext (fun j ↦ ?_)
    simp [dsimp% hc.fac ((forget X).mapCone t) j, ← hm]

end Over

/--
Restrict a cone to the diagram over `j`. This preserves being limiting if the forgetful functor
`Over j ⥤ J` is initial (see `CategoryTheory.Limits.IsLimit.overPost`).
-/
@[to_dual (attr := simps)
/--
Restrict a cocone to the diagram under `j`. This preserves being colimiting if the forgetful functor
`Over j ⥤ J` is final (see `CategoryTheory.Limits.IsColimit.underPost`).
-/]
def Limits.Cone.overPost
    {J C : Type*} [Category* J] [Category* C] {D : J ⥤ C} (c : Cone D) (j : J) :
    Cone (Over.post (X := j) D) where
  pt := Over.mk (c.π.app j)
  π.app k := Over.homMk (c.π.app k.left)

namespace CostructuredArrow

/-- Reinterpreting an `F`-costructured arrow `F.obj d ⟶ X` as an arrow over `X` induces a functor
    `CostructuredArrow F X ⥤ Over X`. -/
@[to_dual (attr := simps!)
/-- Reinterpreting an `F`-structured arrow `X ⟶ F.obj d` as an arrow under `X` induces a functor
    `StructuredArrow X F ⥤ Under X`. -/]
def toOver (F : D ⥤ T) (X : T) : CostructuredArrow F X ⥤ Over X :=
  CostructuredArrow.pre F (𝟭 T) X

@[to_dual]
instance (F : D ⥤ T) (X : T) [F.Faithful] : (toOver F X).Faithful :=
  show (CostructuredArrow.pre _ _ _).Faithful from inferInstance

@[to_dual]
instance (F : D ⥤ T) (X : T) [F.Full] : (toOver F X).Full :=
  show (CostructuredArrow.pre _ _ _).Full from inferInstance

@[to_dual]
instance (F : D ⥤ T) (X : T) [F.EssSurj] : (toOver F X).EssSurj :=
  show (CostructuredArrow.pre _ _ _).EssSurj from inferInstance

/-- An equivalence `F` induces an equivalence `CostructuredArrow F X ≌ Over X`. -/
@[to_dual /-- An equivalence `F` induces an equivalence `StructuredArrow X F ≌ Under X`. -/]
instance isEquivalence_toOver (F : D ⥤ T) (X : T) [F.IsEquivalence] :
    (toOver F X).IsEquivalence :=
  CostructuredArrow.isEquivalence_pre _ _ _

namespace costructuredArrowToOverEquivalence

variable (F : D ⥤ T) {X : T} (Y : Over X)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `costructuredArrowToOverEquivalence`. -/
@[to_dual (attr := simps)]
def functor : CostructuredArrow (toOver F X) Y ⥤ CostructuredArrow F Y.left where
  obj Z := CostructuredArrow.mk Z.hom.left
  map f :=
    CostructuredArrow.homMk f.left.left (by rw [← CostructuredArrow.w f]; dsimp)

/-- Auxiliary definition for `costructuredArrowToOverEquivalence`. -/
@[to_dual (attr := simps)]
def inverse : CostructuredArrow F Y.left ⥤ CostructuredArrow (toOver F X) Y where
  obj Z :=
    CostructuredArrow.mk (Y := CostructuredArrow.mk (Z.hom ≫ Y.hom))
      (Over.homMk Z.hom)
  map f :=
    CostructuredArrow.homMk
      (CostructuredArrow.homMk f.left)
        (by ext; exact CostructuredArrow.w f)

end costructuredArrowToOverEquivalence

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A category of costructured arrows for a functor `toOver F X` identifies
to a category of costructured arrows for `F`. -/
def costructuredArrowToOverEquivalence (F : D ⥤ T) {X : T} (Y : Over X) :
    CostructuredArrow (toOver F X) Y ≌ CostructuredArrow F Y.left where
  functor := costructuredArrowToOverEquivalence.functor F Y
  inverse := costructuredArrowToOverEquivalence.inverse F Y
  unitIso :=
    NatIso.ofComponents (fun f ↦
      CostructuredArrow.isoMk (CostructuredArrow.isoMk (Iso.refl _)
        (by simpa using f.hom.w)))
  counitIso := Iso.refl _

end CostructuredArrow

namespace Functor
variable {X : T} {F : T ⥤ D}

@[to_dual]
lemma essImage.of_overPost {Y : Over (F.obj X)} :
    (Over.post F (X := X)).essImage Y → F.essImage Y.left :=
  fun ⟨Z, ⟨e⟩⟩ ↦ ⟨Z.left, ⟨(Over.forget _).mapIso e⟩⟩

/-- The essential image of `Over.post F` where `F` is full is the same as the essential image of
`F`. -/
@[to_dual (attr := simp)
/-- The essential image of `Under.post F` where `F` is full is the same as the essential image of
`F`. -/]
lemma essImage_overPost [F.Full] {Y : Over (F.obj X)} :
    (Over.post F (X := X)).essImage Y ↔ F.essImage Y.left where
  mp := .of_overPost
  mpr := fun ⟨Z, ⟨e⟩⟩ ↦ let ⟨f, hf⟩ := F.map_surjective (e.hom ≫ Y.hom); ⟨.mk f, ⟨Over.isoMk e⟩⟩

variable {S : Type u₂} [Category.{v₂} S]

/-- Given `X : T`, to upgrade a functor `F : S ⥤ T` to a functor `S ⥤ Over X`, it suffices to
    provide maps `F.obj Y ⟶ X` for all `Y` making the obvious triangles involving all `F.map g`
    commute. -/
@[to_dual (attr := simps!)
/-- Given `X : T`, to upgrade a functor `F : S ⥤ T` to a functor `S ⥤ Under X`, it suffices to
    provide maps `X ⟶ F.obj Y` for all `Y` making the obvious triangles involving all `F.map g`
    commute. -/]
def toOver (F : S ⥤ T) (X : T) (f : (Y : S) → F.obj Y ⟶ X)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : S ⥤ Over X :=
  F.toCostructuredArrow (𝟭 _) X f h

/-- Upgrading a functor `S ⥤ T` to a functor `S ⥤ Over X` and composing with the forgetful functor
    `Over X ⥤ T` recovers the original functor. -/
@[to_dual
/-- Upgrading a functor `S ⥤ T` to a functor `S ⥤ Under X` and composing with the forgetful functor
    `Under X ⥤ T` recovers the original functor. -/]
def toOverCompForget (F : S ⥤ T) (X : T) (f : (Y : S) → F.obj Y ⟶ X)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : F.toOver X f h ⋙ Over.forget _ ≅ F :=
  Iso.refl _

@[to_dual (attr := simp)]
lemma toOver_comp_forget (F : S ⥤ T) (X : T) (f : (Y : S) → F.obj Y ⟶ X)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : F.toOver X f h ⋙ Over.forget _ = F :=
  rfl

end Functor

namespace StructuredArrow

set_option backward.defeqAttrib.useBackward true in
/-- A functor from the structured arrow category on the projection functor for any structured
arrow category. -/
@[to_dual (attr := simps!) ofCostructuredArrowProjEquivalence.functor
/-- A functor from the costructured arrow category on the projection functor for any costructured
arrow category. -/]
def ofStructuredArrowProjEquivalence.functor (F : D ⥤ T) (Y : T) (X : D) :
    StructuredArrow X (StructuredArrow.proj Y F) ⥤ StructuredArrow Y (Under.forget X ⋙ F) :=
  Functor.toStructuredArrow
    (Functor.toUnder (StructuredArrow.proj X _ ⋙ StructuredArrow.proj Y _) _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.right.hom) (by simp)

set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor of `ofStructuredArrowProjEquivalence.functor`. -/
@[to_dual (attr := simps!) ofCostructuredArrowProjEquivalence.inverse
/-- The inverse functor of `ofCostructuredArrowProjEquivalence.functor`. -/]
def ofStructuredArrowProjEquivalence.inverse (F : D ⥤ T) (Y : T) (X : D) :
    StructuredArrow Y (Under.forget X ⋙ F) ⥤ StructuredArrow X (StructuredArrow.proj Y F) :=
  Functor.toStructuredArrow
    (Functor.toStructuredArrow (StructuredArrow.proj Y _ ⋙ Under.forget X) _ _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.right.hom) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Characterization of the structured arrow category on the projection functor of any
structured arrow category. -/
@[to_dual
/-- Characterization of the costructured arrow category on the projection functor of any
costructured arrow category. -/]
def ofStructuredArrowProjEquivalence (F : D ⥤ T) (Y : T) (X : D) :
    StructuredArrow X (StructuredArrow.proj Y F) ≌ StructuredArrow Y (Under.forget X ⋙ F) where
  functor := ofStructuredArrowProjEquivalence.functor F Y X
  inverse := ofStructuredArrowProjEquivalence.inverse F Y X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
/-- The canonical functor from the structured arrow category on the diagonal functor
`T ⥤ T × T` to the structured arrow category on `Under.forget`. -/
@[to_dual (attr := simps!)
/-- The canonical functor from the costructured arrow category on the diagonal functor
`T ⥤ T × T` to the costructured arrow category on `Under.forget`. -/]
def ofDiagEquivalence.functor (X : T × T) :
    StructuredArrow X (Functor.diag _) ⥤ StructuredArrow X.2 (Under.forget X.1) :=
  Functor.toStructuredArrow
    (Functor.toUnder (StructuredArrow.proj X _) _
      (fun f ↦ f.hom.1) (fun g ↦ by simp [← w g])) _ _
    (fun f ↦ f.hom.2) (fun g ↦ by simp [← w g])

/-- The inverse functor of `ofDiagEquivalence.functor`. -/
@[to_dual (attr := simps!)
/-- The inverse functor of `ofDiagEquivalence.functor`. -/]
def ofDiagEquivalence.inverse (X : T × T) :
    StructuredArrow X.2 (Under.forget X.1) ⥤ StructuredArrow X (Functor.diag _) :=
  Functor.toStructuredArrow (StructuredArrow.proj _ _ ⋙ Under.forget _) _ _
    (fun f => (f.right.hom, f.hom)) (fun m => by have := m.w; cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Characterization of the structured arrow category on the diagonal functor `T ⥤ T × T`. -/
@[to_dual ofDiagEquivalence
/-- Characterization of the costructured arrow category on the diagonal functor `T ⥤ T × T`. -/]
def ofDiagEquivalence (X : T × T) :
    StructuredArrow X (Functor.diag _) ≌ StructuredArrow X.2 (Under.forget X.1) where
  functor := ofDiagEquivalence.functor X
  inverse := ofDiagEquivalence.inverse X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

/-- A version of `StructuredArrow.ofDiagEquivalence` with the roles of the first and second
projection swapped. -/
@[to_dual ofDiagEquivalence'
/-- A version of `CostructuredArrow.ofDiagEquivalence` with the roles of the first and second
projection swapped. -/]
def ofDiagEquivalence' (X : T × T) :
    StructuredArrow X (Functor.diag _) ≌ StructuredArrow X.1 (Under.forget X.2) :=
  (ofDiagEquivalence X).trans <|
    (ofStructuredArrowProjEquivalence (𝟭 T) X.1 X.2).trans <|
    StructuredArrow.mapNatIso (Under.forget X.2).rightUnitor

section CommaFst

variable {C : Type u₃} [Category.{v₃} C] (F : C ⥤ T) (G : D ⥤ T)

/-- The functor used to define the equivalence `ofCommaFstEquivalence`. -/
@[to_dual (attr := simps)
/-- The functor used to define the equivalence `ofCommaFstEquivalence`. -/]
def ofCommaFstEquivalenceFunctor (c : C) :
    StructuredArrow c (Comma.fst F G) ⥤ Comma (Under.forget c ⋙ F) G where
  obj X := ⟨Under.mk X.hom, X.right.right, X.right.hom⟩
  map f := ⟨Under.homMk f.right.left (by simp [dsimp% f.w]), f.right.right, by simp⟩

/-- The inverse functor used to define the equivalence `ofCommaFstEquivalence`. -/
@[to_dual (attr := simps!)
/-- The inverse functor used to define the equivalence `ofCommaFstEquivalence`. -/]
def ofCommaFstEquivalenceInverse (c : C) :
    Comma (Under.forget c ⋙ F) G ⥤ StructuredArrow c (Comma.fst F G) :=
  Functor.toStructuredArrow (Comma.preLeft (Under.forget c) F G) _ _
    (fun Y => Y.left.hom) (fun _ => by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- There is a canonical equivalence between the structured arrow category with domain `c` on
the functor `Comma.fst F G : Comma F G ⥤ F` and the comma category over
`Under.forget c ⋙ F : Under c ⥤ T` and `G`. -/
@[to_dual (attr := simps)
/-- There is a canonical equivalence between the costructured arrow category with codomain `c` on
the functor `Comma.fst F G : Comma F G ⥤ F` and the comma category over
`Over.forget c ⋙ F : Over c ⥤ T` and `G`. -/]
def ofCommaFstEquivalence (c : C) :
    StructuredArrow c (Comma.fst F G) ≌ Comma (Under.forget c ⋙ F) G where
  functor := ofCommaFstEquivalenceFunctor F G c
  inverse := ofCommaFstEquivalenceInverse F G c
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

@[deprecated (since := "2026-11-27")]
alias ofCommaSndEquivalenceFunctor := ofCommaFstEquivalenceFunctor
@[deprecated (since := "2026-11-27")]
alias ofCommaSndEquivalenceInverse := ofCommaFstEquivalenceInverse
@[deprecated (since := "2026-11-27")] alias ofCommaSndEquivalence := ofCommaFstEquivalence

end CommaFst

end StructuredArrow

section Opposite

open Opposite

variable (X : T)

/-- The canonical equivalence between over and under categories by reversing structure arrows. -/
@[to_dual (attr := simps)
/-- The canonical equivalence between under and over categories by reversing structure arrows. -/]
def Over.opEquivOpUnder : Over (op X) ≌ (Under X)ᵒᵖ where
  functor.obj Y := ⟨Under.mk Y.hom.unop⟩
  functor.map {Z Y} f := ⟨Under.homMk (f.left.unop) (by dsimp; rw [← unop_comp, Over.w])⟩
  inverse.obj Y := Over.mk (Y.unop.hom.op)
  inverse.map {Z Y} f := Over.homMk f.unop.right.op <| by dsimp; rw [← Under.w f.unop, op_comp]
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end Opposite

end CategoryTheory
