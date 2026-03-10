/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison, Johannes Hölzl
-/
module

public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Tactic.PPWithUniv
public import Mathlib.Tactic.ToAdditive

/-!
# The category `Type`.

In this section we set up the theory so that Lean's types and functions between them
can be viewed as a `LargeCategory` in our framework.

Lean cannot transparently view a function as a morphism in this category, and needs a hint in
order to be able to type check. We provide the abbreviation `asHom f` to guide type checking,
as well as a corresponding notation `↾ f`. (Entered as `\upr `.)

We provide various simplification lemmas for functors and natural transformations valued in `Type`.

We define `uliftFunctor`, from `Type u` to `Type (max u v)`, and show that it is fully faithful
(but not, of course, essentially surjective).

We prove some basic facts about the category `Type`:
*  epimorphisms are surjections and monomorphisms are injections,
* `Iso` is both `Iso` and `Equiv` to `Equiv` (at least within a fixed universe),
* every type level `IsLawfulFunctor` gives a categorical functor `Type ⥤ Type`
  (the corresponding fact about monads is in `Mathlib/CategoryTheory/Monad/Types.lean`).
-/

@[expose] public section

-- morphism levels before object levels. See note [category theory universes].
universe v v' w u u'

set_option backward.privateInPublic true in
/--
The category of types and functions between them. The objects and morphisms are wrapped in
one-field structures, as usual in concrete categories.
-/
@[to_additive_do_translate]
structure TypeCat where
  private mk ::
  /-- The underlying type -/
  carrier : Type u

-- initialize_simps_projections TypeCat (-carrier)

namespace TypeCat

instance : CoeSort TypeCat.{u} (Type u) where
  coe X := X.carrier

attribute [coe] carrier

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object in the category of types associated to a type. -/
abbrev of (X : Type u) : TypeCat.{u} := ⟨X⟩

instance : Inhabited TypeCat.{u} := ⟨of <| PUnit⟩

@[ext]
structure Fun (X Y : Type*) where
  protected as : X → Y

instance instFunLikeFun {X Y : Type*} : FunLike (Fun X Y) X Y where
  coe f x := f.as x
  coe_injective' _ := by aesop

def Fun.Simps.coe (X Y : Type*) (f : Fun X Y) := (f : _ → _)

initialize_simps_projections Fun (as → coe)

-- unif_hint {X Y : Type*} (f f' : Fun X Y) (x x' : X) where
--   f ≟ f'
--   x ≟ x'
--   ⊢ f'.as x' ≟ f x

-- example {X Y : Type*} (f : Fun X Y) (x : X) :
--     f.as x = f x := by
--   with_reducible rfl

-- @[simp]
-- lemma Fun.coe_mk {X Y : Type*} (f : X → Y) : (Fun.mk f) = f :=
--   rfl

@[simp]
lemma Fun.mk_apply {X Y : Type*} (f : X → Y) (x : X) : (Fun.mk f) x = f x :=
  rfl

def Fun.id (X : Type*) : Fun X X where
  as x := x

def Fun.comp {X Y Z : Type*} (f : Fun Y Z) (g : Fun X Y) : Fun X Z where
  as x := f (g x)

def Fun.homEquiv (X Y : Type*) : (Fun X Y) ≃ (X → Y) where
  toFun f := f
  invFun f := ⟨f⟩
  left_inv := by intro; rfl
  right_inv := by intro; rfl

set_option backward.privateInPublic true in
/-- The type of morphisms in `TypeCat`. -/
@[ext]
structure Hom (X Y : TypeCat.{u}) where
  private mk ::
  /-- The underlying function -/
  hom' : Fun X Y

end TypeCat

open TypeCat CategoryTheory

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive_do_translate] -- Expressions involving this instance can still be additivized.
instance CategoryTheory.types : Category.{u} TypeCat.{u} where
  Hom := Hom
  id X := .mk <| .id X
  comp f g := .mk <| g.hom'.comp f.hom'

-- @[simp]
-- lemma TypeCat.Fun.coe_eq_as {X Y : TypeCat.{u}} (f : Fun X Y) (x : X) :
--     f.as x = @DFunLike.coe (Fun X Y) X (fun _ ↦ Y) inferInstance f x := by
--   with_reducible rfl

-- @[simp]
-- lemma TypeCat.Fun.apply {X Y : Type*} (f : Fun X Y) (x : X) : f x = f.as x := rfl

-- unif_hint {X Y : Type*} (f f' : X → Y) (x : X) where
--   f ≟ f'
--   ⊢ (Fun.mk f) x ≟ f' x

-- example {X Y : Type*} (f : X → Y) (x : X) : (Fun.mk f) x = f x := by
--   with_reducible rfl

@[simp]
lemma TypeCat.Fun.id_apply {X : Type*} (x : X) : Fun.id X x = x :=
  rfl

@[simp]
lemma TypeCat.Fun.comp_apply {X Y Z : Type*} (f : Fun Y Z) (g : Fun X Y) (x : X) :
    f.comp g x = f (g x) :=
  rfl

-- @[simp] lemma TypeCat.Fun.comp_apply' {X Y Z : Type*} (f : Y → Z) (g : X → Y) (x : X) :
--     Fun.mk f (Fun.mk g x) = f (g x) :=
--   rfl

-- @[simp]
-- lemma TypeCat.hom_as_apply {X Y : Type*} (f : Fun X Y) (x : X) : f.as x = f x :=
--   rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory TypeCat.{u} (fun X Y ↦ Fun X.carrier Y.carrier) where
  hom := Hom.hom'
  ofHom := Hom.mk

lemma coe_of (X : Type u) : (of X : Type u) = X :=
  rfl

-- Ensure the roundtrips are reducibly defeq (so tactics like `rw` can see through them).
example (X : Type u) : (of X : Type u) = X := by with_reducible rfl
example (X : TypeCat.{u}) : of X = X := by with_reducible rfl

example (X Y : TypeCat.{u}) (f : X ⟶ Y) : (f : X → Y) = (ConcreteCategory.hom f : X → Y) := by
  with_reducible rfl

example (X Y : TypeCat.{u}) (f : X ⟶ Y) (x : X) : f x = (f : X → Y) x := by
  with_reducible rfl

example (X Y : Type*) (f : Fun X Y) : (f : X → Y) = f := by
  with_reducible rfl

example (X Y : Type*) (f : Fun X Y) (x : X) : f x = (f : X → Y) x := by
  with_reducible rfl

namespace TypeCat

/-- Turn a morphism in `TypeCat` back into a function. -/
abbrev Hom.hom {X Y : TypeCat.{u}} (f : Hom X Y) : Fun X Y :=
  ConcreteCategory.hom (C := TypeCat.{u}) f

/-- Typecheck a function as a morphism in `TypeCat`. -/
abbrev ofHom {X Y : Type u} (f : Fun X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : TypeCat.{u}) (f : X ⟶ Y) :=
  ConcreteCategory.hom f

initialize_simps_projections Hom (hom' → hom)

@[simp]
lemma hom_as_apply {X Y : TypeCat.{u}} (f : X ⟶ Y) (x : X) : (ConcreteCategory.hom f).as x =
    ConcreteCategory.hom f x :=
  rfl

example (X : Type u) : CategoryTheory.ToType (of X) = X := by with_reducible rfl
example (X : TypeCat.{u}) : CategoryTheory.ToType X = X.carrier := by with_reducible rfl

@[simp]
lemma ofHom_eq {X Y : TypeCat.{u}} (f : X ⟶ Y) : ofHom ⟨f⟩ = f :=
  rfl

@[simp]
lemma ofHom_apply {X Y : Type u} (f : Fun X Y) (x : X) :
    TypeCat.ofHom f x = f x :=
  rfl

@[simp]
lemma ofHom_hom {X Y : Type u} (f : Fun X Y) : Hom.hom (ofHom f) = f := rfl

@[simp]
lemma hom_ofHom {X Y : TypeCat.{u}} (f : X ⟶ Y) : ofHom (Hom.hom f) = f := rfl

/-- `TypeCat.Hom.hom` bundled as an `Equiv`. -/
def homEquiv {X Y : TypeCat.{u}} : (X ⟶ Y) ≃ (X → Y) :=
  (ConcreteCategory.homEquiv (C := TypeCat)).trans (Fun.homEquiv _ _)

@[simp]
lemma homEquiv_apply {X Y : TypeCat.{u}} (f : X ⟶ Y) :
    homEquiv f = f :=
  rfl

@[simp]
lemma homEquiv_symm_apply {X Y : TypeCat.{u}} (f : X → Y) :
    homEquiv.symm f = ofHom ⟨f⟩ :=
  rfl

end TypeCat

namespace CategoryTheory

theorem types_id (X : TypeCat.{u}) : (𝟙 X : _ → _) = id :=
  rfl

theorem types_comp {X Y Z : TypeCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ConcreteCategory.hom (f ≫ g) = g ∘ f :=
  rfl

@[simp]
lemma types_id_apply (X : TypeCat.{u}) (x : X) : 𝟙 X x = x :=
  rfl

@[simp]
lemma types_comp_apply {X Y Z : TypeCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) :=
  rfl

@[deprecated (since := "2026-02-09")] alias hom_inv_id_apply := Iso.hom_inv_id_apply
@[deprecated (since := "2026-02-09")] alias inv_hom_id_apply := Iso.inv_hom_id_apply
@[deprecated (since := "2026-02-09")] alias asHom := TypeCat.ofHom

namespace Functor

variable {J : Type u} [Category.{v} J]

/-- The sections of a functor `F : J ⥤ Type` are
the choices of a point `u j : F.obj j` for each `j`,
such that `F.map f (u j) = u j'` for every morphism `f : j ⟶ j'`.

We later use these to define limits in `Type` and in many concrete categories.
-/
def sections (F : J ⥤ TypeCat.{w}) : Set (∀ j, F.obj j) :=
  { u | ∀ {j j'} (f : j ⟶ j'), F.map f (u j) = u j' }

@[simp]
lemma sections_property {F : J ⥤ TypeCat.{w}} (s : F.sections)
    {j j' : J} (f : j ⟶ j') : F.map f (s.val j) = s.val j' :=
  s.property f

lemma sections_ext_iff {F : J ⥤ TypeCat.{w}} {x y : F.sections} : x = y ↔ ∀ j, x.val j = y.val j :=
  Subtype.ext_iff.trans funext_iff

variable (J)

/-- The functor which sends a functor to types to its sections. -/
@[simps]
def sectionsFunctor : (J ⥤ TypeCat.{w}) ⥤ TypeCat.{max u w} where
  obj F := .of F.sections
  map {F G} φ := TypeCat.ofHom ⟨fun x ↦ ⟨fun j => φ.app j (x.1 j), fun {j j'} f =>
    by simp [← NatTrans.naturality_apply, x.2 f]⟩⟩

end Functor

namespace FunctorToTypes

variable {C : Type u} [Category.{v} C] (F G H : C ⥤ TypeCat.{w}) {X Y Z : C}
variable (σ : F ⟶ G) (τ : G ⟶ H)

attribute [elementwise nosimp] Functor.map_comp Functor.map_id NatTrans.comp_app

@[deprecated Functor.map_comp_apply (since := "2026-03-09")]
theorem map_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X) :
    (F.map (f ≫ g)) a = (F.map g) ((F.map f) a) :=
  F.map_comp_apply f g a

@[deprecated Functor.map_id_apply (since := "2026-03-09")]
theorem map_id_apply (a : F.obj X) : (F.map (𝟙 X)) a = a :=
  F.map_id_apply X a

@[deprecated (since := "2026-02-09")] alias naturality := NatTrans.naturality_apply

@[deprecated NatTrans.comp_app_apply (since := "2026-03-09")]
theorem comp (x : F.obj X) : (σ ≫ τ).app X x = τ.app X (σ.app X x) :=
  σ.comp_app_apply τ X x

attribute [elementwise (attr := simp)] eqToHom_map_comp

@[deprecated "Use `elementwise_of% eqToHom_map_comp` instead" (since := "2026-02-09")]
theorem eqToHom_map_comp_apply (p : X = Y) (q : Y = Z) (x : F.obj X) :
    F.map (eqToHom q) (F.map (eqToHom p) x) = F.map (eqToHom <| p.trans q) x := by
  cat_disch

variable {D : Type u'} [𝒟 : Category.{u'} D] (I J : D ⥤ C) (ρ : I ⟶ J) {W : D}

@[deprecated "No replacement" (since := "2026-02-09")]
theorem hcomp (x : (I ⋙ F).obj W) : (ρ ◫ σ).app W x = (G.map (ρ.app W)) (σ.app (I.obj W) x) :=
  rfl

attribute [elementwise nosimp] Functor.map_hom_inv Functor.map_inv_hom
  Functor.map_hom_inv' Functor.map_inv_hom'

@[deprecated (since := "2026-02-09")] alias map_inv_map_hom_apply := Functor.map_hom_inv_apply
@[deprecated (since := "2026-02-09")] alias map_hom_map_inv_apply := Functor.map_inv_hom_apply

attribute [elementwise (attr := simp)] Iso.hom_inv_id_app Iso.inv_hom_id_app


@[deprecated (since := "2026-02-09")] alias hom_inv_id_app_apply := Iso.hom_inv_id_app_apply
@[deprecated (since := "2026-02-09")] alias inv_hom_id_app_apply := Iso.inv_hom_id_app_apply

-- TODO: spell the assumptions as `{F G : C ⥤ TypeCat.{*}`}
lemma naturality_symm {F : C ⥤ TypeCat.{w}} {G : C ⥤ TypeCat.{u'}} (e : ∀ j, F.obj j ≃ G.obj j)
    (naturality : ∀ {j j'} (f : j ⟶ j'), e j' ∘ F.map f = G.map f ∘ e j) {j j' : C}
    (f : j ⟶ j') :
    (e j').symm ∘ G.map f = F.map f ∘ (e j).symm := by
  ext x
  obtain ⟨y, rfl⟩ := (e j).surjective x
  apply (e j').injective
  dsimp
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  exact (congr_fun (naturality f) y).symm

end FunctorToTypes

/-- The isomorphism between a `Type` which has been `ULift`ed to the same universe,
and the original type.
-/
def uliftTrivial (V : TypeCat.{u}) : of (ULift.{u} V) ≅ of V where
  hom := ofHom ⟨fun a ↦ a.1⟩
  inv := ofHom ⟨fun a ↦ .up a⟩

/-- The functor embedding `Type u` into `Type (max u v)`.
Write this as `uliftFunctor.{5, 2}` to get `Type 2 ⥤ Type 5`.
-/
@[pp_with_univ, simps obj map]
def uliftFunctor : TypeCat.{u} ⥤ TypeCat.{max u v} where
  obj X := of (ULift.{v} X)
  map {X} {_} f := ofHom ⟨fun x : ULift.{v} X => ULift.up (f x.down)⟩

-- @[deprecated (since := "2026-02-09")] alias uliftFunctor_obj := uliftFunctor_obj_carrier

/-- `uliftFunctor : Type u ⥤ Type max u v` is fully faithful. -/
def fullyFaithfulULiftFunctor : (uliftFunctor.{v, u}).FullyFaithful where
  preimage f := ofHom ⟨fun x ↦ (f (ULift.up x)).down⟩

instance uliftFunctor_full : (uliftFunctor.{v, u}).Full :=
  fullyFaithfulULiftFunctor.full

instance uliftFunctor_faithful : uliftFunctor.{v, u}.Faithful :=
  fullyFaithfulULiftFunctor.faithful

/-- The functor embedding `Type u` into `Type u` via `ULift` is isomorphic to the identity functor.
-/
def uliftFunctorTrivial : uliftFunctor.{u, u} ≅ 𝟭 _ :=
  NatIso.ofComponents uliftTrivial

-- TODO We should connect this to a general story about concrete categories
-- whose forgetful functor is representable.
/-- Any term `x` of a type `X` corresponds to a morphism `PUnit ⟶ X`. -/
def homOfElement {X : TypeCat.{u}} (x : X) : of PUnit ⟶ X := ofHom ⟨fun _ => x⟩

theorem homOfElement_eq_iff {X : TypeCat.{u}} (x y : X) : homOfElement x = homOfElement y ↔ x = y :=
  ⟨fun H => ConcreteCategory.congr_hom H PUnit.unit, by simp_all⟩

/-- A morphism in `Type` is a monomorphism if and only if it is injective. -/
@[stacks 003C]
theorem ofHom_mono_iff_injective {X Y : Type u} (f : X → Y) :
    Mono (ofHom ⟨f⟩) ↔ Function.Injective f := by
  constructor
  · intro H x x' h
    rw [← homOfElement_eq_iff] at h ⊢
    exact (cancel_mono (ofHom ⟨f⟩)).mp h
  · refine fun H => ⟨fun g g' h => ConcreteCategory.hom_ext _ _ fun x ↦
      congrFun (H.comp_left ?_) x⟩
    ext y
    exact ConcreteCategory.congr_hom h y

/-- A morphism in `Type` is a monomorphism if and only if it is injective. -/
@[stacks 003C]
theorem mono_iff_injective {X Y : TypeCat.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := by
  simp [← ofHom_mono_iff_injective]

theorem injective_of_mono {X Y : TypeCat.{u}} (f : X ⟶ Y) [hf : Mono f] : Function.Injective f :=
  (mono_iff_injective f).1 hf

/-- A morphism in `TypeCat` is an epimorphism if and only if it is surjective. -/
@[stacks 003C]
theorem ofHom_epi_iff_surjective {X Y : Type u} (f : X → Y) :
    Epi (ofHom ⟨f⟩) ↔ Function.Surjective f := by
  constructor
  · rintro ⟨H⟩
    refine Function.surjective_of_right_cancellable_Prop fun g₁ g₂ hg => ?_
    rw [← Equiv.ulift.{u}.symm.injective.comp_left.eq_iff]
    suffices ofHom ⟨(Equiv.ulift.symm ∘ g₁)⟩ = ofHom ⟨(Equiv.ulift.symm ∘ g₂)⟩ by
      simpa using congrArg ConcreteCategory.hom this
    apply H
    apply ConcreteCategory.hom_ext
    intro x
    change (ULift.up ∘ g₁ ∘ f) _ = (ULift.up ∘ g₂ ∘ f) _
    rw [hg]
  · refine fun H => ⟨fun g g' h =>  ConcreteCategory.hom_ext _ _ fun x ↦
      congrFun (H.injective_comp_right ?_) x⟩
    ext y
    exact ConcreteCategory.congr_hom h y

/-- A morphism in `Type` is an epimorphism if and only if it is surjective. -/
@[stacks 003C]
theorem epi_iff_surjective {X Y : TypeCat.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  simp [← ofHom_epi_iff_surjective]

theorem surjective_of_epi {X Y : TypeCat.{u}} (f : X ⟶ Y) [hf : Epi f] : Function.Surjective f :=
  (epi_iff_surjective f).1 hf

section

/-- `ofTypeFunctor m` converts from Lean's `Type`-based `Category` to `CategoryTheory`. This
allows us to use these functors in category theory. -/
@[simps obj map]
def ofTypeFunctor (m : Type u → Type v) [_root_.Functor m] [LawfulFunctor m] :
    TypeCat.{u} ⥤ TypeCat.{v} where
  obj x := of (m x.carrier)
  map f := ofHom ⟨(_root_.Functor.map f.hom)⟩
  map_id := fun α => by ext X; apply id_map
  map_comp f g := by
    ext x
    exact comp_map (f := m) f.hom g.hom x

variable (m : Type u → Type v) [_root_.Functor m] [LawfulFunctor m]

-- @[simp]
-- theorem ofTypeFunctor_obj (X : TypeCat.{u}) : (ofTypeFunctor m).obj X = of (m X.carrier) :=
--   rfl

-- @[simp]
-- theorem ofTypeFunctor_map {α β} (f : α → β) :
--     ((ofTypeFunctor m).map (ofHom ⟨f⟩)).hom = ⟨(_root_.Functor.map f : m α → m β)⟩ :=
--   rfl

end

end CategoryTheory

-- Isomorphisms in Type and equivalences.
namespace Equiv

variable {X Y : Type u}

/-- Any equivalence between types in the same universe gives
a categorical isomorphism between those types.
-/
@[simps]
def toIso (e : X ≃ Y) : of X ≅ of Y where
  hom := ofHom ⟨fun x ↦ e x⟩
  inv := ofHom ⟨fun x ↦ e.symm x⟩

end Equiv

namespace CategoryTheory.Iso

open CategoryTheory

variable {X Y : TypeCat.{u}}

/-- Any isomorphism between types gives an equivalence. -/
def toEquiv (i : X ≅ Y) : X ≃ Y where
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv y := by simp

@[simp]
theorem toEquiv_fun (i : X ≅ Y) : (i.toEquiv : X → Y) = i.hom :=
  rfl

theorem toEquiv_fun_apply (i : X ≅ Y) (x : X) : i.toEquiv x = i.hom x :=
  rfl

@[simp]
theorem toEquiv_symm_fun (i : X ≅ Y) : (i.toEquiv.symm :) = (ConcreteCategory.hom i.inv).as :=
  rfl

theorem toEquiv_symm_fun_apply (i : X ≅ Y) (y : Y) : i.toEquiv.symm y = i.inv y :=
  rfl

@[simp]
theorem toEquiv_id (X : TypeCat.{u}) : (Iso.refl X).toEquiv = Equiv.refl X :=
  rfl

@[simp]
theorem toEquiv_comp {X Y Z : TypeCat.{u}} (f : X ≅ Y) (g : Y ≅ Z) :
    (f ≪≫ g).toEquiv = f.toEquiv.trans g.toEquiv :=
  rfl

end CategoryTheory.Iso

namespace CategoryTheory

/-- A morphism in `Type u` is an isomorphism if and only if it is bijective. -/
theorem isIso_iff_bijective {X Y : TypeCat.{u}} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f :=
  Iff.intro (fun _ => (asIso f : X ≅ Y).toEquiv.bijective) fun b =>
    (Equiv.ofBijective f b).toIso.isIso_hom

theorem bijective_iff_isIso_ofHom {X Y : Type u} (f : X → Y) :
    Function.Bijective f ↔ IsIso (ofHom ⟨f⟩) :=
  Iff.intro (fun b => (Equiv.ofBijective f b).toIso.isIso_hom)
    fun _ => (asIso (ofHom ⟨f⟩) : of X ≅ of Y).toEquiv.bijective

instance : SplitEpiCategory TypeCat.{u} where
  isSplitEpi_of_epi f hf :=
    IsSplitEpi.mk' <|
      { section_ := ofHom <| ⟨Function.surjInv <| (epi_iff_surjective f).1 hf⟩
        id := by
          ext x
          exact (Function.rightInverse_surjInv <| (epi_iff_surjective f).1 hf) x }

theorem isSplitEpi_iff_surjective {X Y : TypeCat.{u}} (f : X ⟶ Y) :
    IsSplitEpi f ↔ Function.Surjective f :=
  Iff.intro (fun _ => surjective_of_epi _)
    fun hf => (by simp only [(epi_iff_surjective f).mpr hf, isSplitEpi_of_epi])

-- unif_hint Functor.comp_obj_types {J J' : Type*} [Category* J] [Category* J']
--     (G G' : J' ⥤ J) (F F' : J ⥤ TypeCat.{u}) (j j' : J') where
--   G ≟ G'
--   F ≟ F'
--   j ≟ j'
--   ⊢ (G ⋙ F).obj j ≟ F'.obj (G'.obj j')

end CategoryTheory

-- We prove `equivIsoIso` and then use that to sneakily construct `equivEquivIso`.
-- (In this order the proofs are handled by `cat_disch`.)
/-- Equivalences (between types in the same universe) are the same as (isomorphic to) isomorphisms
of types. -/
@[simps]
def equivIsoIso {X Y : TypeCat.{u}} : of (X ≃ Y) ≅ of (X ≅ Y) where
  hom := ofHom ⟨fun e ↦ e.toIso⟩
  inv := ofHom ⟨fun i ↦ i.toEquiv⟩

/-- Equivalences (between types in the same universe) are the same as (equivalent to) isomorphisms
of types. -/
def equivEquivIso {X Y : Type u} : X ≃ Y ≃ (of X ≅ of Y) :=
  equivIsoIso.toEquiv

@[simp]
theorem equivEquivIso_hom {X Y : Type u} (e : X ≃ Y) : equivEquivIso e = e.toIso :=
  rfl

@[simp]
theorem equivEquivIso_inv {X Y : TypeCat.{u}} (e : X ≅ Y) : equivEquivIso.symm e = e.toEquiv :=
  rfl
