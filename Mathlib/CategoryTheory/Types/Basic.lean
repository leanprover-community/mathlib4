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
structure TypeCat where
  private mk ::
  /-- The underlying type -/
  carrier : Type u

namespace TypeCat

instance : CoeSort TypeCat.{u} (Type u) where coe X := X.carrier

attribute [coe] carrier

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object in the category of types associated to a type. -/
abbrev of (X : Type u) : TypeCat.{u} := ⟨X⟩

lemma coe_of (X : Type u) : (of X : Type u) = X :=
  rfl

-- Ensure the roundtrips are reducibly defeq (so tactics like `rw` can see through them).
example (X : Type u) : (of X : Type u) = X := by with_reducible rfl
example (X : TypeCat.{u}) : of X = X := by with_reducible rfl

set_option backward.privateInPublic true in
/-- The type of morphisms in `TypeCat`. -/
@[ext]
structure Hom (X Y : TypeCat.{u}) where
  private mk ::
  /-- The underlying function -/
  hom' : X.carrier → Y.carrier

end TypeCat

open TypeCat CategoryTheory

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive_do_translate] -- Expressions involving this instance can still be additivized.
instance CategoryTheory.types : Category.{u} TypeCat.{u} where
  Hom := Hom
  id X := .mk fun x => x
  comp f g := .mk fun x => g.hom' <| f.hom' x

instance {X Y : TypeCat.{u}} : FunLike (X → Y) X Y where
  coe f := f
  coe_injective' _ _ h := h

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory TypeCat.{u} (· → ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

namespace TypeCat

/-- Turn a morphism in `TypeCat` back into a function. -/
abbrev Hom.hom {X Y : TypeCat.{u}} (f : Hom X Y) : X → Y :=
  ConcreteCategory.hom (C := TypeCat.{u}) f

/-- Typecheck a function as a morphism in `TypeCat`. -/
abbrev ofHom {X Y : Type u} (f : X → Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : TypeCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

example (X : Type u) : CategoryTheory.ToType (of X) = X := by with_reducible rfl
example (X : TypeCat.{u}) : CategoryTheory.ToType X = X.carrier := by with_reducible rfl

/-!
Some results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

lemma hom_id {X : TypeCat.{u}} : ConcreteCategory.hom (𝟙 X : X ⟶ X) = id := rfl

lemma id_apply (X : TypeCat.{u}) (x : X) :
    (𝟙 X : X ⟶ X).hom x = x := rfl

lemma hom_comp {X Y Z : TypeCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : _ → _) = (g : _ → _) ∘ (f : _ → _) := rfl

lemma comp_apply {X Y Z : TypeCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := rfl

@[ext]
lemma hom_ext {X Y : TypeCat.{u}} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

lemma hom_bijective {X Y : TypeCat.{u}} :
    Function.Bijective (Hom.hom : (X ⟶ Y) → (X → Y)) :=
  ConcreteCategory.hom_bijective (C := TypeCat)

/-- Convenience shortcut for `TypeCat.hom_bijective.injective`. -/
lemma hom_injective {X Y : TypeCat.{u}} :
    Function.Injective (Hom.hom : (X ⟶ Y) → (X → Y)) :=
  hom_bijective.injective

/-- Convenience shortcut for `TypeCat.hom_bijective.surjective`. -/
lemma hom_surjective {X Y : TypeCat.{u}} :
    Function.Surjective (Hom.hom : (X ⟶ Y) → (X → Y)) :=
  hom_bijective.surjective

@[simp]
lemma ofHom_apply {X Y : Type u} (f : X → Y) (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply {X Y : TypeCat.{u}} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

lemma hom_inv_apply {X Y : TypeCat.{u}} (e : X ≅ Y) (x : Y) : e.hom (e.inv x) = x := by
  simp

/-- `TypeCat.Hom.hom` bundled as an `Equiv`. -/
def homEquiv {X Y : TypeCat.{u}} : (X ⟶ Y) ≃ (X → Y) where
  toFun := Hom.hom
  invFun := ofHom

end TypeCat

namespace CategoryTheory

-- @[ext] theorem types_ext {α β : TypeCat.{u}} (f g : α ⟶ β) (h : ∀ a : α, f a = g a) : f = g :=
--   ConcreteCategory.hom_ext _ _ h

theorem types_id (X : TypeCat.{u}) : (𝟙 X : _ → _) = id :=
  rfl

theorem types_comp {X Y Z : TypeCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : _ → _) = g ∘ f :=
  rfl

@[simp]
theorem types_id_apply (X : TypeCat.{u}) (x : X) : (𝟙 X : X → X) x = x :=
  rfl

@[simp]
theorem types_comp_apply {X Y Z : TypeCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
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
lemma sections_property {F : J ⥤ TypeCat.{w}} (s : (F.sections : Type _))
    {j j' : J} (f : j ⟶ j') : F.map f (s.val j) = s.val j' :=
  s.property f

lemma sections_ext_iff {F : J ⥤ TypeCat.{w}} {x y : F.sections} : x = y ↔ ∀ j, x.val j = y.val j :=
  Subtype.ext_iff.trans funext_iff

variable (J)

/-- The functor which sends a functor to types to its sections. -/
@[simps]
def sectionsFunctor : (J ⥤ TypeCat.{w}) ⥤ TypeCat.{max u w} where
  obj F := .of F.sections
  map {F G} φ := TypeCat.ofHom fun x ↦ ⟨fun j => φ.app j (x.1 j), fun {j j'} f =>
    by simp [← NatTrans.naturality_apply, x.2 f]⟩

end Functor

namespace FunctorToTypes

variable {C : Type u} [Category.{v} C] (F G H : C ⥤ TypeCat.{w}) {X Y Z : C}
variable (σ : F ⟶ G) (τ : G ⟶ H)

@[deprecated "No replacement" (since := "2026-02-09")]
theorem map_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X) :
    (F.map (f ≫ g)) a = (F.map g) ((F.map f) a) := by simp only [Functor.map_comp,
      CategoryTheory.comp_apply]

@[deprecated "No replacement" (since := "2026-02-09")]
theorem map_id_apply (a : F.obj X) : (F.map (𝟙 X)) a = a := by simp

@[deprecated (since := "2026-02-09")] alias naturality := NatTrans.naturality_apply

@[deprecated "No replacement" (since := "2026-02-09")]
theorem comp (x : F.obj X) : (σ ≫ τ).app X x = τ.app X (σ.app X x) :=
  rfl

@[deprecated "Use `elementwise_of% eqToHom_map_comp` instead" (since := "2026-02-09")]
theorem eqToHom_map_comp_apply (p : X = Y) (q : Y = Z) (x : F.obj X) :
    F.map (eqToHom q) (F.map (eqToHom p) x) = F.map (eqToHom <| p.trans q) x := by
  cat_disch

variable {D : Type u'} [𝒟 : Category.{u'} D] (I J : D ⥤ C) (ρ : I ⟶ J) {W : D}

@[deprecated "No replacement" (since := "2026-02-09")]
theorem hcomp (x : (I ⋙ F).obj W) : (ρ ◫ σ).app W x = (G.map (ρ.app W)) (σ.app (I.obj W) x) :=
  rfl

attribute [elementwise nosimp] Functor.map_hom_inv Functor.map_inv_hom

@[deprecated (since := "2026-02-09")] alias map_inv_map_hom_apply := Functor.map_hom_inv_apply
@[deprecated (since := "2026-02-09")] alias map_hom_map_inv_apply := Functor.map_inv_hom_apply

attribute [elementwise] Iso.hom_inv_id_app Iso.inv_hom_id_app

@[deprecated (since := "2026-02-09")] alias hom_inv_id_app_apply := Iso.hom_inv_id_app_apply
@[deprecated (since := "2026-02-09")] alias inv_hom_id_app_apply := Iso.inv_hom_id_app_apply

-- TODO: spell the assumptions as `{F G : C ⥤ TypeCat.{*}`}
lemma naturality_symm {F : C ⥤ TypeCat.{u}} {G : C ⥤ TypeCat.{u'}} (e : ∀ j, F.obj j ≃ G.obj j)
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
  hom := ofHom fun a ↦ a.1
  inv := ofHom fun a ↦ .up a

/-- The functor embedding `Type u` into `Type (max u v)`.
Write this as `uliftFunctor.{5, 2}` to get `Type 2 ⥤ Type 5`.
-/
@[pp_with_univ, simps]
def uliftFunctor : TypeCat.{u} ⥤ TypeCat.{max u v} where
  obj X := of (ULift.{v} X)
  map {X} {_} f := ofHom fun x : ULift.{v} X => ULift.up (f x.down)

@[deprecated (since := "2026-02-09")] alias uliftFunctor_obj := uliftFunctor_obj_carrier

/-- `uliftFunctor : Type u ⥤ Type max u v` is fully faithful. -/
def fullyFaithfulULiftFunctor : (uliftFunctor.{v, u}).FullyFaithful where
  preimage f := ofHom fun x ↦ (f (ULift.up x)).down

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
def homOfElement {X : TypeCat.{u}} (x : X) : of PUnit ⟶ X := ofHom fun _ => x

theorem homOfElement_eq_iff {X : TypeCat.{u}} (x y : X) : homOfElement x = homOfElement y ↔ x = y :=
  ⟨fun H => ConcreteCategory.congr_hom H PUnit.unit, by simp_all⟩

/-- A morphism in `Type` is a monomorphism if and only if it is injective. -/
@[stacks 003C]
theorem mono_iff_injective {X Y : TypeCat.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := by
  constructor
  · intro H x x' h
    rw [← homOfElement_eq_iff] at h ⊢
    exact (cancel_mono f).mp h
  · exact fun H => ⟨fun g g' h => ConcreteCategory.hom_ext _ _ fun x ↦
      congrFun (H.comp_left (by simp [← hom_comp, h])) x⟩

theorem injective_of_mono {X Y : TypeCat.{u}} (f : X ⟶ Y) [hf : Mono f] : Function.Injective f :=
  (mono_iff_injective f).1 hf

/-- A morphism in `Type` is an epimorphism if and only if it is surjective. -/
@[stacks 003C]
theorem epi_iff_surjective {X Y : TypeCat.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · rintro ⟨H⟩
    refine Function.surjective_of_right_cancellable_Prop fun g₁ g₂ hg => ?_
    rw [← Equiv.ulift.{u}.symm.injective.comp_left.eq_iff]
    suffices ofHom (Equiv.ulift.symm ∘ g₁) = ofHom (Equiv.ulift.symm ∘ g₂) from
      congrArg ConcreteCategory.hom this
    apply H
    apply ConcreteCategory.hom_ext
    intro x
    change (ULift.up ∘ g₁ ∘ f) _ = (ULift.up ∘ g₂ ∘ f) _
    rw [hg]
  · exact fun H => ⟨fun g g' h =>  ConcreteCategory.hom_ext _ _ fun x ↦
      congrFun (H.injective_comp_right (by simp [← hom_comp, h])) x⟩

theorem surjective_of_epi {X Y : TypeCat.{u}} (f : X ⟶ Y) [hf : Epi f] : Function.Surjective f :=
  (epi_iff_surjective f).1 hf

section

/-- `ofTypeFunctor m` converts from Lean's `Type`-based `Category` to `CategoryTheory`. This
allows us to use these functors in category theory. -/
def ofTypeFunctor (m : Type u → Type v) [_root_.Functor m] [LawfulFunctor m] :
    TypeCat.{u} ⥤ TypeCat.{v} where
  obj x := of (m x.carrier)
  map f := ofHom (_root_.Functor.map f.hom)
  map_id := fun α => by ext X; apply id_map
  map_comp f g := by
    ext x
    exact comp_map (f := m) f.hom g.hom x

variable (m : Type u → Type v) [_root_.Functor m] [LawfulFunctor m]

@[simp]
theorem ofTypeFunctor_obj (X : TypeCat.{u}) : (ofTypeFunctor m).obj X = m X.carrier :=
  rfl

@[simp]
theorem ofTypeFunctor_map {α β} (f : α → β) :
    ((ofTypeFunctor m).map (ofHom f)).hom = (_root_.Functor.map f : m α → m β) :=
  rfl

end

end CategoryTheory

-- Isomorphisms in Type and equivalences.
namespace Equiv

variable {X Y : Type u}

/-- Any equivalence between types in the same universe gives
a categorical isomorphism between those types.
-/
def toIso (e : X ≃ Y) : of X ≅ of Y where
  hom := ofHom e.toFun
  inv := ofHom e.invFun
  hom_inv_id := by ext; exact e.left_inv _
  inv_hom_id := by ext; exact e.right_inv _

@[simp]
theorem toIso_hom {e : X ≃ Y} : (e.toIso.hom : _ → _) = e :=
  rfl

@[simp]
theorem toIso_inv {e : X ≃ Y} : (e.toIso.inv : _ → _) = e.symm :=
  rfl

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

@[simp]
theorem toEquiv_symm_fun (i : X ≅ Y) : (i.toEquiv.symm : Y → X) = i.inv :=
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

instance : SplitEpiCategory TypeCat.{u} where
  isSplitEpi_of_epi f hf :=
    IsSplitEpi.mk' <|
      { section_ := ofHom <| Function.surjInv <| (epi_iff_surjective f).1 hf
        id := by
          ext x
          exact (Function.rightInverse_surjInv <| (epi_iff_surjective f).1 hf) x }

theorem isSplitEpi_iff_surjective {X Y : TypeCat.{u}} (f : X ⟶ Y) :
    IsSplitEpi f ↔ Function.Surjective f :=
  Iff.intro (fun _ => surjective_of_epi _)
    fun hf => (by simp only [(epi_iff_surjective f).mpr hf, isSplitEpi_of_epi])

end CategoryTheory

-- We prove `equivIsoIso` and then use that to sneakily construct `equivEquivIso`.
-- (In this order the proofs are handled by `cat_disch`.)
/-- Equivalences (between types in the same universe) are the same as (isomorphic to) isomorphisms
of types. -/
@[simps]
def equivIsoIso {X Y : TypeCat.{u}} : of (X ≃ Y) ≅ of (X ≅ Y) where
  hom := ofHom fun e ↦ e.toIso
  inv := ofHom fun i ↦ i.toEquiv

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
