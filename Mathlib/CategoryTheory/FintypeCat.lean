/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Adam Topaz
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Data.Finite.Prod

/-!
# The category of finite types.

We define the category of finite types, denoted `FintypeCat` as
(bundled) types with a `Fintype` instance.

We also define `FintypeCat.Skeleton`, the standard skeleton of `FintypeCat` whose objects
are `Fin n` for `n : ℕ`. We prove that the obvious inclusion functor
`FintypeCat.Skeleton ⥤ FintypeCat` is an equivalence of categories in
`FintypeCat.Skeleton.equivalence`.
We prove that `FintypeCat.Skeleton` is a skeleton of `FintypeCat` in `FintypeCat.isSkeleton`.
-/

open CategoryTheory

/-- The category of finite types. -/
structure FintypeCat where
  /-- The underlying type. -/
  carrier : Type*
  [str : Fintype carrier]

attribute [instance] FintypeCat.str

namespace FintypeCat

instance instCoeSort : CoeSort FintypeCat Type* :=
  ⟨carrier⟩

/-- Construct a bundled `FintypeCat` from the underlying type and typeclass. -/
abbrev of (X : Type*) [Fintype X] : FintypeCat where
  carrier := X

instance : Inhabited FintypeCat :=
  ⟨of PEmpty⟩

instance {X : FintypeCat} : Fintype X :=
  X.2

instance : Category FintypeCat :=
  inferInstanceAs (Category (InducedCategory _ carrier))

/-- The fully faithful embedding of `FintypeCat` into the category of types. -/
@[simps!]
def incl : FintypeCat ⥤ Type* :=
  inducedFunctor _

instance : incl.Full := InducedCategory.full _
instance : incl.Faithful := InducedCategory.faithful _

instance (X Y : FintypeCat) : FunLike (X ⟶ Y) X Y where
  coe f := f.hom
  coe_injective' _ _ h := InducedCategory.homEquiv.injective h

instance concreteCategoryFintype : ConcreteCategory FintypeCat (· ⟶ ·) where
  hom f := f
  ofHom f := f

/- Help typeclass inference infer fullness of forgetful functor. -/
instance : (forget FintypeCat).Full := inferInstanceAs <| FintypeCat.incl.Full

@[simp]
theorem id_apply (X : FintypeCat) (x : X) : (𝟙 X : X → X) x = x :=
  rfl

@[simp]
theorem comp_apply {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  rfl

-- Isn't `@[simp]` because `simp` can prove it after importing `Mathlib.CategoryTheory.Elementwise`.
lemma hom_inv_id_apply {X Y : FintypeCat} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
  DFunLike.congr_fun f.hom_inv_id x

-- Isn't `@[simp]` because `simp` can prove it after importing `Mathlib.CategoryTheory.Elementwise`.
lemma inv_hom_id_apply {X Y : FintypeCat} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
  DFunLike.congr_fun f.inv_hom_id y

@[ext]
lemma hom_ext {X Y : FintypeCat} (f g : X ⟶ Y) (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Constructor for morphisms in `FintypeCat`. -/
def homMk {X Y : FintypeCat} (f : X → Y) : X ⟶ Y where
  hom := f

@[simp]
lemma homMk_apply {X Y : FintypeCat} (f : X → Y) (x : X) :
    homMk f x = f x := rfl

@[simp]
lemma id_hom (X : FintypeCat) : InducedCategory.Hom.hom (𝟙 X) = id := rfl

@[simp, reassoc]
lemma comp_hom {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom ∘ f.hom := rfl

-- See `equivEquivIso` in the root namespace for the analogue in `Type`.
/-- Equivalences between finite types are the same as isomorphisms in `FintypeCat`. -/
@[simps]
def equivEquivIso {A B : FintypeCat} : A ≃ B ≃ (A ≅ B) where
  toFun e :=
    { hom := homMk e
      inv := homMk e.symm }
  invFun i :=
    { toFun := i.hom
      invFun := i.inv
      left_inv := ConcreteCategory.congr_hom i.hom_inv_id
      right_inv := ConcreteCategory.congr_hom i.inv_hom_id }
  left_inv := by cat_disch
  right_inv := by cat_disch

instance (X Y : FintypeCat) : Finite (X ⟶ Y) :=
  Finite.of_equiv _ (show (X ⟶ Y) ≃ (X → Y) from InducedCategory.homEquiv).symm

instance (X Y : FintypeCat) : Finite (X ≅ Y) :=
  Finite.of_injective _ (fun _ _ h ↦ Iso.ext h)

instance (X : FintypeCat) : Finite (Aut X) :=
  inferInstanceAs <| Finite (X ≅ X)

universe u

/--
The "standard" skeleton for `FintypeCat`. This is the full subcategory of `FintypeCat`
spanned by objects of the form `ULift (Fin n)` for `n : ℕ`. We parameterize the objects
of `Fintype.Skeleton` directly as `ULift ℕ`, as the type `ULift (Fin m) ≃ ULift (Fin n)`
is nonempty if and only if `n = m`. Specifying universes, `Skeleton : Type u` is a small
skeletal category equivalent to `Fintype.{u}`.
-/
def Skeleton : Type u :=
  ULift ℕ

namespace Skeleton

/-- Given any natural number `n`, this creates the associated object of `Fintype.Skeleton`. -/
def mk : ℕ → Skeleton :=
  ULift.up

instance : Inhabited Skeleton :=
  ⟨mk 0⟩

/-- Given any object of `Fintype.Skeleton`, this returns the associated natural number. -/
def len : Skeleton → ℕ :=
  ULift.down

@[ext]
theorem ext (X Y : Skeleton) : X.len = Y.len → X = Y :=
  ULift.ext _ _

instance : SmallCategory Skeleton.{u} where
  Hom X Y := ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)
  id _ := id
  comp f g := g ∘ f

theorem is_skeletal : Skeletal Skeleton.{u} := fun X Y ⟨h⟩ =>
  ext _ _ <|
    Fin.equiv_iff_eq.mp <|
      Nonempty.intro <|
        { toFun := fun x => (h.hom ⟨x⟩).down
          invFun := fun x => (h.inv ⟨x⟩).down
          left_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.hom ≫ h.inv) _).down = _
            simp
            rfl
          right_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.inv ≫ h.hom) _).down = _
            simp
            rfl }

/-- The canonical fully faithful embedding of `Fintype.Skeleton` into `FintypeCat`. -/
def incl : Skeleton.{u} ⥤ FintypeCat.{u} where
  obj X := FintypeCat.of (ULift (Fin X.len))
  map f := homMk f

instance : incl.Full where map_surjective f := ⟨f.hom, rfl⟩

instance : incl.Faithful where
  map_injective h := InducedCategory.homEquiv.symm.injective h

instance : incl.EssSurj :=
  Functor.EssSurj.mk fun X =>
    let F := Fintype.equivFin X
    ⟨mk (Fintype.card X),
      Nonempty.intro
        { hom := homMk (F.symm ∘ ULift.down)
          inv := homMk (ULift.up ∘ F) }⟩

noncomputable instance : incl.IsEquivalence where

/-- The equivalence between `Fintype.Skeleton` and `Fintype`. -/
noncomputable def equivalence : Skeleton ≌ FintypeCat :=
  incl.asEquivalence

@[simp]
theorem incl_mk_nat_card (n : ℕ) : Fintype.card (incl.obj (mk n)) = n := by
  convert Finset.card_fin n
  apply Fintype.ofEquiv_card

end Skeleton

/-- `Fintype.Skeleton` is a skeleton of `Fintype`. -/
lemma isSkeleton : IsSkeletonOf FintypeCat Skeleton Skeleton.incl where
  skel := Skeleton.is_skeletal
  eqv := by infer_instance

section Universes

universe v

/-- If `u` and `v` are two arbitrary universes, we may construct a functor
`uSwitch.{u, v} : FintypeCat.{u} ⥤ FintypeCat.{v}` by sending
`X : FintypeCat.{u}` to `ULift.{v} (Fin (Fintype.card X))`. -/
noncomputable def uSwitch : FintypeCat.{u} ⥤ FintypeCat.{v} where
  obj X := FintypeCat.of <| ULift.{v} (Fin (Fintype.card X))
  map {X Y} f :=
    homMk (ULift.up ∘ Fintype.equivFin Y ∘ f.hom ∘ (Fintype.equivFin X).symm ∘ ULift.down)
  map_id X := by
    ext x
    rw [homMk_apply]
    simp
  map_comp f g := by
    ext x
    simp only [comp_hom, ConcreteCategory.comp_apply]
    rw [homMk_apply, homMk_apply, homMk_apply]
    simp

/-- Switching the universe of an object `X : FintypeCat.{u}` does not change `X` up to equivalence
of types. This is natural in the sense that it commutes with `uSwitch.map f` for
any `f : X ⟶ Y` in `FintypeCat.{u}`. -/
noncomputable def uSwitchEquiv (X : FintypeCat.{u}) :
    uSwitch.{u, v}.obj X ≃ X :=
  Equiv.ulift.trans (Fintype.equivFin X).symm

lemma uSwitchEquiv_naturality {X Y : FintypeCat.{u}} (f : X ⟶ Y)
    (x : uSwitch.{u, v}.obj X) :
    f (X.uSwitchEquiv x) = Y.uSwitchEquiv (uSwitch.map f x) := by
  simp only [uSwitch, uSwitchEquiv, Equiv.trans_apply, Equiv.ulift_apply]
  rw [homMk_apply]
  aesop

lemma uSwitchEquiv_symm_naturality {X Y : FintypeCat.{u}} (f : X ⟶ Y) (x : X) :
    uSwitch.map f (X.uSwitchEquiv.symm x) = Y.uSwitchEquiv.symm (f x) := by
  rw [← Equiv.apply_eq_iff_eq_symm_apply, ← uSwitchEquiv_naturality f,
    Equiv.apply_symm_apply]

lemma uSwitch_map_uSwitch_map {X Y : FintypeCat.{u}} (f : X ⟶ Y) :
    uSwitch.map (uSwitch.map f) =
    (equivEquivIso ((uSwitch.obj X).uSwitchEquiv.trans X.uSwitchEquiv)).hom ≫
      f ≫ (equivEquivIso ((uSwitch.obj Y).uSwitchEquiv.trans
      Y.uSwitchEquiv)).inv := rfl

attribute [local simp] uSwitch_map_uSwitch_map in
/-- `uSwitch.{u, v}` is an equivalence of categories with quasi-inverse `uSwitch.{v, u}`. -/
noncomputable def uSwitchEquivalence : FintypeCat.{u} ≌ FintypeCat.{v} where
  functor := uSwitch
  inverse := uSwitch
  unitIso := NatIso.ofComponents (fun X ↦ (equivEquivIso <|
    (uSwitch.obj X).uSwitchEquiv.trans X.uSwitchEquiv).symm)
  counitIso := NatIso.ofComponents (fun X ↦ equivEquivIso <|
    (uSwitch.obj X).uSwitchEquiv.trans X.uSwitchEquiv)
  functor_unitIso_comp X := by
    ext x
    simp [← uSwitchEquiv_naturality]

instance : uSwitch.IsEquivalence :=
  uSwitchEquivalence.isEquivalence_functor

end Universes

end FintypeCat

namespace FunctorToFintypeCat

universe u v w

variable {C : Type u} [Category.{v} C] (F G : C ⥤ FintypeCat.{w}) {X Y : C}

lemma naturality (σ : F ⟶ G) (f : X ⟶ Y) (x : F.obj X) :
    σ.app Y (F.map f x) = G.map f (σ.app X x) :=
  DFunLike.congr_fun (σ.naturality f) x

end FunctorToFintypeCat
