/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Adam Topaz
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Data.Finite.Basic

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


open scoped Classical

open CategoryTheory

/-- The category of finite types. -/
def FintypeCat :=
  Bundled Fintype

namespace FintypeCat

instance : CoeSort FintypeCat Type* :=
  Bundled.coeSort

/-- Construct a bundled `FintypeCat` from the underlying type and typeclass. -/
def of (X : Type*) [Fintype X] : FintypeCat :=
  Bundled.of X

instance : Inhabited FintypeCat :=
  ⟨of PEmpty⟩

instance {X : FintypeCat} : Fintype X :=
  X.2

instance : Category FintypeCat :=
  InducedCategory.category Bundled.α

/-- The fully faithful embedding of `FintypeCat` into the category of types. -/
@[simps!]
def incl : FintypeCat ⥤ Type* :=
  inducedFunctor _

instance : incl.Full := InducedCategory.full _
instance : incl.Faithful := InducedCategory.faithful _

instance concreteCategoryFintype : ConcreteCategory FintypeCat :=
  ⟨incl⟩

/- Help typeclass inference infer fullness of forgetful functor. -/
instance : (forget FintypeCat).Full := inferInstanceAs <| FintypeCat.incl.Full

@[simp]
theorem id_apply (X : FintypeCat) (x : X) : (𝟙 X : X → X) x = x :=
  rfl

@[simp]
theorem comp_apply {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  rfl

@[simp]
lemma hom_inv_id_apply {X Y : FintypeCat} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
  congr_fun f.hom_inv_id x

@[simp]
lemma inv_hom_id_apply {X Y : FintypeCat} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
  congr_fun f.inv_hom_id y

-- Porting note (#10688): added to ease automation
@[ext]
lemma hom_ext {X Y : FintypeCat} (f g : X ⟶ Y) (h : ∀ x, f x = g x) : f = g := by
  funext
  apply h

-- See `equivEquivIso` in the root namespace for the analogue in `Type`.
/-- Equivalences between finite types are the same as isomorphisms in `FintypeCat`. -/
@[simps]
def equivEquivIso {A B : FintypeCat} : A ≃ B ≃ (A ≅ B) where
  toFun e :=
    { hom := e
      inv := e.symm }
  invFun i :=
    { toFun := i.hom
      invFun := i.inv
      left_inv := congr_fun i.hom_inv_id
      right_inv := congr_fun i.inv_hom_id }
  left_inv := by aesop_cat
  right_inv := by aesop_cat

instance (X Y : FintypeCat) : Finite (X ⟶ Y) :=
  inferInstanceAs <| Finite (X → Y)

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
  map f := f

instance : incl.Full where map_surjective f := ⟨f, rfl⟩

instance : incl.Faithful where

instance : incl.EssSurj :=
  Functor.EssSurj.mk fun X =>
    let F := Fintype.equivFin X
    ⟨mk (Fintype.card X),
      Nonempty.intro
        { hom := F.symm ∘ ULift.down
          inv := ULift.up ∘ F }⟩

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
`switchUniverse.{u, v} : FintypeCat.{u} ⥤ FintypeCat.{v}` by sending
`X : FintypeCat.{u}` to `ULift.{v} (Fin (Fintype.card X))`. -/
noncomputable def switchUniverse : FintypeCat.{u} ⥤ FintypeCat.{v} where
  obj X := FintypeCat.of <| ULift.{v} (Fin (Fintype.card X))
  map {X Y} f x := ULift.up <| (Fintype.equivFin Y) (f ((Fintype.equivFin X).symm x.down))
  map_comp {X Y Z} f g := by ext; simp

/-- Switching the universe of an object `X : FintypeCat.{u}` does not change `X` up to equivalence
of types. This is natural in the sense that it commutes with `switchUniverse.map f` for
any `f : X ⟶ Y` in `FintypeCat.{u}`. -/
noncomputable def switchUniverseEquiv (X : FintypeCat.{u}) :
    switchUniverse.{u, v}.obj X ≃ X :=
  Equiv.ulift.trans (Fintype.equivFin X).symm

lemma switchUniverseEquiv_naturality {X Y : FintypeCat.{u}} (f : X ⟶ Y)
    (x : switchUniverse.{u, v}.obj X) :
    f (X.switchUniverseEquiv x) = Y.switchUniverseEquiv (switchUniverse.map f x) := by
  simp only [switchUniverse, switchUniverseEquiv, Equiv.trans_apply]
  erw [Equiv.ulift_apply, Equiv.ulift_apply]
  simp only [Equiv.symm_apply_apply]

lemma switchUniverseEquiv_symm_naturality {X Y : FintypeCat.{u}} (f : X ⟶ Y) (x : X) :
    switchUniverse.map f (X.switchUniverseEquiv.symm x) = Y.switchUniverseEquiv.symm (f x) := by
  rw [← Equiv.apply_eq_iff_eq_symm_apply, ← switchUniverseEquiv_naturality f,
    Equiv.apply_symm_apply]

lemma switchUniverse_map_switchUniverse_map {X Y : FintypeCat.{u}} (f : X ⟶ Y) :
    switchUniverse.map (switchUniverse.map f) =
    (equivEquivIso ((switchUniverse.obj X).switchUniverseEquiv.trans X.switchUniverseEquiv)).hom ≫
      f ≫ (equivEquivIso ((switchUniverse.obj Y).switchUniverseEquiv.trans
      Y.switchUniverseEquiv)).inv := by
  ext x
  simp only [comp_apply, equivEquivIso_apply_hom, Equiv.trans_apply]
  rw [switchUniverseEquiv_naturality f, ← switchUniverseEquiv_naturality]
  rfl

/-- `switchUniverse.{u, v}` is an equivalence of categories with quasi-inverse
`switchUniverse.{v, u}`. -/
noncomputable def switchUniverseEquivalence : FintypeCat.{u} ≌ FintypeCat.{v} where
  functor := switchUniverse
  inverse := switchUniverse
  unitIso := NatIso.ofComponents (fun X ↦ (equivEquivIso <|
    (switchUniverse.obj X).switchUniverseEquiv.trans X.switchUniverseEquiv).symm) <| by
    simp [switchUniverse_map_switchUniverse_map]
  counitIso := NatIso.ofComponents (fun X ↦ equivEquivIso <|
    (switchUniverse.obj X).switchUniverseEquiv.trans X.switchUniverseEquiv) <| by
    simp [switchUniverse_map_switchUniverse_map]
  functor_unitIso_comp X := by
    ext x
    simp [← switchUniverseEquiv_naturality]

instance : switchUniverse.IsEquivalence :=
  switchUniverseEquivalence.isEquivalence_functor

end Universes

end FintypeCat

namespace FunctorToFintypeCat

universe u v w

variable {C : Type u} [Category.{v} C] (F G : C ⥤ FintypeCat.{w}) {X Y : C}

lemma naturality (σ : F ⟶ G) (f : X ⟶ Y) (x : F.obj X) :
    σ.app Y (F.map f x) = G.map f (σ.app X x) :=
  congr_fun (σ.naturality f) x

end FunctorToFintypeCat
