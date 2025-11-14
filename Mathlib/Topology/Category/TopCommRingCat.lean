/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Category of topological commutative rings

We introduce the category `TopCommRingCat` of topological commutative rings together with the
relevant forgetful functors to topological spaces and commutative rings.
-/


universe u

open CategoryTheory Limits

@[ext]
structure ContinuousRingHom (A B : Type*)
    [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [Ring B] [TopologicalSpace B] [IsTopologicalRing B] extends A →+* B, C(A, B)

infixr:25 " →ₜ+* " => ContinuousRingHom

section ContinuousRingHom

variable {A B C : Type*}
    [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [Ring B] [TopologicalSpace B] [IsTopologicalRing B]
    [Ring C] [TopologicalSpace C] [IsTopologicalRing C]

instance : FunLike (A →ₜ+* B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨ ⟨ _ , _ ⟩ , _ ⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨ _ , _ ⟩, _⟩, _⟩ := g
    congr

instance : RingHomClass (A →ₜ+* B) A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

instance TopCommRingCat.instContinuousMapClass : ContinuousMapClass (A →ₜ+* B) A B where
  map_continuous f := f.continuous_toFun

def ContinuousRingHom.id (A : Type*) [Ring A] [TopologicalSpace A] [IsTopologicalRing A] :
    A →ₜ+* A := ⟨.id _, by fun_prop⟩

def ContinuousRingHom.comp {A B C : Type*}
    [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [Ring B] [TopologicalSpace B] [IsTopologicalRing B]
    [Ring C] [TopologicalSpace C] [IsTopologicalRing C]
    (f : B →ₜ+* C) (g : A →ₜ+* B) : A →ₜ+* C :=
    ⟨f.toRingHom.comp g.toRingHom, (map_continuous f).comp (map_continuous g)⟩

end ContinuousRingHom

structure TopCommRingCat where
  private mk ::
  carrier : Type u
  [commRing : CommRing carrier]
  [top : TopologicalSpace carrier]
  [topRing : IsTopologicalRing carrier]

attribute [instance] TopCommRingCat.commRing TopCommRingCat.top TopCommRingCat.topRing

initialize_simps_projections TopCommRingCat (-commRing, -top, -topRing)

namespace TopCommRingCat

instance : CoeSort (TopCommRingCat) (Type u) :=
  ⟨TopCommRingCat.carrier⟩

attribute [coe] TopCommRingCat.carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `CommRingCat`. -/
abbrev of (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] : TopCommRingCat :=
  ⟨R⟩

lemma coe_of (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    (of R : Type u) = R :=
  rfl

lemma of_carrier (R : TopCommRingCat.{u}) : of R = R := rfl

variable {R} in
@[ext]
structure Hom (R S : TopCommRingCat.{u}) where
  private mk ::
  hom' : R →ₜ+* S

instance : Category TopCommRingCat where
  Hom R S := Hom R S
  id R := ⟨ContinuousRingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory.{u} TopCommRingCat (fun R S => R →ₜ+* S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

abbrev Hom.hom {R S : TopCommRingCat.{u}} (f : Hom R S) :=
  ConcreteCategory.hom (C := TopCommRingCat) f

abbrev ofHom {R S : Type u}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (f : R →ₜ+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom (C := TopCommRingCat) f

def Hom.Simps.hom (R S : TopCommRingCat) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

def uniformSpace (R : TopCommRingCat) : UniformSpace R := by
  exact IsTopologicalAddGroup.toUniformSpace _

instance : HasForget₂ TopCommRingCat CommRingCat where
  forget₂ := {
    obj X := CommRingCat.of X
    map f := CommRingCat.ofHom f.hom }

instance : HasForget₂ TopCommRingCat TopCat where
  forget₂ := {
    obj X := TopCat.of X
    map f := TopCat.ofHom f.hom }

section Limits

open Limits

universe v t w

instance : HasProducts.{u} TopCommRingCat.{u} := by
  refine hasProducts_of_limit_fans (fun {J} f ↦ Fan.mk
      (TopCommRingCat.of.{u} (∀ j, f j))
      (fun b ↦ ofHom ⟨Pi.evalRingHom _ b, (ContinuousMap.eval b).continuous_toFun⟩))
    (fun {J} f ↦ {
      lift c := ⟨Pi.ringHom fun b ↦ (ConcreteCategory.hom (c.π.app ⟨b⟩)).toRingHom, by
        apply continuous_pi
        intro b
        exact (ConcreteCategory.hom (c.π.app ⟨b⟩)).continuous_toFun⟩
      fac s _ := by rfl
      uniq s m h := by
        apply ConcreteCategory.hom_ext
        intro x
        apply funext
        intro y
        specialize h ⟨y⟩
        rw [ConcreteCategory.hom_ext_iff] at h
        exact h x })

def equalizerFork {X Y : TopCommRingCat.{u}} (f g : X ⟶ Y) : Fork f g :=
  Fork.ofι (TopCommRingCat.ofHom ⟨(RingHom.eqLocus f.hom.toRingHom g.hom.toRingHom).subtype,
    by continuity⟩) <| by
      apply ConcreteCategory.hom_ext
      intro ⟨x, e⟩
      simpa using e

/-- The equalizer in `CommRingCat` is the equalizer as sets. -/
def equalizerForkIsLimit {X Y : TopCommRingCat.{u}} (f g : X ⟶ Y) :
    IsLimit (equalizerFork f g) := by
  fapply Fork.IsLimit.mk'
  intro s
  use ofHom <| ⟨s.ι.hom.toRingHom.codRestrict _
    fun x => (ConcreteCategory.congr_hom s.condition x :), by
      simp only [RingHom.codRestrict, Functor.const_obj_obj, parallelPair_obj_zero,
        RingHom.toMonoidHom_eq_coe, RingHom.coe_monoidHom_mk, OneHom.toFun_eq_coe, OneHom.coe_mk]
      apply Continuous.codRestrict
      exact ContinuousRingHom.continuous_toFun _⟩
  constructor
  · ext
    rfl
  · intro m hm
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    have := congrArg Hom.hom hm
    apply_fun ContinuousRingHom.toRingHom at this
    exact RingHom.congr_fun this x

instance {X Y : TopCommRingCat.{u}} (f g : X ⟶ Y) : HasLimit (parallelPair f g) :=
  ⟨⟨equalizerFork f g, equalizerForkIsLimit f g⟩⟩

instance : HasEqualizers TopCommRingCat := by
  apply hasEqualizers_of_hasLimit_parallelPair

instance : HasLimits TopCommRingCat := has_limits_of_hasEqualizers_and_products

end Limits

instance forgetToTopCatCommRing (R : TopCommRingCat) :
    CommRing ((forget₂ TopCommRingCat TopCat).obj R) :=
  inferInstanceAs (CommRing R)

instance forgetToTopCatTopologicalRing (R : TopCommRingCat) :
    IsTopologicalRing ((forget₂ TopCommRingCat TopCat).obj R) :=
  inferInstanceAs (IsTopologicalRing R)

/-- The forgetful functors to `Type` do not reflect isomorphisms,
but the forgetful functor from `TopCommRingCat` to `TopCat` does.
-/
instance : (forget₂ TopCommRingCat.{u} TopCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    -- We have an isomorphism in `TopCat`,
    let i_Top := asIso ((forget₂ TopCommRingCat TopCat).map f)
    -- and a `RingEquiv`.
    let e_Ring : X ≃+* Y := { f.1, ((forget TopCat).mapIso i_Top).toEquiv with }
    -- Putting these together we obtain the isomorphism we're after:
    exact
      ⟨⟨⟨e_Ring.symm, i_Top.inv.hom.2⟩,
          ⟨by
            apply ConcreteCategory.ext
            ext x
            exact e_Ring.left_inv x, by
            ext x
            exact e_Ring.right_inv x⟩⟩⟩

end TopCommRingCat

section TopAlgCat

structure TopAlgCat (R : Type u) [CommRing R] where
  private mk ::
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]
  [top : TopologicalSpace carrier]
  [topRing : IsTopologicalRing carrier]

attribute [instance] TopAlgCat.commRing TopAlgCat.top TopAlgCat.topRing TopAlgCat.algebra

initialize_simps_projections TopAlgCat (-commRing, -algebra, -top, -topRing)

namespace TopAlgCat

variable (A : Type u) [CommRing A]

instance : CoeSort (TopAlgCat A) (Type u) :=
  ⟨TopAlgCat.carrier⟩

attribute [coe] TopCommRingCat.carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `CommRingCat`. -/
abbrev of (R : Type u) [CommRing R] [Algebra A R] [TopologicalSpace R] [IsTopologicalRing R] :
    TopAlgCat A :=
  ⟨R⟩

lemma coe_of (R : Type u) [CommRing R] [Algebra A R] [TopologicalSpace R] [IsTopologicalRing R] :
    (of A R : Type u) = R :=
  rfl

lemma of_carrier (R : TopAlgCat.{u} A) : of A R = R := rfl

variable {A} in
@[ext]
structure Hom (R S : TopAlgCat.{u} A) where
  private mk ::
  hom' : R →A[A] S

instance : Category (TopAlgCat A) where
  Hom R S := Hom R S
  id R := ⟨ContinuousAlgHom.id A R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory.{u} (TopAlgCat A) (fun R S => R →A[A] S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

abbrev Hom.hom {R S : TopAlgCat.{u} A} (f : Hom R S) :=
  ConcreteCategory.hom (C := TopAlgCat A) f

abbrev ofHom {R S : Type u}
    [CommRing R] [Algebra A R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [Algebra A S] [TopologicalSpace S] [IsTopologicalRing S] (f : R →A[A] S) :
    of A R ⟶ of A S :=
  ConcreteCategory.ofHom (C := TopAlgCat A) f

def Hom.Simps.hom (R S : TopAlgCat A) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

open Limits

instance : HasForget₂ (TopAlgCat A) TopCommRingCat where
  forget₂ := {
    obj X := TopCommRingCat.of X
    map f := TopCommRingCat.ofHom ⟨f.hom.toRingHom, f.hom.cont⟩ }

end TopAlgCat

end TopAlgCat
