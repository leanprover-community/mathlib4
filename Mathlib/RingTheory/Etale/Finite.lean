/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.CategoryTheory.FintypeCat

/-!
# Category of finite étale `R`-algebras

In this file we define the category of finite étale `R`-algebras over a ring `R`. For any
geometric point `Ω` of `R`, we define a fiber functor sending a finite étale `R`-algebra
`S` to the finite set of `R`-algebra homomorphisms `S →ₐ[R] Ω`.

## Main definitions

- `CommAlgCat.FiniteEtale`: The category of finite étale `R`-algebras.
- `CommAlgCat.FiniteEtale.fiber`: For a geometric point `Ω` of `R`, the fiber functor
  `S ↦ (S →ₐ[R] Ω)`.

## Main results

- `CommAlgCat.FiniteEtale.equivOfIsSepClosed`: If `R = Ω` is separably closed,
  the category of finite étale `Ω`-algebras is anti-equivalent to `FintypeCat`.
  In particular, the functor `CommAlgCat.FiniteEtale.fiber` is an equivalence
  of categories in this case.
-/

public section

open CategoryTheory TensorProduct

universe v w u

namespace CommAlgCat

variable (R : Type u) [CommRing R] (k : Type u) [Field k]

section

/-- The object property of finite `R`-algebras. -/
abbrev finite : ObjectProperty (CommAlgCat.{v} R) :=
  fun S ↦ Module.Finite R S

/-- The object property of étale `R`-algebras. -/
abbrev etale : ObjectProperty (CommAlgCat.{v} R) :=
  fun S ↦ Algebra.Etale R S

/-- The object property of finite étale `R`-algebras. -/
abbrev finiteEtale : ObjectProperty (CommAlgCat.{v} R) :=
  finite R ⊓ etale R

/-- The category of finite étale `R`-algebras. -/
abbrev FiniteEtale (R : Type u) [CommRing R] : Type _ :=
  (finiteEtale.{v} R).FullSubcategory

instance : CoeSort (FiniteEtale.{v} R) (Type v) := ⟨fun R ↦ R.obj⟩

instance (S : FiniteEtale.{v} R) : Algebra.Etale R S :=
  S.property.right

instance (S : FiniteEtale.{v} R) : Module.Finite R S :=
  S.property.left

/-- Construct a term of `FiniteEtale R` from a finite étale `R`-algebra. -/
@[simps obj]
abbrev FiniteEtale.of (S : Type v) [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.Etale R S] :
    FiniteEtale.{v} R where
  obj := .of R S
  property := ⟨‹_›, ‹_›⟩

variable {R}

/-- Construct a morphism in `FiniteEtale R` from an algebra map. -/
@[simps]
abbrev FiniteEtale.ofHom {S T : Type v} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.Finite R S] [Algebra.Etale R S] [Module.Finite R T]
    [Algebra.Etale R T] (f : S →ₐ[R] T) :
    FiniteEtale.of R S ⟶ FiniteEtale.of R T where
  hom := CommAlgCat.ofHom f

/-- Construct an isomorphism in `FiniteEtale R` from an algebra equivalence. -/
@[simps!]
abbrev FiniteEtale.isoMk {S T : FiniteEtale R} (e : S.obj ≃ₐ[R] T.obj) :
    S ≅ T :=
  ObjectProperty.isoMk _ (CommAlgCat.isoMk e)

end

instance (R : FiniteEtale k) : IsArtinianRing R :=
  have := Algebra.FormallyUnramified.finite_of_free k R
  isArtinian_of_tower k inferInstance

variable (Ω : Type w) [Field Ω] [Algebra R Ω]
  (S : Type w) [CommRing S] [Algebra R S] [Algebra S Ω] [IsScalarTower R S Ω]

/-- If `S` is an `R`-algebra, this is the base change functor `A ↦ S ⊗[R] A`. -/
@[expose, simps]
def FiniteEtale.baseChange : FiniteEtale.{v} R ⥤ FiniteEtale.{max w v} S where
  obj A := .of S (S ⊗[R] A)
  map {A B} f := FiniteEtale.ofHom (Algebra.TensorProduct.map (.id _ _) f.hom.hom)

/-- Base change from `R` to `R` is isomorphic to the identity. -/
@[expose, simps!]
def FiniteEtale.baseChangeSelfIso : baseChange R R ≅ 𝟭 (FiniteEtale R) :=
  NatIso.ofComponents (fun A ↦ isoMk (Algebra.TensorProduct.lid _ _)) <| fun {A B} f ↦ by
    dsimp [baseChange]
    ext
    simp

/-- The fiber functor for finite étale `R`-algebras at the geometric point `Ω`: This is the
functor sending `S` to `R`-algebra homomorphisms `S →ₐ[R] Ω`. -/
@[expose, simps]
def FiniteEtale.fiber (R : Type u) [CommRing R] (Ω : Type w) [Field Ω] [Algebra R Ω] :
    (FiniteEtale.{v} R)ᵒᵖ ⥤ FintypeCat.{max v w} where
  obj S := .of (S.unop →ₐ[R] Ω)
  map {S T} f := FintypeCat.homMk (·.comp f.unop.hom.hom)

/-- If `k` is a field, this is the `Spec` functor sending a finite étale `k`-algebra `R`
to its finite prime spectrum. -/
@[expose, simps]
def FiniteEtale.finiteSpec (k : Type u) [Field k] : (FiniteEtale.{v} k)ᵒᵖ ⥤ FintypeCat.{v} where
  obj R := .of (PrimeSpectrum R.unop.obj)
  map f := FintypeCat.homMk (PrimeSpectrum.comap f.unop.hom.hom)

/-- If the geometric point `Ω` factors through `S`, the fiber can be computed after base change
to `S`. -/
@[expose, simps!]
def FiniteEtale.fiberIsoBaseChangeFiber :
    FiniteEtale.fiber.{v} R Ω ≅
      (FiniteEtale.baseChange.{v} R S).op ⋙ FiniteEtale.fiber S Ω :=
  NatIso.ofComponents
    (fun A ↦ FintypeCat.equivEquivIso (Algebra.TensorProduct.liftEquivRight _ _ _ _))

/-- If `Ω` is separably closed, the fiber functor for finite étale `Ω`-algebras
is naturally isomorphic to the (finite) `Spec` functor. -/
@[expose, simps!]
noncomputable
def FiniteEtale.fiberIsoFiniteSpec [IsSepClosed Ω] :
    FiniteEtale.fiber Ω Ω ≅ FiniteEtale.finiteSpec Ω :=
  NatIso.ofComponents
    (fun R ↦ FintypeCat.equivEquivIso (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum _ _))

/-- If `Ω` is separably closed, the fiber `S →ₐ[R] Ω`
is isomorphic to the prime spectrum of the base change `Ω ⊗[R] S`. -/
@[expose, simps!]
noncomputable
def FiniteEtale.fiberIsoComp [IsSepClosed Ω] :
    FiniteEtale.fiber.{v} R Ω ≅
      (FiniteEtale.baseChange.{v} R Ω).op ⋙ FiniteEtale.finiteSpec.{max w v} Ω :=
  fiberIsoBaseChangeFiber _ _ Ω ≪≫ Functor.isoWhiskerLeft _ (fiberIsoFiniteSpec _)

set_option backward.isDefEq.respectTransparency false in
/-- If `Ω` is a separably closed field, the category of finite étale `Ω`-algebras is
anti-equivalent to `FintypeCat`. -/
@[expose, simps! functor inverse_obj inverse_map]
noncomputable def FiniteEtale.equivOfIsSepClosed (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    (FiniteEtale.{u} Ω)ᵒᵖ ≌ FintypeCat.{u} := .symm
  { functor.obj X := .op (.of _ (X → Ω))
    functor.map {X Y} f := .op (FiniteEtale.ofHom <| Pi.algHom _ _ fun i ↦ Pi.evalAlgHom _ _ (f i))
    inverse := FiniteEtale.finiteSpec Ω
    counitIso :=
      NatIso.ofComponents
        (fun R ↦ (FiniteEtale.isoMk (Algebra.FormallyEtale.equivPiOfIsSepClosed Ω R.unop)).op)
        fun {R S} f ↦ by
          apply Quiver.Hom.unop_inj
          ext x
          exact funext fun p ↦ Algebra.FormallyEtale.equivPiOfIsSepClosed_comap _ _ _
    unitIso := NatIso.ofComponents
      fun X ↦ FintypeCat.equivEquivIso <|
        (Equiv.sigmaUnique _ _).symm.trans (PrimeSpectrum.sigmaToPiHomeo _).toEquiv
    functor_unitIso_comp X := by
      dsimp [FiniteEtale.finiteSpec]
      apply Quiver.Hom.unop_inj
      ext x i
      dsimp
      rw [FintypeCat.equivEquivIso_apply_hom, FintypeCat.homMk_apply]
      dsimp
      rw [← Pi.coe_evalAlgHom Ω]
      simp [Algebra.FormallyEtale.equivPiOfIsSepClosed_comap,
        Algebra.FormallyEtale.equivPiOfIsSepClosed_self_apply] }

instance (Ω : Type u) [Field Ω] [IsSepClosed Ω] : (FiniteEtale.finiteSpec.{u} Ω).IsEquivalence :=
  (FiniteEtale.equivOfIsSepClosed.{u} Ω).isEquivalence_functor

instance (Ω : Type u) [Field Ω] [IsSepClosed Ω] : (FiniteEtale.fiber.{u} Ω Ω).IsEquivalence :=
  Functor.isEquivalence_of_iso (FiniteEtale.fiberIsoFiniteSpec _).symm

end CommAlgCat
