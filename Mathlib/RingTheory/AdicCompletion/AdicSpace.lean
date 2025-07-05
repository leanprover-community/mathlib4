import Mathlib

universe u

open Topology CategoryTheory TopologicalSpace

structure HuberRing.ringOfDefinition (R₀ : Type u) (R : Type u)
    [CommRing R₀] [TopologicalSpace R₀] [IsTopologicalRing R₀]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] extends Algebra R₀ R where
  emb : IsOpenEmbedding (_root_.algebraMap R₀ R)
  J : Ideal R₀
  fg : J.FG
  adic : IsAdic J

class HuberRing (R : Type u) extends CommRing R, TopologicalSpace R, IsTopologicalRing R where
  pod : ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : TopologicalSpace R₀) (_ : IsTopologicalRing R₀),
    Nonempty (HuberRing.ringOfDefinition R₀ R)

structure IsRingOfIntegralElements (R₀ : Type u) (R : Type u)
    [CommRing R₀] [TopologicalSpace R₀] [HuberRing R] [Algebra R₀ R] : Prop extends
    IsIntegrallyClosedIn R₀ R, IsOpenEmbedding (algebraMap R₀ R) where
  is_power_bounded (r : R₀) : ∀ U ∈ nhds (0 : R), ∃ V ∈ nhds (0 : R),
    ∀ n : ℕ, ∀ v ∈ V, v * (algebraMap R₀ R r) ^ n ∈ U

lemma IsRingOfIntegralElements.isTopologicalRing {R₀ : Type u} {R : Type u}
    [CommRing R₀] [TopologicalSpace R₀] [HuberRing R] [Algebra R₀ R]
    (h : IsRingOfIntegralElements R₀ R) : IsTopologicalRing R₀ := by
  sorry

structure HuberPair where
  plus : Type u
  carrier : Type u
  [ring : CommRing plus]
  [topologicalSpace : TopologicalSpace plus]
  [huber : HuberRing carrier]
  [algebra : Algebra plus carrier]
  int : IsRingOfIntegralElements plus carrier

namespace HuberPair

instance : CoeSort HuberPair (Type u) where
  coe := carrier

variable (A : HuberPair)

instance : HuberRing A := A.huber

instance : CommRing A.plus := A.ring

instance : TopologicalSpace A.plus := A.topologicalSpace

instance : Algebra A.plus A := A.algebra

instance : IsTopologicalRing A.plus := A.int.isTopologicalRing

end HuberPair

-- TODO: change this to use the modern approach of `ValuativeRel` instead.
def Spv (R : Type u) [CommRing R] : Type u :=
  {rel : R → R → Prop // ∃ (Γ₀ : Type u)
    (_ : LinearOrderedCommGroupWithZero Γ₀), ∃ (v : Valuation R Γ₀), ∀ r s : R, v r ≤ v s ↔ rel r s}

def Spv.outΓ₀ {R : Type u} [CommRing R] (v : Spv R) : Type u := v.2.choose

noncomputable
instance {R : Type u} [CommRing R] (v : Spv R) : LinearOrderedCommGroupWithZero (Spv.outΓ₀ v) :=
  v.2.choose_spec.choose

noncomputable def Spv.out {R : Type u} [CommRing R] (v : Spv R) : Valuation R (v.outΓ₀) :=
  v.2.choose_spec.choose_spec.choose

noncomputable instance (R : Type u) [CommRing R] :
    CoeFun (Spv R) (fun v ↦ (R → Spv.outΓ₀ v)) where
  coe v := (v.out : R → v.outΓ₀)

noncomputable def Spv.lift {R : Type u} [CommRing R] {X : Type*}
    (f : ∀ ⦃Γ₀ : Type u⦄ [LinearOrderedCommGroupWithZero Γ₀], Valuation R Γ₀ → X) (v : Spv R) : X :=
  f (out v)

instance (R : Type u) [CommRing R] : TopologicalSpace (Spv R) := sorry

def Valuation.IsContinuous {R : Type u} [CommRing R] [TopologicalSpace R]
    {Γ₀ : Type u} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) : Prop :=
  sorry
  -- ∀ g : ValueMonoid v, IsOpen {r : R | CanonicalValuation v r < g}

def Spv.IsContinuous {R : Type u} [CommRing R] [TopologicalSpace R] (v : Spv R) : Prop :=
  lift (R := R) (fun _ _ v' ↦ v'.IsContinuous) v

section TopRingCat

structure ContinuousRingHom (A B : Type*)
    [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [Ring B] [TopologicalSpace B] [IsTopologicalRing B] extends A →+* B, C(A, B)

infixr:25 " →ₜ+* " => ContinuousRingHom

variable {A B C : Type*}
    [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [Ring B] [TopologicalSpace B] [IsTopologicalRing B]
    [Ring C] [TopologicalSpace C] [IsTopologicalRing C]

instance instFunLike : FunLike (A →ₜ+* B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨ ⟨ _ , _ ⟩ , _ ⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨ _ , _ ⟩, _⟩, _⟩ := g
    congr

instance instMonoidHomClass : RingHomClass (A →ₜ+* B) A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

instance instContinuousMapClass : ContinuousMapClass (A →ₜ+* B) A B where
  map_continuous f := f.continuous_toFun

def ContinuousRingHom.id (A : Type*) [Ring A] [TopologicalSpace A] [IsTopologicalRing A] :
    A →ₜ+* A := ⟨.id _, by fun_prop⟩

def ContinuousRingHom.comp {A B C : Type*}
    [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [Ring B] [TopologicalSpace B] [IsTopologicalRing B]
    [Ring C] [TopologicalSpace C] [IsTopologicalRing C]
    (f : B →ₜ+* C) (g : A →ₜ+* B) : A →ₜ+* C :=
    ⟨f.toRingHom.comp g.toRingHom, (map_continuous f).comp (map_continuous g)⟩

structure TopRingCat where
  private mk ::
  carrier : Type u
  [commRing : CommRing carrier]
  [top : TopologicalSpace carrier]
  [topRing : IsTopologicalRing carrier]

attribute [instance] TopRingCat.commRing TopRingCat.top TopRingCat.topRing

initialize_simps_projections TopRingCat (-commRing, -top, -topRing)

namespace TopRingCat

instance : CoeSort (TopRingCat) (Type u) :=
  ⟨TopRingCat.carrier⟩

attribute [coe] TopRingCat.carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `CommRingCat`. -/
abbrev of (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] : TopRingCat :=
  ⟨R⟩

lemma coe_of (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    (of R : Type u) = R :=
  rfl

lemma of_carrier (R : TopRingCat.{u}) : of R = R := rfl

variable {R} in
@[ext]
structure Hom (R S : TopRingCat.{u}) where
  private mk ::
  hom' : R →ₜ+* S

instance : Category TopRingCat where
  Hom R S := Hom R S
  id R := ⟨ContinuousRingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory.{u} TopRingCat (fun R S => R →ₜ+* S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

abbrev Hom.hom {R S : TopRingCat.{u}} (f : Hom R S) :=
  ConcreteCategory.hom (C := TopRingCat) f

abbrev ofHom {R S : Type u}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (f : R →ₜ+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom (C := TopRingCat) f

def Hom.Simps.hom (R S : TopRingCat) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

open Limits

instance : HasForget₂ TopRingCat CommRingCat where
  forget₂ := {
    obj X := CommRingCat.of X
    map f := CommRingCat.ofHom f.hom.toRingHom }

def uniformSpace (R : TopRingCat) : UniformSpace R := by
  exact IsTopologicalAddGroup.toUniformSpace _

end TopRingCat

end TopRingCat

open TopCat

def TopCat.Presheaf.forgetToRing {X : TopCat.{u}} (ℱ : X.Presheaf TopRingCat) :
    X.Presheaf CommRingCat :=
  ℱ ⋙ forget₂ TopRingCat CommRingCat

def spa (A : HuberPair) : Type u :=
  {v : Spv A // v.IsContinuous ∧ ∀ r : A.plus, v (algebraMap A.plus A r) ≤ 1}

instance (A : HuberPair) : TopologicalSpace (spa A) := sorry

def spa.presheaf (A : HuberPair) : Presheaf TopRingCat (of (spa A))  := sorry

def spa.stalk_valuation (A : HuberPair) (x : of (spa A)) :
    Spv (((spa.presheaf A).forgetToRing).stalk x) :=
  sorry

open AlgebraicGeometry Opposite

structure PreValuedRingedSpace extends PresheafedSpace TopRingCat where
  valuation : ∀ x : carrier, Spv (presheaf.forgetToRing.stalk x)

instance PreValuedRingedSpace.coeCarrier :
    CoeOut PreValuedRingedSpace TopCat where coe X :=
  X.carrier

instance PreValuedRingedSpace.coeSort : CoeSort PreValuedRingedSpace Type* where
  coe X := X.1

def PreValuedRingedSpace.toTopCat (X : PreValuedRingedSpace.{u}) : TopCat.{u} :=
  of X

instance : Category.{u} PreValuedRingedSpace.{u} := sorry

attribute [local instance] TopRingCat.uniformSpace

structure CLVRS extends SheafedSpace TopRingCat where
  complete (U : Opens carrier) : CompleteSpace (presheaf.obj (op U))
  isLocalRing (x : carrier) : presheaf.forgetToRing.stalk x
  valuation (x : carrier) : Spv (presheaf.forgetToRing.stalk x)
  supp_maximal (x : carrier) : Ideal.IsMaximal (valuation x).out.supp

instance CLVRS.coeCarrier :
    CoeOut CLVRS TopCat where coe X :=
  X.carrier

instance CLVRS.coeSort : CoeSort CLVRS Type* where
  coe X := X.1

def CLVRS.toPreValuedRingedSpace (X : CLVRS.{u}) : PreValuedRingedSpace.{u} where
  carrier := X.carrier
  presheaf := sorry
  valuation := sorry

def PreValuedRingedSpace.restrict {U : TopCat.{u}} (X : PreValuedRingedSpace.{u})
    {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f) : PreValuedRingedSpace where
  carrier := of U
  presheaf := sorry
  valuation := sorry

def Spa (A : HuberPair.{u}) : PreValuedRingedSpace.{u} where
  carrier := of (spa A)
  presheaf := spa.presheaf A
  valuation := spa.stalk_valuation A

open TopologicalSpace

def CLVRS.IsAdicSpace (X : CLVRS.{u}) : Prop :=
  ∀ x : X, ∃ (U : OpenNhds x) (R : HuberPair.{u}),
    (Nonempty (Spa.{u} R ≅ (X.toPreValuedRingedSpace.restrict U.isOpenEmbedding)))

structure AdicSpace where
  X : CLVRS
  isAdic : X.IsAdicSpace
