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

open CategoryTheory

universe v w u

variable (R : Type*) [CommRing R]
variable (k : Type u) [Field k]

variable {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)]

open TensorProduct

/-- Algebra maps `A ⊗[R] S →ₐ[A] T` are the same as algebra maps `S →ₐ[R] T`. -/
@[expose, simps]
def Algebra.TensorProduct.algHomEquiv (R S T A : Type*) [CommRing R] [CommRing S] [CommRing T]
    [CommRing A] [Algebra R S] [Algebra R T] [Algebra R A] [Algebra A T] [IsScalarTower R A T] :
    (A ⊗[R] S →ₐ[A] T) ≃ (S →ₐ[R] T) where
  toFun f := AlgHom.comp (f.restrictScalars R) Algebra.TensorProduct.includeRight
  invFun f := Algebra.TensorProduct.lift (Algebra.ofId _ _) f fun _ _ ↦ .all _ _
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

@[simp]
lemma IsArtinianRing.equivPi_apply (R : Type*) [CommRing R] [IsArtinianRing R] [IsReduced R]
    (x : R) (m : MaximalSpectrum R) :
    IsArtinianRing.equivPi R x m = Ideal.Quotient.mk m.asIdeal x :=
  rfl

lemma IsSepClosed.algebraMap_bijective (k K : Type*) [Field k] [Field K] [Algebra k K]
    [IsSepClosed k] [Algebra k K] [Algebra.IsSeparable k K] :
    Function.Bijective (algebraMap k K) :=
  ⟨RingHom.injective _, IsSepClosed.algebraMap_surjective _ _⟩

instance (k R : Type*) [Field k] [CommRing R] [Algebra k R] [Algebra.FormallyEtale k R]
    [Algebra.EssFiniteType k R]
    (m : Ideal R) [m.IsMaximal] :
    Algebra.IsSeparable k (R ⧸ m) := by
  have := Algebra.FormallyUnramified.finite_of_free k R
  have : IsArtinianRing R := isArtinian_of_tower k inferInstance
  have := Algebra.FormallyUnramified.isReduced_of_field k R
  let := Ideal.Quotient.field m
  rw [← Algebra.FormallyEtale.iff_isSeparable]
  have : Algebra.FormallyEtale k (Π (m : MaximalSpectrum R), (R ⧸ m.asIdeal)) :=
    .of_equiv ((IsArtinianRing.equivPi _).restrictScalars k)
  rw [Algebra.FormallyEtale.pi_iff] at this
  exact this ⟨m, ‹_›⟩

/-- If `R` is an étale `k`-algebra over a separably closed field `k`, it is
isomorphic to the (finite) product of copies of `k` indexed by the prime spectrum of `R`. -/
noncomputable
def Algebra.FormallyEtale.equivPiOfIsSepClosed (k R : Type*) [Field k] [CommRing R] [Algebra k R]
    [Algebra.EssFiniteType k R] [Algebra.FormallyEtale k R] [IsSepClosed k] :
    R ≃ₐ[k] PrimeSpectrum R → k :=
  haveI := Algebra.FormallyUnramified.finite_of_free k R
  haveI : IsArtinianRing R := isArtinian_of_tower k inferInstance
  haveI := Algebra.FormallyUnramified.isReduced_of_field k R
  letI _ (m : MaximalSpectrum R) : Field (R ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  ((IsArtinianRing.equivPi _).restrictScalars k).trans <|
    (AlgEquiv.piCongrRight fun _ ↦ (AlgEquiv.ofBijective (Algebra.ofId k _)
      (IsSepClosed.algebraMap_bijective _ _)).symm).trans <|
    (AlgEquiv.piCongrLeft _ (fun _ ↦ k) IsArtinianRing.primeSpectrumEquivMaximalSpectrum).symm

set_option backward.isDefEq.respectTransparency false in
lemma Algebra.FormallyEtale.equivPiOfIsSepClosed_self_apply [IsSepClosed k] (x : k)
    (p : PrimeSpectrum k) :
    equivPiOfIsSepClosed k k x p = x := by
  let := Ideal.Quotient.field p.asIdeal
  dsimp [equivPiOfIsSepClosed]
  simp only [Equiv.piCongrLeft_symm_apply, AlgEquiv.piCongrRight_apply,
    IsArtinianRing.primeSpectrumEquivMaximalSpectrum_apply_asIdeal, IsArtinianRing.equivPi_apply]
  apply (AlgEquiv.ofBijective (ofId k (k ⧸ p.asIdeal))
    (IsSepClosed.algebraMap_bijective _ _)).injective
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma Algebra.FormallyEtale.equivPiOfIsSepClosed_comap {k R S : Type*} [Field k] [CommRing R]
    [CommRing S]
    [Algebra k R] [Algebra.EssFiniteType k R] [Algebra.FormallyEtale k R]
    [Algebra k S] [Algebra.EssFiniteType k S] [Algebra.FormallyEtale k S]
    [IsSepClosed k] (f : R →ₐ[k] S) (x : R) (p : PrimeSpectrum S) :
    equivPiOfIsSepClosed k R x (PrimeSpectrum.comap f p) =
      equivPiOfIsSepClosed k S (f x) p := by
  dsimp [equivPiOfIsSepClosed]
  simp only [Equiv.piCongrLeft_symm_apply, AlgEquiv.piCongrRight_apply,
    IsArtinianRing.primeSpectrumEquivMaximalSpectrum_apply_asIdeal, PrimeSpectrum.comap_asIdeal,
    IsArtinianRing.equivPi_apply]
  have : ofId k (S ⧸ p.asIdeal) =
      AlgHom.comp (Ideal.quotientMapₐ p.asIdeal f le_rfl) (ofId _ _) := by
    simp
  suffices h : Ideal.quotientMapₐ p.asIdeal f le_rfl x = f x by
    apply FaithfulSMul.algebraMap_injective k (S ⧸ p.asIdeal)
    dsimp [IsArtinianRing.primeSpectrumEquivMaximalSpectrum]
    rw [← Algebra.ofId_apply, ← Algebra.ofId_apply]
    nth_rw 1 [this]
    dsimp only [AlgHom.coe_comp, Function.comp_apply]
    rw [AlgEquiv.ofBijective_apply_symm_apply]
    convert h
    apply AlgEquiv.ofBijective_apply_symm_apply
  simp

lemma Pi.coe_evalAlgHom {ι : Type*} (R : Type*) (A : ι → Type*) [CommSemiring R]
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] (i : ι) :
    Pi.evalAlgHom R A i = Pi.evalRingHom A i :=
  rfl

instance (k R : Type*) [Field k] [CommRing R] [Algebra k R] [IsSepClosed k]
    [Algebra.EssFiniteType k R] [Algebra.FormallyEtale k R] :
    Algebra.IsFiniteSplit k R := by
  have := Algebra.FormallyUnramified.finite_of_free k R
  have : IsArtinianRing R := isArtinian_of_tower k inferInstance
  exact .of_algEquiv (Algebra.FormallyEtale.equivPiOfIsSepClosed k R).symm

lemma Algebra.IsFiniteSplit.bijective_algebraMap_quotient (k : Type*) {R : Type*} [Field k]
    [CommRing R] [Algebra k R] [Algebra.IsFiniteSplit k R] (p : Ideal R) [p.IsPrime] :
    Function.Bijective (algebraMap k (R ⧸ p)) := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun k R
  let p' : Ideal (Fin n → k) := p.comap e.symm
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq ⟨p', inferInstance⟩
  obtain rfl : q = ⊥ := Subsingleton.elim _ _
  let g : (R ⧸ p) ≃ₐ[k] k :=
    (Ideal.quotientEquivAlg _ p' e <| Ideal.comap_symm e.toRingEquiv).trans <|
    (Ideal.quotientEquivAlgOfEq k congr($(hq).asIdeal).symm).trans <|
    Ideal.quotientKerAlgEquivOfSurjective (f := Pi.evalAlgHom k (fun _ ↦ k) i)
      (Function.surjective_eval _)
  simpa [← g.symm.toAlgHom.comp_algebraMap] using g.symm.bijective

/-- If `R` is finite split over a field `k`, the `k`-rational points of `R`
are in one-to-one correspondence with its prime spectrum. -/
noncomputable
def Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum (k R : Type*) [Field k] [CommRing R]
    [Algebra k R] [Algebra.IsFiniteSplit k R] :
    (R →ₐ[k] k) ≃ PrimeSpectrum R where
  toFun f := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  invFun p := AlgHom.comp
    (AlgEquiv.ofBijective (Algebra.ofId _ _) (bijective_algebraMap_quotient _ _)).symm.toAlgHom
    (Ideal.Quotient.mkₐ _ p.asIdeal)
  left_inv f := by
    ext
    dsimp
    have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    apply (AlgEquiv.ofBijective (ofId k (R ⧸ RingHom.ker f))
      (bijective_algebraMap_quotient _ _)).injective
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.coe_ofBijective, ofId_apply,
      IsScalarTower.algebraMap_apply k R]
    simp [-Ideal.Quotient.mk_algebraMap, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  right_inv p := by
    ext : 1
    dsimp
    rw [← AlgHom.comap_ker, ← RingHom.ker_coe_toRingHom, AlgHomClass.toRingHom_toAlgHom,
      AlgHom.ker_coe_equiv, ← RingHom.ker_eq_comap_bot, ← RingHom.ker_coe_toRingHom,
      Ideal.Quotient.mkₐ_ker]

namespace CommAlgCat

section

variable (R : Type*) [CommRing R]

/-- The object property of finite `R`-algebras. -/
abbrev finite (R : Type u) [CommRing R] : ObjectProperty (CommAlgCat.{v} R) :=
  fun S ↦ Module.Finite R S

/-- The object property of étale `R`-algebras. -/
abbrev etale (R : Type u) [CommRing R] : ObjectProperty (CommAlgCat.{v} R) :=
  fun S ↦ Algebra.Etale R S

/-- The object property of finite étale `R`-algebras. -/
abbrev finiteEtale (R : Type u) [CommRing R] : ObjectProperty (CommAlgCat.{v} R) :=
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
abbrev FiniteEtale.of (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
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

open TensorProduct

instance (R : Type*) [CommRing R] (K : Type*) [Field K] [Algebra R K]
    (S : Type*) [CommRing S] [Algebra R S] [Module.Finite R S] :
    Finite (S →ₐ[R] K) :=
  .of_equiv _ (Algebra.TensorProduct.algHomEquiv _ _ _ K)

instance (R : FiniteEtale k) : IsArtinianRing R :=
  have := Algebra.FormallyUnramified.finite_of_free k R
  isArtinian_of_tower k inferInstance

/-- If `S` is an `R`-algebra, this is the base change functor `A ↦ S ⊗[R] A`. -/
@[expose, simps]
def FiniteEtale.baseChange (R : Type u) (S : Type w) [CommRing R] [CommRing S] [Algebra R S] :
    FiniteEtale.{v} R ⥤ FiniteEtale.{max w v} S where
  obj A := .of S (S ⊗[R] A)
  map {A B} f := FiniteEtale.ofHom (Algebra.TensorProduct.map (.id _ _) f.hom.hom)

variable (R : Type u) [CommRing R] (Ω : Type w) [Field Ω] [Algebra R Ω]
variable (S : Type w) [CommRing S] [Algebra R S] [Algebra S Ω] [IsScalarTower R S Ω]

/-- Base change from `R` to `R` is isomorphic to the identity. -/
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
def FiniteEtale.fiberIsoBaseChangeFiber :
    FiniteEtale.fiber.{v} R Ω ≅
      (FiniteEtale.baseChange.{v} R S).op ⋙ FiniteEtale.fiber S Ω :=
  NatIso.ofComponents
    (fun A ↦ FintypeCat.equivEquivIso (Algebra.TensorProduct.algHomEquiv _ _ _ _).symm)

/-- If `Ω` is separably closed, the fiber functor for finite étale `Ω`-algebras
is naturally isomorphic to the (finite) `Spec` functor. -/
noncomputable
def FiniteEtale.fiberIsoFiniteSpec [IsSepClosed Ω] :
    FiniteEtale.fiber Ω Ω ≅ FiniteEtale.finiteSpec Ω :=
  NatIso.ofComponents
    (fun R ↦ FintypeCat.equivEquivIso (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum _ _))

/-- If `Ω` is separably closed, the fiber `S →ₐ[R] Ω`
is isomorphic to the prime spectrum of the base change `Ω ⊗[R] S`. -/
noncomputable
def FiniteEtale.fiberIsoComp [IsSepClosed Ω] :
    FiniteEtale.fiber.{v} R Ω ≅
      (FiniteEtale.baseChange.{v} R Ω).op ⋙ FiniteEtale.finiteSpec.{max w v} Ω :=
  fiberIsoBaseChangeFiber _ _ Ω ≪≫ Functor.isoWhiskerLeft _ (fiberIsoFiniteSpec _)

attribute [simp] PrimeSpectrum.sigmaHomeoPi_apply

set_option backward.isDefEq.respectTransparency false in
/-- If `Ω` is a separably closed field, the category of finite étale `Ω`-algebras is
anti-equivalent to `FintypeCat`. -/
@[expose, simps! functor inverse_obj inverse_map]
noncomputable def FiniteEtale.equivOfIsSepClosed (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    (FiniteEtale.{u} Ω)ᵒᵖ ≌ FintypeCat.{u} := .symm
{
  functor.obj X := .op (.of _ (X → Ω))
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
      (Equiv.sigmaUnique _ _).symm.trans (PrimeSpectrum.sigmaHomeoPi _).toEquiv
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
