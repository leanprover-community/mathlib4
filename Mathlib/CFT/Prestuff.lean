/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Conductor
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Noetherian.Nilpotent
/-! #Stuff -/

@[expose] public section

open TensorProduct

instance {K A : Type*} [Field K] [CommRing A] [Algebra K A] (P : Ideal A) [P.IsPrime] :
    P.LiesOver (⊥ : Ideal K) :=
  ⟨((IsSimpleOrder.eq_bot_or_eq_top _).resolve_right Ideal.IsPrime.ne_top').symm⟩

instance {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime] :
    (⊥ : Ideal P.ResidueField).LiesOver P := ⟨P.ker_algebraMap_residueField.symm⟩

attribute [ext high] Ideal.Quotient.algHom_ext

attribute [instance] RingHom.ker_isPrime

open scoped nonZeroDivisors

open TopologicalSpace Topology PrimeSpectrum in
lemma _root_.PrimeSpectrum.sigmaToPi_preimage_basicOpen_single
    {I : Type*} (R : I → Type*) [∀ i, CommRing (R i)]
    [DecidableEq I] (i : I) (r : R i) :
    sigmaToPi R ⁻¹' (basicOpen (Pi.single i r)) = Sigma.mk i '' (basicOpen r) := by
  ext ⟨j, x⟩
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

open TopologicalSpace Topology PrimeSpectrum in
def PrimeSpectrum.isEmbedding_pi {I : Type*} (R : I → Type*) [∀ i, CommRing (R i)] :
    IsEmbedding (PrimeSpectrum.sigmaToPi R) := by
  classical
  refine ⟨⟨le_antisymm ?_ ?_⟩, PrimeSpectrum.sigmaToPi_injective R⟩
  · exact continuous_iff_le_induced.mp
      (continuous_sigma fun i ↦ (PrimeSpectrum.comap (Pi.evalRingHom R i)).2)
  · suffices ∀ (i : I) (y : R i), ∃ t, IsOpen t ∧ sigmaToPi R ⁻¹' t = Sigma.mk i '' basicOpen y by
      simpa [(IsTopologicalBasis.sigma fun _ ↦ isBasis_basic_opens).eq_generateFrom,
        isOpen_induced_iff, Set.range_subset_iff, le_generateFrom_iff_subset_isOpen,
        Set.iUnion_subset_iff]
    intro i r
    exact ⟨_, (basicOpen (Pi.single i r)).isOpen, sigmaToPi_preimage_basicOpen_single _ _ _⟩

noncomputable
def _root_.PrimeSpectrum.piHomeomorph {I : Type*} [Finite I] (R : I → Type*)
    [∀ i, CommRing (R i)] :
    PrimeSpectrum (Π i, R i) ≃ₜ Σ i, (PrimeSpectrum (R i)) :=
  ((PrimeSpectrum.isEmbedding_pi R).toHomeomorphOfSurjective
    (PrimeSpectrum.sigmaToPi_bijective R).surjective).symm

theorem Algebra.TensorProduct.map_surjective
    {R S A B C D : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Semiring B] [Algebra R B]
    [Semiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
    [Semiring D] [Algebra R D] (f : A →ₐ[S] C) (g : B →ₐ[R] D) (hf : Function.Surjective f)
    (hg : Function.Surjective g) :
    Function.Surjective (Algebra.TensorProduct.map f g) := by
  intro x
  induction x with
  | zero => exact ⟨0, by simp⟩
  | tmul x y =>
    obtain ⟨x, rfl⟩ := hf x
    obtain ⟨y, rfl⟩ := hg y
    exact ⟨x ⊗ₜ y, by simp⟩
  | add x y h₁ h₂ =>
    obtain ⟨x, rfl⟩ := h₁
    obtain ⟨y, rfl⟩ := h₂
    exact ⟨x + y, by simp⟩

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (Q : Ideal S) [Q.IsPrime] :
  IsScalarTower R (S ⧸ Q) Q.ResidueField := .of_algebraMap_eq' rfl

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p] [IsLocalRing S] :
    (IsLocalRing.maximalIdeal S).LiesOver p :=
  ⟨(IsLocalization.AtPrime.comap_maximalIdeal _ _).symm⟩

lemma _root_.IsNoetherianRing.of_essFiniteType
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
    [IsNoetherianRing R] : IsNoetherianRing S :=
  IsLocalization.isNoetherianRing (Algebra.EssFiniteType.submonoid R S) _
    (Algebra.FiniteType.isNoetherianRing R _)

attribute [-instance] Module.free_of_finite_type_torsion_free'
  NoZeroSMulDivisors.instFaithfulSMulOfNontrivial
  Module.Free.instFaithfulSMulOfNontrivial in
instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : Ideal R) [P.IsPrime]
    (Q' : Ideal (P.ResidueField ⊗[R] S)) [Q'.IsPrime] : Q'.LiesOver P :=
  .trans _ (⊥ : Ideal P.ResidueField) _

set_option maxHeartbeats 0 in
attribute [-instance] Module.free_of_finite_type_torsion_free'
  NoZeroSMulDivisors.instFaithfulSMulOfNontrivial
  Module.Free.instFaithfulSMulOfNontrivial in
noncomputable def Ideal.Fiber.residueFieldEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P]
    (Q' : Ideal (P.Fiber S)) [Q'.IsPrime]
    (H : Q'.comap Algebra.TensorProduct.includeRight = Q) :
    Q'.ResidueField ≃ₐ[P.ResidueField] Q.ResidueField :=
  let f₁ : Q.ResidueField →+* Q'.ResidueField :=
    Ideal.ResidueField.map _ _ Algebra.TensorProduct.includeRight.toRingHom H.symm
  let f₂ : Q.ResidueField →ₐ[R] Q'.ResidueField := ⟨f₁, by
    simp [f₁, IsScalarTower.algebraMap_apply R S Q.ResidueField,
      IsScalarTower.algebraMap_apply R (P.ResidueField ⊗[R] S) Q'.ResidueField]⟩
  let f₃ : P.Fiber S →ₐ[R] Q.ResidueField :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom _ _ _)
      (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _
  have hf₃ : Q' = RingHom.ker f₃ :=
    congr($(((PrimeSpectrum.preimageEquivFiber R S ⟨P, ‹_›⟩).symm_apply_eq
      (x := ⟨Q', ‹_›⟩) (y := ⟨⟨Q, ‹_›⟩, PrimeSpectrum.ext (Q.over_def P).symm⟩)).mp
      (Subtype.ext <| PrimeSpectrum.ext H)).1)
  let f₄ : Q'.ResidueField →ₐ[R] Q.ResidueField :=
    Ideal.ResidueField.liftₐ _ f₃ hf₃.le fun x hx ↦ by
      simpa [IsUnit.mem_submonoid_iff, hf₃] using hx
  let f₅ : Q'.ResidueField ≃ₐ[R] Q.ResidueField :=
    .ofAlgHom f₄ f₂ (by ext; simp [f₁, f₂, f₃, f₄]) (by ext; simp [f₁, f₂, f₃, f₄])
  have hf₅ : f₄.comp (IsScalarTower.toAlgHom R P.ResidueField _) =
      IsScalarTower.toAlgHom R P.ResidueField _ := by ext
  { __ := f₅,
    commutes' _ := congr($hf₅ _) }

lemma Ideal.algebraMap_residueField_surjective
    {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal] :
    Function.Surjective (algebraMap R I.ResidueField) := by
  rw [IsScalarTower.algebraMap_eq R (R ⧸ I) _]
  exact I.bijective_algebraMap_quotient_residueField.surjective.comp Ideal.Quotient.mk_surjective

instance {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal] :
    Module.Finite R I.ResidueField :=
  .of_surjective (Algebra.linearMap _ _) I.algebraMap_residueField_surjective

lemma RingHom.SurjectiveOnStalks.residueFieldMap_bijective
    {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (H : f.SurjectiveOnStalks)
    (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime] (hf : I = J.comap f) :
    Function.Bijective (Ideal.ResidueField.map I J f hf) := by
  subst hf
  exact ⟨RingHom.injective _, Ideal.Quotient.lift_surjective_of_surjective _ _
    (Ideal.Quotient.mk_surjective.comp (H J ‹_›))⟩


@[ext high]
lemma Algebra.TensorProduct.ringHom_ext
    {R S T A : Type*}
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra R T] (f g : S ⊗[R] T →+* A) (H : ∀ x y, f (x ⊗ₜ y) = g (x ⊗ₜ y)) :
    f = g := by
  ext x; induction x <;> aesop

instance {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (I : Ideal S) (J : Ideal T) [J.LiesOver I] : J.LiesOver (I.under R) :=
  ⟨by rw [← Ideal.under_under (B := S) J, J.over_def I]⟩

lemma _root_.Module.finite_of_surjective_of_ker_le_nilradical
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    [Module.Finite R T] (f : S →ₐ[R] T)
    (hf₁ : Function.Surjective f) (hf₂ : RingHom.ker f ≤ nilradical S)
    (hf₃ : (RingHom.ker f).FG) :
    Module.Finite R S := by
  have : Module.Finite R (S ⧸ RingHom.ker f) :=
    let e := Ideal.quotientKerAlgEquivOfSurjective hf₁
    .of_surjective e.symm.toLinearMap e.symm.surjective
  generalize hI : RingHom.ker f = I at *
  suffices ∀ i, Module.Finite R (S ⧸ I ^ i) by
    obtain ⟨n, hn : _ = ⊥⟩ := hf₃.isNilpotent_iff_le_nilradical.mpr hf₂
    let e : (S ⧸ I ^ n) ≃ₐ[R] S := hn ▸ (AlgEquiv.quotientBot R S)
    exact .of_surjective e.toLinearMap e.surjective
  intro n
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; infer_instance
  | succ n IH =>
    let φ : (S ⧸ I ^ (n + 1)) →ₐ[S] S ⧸ I ^ n :=
      Ideal.Quotient.factorₐ _ (Ideal.pow_le_pow_right n.le_succ)
    have hφ : Function.Surjective φ :=
      Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right n.le_succ)
    have hφ' : φ.toLinearMap ∘ₗ (I ^ (n + 1)).mkQ = (I ^ n).mkQ := rfl
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (φ.toLinearMap.restrictScalars R) ?_ ?_⟩
    · simpa [LinearMap.range_eq_top_of_surjective (φ.toLinearMap.restrictScalars R) hφ] using
        Module.Finite.fg_top
    · have : Module.Finite R ((S ⧸ I) ⊗[S] ↑(I ^ n)) := by
        have : Module.Finite S ↑(I ^ n) := Module.Finite.iff_fg.mpr (.pow hf₃ _)
        exact .trans (S ⧸ I) _
      let ψ : (S ⧸ I) ⊗[S] ↑(I ^ n) →ₗ[S] (S ⧸ I ^ (n + 1)) := by
        refine ?_ ∘ₗ (TensorProduct.quotTensorEquivQuotSMul _ I).toLinearMap
        refine Submodule.liftQ _ ((Submodule.mkQ _).comp (I ^ n).subtype) ?_
        rw [LinearMap.ker_comp, ← Submodule.map_le_map_iff_of_injective (I ^ n).subtype_injective,
          Submodule.map_smul'', Submodule.map_comap_eq]
        simpa [pow_succ'] using Ideal.mul_le_left (I := I) (J := I ^ n)
      convert Module.Finite.fg_top.map (ψ.restrictScalars R) using 1
      suffices LinearMap.ker φ.toLinearMap = Submodule.map (I ^ (n + 1)).mkQ (I ^ n) by
        simpa [LinearMap.range_restrictScalars, ψ, LinearMap.range_comp, Submodule.range_liftQ]
      apply Submodule.comap_injective_of_surjective (I ^ (n + 1)).mkQ_surjective
      simpa [← LinearMap.ker_comp, hφ'] using Ideal.pow_le_pow_right n.le_succ

lemma _root_.Ideal.algebraMap_localization_residueField_surjective
    {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal] :
    Function.Surjective (algebraMap (Localization.AtPrime I) I.ResidueField) :=
  .of_comp I.algebraMap_residueField_surjective

instance Subalgebra.faithfulSMul_right
    {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [FaithfulSMul R A]
    (S : Subalgebra R A) : FaithfulSMul R S := .tower_bot R S A

open scoped Polynomial

@[simp]
lemma AlgHom.range_codRestrict {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Semiring B] [Algebra R B] (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ (x : A), f x ∈ S) :
    (f.codRestrict S hf).range = f.range.comap S.val := by
  simp [SetLike.ext_iff, ← SetLike.coe_eq_coe]

attribute [simp] Subalgebra.range_val

instance {R : Type*} [CommRing R] [IsDomain R] : FaithfulSMul R[X] (RatFunc R) :=
  IsFractionRing.instFaithfulSMul _ _

@[simp]
lemma RatFunc.liftRingHom_algebraMap
    {L : Type*} {R : Type*} [Field L] [CommRing R] [IsDomain R] (φ : R[X] →+* L)
    (hφ : R[X]⁰ ≤ Submonoid.comap φ L⁰) (x : R[X]) :
    RatFunc.liftRingHom φ hφ (algebraMap R[X] _ x) = φ x := by
  change (RatFunc.mk (algebraMap _ _ x) 1).liftOn .. = _
  rw [RatFunc.mk_eq_localization_mk _ (by simp)]
  refine (RatFunc.liftOn_ofFractionRing_mk _ _ _ _).trans ?_
  simp

@[simp]
lemma RatFunc.liftRingHom_comp_algebraMap
    {L : Type*} {R : Type*} [Field L] [CommRing R] [IsDomain R] (φ : R[X] →+* L)
    (hφ : R[X]⁰ ≤ Submonoid.comap φ L⁰) :
    (RatFunc.liftRingHom φ hφ).comp (algebraMap R[X] _) = φ :=
  RingHom.ext fun _ ↦ RatFunc.liftRingHom_algebraMap _ hφ _

@[simp]
lemma RatFunc.liftRingHom_C
    {L : Type*} {R : Type*} [Field L] [CommRing R] [IsDomain R] (φ : R[X] →+* L)
    (hφ : R[X]⁰ ≤ Submonoid.comap φ L⁰) (x) :
    RatFunc.liftRingHom φ hφ (.C x) = φ (.C x) :=
  RatFunc.liftRingHom_algebraMap _ _ _

@[simp]
lemma RatFunc.liftRingHom_X
    {L : Type*} {R : Type*} [Field L] [CommRing R] [IsDomain R] (φ : R[X] →+* L)
    (hφ : R[X]⁰ ≤ Submonoid.comap φ L⁰) :
    RatFunc.liftRingHom φ hφ (.X) = φ (.X) :=
  RatFunc.liftRingHom_algebraMap _ _ _

attribute [-instance] Module.free_of_finite_type_torsion_free'
  NoZeroSMulDivisors.instFaithfulSMulOfNontrivial
  Module.Free.instFaithfulSMulOfNontrivial in
/-- `κ(I[X]) ≃ₐ[κ(I)] κ(I)(X)`. -/
noncomputable
def Polynomial.residueFieldMapCAlgEquiv
    {R : Type*} [CommRing R] (I : Ideal R) [I.IsPrime] (J : Ideal R[X]) [J.IsPrime]
    [J.LiesOver I] (hJ : J = I.map C) :
    J.ResidueField ≃ₐ[I.ResidueField] RatFunc I.ResidueField := by
  letI f : J.ResidueField →+* RatFunc I.ResidueField := by
    refine Ideal.ResidueField.lift _
        ((algebraMap I.ResidueField[X] _).comp (mapRingHom (algebraMap _ _))) ?_ ?_
    · simp [hJ, Ideal.map_le_iff_le_comap, RingHom.comap_ker _ C, mapRingHom_comp_C,
        RingHom.ker_comp_of_injective, C_injective,
        FaithfulSMul.algebraMap_injective I.ResidueField[X] (RatFunc I.ResidueField)]
    · rintro x (hx : x ∉ J)
      suffices ∃ i, x.coeff i ∉ I by simpa [IsUnit.mem_submonoid_iff, Polynomial.ext_iff]
      contrapose! hx
      rwa [hJ, Ideal.mem_map_C_iff]
  haveI hf : f.comp (algebraMap I.ResidueField _) = algebraMap _ _ := by
    ext
    simp [f, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R[X] J.ResidueField]
  refine .ofAlgHom ⟨f, fun r ↦ congr($hf r)⟩
      (RatFunc.liftAlgHom (aeval (algebraMap R[X] _ X)) fun x ↦ ?_) ?_ ?_
  · suffices Function.Injective (aeval (R := I.ResidueField) (algebraMap R[X] J.ResidueField X)) by
      simp [← this.eq_iff]
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, hr⟩ := map_surjective _ Ideal.Quotient.mk_surjective
      (IsLocalization.integerNormalization (R ⧸ I)⁰ x)
    obtain ⟨s, hs, hr⟩ : ∃ s ∉ I, r.map (algebraMap _ _) = s • x := by
      obtain ⟨⟨b, hb0⟩, hb⟩ := IsLocalization.integerNormalization_map_to_map (R ⧸ I)⁰ x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨s, by simpa [Ideal.Quotient.eq_zero_iff_mem] using hb0, ?_⟩
      simpa [← hr, map_map, ← Ideal.Quotient.algebraMap_eq] using hb
    replace hx : r ∈ J := by
      apply_fun aeval (algebraMap R[X] J.ResidueField X) at hr
      simpa [hx, aeval_map_algebraMap, aeval_algebraMap_apply, Algebra.smul_def] using hr
    refine ((IsUnit.mk0 (algebraMap R I.ResidueField s) (by simpa)).map C).mul_right_injective ?_
    simp only [← algebraMap_eq, ← Algebra.smul_def, algebraMap_smul, ← hr]
    simpa [Polynomial.ext_iff, Ideal.mem_map_C_iff] using hJ.le hx
  · apply AlgHom.coe_ringHom_injective
    apply IsFractionRing.injective_comp_algebraMap (A := I.ResidueField[X])
    dsimp [RatFunc.liftAlgHom]
    simp only [AlgHom.comp_toRingHom, AlgHom.coe_ringHom_mk, RingHom.comp_assoc,
      RatFunc.liftRingHom_comp_algebraMap, RingHomCompTriple.comp_eq, f]
    ext <;> simp [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R R[X] J.ResidueField]
  · apply AlgHom.coe_ringHom_injective
    ext
    · simp [f, RatFunc.liftAlgHom, ← IsScalarTower.algebraMap_apply]; rfl
    · simp [f, RatFunc.liftAlgHom]

lemma RatFunc.not_isIntegral_X {R : Type*} [CommRing R] [IsDomain R] :
    ¬ IsIntegral R (X (K := R)) := by
  rintro ⟨p, hp, e : Polynomial.aeval X p = 0⟩
  aesop

def Subalgebra.localized {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (s : Subalgebra R S) (M : Submonoid S) (H : M ≤ s.toSubmonoid) :
    Subalgebra R S where
  carrier := { x | ∃ m ∈ M, m * x ∈ s }
  mul_mem' := by
    intro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨_, mul_mem hm hn, mul_mul_mul_comm m n a b ▸ mul_mem ha hb⟩
  add_mem' := by
    intro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨_, mul_mem hn hm, ?_⟩
    rw [mul_add, mul_assoc, mul_comm n m, mul_assoc]
    exact add_mem (mul_mem (H hn) ha) (mul_mem (H hm) hb)
  algebraMap_mem' r := ⟨1, one_mem _, by simp⟩

@[simp] lemma Subalgebra.mem_localized {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    {s : Subalgebra R S} {M : Submonoid S} {H : M ≤ s.toSubmonoid} {x : S} :
    x ∈ s.localized M H ↔ ∃ m ∈ M, m • x ∈ s := .rfl

attribute [local instance 2000] RingHom.instRingHomClass RingHomClass.toAddMonoidHomClass
  Algebra.toModule Module.toDistribMulAction in
lemma Localization.localRingHom_bijective_of_localized_inf_eq_top
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {P : Ideal S} [P.IsPrime] {s : Subalgebra R S}
    (H : s.localized (P.primeCompl ⊓ s.toSubmonoid) (by simp) = ⊤) (p : Ideal s)
    [p.IsPrime] [P.LiesOver p] :
    Function.Bijective (Localization.localRingHom _ _ _ (P.over_def p)) := by
  constructor
  · refine (injective_iff_map_eq_zero _).mpr ?_
    suffices ∀ y ∈ s, ∀ z ∉ P, z * y = 0 → ∃ t ∉ P, t ∈ s ∧ t * y = 0 by
      simpa [(IsLocalization.mk'_surjective p.primeCompl).forall, P.over_def p,
        Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff, Subtype.ext_iff] using this
    intro y hys z hzP e
    obtain ⟨t, ⟨htP, _⟩, ht⟩ := H.ge (Set.mem_univ z)
    exact ⟨_, ‹P.IsPrime›.mul_notMem htP hzP, ht, by simp [mul_assoc, e]⟩
  · suffices ∀ y, ∀ z ∉ P, ∃ y' ∈ s, ∃ z' ∉ P, z' ∈ s ∧ ∃ t ∉ P, t * (z * y') = t * (z' * y) by
      simpa [(IsLocalization.mk'_surjective p.primeCompl).exists,
        (IsLocalization.mk'_surjective P.primeCompl).forall, P.over_def p,
        Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq, - map_mul,
        IsLocalization.eq_iff_exists P.primeCompl, Function.Surjective] using this
    intro y z hzP
    obtain ⟨a, ⟨haP, has⟩, ha⟩ := H.ge (Set.mem_univ y)
    obtain ⟨b, ⟨hbP, hbs⟩, hb⟩ := H.ge (Set.mem_univ z)
    exact ⟨_, mul_mem ha hbs, _, P.primeCompl.mul_mem (mul_mem hbP hzP) haP, mul_mem hb has, 1,
      P.primeCompl.one_mem, by ring⟩

attribute [local instance 2000] RingHom.instRingHomClass RingHomClass.toAddMonoidHomClass
  Algebra.toModule Module.toDistribMulAction in
lemma Localization.localRingHom_bijective_of_not_conductor_le
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {x : S} {P : Ideal S} [P.IsPrime] (hx : ¬ conductor R x ≤ P) {s : Subalgebra R S}
    (hs : s = Algebra.adjoin R {x}) (p : Ideal s) [p.IsPrime] [P.LiesOver p] :
    Function.Bijective (Localization.localRingHom _ _ _ (P.over_def p)) := by
  obtain ⟨a, ha, haP⟩ := SetLike.not_le_iff_exists.mp hx
  replace ha (b : _) : a * b ∈ s := by simpa [hs] using ha b
  exact Localization.localRingHom_bijective_of_localized_inf_eq_top
    (top_le_iff.mp fun y _ ↦ ⟨a, ⟨haP, by simpa using ha 1⟩, ha _⟩) _

section

/-- The natural isomorphism `A ⊗[S] (S ⊗[R] B) ≃ₐ[T] A ⊗[R] B`. -/
def Algebra.TensorProduct.cancelBaseChangeLeft
    (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A]
    [CommRing B] [Algebra R S] [Algebra R A] [Algebra S B] [Algebra R B]
    [IsScalarTower R S B] : (S ⊗[R] A) ⊗[S] B ≃ₐ[R] A ⊗[R] B :=
  .trans ((Algebra.TensorProduct.comm S _ _).restrictScalars R) <|
  .trans ((Algebra.TensorProduct.cancelBaseChange _ _ S _ _).restrictScalars R) <|
    Algebra.TensorProduct.comm _ _ _

@[simp]
lemma Algebra.TensorProduct.cancelBaseChangeLeft_apply
    (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A]
    [CommRing B] [Algebra R S] [Algebra R A] [Algebra S B] [Algebra R B]
    [IsScalarTower R S B] (s a b) :
    cancelBaseChangeLeft R S A B ((s ⊗ₜ a) ⊗ₜ b) = a ⊗ₜ (s • b) := by
  simp [cancelBaseChangeLeft]

end

lemma Polynomial.not_isIntegral_X {R : Type*} [CommRing R] [IsDomain R] :
    ¬ IsIntegral R (X (R := R)) := by
  rintro ⟨p, hp, e⟩
  aesop
