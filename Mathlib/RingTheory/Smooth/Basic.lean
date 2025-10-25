/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Smooth.Kaehler

/-!

# Smooth morphisms

An `R`-algebra `A` is formally smooth if `Ω[A⁄R]` is `A`-projective and `H¹(L_{S/R}) = 0`.
This is equivalent to the standard definition that "for every `R`-algebra `B`,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
at least one lift `A →ₐ[R] B`".
An `R`-algebra `A` is smooth if it is formally smooth and of finite presentation.

We show that the property of being formally smooth extends onto nilpotent ideals,
and that it is stable under `R`-algebra homomorphisms and compositions.

We show that smooth is stable under algebra isomorphisms, composition and
localization at an element.

-/

open scoped TensorProduct
open Algebra.Extension KaehlerDifferential MvPolynomial

universe u v w

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {B P C : Type*} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  [CommRing P] [Algebra R P]
namespace Algebra

section

variable (R A) in
/--
An `R`-algebra `A` is formally smooth if `Ω[A⁄R]` is `A`-projective and `H¹(L_{S/R}) = 0`.
For the infinitesimal lifting definition,
see `FormallySmooth.lift` and `FormallySmooth.iff_comp_surjective`.
-/
@[stacks 00TI "Also see 031J (6) for the the equivalence with the definition given here.", mk_iff]
class FormallySmooth : Prop where
  projective_kaehlerDifferential : Module.Projective A Ω[A⁄R]
  subsingleton_h1Cotangent : Subsingleton (H1Cotangent R A)

attribute [instance] FormallySmooth.projective_kaehlerDifferential
  FormallySmooth.subsingleton_h1Cotangent

@[deprecated (since := "2025-10-25")]
alias FormallySmooth.iff_subsingleton_and_projective := Algebra.formallySmooth_iff

variable (R A) in
lemma FormallySmooth.comp_surjective [FormallySmooth R A] (I : Ideal B) (hI : I ^ 2 = ⊥) :
    Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) := by
  intro f
  let P : Algebra.Generators R A A := Generators.self R A
  have hP : Function.Injective P.toExtension.cotangentComplex := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
    exact FormallySmooth.subsingleton_h1Cotangent
  obtain ⟨l, hl⟩ := ((P.toExtension.exact_cotangentComplex_toKaehler.split_tfae'.out 0 1 rfl rfl).mp
    ⟨P.toExtension.subsingleton_h1Cotangent.mp FormallySmooth.subsingleton_h1Cotangent,
      Module.projective_lifting_property _ _ P.toExtension.toKaehler_surjective⟩).2
  obtain ⟨g, hg⟩ := retractionKerCotangentToTensorEquivSection (R := R) P.algebraMap_surjective
    ⟨⟨⟨Cotangent.val, by simp⟩, by simpa using Cotangent.val_smul' (P := P.toExtension)⟩ ∘ₗ
      l.restrictScalars P.toExtension.Ring, LinearMap.ext fun x ↦ congr($hl x)⟩
  let σ := Function.surjInv (f := algebraMap B (B ⧸ I)) Ideal.Quotient.mk_surjective
  have H (x : P.Ring) : ↑(aeval (σ ∘ f) x) = f (algebraMap _ A x) := by
    rw [← Ideal.Quotient.algebraMap_eq, ← aeval_algebraMap_apply, P.algebraMap_eq,
      AlgHom.coe_toRingHom, comp_aeval_apply, ← Function.comp_assoc, Function.comp_surjInv,]
    rfl
  let l : P.Ring ⧸ (RingHom.ker (algebraMap P.Ring A)) ^ 2 →ₐ[R] B :=
    Ideal.Quotient.liftₐ _ (aeval (σ ∘ f)) <|
      have : RingHom.ker (algebraMap P.Ring A) ≤ I.comap (aeval (σ ∘ f)).toRingHom := fun x hx ↦ by
        simp_all [← Ideal.Quotient.eq_zero_iff_mem (I := I), -map_aeval]
      show RingHom.ker _ ^ 2 ≤ RingHom.ker _ from
        (Ideal.pow_right_mono this 2).trans ((Ideal.le_comap_pow _ _).trans_eq (hI ▸ rfl))
  have : f.comp (IsScalarTower.toAlgHom R P.Ring A).kerSquareLift =
      (Ideal.Quotient.mkₐ R _).comp l := by
    refine Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun i ↦ ?_)
    change f (algebraMap P.Ring A (.X i)) = algebraMap _ _ (MvPolynomial.aeval (σ ∘ f) (.X i))
    simpa using (Function.surjInv_eq _ _).symm
  exact ⟨l.comp g, by rw [← AlgHom.comp_assoc, ← this, AlgHom.comp_assoc, hg, AlgHom.comp_id]⟩

instance mvPolynomial (σ : Type*) : FormallySmooth R (MvPolynomial σ R) := by
  let P : Generators R (MvPolynomial σ R) σ :=
    .ofSurjective X (by simp [aeval_X_left, Function.Surjective])
  have : Subsingleton ↥P.toExtension.ker :=
    Submodule.subsingleton_iff_eq_bot.mpr (by simp [SetLike.ext_iff, map_id])
  have : Subsingleton P.toExtension.Cotangent := Cotangent.mk_surjective.subsingleton
  have := P.toExtension.h1Cotangentι_injective.subsingleton
  exact ⟨inferInstance, P.equivH1Cotangent.symm.subsingleton⟩

end

namespace FormallySmooth

theorem exists_lift
    [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I) (g : A →ₐ[R] B ⧸ I) :
    ∃ f : A →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f = g := by
  revert g
  change Function.Surjective (Ideal.Quotient.mkₐ R I).comp
  revert ‹Algebra R B›
  apply Ideal.IsNilpotent.induction_on (S := B) I hI
  · intro B _ I hI _; exact FormallySmooth.comp_surjective R A I hI
  · intro B _ I J hIJ h₁ h₂ _ g
    let this : ((B ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) ≃ₐ[R] B ⧸ J :=
      {
        (DoubleQuot.quotQuotEquivQuotSup I J).trans
          (Ideal.quotEquivOfEq (sup_eq_right.mpr hIJ)) with
        commutes' := fun x => rfl }
    obtain ⟨g', e⟩ := h₂ (this.symm.toAlgHom.comp g)
    obtain ⟨g', rfl⟩ := h₁ g'
    replace e := congr_arg this.toAlgHom.comp e
    conv_rhs at e =>
      rw [← AlgHom.comp_assoc, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_eq_coe,
        AlgEquiv.comp_symm, AlgHom.id_comp]
    exact ⟨g', e⟩

/-- For a formally smooth `R`-algebra `A` and a map `f : A →ₐ[R] B ⧸ I` with `I` square-zero,
this is an arbitrary lift `A →ₐ[R] B`. -/
noncomputable def lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A →ₐ[R] B ⧸ I) : A →ₐ[R] B :=
  (FormallySmooth.exists_lift I hI g).choose

@[simp]
theorem comp_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A →ₐ[R] B ⧸ I) : (Ideal.Quotient.mkₐ R I).comp (FormallySmooth.lift I hI g) = g :=
  (FormallySmooth.exists_lift I hI g).choose_spec

@[simp]
theorem mk_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A →ₐ[R] B ⧸ I) (x : A) : Ideal.Quotient.mk I (FormallySmooth.lift I hI g x) = g x :=
  AlgHom.congr_fun (FormallySmooth.comp_lift I hI g :) x

variable {C : Type*} [CommRing C] [Algebra R C]

/-- For a formally smooth `R`-algebra `A` and a map `f : A →ₐ[R] B ⧸ I` with `I` nilpotent,
this is an arbitrary lift `A →ₐ[R] B`. -/
noncomputable def liftOfSurjective [FormallySmooth R A] (f : A →ₐ[R] C)
    (g : B →ₐ[R] C) (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker (g : B →+* C)) :
    A →ₐ[R] B :=
  FormallySmooth.lift _ hg' ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f)

@[simp]
theorem liftOfSurjective_apply [FormallySmooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker g) (x : A) :
    g (FormallySmooth.liftOfSurjective f g hg hg' x) = f x := by
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).symm.injective
  conv_rhs => rw [← AlgHom.coe_coe, ← AlgHom.comp_apply, ← FormallySmooth.mk_lift (A := A) _ hg']
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).injective
  rw [AlgEquiv.apply_symm_apply, Ideal.quotientKerAlgEquivOfSurjective_apply]
  simp only [liftOfSurjective, ← RingHom.ker_coe_toRingHom g, RingHom.kerLift_mk,
    AlgEquiv.toAlgHom_eq_coe, RingHom.coe_coe]

@[simp]
theorem comp_liftOfSurjective [FormallySmooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker (g : B →+* C)) :
    g.comp (FormallySmooth.liftOfSurjective f g hg hg') = f :=
  AlgHom.ext (FormallySmooth.liftOfSurjective_apply f g hg hg')

end FormallySmooth

namespace Extension

/--
Given extensions `0 → I₁ → P₁ → A → 0` and `0 → I₂ → P₂ → A → 0` with `P₁` formally smooth,
this is an arbitrarily chosen map `P₁/I₁² → P₂/I₂²` of extensions.
-/
noncomputable
def homInfinitesimal (P₁ P₂ : Extension R A) [FormallySmooth R P₁.Ring] :
    P₁.infinitesimal.Hom P₂.infinitesimal :=
  letI lift : P₁.Ring →ₐ[R] P₂.infinitesimal.Ring := FormallySmooth.liftOfSurjective
    (IsScalarTower.toAlgHom R P₁.Ring A)
    (IsScalarTower.toAlgHom R P₂.infinitesimal.Ring A)
    P₂.infinitesimal.algebraMap_surjective
    ⟨2, show P₂.infinitesimal.ker ^ 2 = ⊥ by
      rw [ker_infinitesimal]; exact Ideal.cotangentIdeal_square _⟩
  { toRingHom := (Ideal.Quotient.liftₐ (P₁.ker ^ 2) lift (by
        change P₁.ker ^ 2 ≤ RingHom.ker lift
        rw [pow_two, Ideal.mul_le]
        have : ∀ r ∈ P₁.ker, lift r ∈ P₂.infinitesimal.ker :=
          fun r hr ↦ (FormallySmooth.liftOfSurjective_apply _
            (IsScalarTower.toAlgHom R P₂.infinitesimal.Ring A) _ _ r).trans hr
        intro r hr s hs
        rw [RingHom.mem_ker, map_mul, ← Ideal.mem_bot, ← P₂.ker.cotangentIdeal_square,
          ← ker_infinitesimal, pow_two]
        exact Ideal.mul_mem_mul (this r hr) (this s hs))).toRingHom
    toRingHom_algebraMap := by simp
    algebraMap_toRingHom x := by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact FormallySmooth.liftOfSurjective_apply _
            (IsScalarTower.toAlgHom R P₂.infinitesimal.Ring A) _ _ x }

/-- Formally smooth extensions have isomorphic `H¹(L_P)`. -/
noncomputable
def H1Cotangent.equivOfFormallySmooth (P₁ P₂ : Extension R A)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] :
    P₁.H1Cotangent ≃ₗ[A] P₂.H1Cotangent :=
  .ofBijective _ (H1Cotangent.map_toInfinitesimal_bijective P₁) ≪≫ₗ
    H1Cotangent.equiv (Extension.homInfinitesimal _ _) (Extension.homInfinitesimal _ _)
    ≪≫ₗ .symm (.ofBijective _ (H1Cotangent.map_toInfinitesimal_bijective P₂))

lemma H1Cotangent.equivOfFormallySmooth_toLinearMap {P₁ P₂ : Extension R A} (f : P₁.Hom P₂)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] :
    (H1Cotangent.equivOfFormallySmooth P₁ P₂).toLinearMap = map f := by
  ext1 x
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  change ((map (P₁.homInfinitesimal P₂)).restrictScalars A ∘ₗ map P₁.toInfinitesimal) x =
    ((map P₂.toInfinitesimal).restrictScalars A ∘ₗ map f) x
  rw [← map_comp, ← map_comp, map_eq]

lemma H1Cotangent.equivOfFormallySmooth_apply {P₁ P₂ : Extension R A} (f : P₁.Hom P₂)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] (x) :
    H1Cotangent.equivOfFormallySmooth P₁ P₂ x = map f x := by
  rw [← equivOfFormallySmooth_toLinearMap]; rfl

lemma H1Cotangent.equivOfFormallySmooth_symm (P₁ P₂ : Extension R A)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] :
    (equivOfFormallySmooth P₁ P₂).symm = equivOfFormallySmooth P₂ P₁ := rfl

/-- Any formally smooth extension can be used to calculate `H¹(L_{A/R})`. -/
noncomputable
def equivH1CotangentOfFormallySmooth (P : Extension R A) [FormallySmooth R P.Ring] :
    P.H1Cotangent ≃ₗ[A] H1Cotangent R A :=
  have : FormallySmooth R (Generators.self R A).toExtension.Ring :=
    inferInstanceAs (FormallySmooth R (MvPolynomial _ _))
  H1Cotangent.equivOfFormallySmooth _ _

end Algebra.Extension

namespace Algebra.FormallySmooth

section iff_split

variable [Algebra.FormallySmooth R P]

/--
Given a formally smooth `R`-algebra `P` and a surjective algebra homomorphism `f : P →ₐ[R] A`
with kernel `I` (typically a presentation `R[X] → A`),
`A` is formally smooth iff the `P`-linear map `I/I² → A ⊗[P] Ω[P⁄R]` is split injective.
Also see `Algebra.Extension.formallySmooth_iff_split_injection`
for the version in terms of `Extension`.
-/
@[stacks 031I]
theorem iff_split_injection
    [Algebra P A] [IsScalarTower R P A] (hf : Function.Surjective (algebraMap P A)) :
    Algebra.FormallySmooth R A ↔ ∃ l, l ∘ₗ (kerCotangentToTensor R P A) = LinearMap.id := by
  rw [formallySmooth_iff, and_comm,
    Module.Projective.iff_split_of_projective (KaehlerDifferential.mapBaseChange R P A)
      (mapBaseChange_surjective R P A hf)]
  convert (((exact_kerCotangentToTensor_mapBaseChange R _ _ hf).split_tfae'
    (g := (KaehlerDifferential.mapBaseChange R P A).restrictScalars P)).out 0 1) using 2
  · let P' : Extension R A := ⟨P, _, Function.surjInv_eq hf⟩
    rw [← P'.equivH1CotangentOfFormallySmooth.subsingleton_congr, P'.subsingleton_h1Cotangent]
    rfl
  · rw [← (LinearMap.extendScalarsOfSurjectiveEquiv hf).exists_congr_right]
    simp only [LinearMap.ext_iff]; rfl
  · rw [and_iff_right (by exact mapBaseChange_surjective R P A hf)]

/--
Given a formally smooth `R`-algebra `P` and a surjective algebra homomorphism `f : P →ₐ[R] S`
with kernel `I` (typically a presentation `R[X] → S`),
`S` is formally smooth iff the `P`-linear map `I/I² → S ⊗[P] Ω[P⁄R]` is split injective.
-/
@[stacks 031I]
theorem _root_.Algebra.Extension.formallySmooth_iff_split_injection
    (P : Algebra.Extension.{w} R A) [FormallySmooth R P.Ring] :
    Algebra.FormallySmooth R A ↔ ∃ l, l ∘ₗ P.cotangentComplex = LinearMap.id := by
  refine (Algebra.FormallySmooth.iff_split_injection P.algebraMap_surjective).trans ?_
  let e : P.ker.Cotangent ≃ₗ[P.Ring] P.Cotangent :=
    { __ := AddEquiv.refl _, map_smul' r m := by ext1; simp; rfl }
  constructor
  · intro ⟨l, hl⟩
    exact ⟨(e.comp l).extendScalarsOfSurjective P.algebraMap_surjective,
      LinearMap.ext (DFunLike.congr_fun hl : _)⟩
  · intro ⟨l, hl⟩
    exact ⟨e.symm.toLinearMap ∘ₗ l.restrictScalars P.Ring,
      LinearMap.ext (DFunLike.congr_fun hl : _)⟩

/-- Let `P →ₐ[R] A` be a surjection with kernel `J`, and `P` a formally smooth `R`-algebra,
then `A` is formally smooth over `R` iff the surjection `P ⧸ J ^ 2 →ₐ[R] A` has a section.

Geometric intuition: we require that a first-order thickening of `Spec A` inside `Spec P` admits
a retraction. -/
theorem iff_split_surjection (f : P →ₐ[R] A) (hf : Function.Surjective f) :
    FormallySmooth R A ↔ ∃ g, f.kerSquareLift.comp g = AlgHom.id R A := by
  letI := f.toAlgebra
  rw [iff_split_injection hf, ← nonempty_subtype, ← nonempty_subtype,
    (retractionKerCotangentToTensorEquivSection hf).nonempty_congr]
  rfl

theorem of_split (f : P →ₐ[R] A) (g : A →ₐ[R] P ⧸ RingHom.ker f.toRingHom ^ 2)
    (h : f.kerSquareLift.comp g = AlgHom.id R A) :
    FormallySmooth R A := by
  refine (iff_split_surjection f fun x ↦ ?_).mpr ⟨g, h⟩
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (g x)
  exact ⟨y, congr(f.kerSquareLift $hy).trans congr($h x)⟩

theorem of_comp_surjective
    (H : ∀ ⦃B : Type max u v⦄ [CommRing B] [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
        Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)) :
    FormallySmooth R A := by
  let P := Generators.self R A
  let f := IsScalarTower.toAlgHom R P.Ring A
  rw [iff_split_surjection f P.algebraMap_surjective]
  have surj : Function.Surjective f.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ P.algebraMap_surjective
  have sqz : RingHom.ker f.kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  dsimp only [AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom] at sqz
  obtain ⟨g, hg⟩ := H _ sqz (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom
  refine ⟨g, AlgHom.ext fun x ↦ congr(f.kerSquareLift.kerLift ($hg x)).trans ?_⟩
  obtain ⟨x, rfl⟩ := (Ideal.quotientKerAlgEquivOfSurjective surj).surjective x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [AlgHom.toRingHom_eq_coe, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
    AlgEquiv.symm_apply_apply, AlgHom.coe_id, id_eq]
  simp only [Ideal.quotientKerAlgEquivOfSurjective_apply]

/--
An `R`-algebra `A` is formally smooth iff "for every `R`-algebra `B`,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
at least one lift `A →ₐ[R] B`".
-/
theorem iff_comp_surjective :
   FormallySmooth R A ↔ ∀ ⦃B : Type max u v⦄ [CommRing B] [Algebra R B] (I : Ideal B), I ^ 2 = ⊥ →
      Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) :=
  ⟨fun _ _ ↦ comp_surjective R A, of_comp_surjective⟩

end iff_split

section OfEquiv

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

theorem of_equiv [FormallySmooth R A] (e : A ≃ₐ[R] B) : FormallySmooth R B :=
  (iff_split_surjection e.toAlgHom e.surjective).mpr
    ⟨(Ideal.Quotient.mkₐ _ _).comp e.symm, AlgHom.ext e.apply_symm_apply⟩

theorem iff_of_equiv (e : A ≃ₐ[R] B) : FormallySmooth R A ↔ FormallySmooth R B :=
  ⟨fun _ ↦ of_equiv e, fun _ ↦ of_equiv e.symm⟩

end OfEquiv

section Polynomial

open scoped Polynomial in
instance polynomial (R : Type*) [CommRing R] :
  FormallySmooth R R[X] := .of_equiv (MvPolynomial.pUnitAlgEquiv.{_, 0} R)

end Polynomial

section Comp

variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]
variable (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem comp [FormallySmooth R A] [FormallySmooth A B] : FormallySmooth R B := by
  refine .of_comp_surjective fun C _ _ I hI f ↦ ?_
  obtain ⟨f', e⟩ := FormallySmooth.comp_surjective _ _ I hI (f.comp (IsScalarTower.toAlgHom R A B))
  letI := f'.toRingHom.toAlgebra
  obtain ⟨f'', e'⟩ := comp_surjective _ _ I hI { f with commutes' := AlgHom.congr_fun e.symm }
  apply_fun AlgHom.restrictScalars R at e'
  exact ⟨f''.restrictScalars _, e'.trans (AlgHom.ext fun _ => rfl)⟩

end Comp

section BaseChange

open scoped TensorProduct

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable (B : Type*) [CommRing B] [Algebra R B]

instance base_change [FormallySmooth R A] : FormallySmooth B (B ⊗[R] A) := by
  refine .of_comp_surjective fun C _ _ I hI f ↦ ?_
  letI := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨TensorProduct.productLeftAlgHom (Algebra.ofId B C) ?_, ?_⟩
  · exact FormallySmooth.lift I ⟨2, hI⟩ ((f.restrictScalars R).comp TensorProduct.includeRight)
  · apply AlgHom.restrictScalars_injective R
    apply TensorProduct.ext'
    intro b a
    suffices algebraMap B _ b * f (1 ⊗ₜ[R] a) = f (b ⊗ₜ[R] a) by simpa [Algebra.ofId_apply]
    rw [← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end BaseChange

section Localization

variable {R A Rₘ Sₘ : Type*} [CommRing R] [CommRing A] [CommRing Rₘ] [CommRing Sₘ]
variable (M : Submonoid R)
variable [Algebra R A] [Algebra R Sₘ] [Algebra A Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R A Sₘ]
variable [IsLocalization M Rₘ] [IsLocalization (M.map (algebraMap R A)) Sₘ]
include M

theorem of_isLocalization : FormallySmooth R Rₘ := by
  refine .of_comp_surjective fun Q _ _ I e f ↦ ?_
  have : ∀ x : M, IsUnit (algebraMap R Q x) := by
    intro x
    apply (IsNilpotent.isUnit_quotient_mk_iff ⟨2, e⟩).mp
    convert (IsLocalization.map_units Rₘ x).map f
    simp only [Ideal.Quotient.mk_algebraMap, AlgHom.commutes]
  let this : Rₘ →ₐ[R] Q :=
    { IsLocalization.lift this with commutes' := IsLocalization.lift_eq this }
  use this
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext M ?_
  ext
  simp

theorem localization_base [FormallySmooth R Sₘ] : FormallySmooth Rₘ Sₘ := by
  refine .of_comp_surjective fun Q _ _ I e f ↦ ?_
  letI := ((algebraMap Rₘ Q).comp (algebraMap R Rₘ)).toAlgebra
  letI : IsScalarTower R Rₘ Q := IsScalarTower.of_algebraMap_eq' rfl
  let f : Sₘ →ₐ[Rₘ] Q := by
    refine { FormallySmooth.lift I ⟨2, e⟩ (f.restrictScalars R) with commutes' := ?_ }
    intro r
    change
      (RingHom.comp (FormallySmooth.lift I ⟨2, e⟩ (f.restrictScalars R) : Sₘ →+* Q)
            (algebraMap _ _))
          r =
        algebraMap _ _ r
    congr 1
    refine IsLocalization.ringHom_ext M ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq,
      AlgHom.comp_algebraMap]
  use f
  ext
  simp [f]

theorem localization_map [FormallySmooth R A] : FormallySmooth Rₘ Sₘ := by
  haveI : FormallySmooth A Sₘ := FormallySmooth.of_isLocalization (M.map (algebraMap R A))
  haveI : FormallySmooth R Sₘ := FormallySmooth.comp R A Sₘ
  exact FormallySmooth.localization_base M

end Localization

end FormallySmooth

section

variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]

/-- An `R` algebra `A` is smooth if it is formally smooth and of finite presentation. -/
@[stacks 00T2 "In the stacks project, the definition of smooth is completely different, and tag
<https://stacks.math.columbia.edu/tag/00TN> proves that their definition is equivalent to this.",
mk_iff]
class Smooth [CommRing R] (A : Type u) [CommRing A] [Algebra R A] : Prop where
  formallySmooth : FormallySmooth R A := by infer_instance
  finitePresentation : FinitePresentation R A := by infer_instance

end

namespace Smooth

attribute [instance] formallySmooth finitePresentation

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Being smooth is transported via algebra isomorphisms. -/
theorem of_equiv [Smooth R A] (e : A ≃ₐ[R] B) : Smooth R B where
  formallySmooth := FormallySmooth.of_equiv e
  finitePresentation := FinitePresentation.equiv e

/-- Localization at an element is smooth. -/
theorem of_isLocalization_Away (r : R) [IsLocalization.Away r A] : Smooth R A where
  formallySmooth := Algebra.FormallySmooth.of_isLocalization (Submonoid.powers r)
  finitePresentation := IsLocalization.Away.finitePresentation r

section Comp

variable (R A B)

/-- Smooth is stable under composition. -/
theorem comp [Algebra A B] [IsScalarTower R A B] [Smooth R A] [Smooth A B] : Smooth R B where
  formallySmooth := FormallySmooth.comp R A B
  finitePresentation := FinitePresentation.trans R A B

/-- Smooth is stable under base change. -/
instance baseChange [Smooth R A] : Smooth B (B ⊗[R] A) where

end Comp

end Smooth

end Algebra
