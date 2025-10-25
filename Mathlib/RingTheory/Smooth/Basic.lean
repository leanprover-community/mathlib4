/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Unramified.Basic

/-!

# Smooth morphisms

An `R`-algebra `A` is formally smooth if for every `R`-algebra,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
at least one lift `A →ₐ[R] B`.
It is smooth if it is formally smooth and of finite presentation.

We show that the property of being formally smooth extends onto nilpotent ideals,
and that it is stable under `R`-algebra homomorphisms and compositions.

We show that smooth is stable under algebra isomorphisms, composition and
localization at an element.

-/

open scoped TensorProduct

universe u

namespace Algebra

section

variable (R : Type u) [CommSemiring R]
variable (A : Type u) [Semiring A] [Algebra R A]

/-- An `R` algebra `A` is formally smooth if for every `R`-algebra, every square-zero ideal
`I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at least one lift `A →ₐ[R] B`. -/
@[mk_iff, stacks 00TI]
class FormallySmooth : Prop where
  comp_surjective :
    ∀ ⦃B : Type u⦄ [CommRing B],
      ∀ [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
        Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)

end

namespace FormallySmooth

section

variable {R : Type u} [CommSemiring R]
variable {A : Type u} [Semiring A] [Algebra R A]
variable {B : Type u} [CommRing B] [Algebra R B]

theorem exists_lift {B : Type u} [CommRing B] [_RB : Algebra R B]
    [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I) (g : A →ₐ[R] B ⧸ I) :
    ∃ f : A →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f = g := by
  revert g
  change Function.Surjective (Ideal.Quotient.mkₐ R I).comp
  revert _RB
  apply Ideal.IsNilpotent.induction_on (S := B) I hI
  · intro B _ I hI _; exact FormallySmooth.comp_surjective I hI
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

variable {C : Type u} [CommRing C] [Algebra R C]

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

end

section OfEquiv

variable {R : Type u} [CommSemiring R]
variable {A B : Type u} [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem of_equiv [FormallySmooth R A] (e : A ≃ₐ[R] B) : FormallySmooth R B := by
  constructor
  intro C _ _ I hI f
  use (FormallySmooth.lift I ⟨2, hI⟩ (f.comp e : A →ₐ[R] C ⧸ I)).comp e.symm
  rw [← AlgHom.comp_assoc, FormallySmooth.comp_lift, AlgHom.comp_assoc, AlgEquiv.comp_symm,
    AlgHom.comp_id]

theorem iff_of_equiv (e : A ≃ₐ[R] B) : FormallySmooth R A ↔ FormallySmooth R B :=
  ⟨fun _ ↦ of_equiv e, fun _ ↦ of_equiv e.symm⟩

end OfEquiv

section Polynomial

open scoped Polynomial

variable (R : Type u) [CommSemiring R]

instance mvPolynomial (σ : Type u) : FormallySmooth R (MvPolynomial σ R) := by
  constructor
  intro C _ _ I _ f
  have : ∀ s : σ, ∃ c : C, Ideal.Quotient.mk I c = f (MvPolynomial.X s) := fun s =>
    Ideal.Quotient.mk_surjective _
  choose g hg using this
  refine ⟨MvPolynomial.aeval g, ?_⟩
  ext s
  rw [← hg, AlgHom.comp_apply, MvPolynomial.aeval_X]
  rfl

instance polynomial : FormallySmooth R R[X] :=
  FormallySmooth.of_equiv (MvPolynomial.pUnitAlgEquiv R)

instance : FormallySmooth R R := .of_equiv (MvPolynomial.isEmptyAlgEquiv R PEmpty)

end Polynomial

section Comp

variable (R : Type u) [CommSemiring R]
variable (A : Type u) [CommSemiring A] [Algebra R A]
variable (B : Type u) [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem comp [FormallySmooth R A] [FormallySmooth A B] : FormallySmooth R B := by
  constructor
  intro C _ _ I hI f
  obtain ⟨f', e⟩ := FormallySmooth.comp_surjective I hI (f.comp (IsScalarTower.toAlgHom R A B))
  letI := f'.toRingHom.toAlgebra
  obtain ⟨f'', e'⟩ :=
    FormallySmooth.comp_surjective I hI { f.toRingHom with commutes' := AlgHom.congr_fun e.symm }
  apply_fun AlgHom.restrictScalars R at e'
  exact ⟨f''.restrictScalars _, e'.trans (AlgHom.ext fun _ => rfl)⟩

lemma of_restrictScalars (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [FormallyUnramified R S] [FormallySmooth R T] :
    FormallySmooth S T where
  comp_surjective B _ _ I hI f := by
    letI := Algebra.compHom B (algebraMap R S)
    have : IsScalarTower R S B := .of_algebraMap_eq' rfl
    obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective I hI (f.restrictScalars R)
    suffices g.comp (IsScalarTower.toAlgHom R S T) = IsScalarTower.toAlgHom R S B from
      ⟨{ __ := g,  commutes' x := congr($this x) }, AlgHom.ext fun x ↦ congr($hg x)⟩
    apply Algebra.FormallyUnramified.comp_injective _ hI
    rw [← AlgHom.comp_assoc, hg]
    exact AlgHom.ext f.commutes

end Comp

section OfSurjective

variable {R : Type u} [CommRing R]
variable {P A : Type u} [CommRing A] [Algebra R A] [CommRing P] [Algebra R P]
variable (f : P →ₐ[R] A)

theorem of_split [FormallySmooth R P] (g : A →ₐ[R] P ⧸ (RingHom.ker f.toRingHom) ^ 2)
    (hg : f.kerSquareLift.comp g = AlgHom.id R A) : FormallySmooth R A := by
  constructor
  intro C _ _ I hI i
  let l : P ⧸ (RingHom.ker f.toRingHom) ^ 2 →ₐ[R] C := by
    refine Ideal.Quotient.liftₐ _ (FormallySmooth.lift I ⟨2, hI⟩ (i.comp f)) ?_
    have : RingHom.ker f ≤ I.comap (FormallySmooth.lift I ⟨2, hI⟩ (i.comp f)) := by
      rintro x (hx : f x = 0)
      have : _ = i (f x) := (FormallySmooth.mk_lift I ⟨2, hI⟩ (i.comp f) x :)
      rwa [hx, map_zero, ← Ideal.Quotient.mk_eq_mk, Submodule.Quotient.mk_eq_zero] at this
    intro x hx
    have := (Ideal.pow_right_mono this 2).trans (Ideal.le_comap_pow _ 2) hx
    rwa [hI] at this
  have : i.comp f.kerSquareLift = (Ideal.Quotient.mkₐ R _).comp l := by
    apply AlgHom.coe_ringHom_injective
    apply Ideal.Quotient.ringHom_ext
    ext x
    exact (FormallySmooth.mk_lift I ⟨2, hI⟩ (i.comp f) x).symm
  exact ⟨l.comp g, by rw [← AlgHom.comp_assoc, ← this, AlgHom.comp_assoc, hg, AlgHom.comp_id]⟩

variable (hf : Function.Surjective f)
include hf

/-- Let `P →ₐ[R] A` be a surjection with kernel `J`, and `P` a formally smooth `R`-algebra,
then `A` is formally smooth over `R` iff the surjection `P ⧸ J ^ 2 →ₐ[R] A` has a section.

Geometric intuition: we require that a first-order thickening of `Spec A` inside `Spec P` admits
a retraction. -/
theorem iff_split_surjection [FormallySmooth R P] :
    FormallySmooth R A ↔ ∃ g, f.kerSquareLift.comp g = AlgHom.id R A := by
  constructor
  · intro
    have surj : Function.Surjective f.kerSquareLift := fun x =>
      ⟨Submodule.Quotient.mk (hf x).choose, (hf x).choose_spec⟩
    have sqz : RingHom.ker f.kerSquareLift.toRingHom ^ 2 = 0 := by
      rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square, Ideal.zero_eq_bot]
    dsimp only [AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom] at sqz
    refine
      ⟨FormallySmooth.lift _ ⟨2, sqz⟩ (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom,
        ?_⟩
    dsimp only [AlgHom.toRingHom_eq_coe, AlgEquiv.toAlgHom_eq_coe]
    ext x
    have :=
      (Ideal.quotientKerAlgEquivOfSurjective surj).congr_arg
        (FormallySmooth.mk_lift (R := R) _ ⟨2, sqz⟩
          (Ideal.quotientKerAlgEquivOfSurjective surj).symm x)
    dsimp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_coe] at this
    rw [AlgEquiv.apply_symm_apply] at this
    conv_rhs => rw [← this, AlgHom.id_apply]
    rfl
  · rintro ⟨g, hg⟩; exact FormallySmooth.of_split f g hg

omit hf in
lemma iff_of_surjective (h : Function.Surjective (algebraMap R A)) :
    Algebra.FormallySmooth R A ↔ IsIdempotentElem (RingHom.ker (algebraMap R A)) := by
  rw [Algebra.FormallySmooth.iff_split_surjection (Algebra.ofId R A) h]
  constructor
  · rintro ⟨g, hg⟩
    let e : A ≃ₐ[R] R ⧸ RingHom.ker (algebraMap R A) ^ 2 :=
      .ofAlgHom _ _ (Ideal.Quotient.algHom_ext _ (by ext)) hg
    rw [IsIdempotentElem, ← pow_two, ← Ideal.mk_ker (I := _ ^ 2), ← Ideal.Quotient.algebraMap_eq,
      ← e.toAlgHom.comp_algebraMap, RingHom.ker_comp_of_injective _ (by exact e.injective)]
  · intro H
    let e := (Ideal.quotientEquivAlgOfEq _ ((pow_two _).trans H)).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R A) h)
    refine ⟨e.symm.toAlgHom, AlgHom.ext <| h.forall.mpr fun x ↦ by simp⟩

end OfSurjective

section BaseChange

open scoped TensorProduct

variable {R : Type u} [CommSemiring R]
variable {A : Type u} [Semiring A] [Algebra R A]
variable (B : Type u) [CommSemiring B] [Algebra R B]

instance base_change [FormallySmooth R A] : FormallySmooth B (B ⊗[R] A) := by
  constructor
  intro C _ _ I hI f
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

variable {R S Rₘ Sₘ : Type u} [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
variable (M : Submonoid R)
variable [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
variable [IsLocalization M Rₘ] [IsLocalization (M.map (algebraMap R S)) Sₘ]
include M

theorem of_isLocalization : FormallySmooth R Rₘ := by
  constructor
  intro Q _ _ I e f
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
  constructor
  intro Q _ _ I e f
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

theorem localization_map [FormallySmooth R S] : FormallySmooth Rₘ Sₘ := by
  haveI : FormallySmooth S Sₘ := FormallySmooth.of_isLocalization (M.map (algebraMap R S))
  haveI : FormallySmooth R Sₘ := FormallySmooth.comp R S Sₘ
  exact FormallySmooth.localization_base M

end Localization

end FormallySmooth

section

variable (R : Type u) [CommSemiring R]
variable (A : Type u) [Semiring A] [Algebra R A]

/-- An `R` algebra `A` is smooth if it is formally smooth and of finite presentation. -/
@[stacks 00T2 "In the stacks project, the definition of smooth is completely different, and tag
<https://stacks.math.columbia.edu/tag/00TN> proves that their definition is equivalent to this.",
mk_iff]
class Smooth [CommSemiring R] (A : Type u) [Semiring A] [Algebra R A] : Prop where
  formallySmooth : FormallySmooth R A := by infer_instance
  finitePresentation : FinitePresentation R A := by infer_instance

end

namespace Smooth

attribute [instance] formallySmooth finitePresentation

variable {R : Type u} [CommRing R]
variable {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

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
