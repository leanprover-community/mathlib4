/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kenny Lau
-/
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.TensorProduct.Basic

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

universe u v

namespace Algebra

section

variable (R : Type u) [CommSemiring R]
variable (A : Type v) [Semiring A] [Algebra R A]

/-- An `R` algebra `A` is formally smooth if for every `R`-algebra, every square-zero ideal
`I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at least one lift `A →ₐ[R] B`. -/
@[mk_iff, stacks 00TI]
class FormallySmooth : Prop where
  comp_surjective' :
    ∀ ⦃B : Type (max u v)⦄ [CommRing B],
      ∀ [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
        Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)

end

namespace FormallySmooth

section

/-! # The necessary results to make the definition universe polymorphic -/

theorem comp_surjective_mvPolynomial (R : Type*) [CommSemiring R] (σ : Type*)
    (A : Type*) [CommRing A] [Algebra R A] (I : Ideal A) :
    Function.Surjective ((Ideal.Quotient.mkₐ R I).comp :
      (MvPolynomial σ R →ₐ[R] A) → MvPolynomial σ R →ₐ[R] A ⧸ I) :=
  fun f ↦ ⟨MvPolynomial.aeval fun s ↦ (f <| .X s).out, by ext; simp⟩

-- MOVE
def _root_.Ideal.quotCotangentₐ {R : Type*} [CommRing R] (I : Ideal R) :
    ((R ⧸ I ^ 2) ⧸ I.cotangentIdeal) ≃ₐ[R] R ⧸ I where
  __ := I.quotCotangent
  commutes' _ := rfl

@[simp] lemma _root_.Ideal.quotCotangentₐ_apply {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
    I.quotCotangentₐ x = x :=
  rfl

-- replaced with `iff_split_surjection` below
private theorem split_of_formallySmooth_of_surjective'
    (R : Type u) (A : Type (max u v)) [CommRing R] [CommRing A] [Algebra R A]
    (B : Type v) [CommRing B] [Algebra R B] [FormallySmooth R B]
    (f : A →ₐ[R] B) (hf : Function.Surjective f) :
    ∃ s : B →ₐ[R] A ⧸ RingHom.ker f ^ 2, f.kerSquareLift.comp s = AlgHom.id R B := by
  let e := ((Ideal.quotCotangentₐ _).restrictScalars R).trans
    (Ideal.quotientKerAlgEquivOfSurjective hf)
  obtain ⟨s, hs⟩ := FormallySmooth.comp_surjective' (R := R) (A := B)
    ((RingHom.ker f).cotangentIdeal) (Ideal.cotangentIdeal_square _) e.symm
  refine ⟨s, AlgHom.ext fun x ↦ ?_⟩
  replace hs := congr($hs x)
  rw [AlgHom.coe_coe, AlgEquiv.eq_symm_apply] at hs
  rw [AlgHom.comp_apply] at hs ⊢
  generalize s x = y at hs ⊢
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact hs

-- replaced by `of_split` below
private theorem comp_surjective_of_split'
    (R σ A : Type*) [CommRing R] [CommRing A] [Algebra R A] (f : MvPolynomial σ R →ₐ[R] A)
    (s : A →ₐ[R] MvPolynomial σ R ⧸ RingHom.ker f ^ 2) (hs : f.kerSquareLift.comp s = AlgHom.id R A)
    (B : Type*) [CommRing B] [Algebra R B] (I : Ideal B) (hi : I ^ 2 = ⊥) :
    Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) := fun φ ↦ by
  let ⟨φ₁, hφ₁⟩ := comp_surjective_mvPolynomial R σ B I (φ.comp f)
  have h : RingHom.ker f ^ 2 ≤ RingHom.ker φ₁ :=
    (sq _).trans_le <| Ideal.mul_le.mpr fun r₁ (hr₁ : _ = 0) r₂ (hr₂ : _ = 0) ↦
      (map_mul _ _ _).trans <| Ideal.mem_bot.mp <| hi ▸ sq I ▸ Ideal.mul_mem_mul
        (Ideal.Quotient.eq_zero_iff_mem.mp <| by simpa [hr₁] using congr($hφ₁ r₁))
        (Ideal.Quotient.eq_zero_iff_mem.mp <| by simpa [hr₂] using congr($hφ₁ r₂))
  refine ⟨(Ideal.Quotient.liftₐ _ φ₁ h).comp s, AlgHom.ext fun r ↦ ?_⟩
  replace hs := congr($hs r)
  simp_rw [AlgHom.comp_apply] at hs ⊢
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (s r)
  replace hφ₁ := congr($hφ₁ x)
  conv at hs => enter [1,2]; exact hx.symm -- kerSquareLift has RingHom.ker f.toRingHom which is bad
  simpa [← hx, show f x = r from hs] using hφ₁

/-- If an `R`-algebra `A` is formally smooth, then it can "lift along nilpotent ideals", meaning
that if `B` is any arbitrary `R`-algebra and `I` is an ideal in `B` with `I ^ 2 = ⊥`, then
the natural map `(A →ₐ[R] B) → (A →ₐ[R] B ⧸ I)` is surjective. -/
theorem comp_surjective {R A B : Type*} [CommRing R] [CommRing A] [Algebra R A] [FormallySmooth R A]
    [CommRing B] [Algebra R B] (I : Ideal B) (hi : I ^ 2 = ⊥) :
    Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) :=
  let ⟨s, hs⟩ := split_of_formallySmooth_of_surjective' R (MvPolynomial A R) A
    (MvPolynomial.aeval _root_.id) fun a ↦ ⟨.X a, by simp⟩
  comp_surjective_of_split' _ _ _ _ s hs _ _ hi

end

section

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {B : Type*} [CommRing B] [Algebra R B]

theorem exists_lift {B : Type*} [CommRing B] [_RB : Algebra R B]
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

end

section OfEquiv

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

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

variable (R : Type*) [CommSemiring R] (σ : Type*)

instance mvPolynomial : FormallySmooth R (MvPolynomial σ R) :=
  ⟨fun _ _ _ _ _ ↦ comp_surjective_mvPolynomial _ _ _ _⟩

instance polynomial : FormallySmooth R R[X] :=
  ⟨fun _ _ _ _ _ f ↦ ⟨Polynomial.aeval (f .X).out, by ext; simp⟩⟩

end Polynomial

section Comp

variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]
variable (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem comp [FormallySmooth R A] [FormallySmooth A B] : FormallySmooth R B := by
  constructor
  intro C _ _ I hI f
  obtain ⟨f', e⟩ := FormallySmooth.comp_surjective I hI (f.comp (IsScalarTower.toAlgHom R A B))
  letI := f'.toRingHom.toAlgebra
  obtain ⟨f'', e'⟩ :=
    FormallySmooth.comp_surjective I hI { f.toRingHom with commutes' := AlgHom.congr_fun e.symm }
  apply_fun AlgHom.restrictScalars R at e'
  exact ⟨f''.restrictScalars _, e'.trans (AlgHom.ext fun _ => rfl)⟩


end Comp

section OfSurjective

variable {R : Type*} [CommRing R]
variable {P A : Type*} [CommRing A] [Algebra R A] [CommRing P] [Algebra R P]
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

end OfSurjective

section BaseChange

open scoped TensorProduct

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable (B : Type*) [CommRing B] [Algebra R B]

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

variable {R S Rₘ Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
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

variable (R : Type*) [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]

/-- An `R` algebra `A` is smooth if it is formally smooth and of finite presentation. -/
@[stacks 00T2 "In the stacks project, the definition of smooth is completely different, and tag
<https://stacks.math.columbia.edu/tag/00TN> proves that their definition is equivalent to this.",
mk_iff]
class Smooth [CommSemiring R] (A : Type*) [Semiring A] [Algebra R A] : Prop where
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
