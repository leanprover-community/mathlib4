/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.QuotientNilpotent
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

#align_import ring_theory.etale from "leanprover-community/mathlib"@"73f96237417835f148a1f7bc1ff55f67119b7166"

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

-- Porting note: added to make the syntax work below.
open scoped TensorProduct

universe u

namespace Algebra

section

variable (R : Type u) [CommSemiring R]
variable (A : Type u) [Semiring A] [Algebra R A]

/-- An `R` algebra `A` is formally smooth if for every `R`-algebra, every square-zero ideal
`I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at least one lift `A →ₐ[R] B`. -/
@[mk_iff]
class FormallySmooth : Prop where
  comp_surjective :
    ∀ ⦃B : Type u⦄ [CommRing B],
      ∀ [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
        Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)
#align algebra.formally_smooth Algebra.FormallySmooth

end

namespace FormallySmooth

section

variable {R : Type u} [CommSemiring R]
variable {A : Type u} [Semiring A] [Algebra R A]
variable {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B)

theorem exists_lift {B : Type u} [CommRing B] [_RB : Algebra R B]
    [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I) (g : A →ₐ[R] B ⧸ I) :
    ∃ f : A →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f = g := by
  revert g
  change Function.Surjective (Ideal.Quotient.mkₐ R I).comp
  revert _RB
  apply Ideal.IsNilpotent.induction_on (R := B) I hI
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
#align algebra.formally_smooth.exists_lift Algebra.FormallySmooth.exists_lift

/-- For a formally smooth `R`-algebra `A` and a map `f : A →ₐ[R] B ⧸ I` with `I` square-zero,
this is an arbitrary lift `A →ₐ[R] B`. -/
noncomputable def lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A →ₐ[R] B ⧸ I) : A →ₐ[R] B :=
  (FormallySmooth.exists_lift I hI g).choose
#align algebra.formally_smooth.lift Algebra.FormallySmooth.lift

@[simp]
theorem comp_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A →ₐ[R] B ⧸ I) : (Ideal.Quotient.mkₐ R I).comp (FormallySmooth.lift I hI g) = g :=
  (FormallySmooth.exists_lift I hI g).choose_spec
#align algebra.formally_smooth.comp_lift Algebra.FormallySmooth.comp_lift

@[simp]
theorem mk_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A →ₐ[R] B ⧸ I) (x : A) : Ideal.Quotient.mk I (FormallySmooth.lift I hI g x) = g x :=
  AlgHom.congr_fun (FormallySmooth.comp_lift I hI g : _) x
#align algebra.formally_smooth.mk_lift Algebra.FormallySmooth.mk_lift

variable {C : Type u} [CommRing C] [Algebra R C]

/-- For a formally smooth `R`-algebra `A` and a map `f : A →ₐ[R] B ⧸ I` with `I` nilpotent,
this is an arbitrary lift `A →ₐ[R] B`. -/
noncomputable def liftOfSurjective [FormallySmooth R A] (f : A →ₐ[R] C)
    (g : B →ₐ[R] C) (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker (g : B →+* C)) :
    A →ₐ[R] B :=
  FormallySmooth.lift _ hg' ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f)
#align algebra.formally_smooth.lift_of_surjective Algebra.FormallySmooth.liftOfSurjective

@[simp]
theorem liftOfSurjective_apply [FormallySmooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker (g : B →+* C)) (x : A) :
    g (FormallySmooth.liftOfSurjective f g hg hg' x) = f x := by
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).symm.injective
  change _ = ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f) x
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [← FormallySmooth.mk_lift _ hg'
    ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f)]
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).injective
  simp only [liftOfSurjective, AlgEquiv.apply_symm_apply, AlgEquiv.toAlgHom_eq_coe,
    Ideal.quotientKerAlgEquivOfSurjective_apply, RingHom.kerLift_mk, RingHom.coe_coe]
#align algebra.formally_smooth.lift_of_surjective_apply Algebra.FormallySmooth.liftOfSurjective_apply

@[simp]
theorem comp_liftOfSurjective [FormallySmooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker (g : B →+* C)) :
    g.comp (FormallySmooth.liftOfSurjective f g hg hg') = f :=
  AlgHom.ext (FormallySmooth.liftOfSurjective_apply f g hg hg')
#align algebra.formally_smooth.comp_lift_of_surjective Algebra.FormallySmooth.comp_liftOfSurjective

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
#align algebra.formally_smooth.of_equiv Algebra.FormallySmooth.of_equiv

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
#align algebra.formally_smooth.mv_polynomial Algebra.FormallySmooth.mvPolynomial

instance polynomial : FormallySmooth R R[X] :=
  FormallySmooth.of_equiv (MvPolynomial.pUnitAlgEquiv R)
#align algebra.formally_smooth.polynomial Algebra.FormallySmooth.polynomial

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
#align algebra.formally_smooth.comp Algebra.FormallySmooth.comp


end Comp

section OfSurjective

variable {R S : Type u} [CommRing R] [CommSemiring S]
variable {P A : Type u} [CommRing A] [Algebra R A] [CommRing P] [Algebra R P]
variable (I : Ideal P) (f : P →ₐ[R] A) (hf : Function.Surjective f)

set_option backward.isDefEq.lazyWhnfCore false in -- See https://github.com/leanprover-community/mathlib4/issues/12534
theorem of_split [FormallySmooth R P] (g : A →ₐ[R] P ⧸ (RingHom.ker f.toRingHom) ^ 2)
    (hg : f.kerSquareLift.comp g = AlgHom.id R A) : FormallySmooth R A := by
  constructor
  intro C _ _ I hI i
  let l : P ⧸ (RingHom.ker f.toRingHom) ^ 2 →ₐ[R] C := by
    refine Ideal.Quotient.liftₐ _ (FormallySmooth.lift I ⟨2, hI⟩ (i.comp f)) ?_
    have : RingHom.ker f ≤ I.comap (FormallySmooth.lift I ⟨2, hI⟩ (i.comp f)) := by
      rintro x (hx : f x = 0)
      have : _ = i (f x) := (FormallySmooth.mk_lift I ⟨2, hI⟩ (i.comp f) x : _)
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
#align algebra.formally_smooth.of_split Algebra.FormallySmooth.of_split

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
    refine
      ⟨FormallySmooth.lift _ ⟨2, sqz⟩ (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom,
        ?_⟩
    ext x
    have :=
      (Ideal.quotientKerAlgEquivOfSurjective surj).toAlgHom.congr_arg
        (FormallySmooth.mk_lift _ ⟨2, sqz⟩
          (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom x)
    -- Porting note: was
    -- dsimp at this
    -- rw [AlgEquiv.apply_symm_apply] at this
    erw [AlgEquiv.apply_symm_apply] at this
    conv_rhs => rw [← this, AlgHom.id_apply]
    rfl
    -- Porting note: lean3 was not finished here:
    -- obtain ⟨y, e⟩ :=
    --   Ideal.Quotient.mk_surjective
    --     (FormallySmooth.lift _ ⟨2, sqz⟩
    --       (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom
    --       x)
    -- dsimp at e ⊢
    -- rw [← e]
    -- rfl
  · rintro ⟨g, hg⟩; exact FormallySmooth.of_split f g hg
#align algebra.formally_smooth.iff_split_surjection Algebra.FormallySmooth.iff_split_surjection

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
#align algebra.formally_smooth.base_change Algebra.FormallySmooth.base_change

end BaseChange

section Localization

variable {R S Rₘ Sₘ : Type u} [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
variable (M : Submonoid R)
variable [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
variable [IsLocalization M Rₘ] [IsLocalization (M.map (algebraMap R S)) Sₘ]

-- Porting note: no longer supported
-- attribute [local elab_as_elim] Ideal.IsNilpotent.induction_on

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
#align algebra.formally_smooth.of_is_localization Algebra.FormallySmooth.of_isLocalization

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
#align algebra.formally_smooth.localization_base Algebra.FormallySmooth.localization_base

theorem localization_map [FormallySmooth R S] : FormallySmooth Rₘ Sₘ := by
  haveI : FormallySmooth S Sₘ := FormallySmooth.of_isLocalization (M.map (algebraMap R S))
  haveI : FormallySmooth R Sₘ := FormallySmooth.comp R S Sₘ
  exact FormallySmooth.localization_base M
#align algebra.formally_smooth.localization_map Algebra.FormallySmooth.localization_map

end Localization

end FormallySmooth

section

variable (R : Type u) [CommSemiring R]
variable (A : Type u) [Semiring A] [Algebra R A]

/-- An `R` algebra `A` is smooth if it is formally smooth and of finite presentation. -/
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
