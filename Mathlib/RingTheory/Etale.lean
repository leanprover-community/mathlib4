/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module ring_theory.etale
! leanprover-community/mathlib commit 73f96237417835f148a1f7bc1ff55f67119b7166
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.QuotientNilpotent
import Mathbin.RingTheory.Kaehler

/-!

# Formally étale morphisms

An `R`-algebra `A` is formally étale (resp. unramified, smooth) if for every `R`-algebra,
every square-zero ideal `I : ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
exactly (resp. at most, at least) one lift `A →ₐ[R] B`.

We show that the property extends onto nilpotent ideals, and that these properties are stable
under `R`-algebra homomorphisms and compositions.

-/


universe u

namespace Algebra

section

variable (R : Type u) [CommSemiring R]

variable (A : Type u) [Semiring A] [Algebra R A]

variable {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B)

/-- An `R`-algebra `A` is formally unramified if for every `R`-algebra, every square-zero ideal
`I : ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at most one lift `A →ₐ[R] B`. -/
@[mk_iff]
class FormallyUnramified : Prop where
  comp_injective :
    ∀ ⦃B : Type u⦄ [CommRing B],
      ∀ [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥),
        Function.Injective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)
#align algebra.formally_unramified Algebra.FormallyUnramified

/-- An `R` algebra `A` is formally smooth if for every `R`-algebra, every square-zero ideal
`I : ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at least one lift `A →ₐ[R] B`. -/
@[mk_iff]
class FormallySmooth : Prop where
  comp_surjective :
    ∀ ⦃B : Type u⦄ [CommRing B],
      ∀ [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥),
        Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)
#align algebra.formally_smooth Algebra.FormallySmooth

/-- An `R` algebra `A` is formally étale if for every `R`-algebra, every square-zero ideal
`I : ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists exactly one lift `A →ₐ[R] B`. -/
@[mk_iff]
class FormallyEtale : Prop where
  comp_bijective :
    ∀ ⦃B : Type u⦄ [CommRing B],
      ∀ [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥),
        Function.Bijective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)
#align algebra.formally_etale Algebra.FormallyEtale

variable {R A}

theorem FormallyEtale.iff_unramified_and_smooth :
    FormallyEtale R A ↔ FormallyUnramified R A ∧ FormallySmooth R A :=
  by
  rw [formally_unramified_iff, formally_smooth_iff, formally_etale_iff]
  simp_rw [← forall_and]
  rfl
#align algebra.formally_etale.iff_unramified_and_smooth Algebra.FormallyEtale.iff_unramified_and_smooth

instance (priority := 100) FormallyEtale.to_unramified [h : FormallyEtale R A] :
    FormallyUnramified R A :=
  (FormallyEtale.iff_unramified_and_smooth.mp h).1
#align algebra.formally_etale.to_unramified Algebra.FormallyEtale.to_unramified

instance (priority := 100) FormallyEtale.to_smooth [h : FormallyEtale R A] : FormallySmooth R A :=
  (FormallyEtale.iff_unramified_and_smooth.mp h).2
#align algebra.formally_etale.to_smooth Algebra.FormallyEtale.to_smooth

theorem FormallyEtale.of_unramified_and_smooth [h₁ : FormallyUnramified R A]
    [h₂ : FormallySmooth R A] : FormallyEtale R A :=
  FormallyEtale.iff_unramified_and_smooth.mpr ⟨h₁, h₂⟩
#align algebra.formally_etale.of_unramified_and_smooth Algebra.FormallyEtale.of_unramified_and_smooth

theorem FormallyUnramified.lift_unique {B : Type u} [CommRing B] [_RB : Algebra R B]
    [FormallyUnramified R A] (I : Ideal B) (hI : IsNilpotent I) (g₁ g₂ : A →ₐ[R] B)
    (h : (Ideal.Quotient.mkₐ R I).comp g₁ = (Ideal.Quotient.mkₐ R I).comp g₂) : g₁ = g₂ :=
  by
  revert g₁ g₂
  change Function.Injective (Ideal.Quotient.mkₐ R I).comp
  revert _RB
  apply Ideal.IsNilpotent.induction_on I hI
  · intro B _ I hI _; exact formally_unramified.comp_injective I hI
  · intro B _ I J hIJ h₁ h₂ _ g₁ g₂ e
    apply h₁
    apply h₂
    ext x
    replace e := AlgHom.congr_fun e x
    dsimp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at e ⊢
    rwa [Ideal.Quotient.eq, ← map_sub, Ideal.mem_quotient_iff_mem hIJ, ← Ideal.Quotient.eq]
#align algebra.formally_unramified.lift_unique Algebra.FormallyUnramified.lift_unique

theorem FormallyUnramified.ext [FormallyUnramified R A] (hI : IsNilpotent I) {g₁ g₂ : A →ₐ[R] B}
    (H : ∀ x, Ideal.Quotient.mk I (g₁ x) = Ideal.Quotient.mk I (g₂ x)) : g₁ = g₂ :=
  FormallyUnramified.lift_unique I hI g₁ g₂ (AlgHom.ext H)
#align algebra.formally_unramified.ext Algebra.FormallyUnramified.ext

theorem FormallyUnramified.lift_unique_of_ringHom [FormallyUnramified R A] {C : Type u} [CommRing C]
    (f : B →+* C) (hf : IsNilpotent f.ker) (g₁ g₂ : A →ₐ[R] B)
    (h : f.comp ↑g₁ = f.comp (g₂ : A →+* B)) : g₁ = g₂ :=
  FormallyUnramified.lift_unique _ hf _ _
    (by
      ext x
      have := RingHom.congr_fun h x
      simpa only [Ideal.Quotient.eq, Function.comp_apply, AlgHom.coe_comp, Ideal.Quotient.mkₐ_eq_mk,
        RingHom.mem_ker, map_sub, sub_eq_zero])
#align algebra.formally_unramified.lift_unique_of_ring_hom Algebra.FormallyUnramified.lift_unique_of_ringHom

theorem FormallyUnramified.ext' [FormallyUnramified R A] {C : Type u} [CommRing C] (f : B →+* C)
    (hf : IsNilpotent f.ker) (g₁ g₂ : A →ₐ[R] B) (h : ∀ x, f (g₁ x) = f (g₂ x)) : g₁ = g₂ :=
  FormallyUnramified.lift_unique_of_ringHom f hf g₁ g₂ (RingHom.ext h)
#align algebra.formally_unramified.ext' Algebra.FormallyUnramified.ext'

theorem FormallyUnramified.lift_unique' [FormallyUnramified R A] {C : Type u} [CommRing C]
    [Algebra R C] (f : B →ₐ[R] C) (hf : IsNilpotent (f : B →+* C).ker) (g₁ g₂ : A →ₐ[R] B)
    (h : f.comp g₁ = f.comp g₂) : g₁ = g₂ :=
  FormallyUnramified.ext' _ hf g₁ g₂ (AlgHom.congr_fun h)
#align algebra.formally_unramified.lift_unique' Algebra.FormallyUnramified.lift_unique'

theorem FormallySmooth.exists_lift {B : Type u} [CommRing B] [_RB : Algebra R B]
    [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I) (g : A →ₐ[R] B ⧸ I) :
    ∃ f : A →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f = g :=
  by
  revert g
  change Function.Surjective (Ideal.Quotient.mkₐ R I).comp
  revert _RB
  apply Ideal.IsNilpotent.induction_on I hI
  · intro B _ I hI _; exact formally_smooth.comp_surjective I hI
  · intro B _ I J hIJ h₁ h₂ _ g
    let this.1 : ((B ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) ≃ₐ[R] B ⧸ J :=
      {
        (DoubleQuot.quotQuotEquivQuotSup I J).trans
          (Ideal.quotEquivOfEq (sup_eq_right.mpr hIJ)) with
        commutes' := fun x => rfl }
    obtain ⟨g', e⟩ := h₂ (this.symm.to_alg_hom.comp g)
    obtain ⟨g', rfl⟩ := h₁ g'
    replace e := congr_arg this.to_alg_hom.comp e
    conv_rhs at e =>
      rw [← AlgHom.comp_assoc, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_eq_coe,
        AlgEquiv.comp_symm, AlgHom.id_comp]
    exact ⟨g', e⟩
#align algebra.formally_smooth.exists_lift Algebra.FormallySmooth.exists_lift

/-- For a formally smooth `R`-algebra `A` and a map `f : A →ₐ[R] B ⧸ I` with `I` square-zero,
this is an arbitrary lift `A →ₐ[R] B`. -/
noncomputable def FormallySmooth.lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A →ₐ[R] B ⧸ I) : A →ₐ[R] B :=
  (FormallySmooth.exists_lift I hI g).some
#align algebra.formally_smooth.lift Algebra.FormallySmooth.lift

@[simp]
theorem FormallySmooth.comp_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A →ₐ[R] B ⧸ I) : (Ideal.Quotient.mkₐ R I).comp (FormallySmooth.lift I hI g) = g :=
  (FormallySmooth.exists_lift I hI g).choose_spec
#align algebra.formally_smooth.comp_lift Algebra.FormallySmooth.comp_lift

@[simp]
theorem FormallySmooth.mk_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A →ₐ[R] B ⧸ I) (x : A) : Ideal.Quotient.mk I (FormallySmooth.lift I hI g x) = g x :=
  AlgHom.congr_fun (FormallySmooth.comp_lift I hI g : _) x
#align algebra.formally_smooth.mk_lift Algebra.FormallySmooth.mk_lift

variable {C : Type u} [CommRing C] [Algebra R C]

/-- For a formally smooth `R`-algebra `A` and a map `f : A →ₐ[R] B ⧸ I` with `I` nilpotent,
this is an arbitrary lift `A →ₐ[R] B`. -/
noncomputable def FormallySmooth.liftOfSurjective [FormallySmooth R A] (f : A →ₐ[R] C)
    (g : B →ₐ[R] C) (hg : Function.Surjective g) (hg' : IsNilpotent (g : B →+* C).ker) :
    A →ₐ[R] B :=
  FormallySmooth.lift _ hg' ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f)
#align algebra.formally_smooth.lift_of_surjective Algebra.FormallySmooth.liftOfSurjective

@[simp]
theorem FormallySmooth.liftOfSurjective_apply [FormallySmooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (hg : Function.Surjective g) (hg' : IsNilpotent (g : B →+* C).ker) (x : A) :
    g (FormallySmooth.liftOfSurjective f g hg hg' x) = f x :=
  by
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).symm.Injective
  change _ = ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f) x
  rw [←
    formally_smooth.mk_lift _ hg' ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f)]
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).Injective
  rw [AlgEquiv.apply_symm_apply, Ideal.quotientKerAlgEquivOfSurjective,
    Ideal.quotientKerAlgEquivOfRightInverse.apply]
  exact (Ideal.kerLiftAlg_mk _ _).symm
#align algebra.formally_smooth.lift_of_surjective_apply Algebra.FormallySmooth.liftOfSurjective_apply

@[simp]
theorem FormallySmooth.comp_liftOfSurjective [FormallySmooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (hg : Function.Surjective g) (hg' : IsNilpotent (g : B →+* C).ker) :
    g.comp (FormallySmooth.liftOfSurjective f g hg hg') = f :=
  AlgHom.ext (FormallySmooth.liftOfSurjective_apply f g hg hg')
#align algebra.formally_smooth.comp_lift_of_surjective Algebra.FormallySmooth.comp_liftOfSurjective

end

section OfEquiv

variable {R : Type u} [CommSemiring R]

variable {A B : Type u} [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem FormallySmooth.of_equiv [FormallySmooth R A] (e : A ≃ₐ[R] B) : FormallySmooth R B :=
  by
  constructor
  intro C _ _ I hI f
  use (formally_smooth.lift I ⟨2, hI⟩ (f.comp e : A →ₐ[R] C ⧸ I)).comp e.symm
  rw [← AlgHom.comp_assoc, formally_smooth.comp_lift, AlgHom.comp_assoc, AlgEquiv.comp_symm,
    AlgHom.comp_id]
#align algebra.formally_smooth.of_equiv Algebra.FormallySmooth.of_equiv

theorem FormallyUnramified.of_equiv [FormallyUnramified R A] (e : A ≃ₐ[R] B) :
    FormallyUnramified R B := by
  constructor
  intro C _ _ I hI f₁ f₂ e'
  rw [← f₁.comp_id, ← f₂.comp_id, ← e.comp_symm, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
  congr 1
  refine' formally_unramified.comp_injective I hI _
  rw [← AlgHom.comp_assoc, e', AlgHom.comp_assoc]
#align algebra.formally_unramified.of_equiv Algebra.FormallyUnramified.of_equiv

theorem FormallyEtale.of_equiv [FormallyEtale R A] (e : A ≃ₐ[R] B) : FormallyEtale R B :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.of_equiv e, FormallySmooth.of_equiv e⟩
#align algebra.formally_etale.of_equiv Algebra.FormallyEtale.of_equiv

end OfEquiv

section Polynomial

open scoped Polynomial

variable (R : Type u) [CommSemiring R]

instance FormallySmooth.mvPolynomial (σ : Type u) : FormallySmooth R (MvPolynomial σ R) :=
  by
  constructor
  intro C _ _ I hI f
  have : ∀ s : σ, ∃ c : C, Ideal.Quotient.mk I c = f (MvPolynomial.X s) := fun s =>
    Ideal.Quotient.mk_surjective _
  choose g hg
  refine' ⟨MvPolynomial.aeval g, _⟩
  ext s
  rw [← hg, AlgHom.comp_apply, MvPolynomial.aeval_X]
  rfl
#align algebra.formally_smooth.mv_polynomial Algebra.FormallySmooth.mvPolynomial

instance FormallySmooth.polynomial : FormallySmooth R R[X] :=
  @FormallySmooth.of_equiv _ _ _ _ _ (FormallySmooth.mvPolynomial R PUnit)
    (MvPolynomial.pUnitAlgEquiv R)
#align algebra.formally_smooth.polynomial Algebra.FormallySmooth.polynomial

end Polynomial

section Comp

variable (R : Type u) [CommSemiring R]

variable (A : Type u) [CommSemiring A] [Algebra R A]

variable (B : Type u) [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem FormallySmooth.comp [FormallySmooth R A] [FormallySmooth A B] : FormallySmooth R B :=
  by
  constructor
  intro C _ _ I hI f
  obtain ⟨f', e⟩ := formally_smooth.comp_surjective I hI (f.comp (IsScalarTower.toAlgHom R A B))
  letI := f'.to_ring_hom.to_algebra
  obtain ⟨f'', e'⟩ :=
    formally_smooth.comp_surjective I hI { f.to_ring_hom with commutes' := AlgHom.congr_fun e.symm }
  apply_fun AlgHom.restrictScalars R at e' 
  exact ⟨f''.restrict_scalars _, e'.trans (AlgHom.ext fun _ => rfl)⟩
#align algebra.formally_smooth.comp Algebra.FormallySmooth.comp

theorem FormallyUnramified.comp [FormallyUnramified R A] [FormallyUnramified A B] :
    FormallyUnramified R B := by
  constructor
  intro C _ _ I hI f₁ f₂ e
  have e' :=
    formally_unramified.lift_unique I ⟨2, hI⟩ (f₁.comp <| IsScalarTower.toAlgHom R A B)
      (f₂.comp <| IsScalarTower.toAlgHom R A B) (by rw [← AlgHom.comp_assoc, e, AlgHom.comp_assoc])
  letI := (f₁.comp (IsScalarTower.toAlgHom R A B)).toRingHom.toAlgebra
  let F₁ : B →ₐ[A] C := { f₁ with commutes' := fun r => rfl }
  let F₂ : B →ₐ[A] C := { f₂ with commutes' := AlgHom.congr_fun e'.symm }
  ext1
  change F₁ x = F₂ x
  congr
  exact formally_unramified.ext I ⟨2, hI⟩ (AlgHom.congr_fun e)
#align algebra.formally_unramified.comp Algebra.FormallyUnramified.comp

theorem FormallyUnramified.of_comp [FormallyUnramified R B] : FormallyUnramified A B :=
  by
  constructor
  intro Q _ _ I e f₁ f₂ e'
  letI := ((algebraMap A Q).comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A Q := IsScalarTower.of_algebraMap_eq' rfl
  refine' AlgHom.restrictScalars_injective R _
  refine' formally_unramified.ext I ⟨2, e⟩ _
  intro x
  exact AlgHom.congr_fun e' x
#align algebra.formally_unramified.of_comp Algebra.FormallyUnramified.of_comp

theorem FormallyEtale.comp [FormallyEtale R A] [FormallyEtale A B] : FormallyEtale R B :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.comp R A B, FormallySmooth.comp R A B⟩
#align algebra.formally_etale.comp Algebra.FormallyEtale.comp

end Comp

section OfSurjective

variable {R S : Type u} [CommRing R] [CommSemiring S]

variable {P A : Type u} [CommRing A] [Algebra R A] [CommRing P] [Algebra R P]

variable (I : Ideal P) (f : P →ₐ[R] A) (hf : Function.Surjective f)

theorem FormallySmooth.of_split [FormallySmooth R P] (g : A →ₐ[R] P ⧸ f.toRingHom.ker ^ 2)
    (hg : f.kerSquareLift.comp g = AlgHom.id R A) : FormallySmooth R A :=
  by
  constructor
  intro C _ _ I hI i
  let l : P ⧸ f.to_ring_hom.ker ^ 2 →ₐ[R] C :=
    by
    refine' Ideal.Quotient.liftₐ _ (formally_smooth.lift I ⟨2, hI⟩ (i.comp f)) _
    have : RingHom.ker f ≤ I.comap (formally_smooth.lift I ⟨2, hI⟩ (i.comp f)) :=
      by
      rintro x (hx : f x = 0)
      have : _ = i (f x) := (formally_smooth.mk_lift I ⟨2, hI⟩ (i.comp f) x : _)
      rwa [hx, map_zero, ← Ideal.Quotient.mk_eq_mk, Submodule.Quotient.mk_eq_zero] at this 
    intro x hx
    have := (Ideal.pow_mono this 2).trans (Ideal.le_comap_pow _ 2) hx
    rwa [hI] at this 
  have : i.comp f.ker_square_lift = (Ideal.Quotient.mkₐ R _).comp l :=
    by
    apply AlgHom.coe_ringHom_injective
    apply Ideal.Quotient.ringHom_ext
    ext x
    exact (formally_smooth.mk_lift I ⟨2, hI⟩ (i.comp f) x).symm
  exact ⟨l.comp g, by rw [← AlgHom.comp_assoc, ← this, AlgHom.comp_assoc, hg, AlgHom.comp_id]⟩
#align algebra.formally_smooth.of_split Algebra.FormallySmooth.of_split

/-- Let `P →ₐ[R] A` be a surjection with kernel `J`, and `P` a formally smooth `R`-algebra,
then `A` is formally smooth over `R` iff the surjection `P ⧸ J ^ 2 →ₐ[R] A` has a section.

Geometric intuition: we require that a first-order thickening of `Spec A` inside `Spec P` admits
a retraction. -/
theorem FormallySmooth.iff_split_surjection [FormallySmooth R P] :
    FormallySmooth R A ↔ ∃ g, f.kerSquareLift.comp g = AlgHom.id R A :=
  by
  constructor
  · intro
    have surj : Function.Surjective f.ker_square_lift := fun x =>
      ⟨Submodule.Quotient.mk (hf x).some, (hf x).choose_spec⟩
    have sqz : RingHom.ker f.ker_square_lift.to_ring_hom ^ 2 = 0 := by
      rw [AlgHom.ker_ker_sqare_lift, Ideal.cotangentIdeal_square, Ideal.zero_eq_bot]
    refine'
      ⟨formally_smooth.lift _ ⟨2, sqz⟩ (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom,
        _⟩
    ext x
    have :=
      (Ideal.quotientKerAlgEquivOfSurjective surj).toAlgHom.congr_arg
        (formally_smooth.mk_lift _ ⟨2, sqz⟩
          (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom x)
    dsimp at this 
    rw [AlgEquiv.apply_symm_apply] at this 
    conv_rhs => rw [← this, AlgHom.id_apply]
    obtain ⟨y, e⟩ :=
      Ideal.Quotient.mk_surjective
        (formally_smooth.lift _ ⟨2, sqz⟩ (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom
          x)
    dsimp at e ⊢
    rw [← e]
    rfl
  · rintro ⟨g, hg⟩; exact formally_smooth.of_split f g hg
#align algebra.formally_smooth.iff_split_surjection Algebra.FormallySmooth.iff_split_surjection

end OfSurjective

section UnramifiedDerivation

open scoped TensorProduct

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

instance FormallyUnramified.subsingleton_kaehlerDifferential [FormallyUnramified R S] :
    Subsingleton (Ω[S⁄R]) := by
  rw [← not_nontrivial_iff_subsingleton]
  intro h
  obtain ⟨f₁, f₂, e⟩ := (KaehlerDifferential.endEquiv R S).Injective.Nontrivial
  apply e
  ext1
  apply formally_unramified.lift_unique' _ _ _ _ (f₁.2.trans f₂.2.symm)
  rw [← AlgHom.toRingHom_eq_coe, AlgHom.ker_ker_sqare_lift]
  exact ⟨_, Ideal.cotangentIdeal_square _⟩
#align algebra.formally_unramified.subsingleton_kaehler_differential Algebra.FormallyUnramified.subsingleton_kaehlerDifferential

theorem FormallyUnramified.iff_subsingleton_kaehlerDifferential :
    FormallyUnramified R S ↔ Subsingleton (Ω[S⁄R]) :=
  by
  constructor
  · intros; infer_instance
  · intro H
    constructor
    intro B _ _ I hI f₁ f₂ e
    letI := f₁.to_ring_hom.to_algebra
    haveI := IsScalarTower.of_algebraMap_eq' f₁.comp_algebra_map.symm
    have :=
      ((KaehlerDifferential.linearMapEquivDerivation R S).toEquiv.trans
            (derivationToSquareZeroEquivLift I hI)).Surjective.Subsingleton
    exact subtype.ext_iff.mp (@Subsingleton.elim this ⟨f₁, rfl⟩ ⟨f₂, e.symm⟩)
#align algebra.formally_unramified.iff_subsingleton_kaehler_differential Algebra.FormallyUnramified.iff_subsingleton_kaehlerDifferential

end UnramifiedDerivation

section BaseChange

open scoped TensorProduct

variable {R : Type u} [CommSemiring R]

variable {A : Type u} [Semiring A] [Algebra R A]

variable (B : Type u) [CommSemiring B] [Algebra R B]

instance FormallyUnramified.base_change [FormallyUnramified R A] :
    FormallyUnramified B (B ⊗[R] A) := by
  constructor
  intro C _ _ I hI f₁ f₂ e
  letI := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  apply AlgHom.restrictScalars_injective R
  apply TensorProduct.ext
  any_goals infer_instance
  intro b a
  have : b ⊗ₜ[R] a = b • 1 ⊗ₜ a := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [this, AlgHom.restrictScalars_apply, AlgHom.restrictScalars_apply, map_smul, map_smul]
  congr 1
  change
    ((f₁.restrict_scalars R).comp tensor_product.include_right) a =
      ((f₂.restrict_scalars R).comp tensor_product.include_right) a
  congr 1
  refine' formally_unramified.ext I ⟨2, hI⟩ _
  intro x
  exact AlgHom.congr_fun e (1 ⊗ₜ x)
#align algebra.formally_unramified.base_change Algebra.FormallyUnramified.base_change

instance FormallySmooth.base_change [FormallySmooth R A] : FormallySmooth B (B ⊗[R] A) :=
  by
  constructor
  intro C _ _ I hI f
  letI := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  refine' ⟨tensor_product.product_left_alg_hom (Algebra.ofId B C) _, _⟩
  · exact formally_smooth.lift I ⟨2, hI⟩ ((f.restrict_scalars R).comp tensor_product.include_right)
  · apply AlgHom.restrictScalars_injective R
    apply TensorProduct.ext
    any_goals infer_instance
    intro b a
    suffices algebraMap B _ b * f (1 ⊗ₜ[R] a) = f (b ⊗ₜ[R] a) by simpa [Algebra.ofId_apply]
    rw [← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
#align algebra.formally_smooth.base_change Algebra.FormallySmooth.base_change

instance FormallyEtale.base_change [FormallyEtale R A] : FormallyEtale B (B ⊗[R] A) :=
  FormallyEtale.iff_unramified_and_smooth.mpr ⟨inferInstance, inferInstance⟩
#align algebra.formally_etale.base_change Algebra.FormallyEtale.base_change

end BaseChange

section Localization

variable {R S Rₘ Sₘ : Type u} [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]

variable (M : Submonoid R)

variable [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]

variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]

variable [IsLocalization M Rₘ] [IsLocalization (M.map (algebraMap R S)) Sₘ]

attribute [local elab_as_elim] Ideal.IsNilpotent.induction_on

theorem FormallySmooth.of_isLocalization : FormallySmooth R Rₘ :=
  by
  constructor
  intro Q _ _ I e f
  have : ∀ x : M, IsUnit (algebraMap R Q x) := by
    intro x
    apply (IsNilpotent.isUnit_quotient_mk_iff ⟨2, e⟩).mp
    convert (IsLocalization.map_units Rₘ x).map f
    simp only [Ideal.Quotient.mk_algebraMap, AlgHom.commutes]
  let this.1 : Rₘ →ₐ[R] Q :=
    { IsLocalization.lift this with commutes' := IsLocalization.lift_eq this }
  use this
  apply AlgHom.coe_ringHom_injective
  refine' IsLocalization.ringHom_ext M _
  ext
  simp
#align algebra.formally_smooth.of_is_localization Algebra.FormallySmooth.of_isLocalization

/-- This holds in general for epimorphisms. -/
theorem FormallyUnramified.of_isLocalization : FormallyUnramified R Rₘ :=
  by
  constructor
  intro Q _ _ I e f₁ f₂ e
  apply AlgHom.coe_ringHom_injective
  refine' IsLocalization.ringHom_ext M _
  ext
  simp
#align algebra.formally_unramified.of_is_localization Algebra.FormallyUnramified.of_isLocalization

theorem FormallyEtale.of_isLocalization : FormallyEtale R Rₘ :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.of_isLocalization M, FormallySmooth.of_isLocalization M⟩
#align algebra.formally_etale.of_is_localization Algebra.FormallyEtale.of_isLocalization

theorem FormallySmooth.localization_base [FormallySmooth R Sₘ] : FormallySmooth Rₘ Sₘ :=
  by
  constructor
  intro Q _ _ I e f
  letI := ((algebraMap Rₘ Q).comp (algebraMap R Rₘ)).toAlgebra
  letI : IsScalarTower R Rₘ Q := IsScalarTower.of_algebraMap_eq' rfl
  let f : Sₘ →ₐ[Rₘ] Q :=
    by
    refine' { formally_smooth.lift I ⟨2, e⟩ (f.restrict_scalars R) with commutes' := _ }
    intro r
    change
      (RingHom.comp (formally_smooth.lift I ⟨2, e⟩ (f.restrict_scalars R) : Sₘ →+* Q)
            (algebraMap _ _))
          r =
        algebraMap _ _ r
    congr 1
    refine' IsLocalization.ringHom_ext M _
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq,
      AlgHom.comp_algebraMap]
  use f
  ext
  simp
#align algebra.formally_smooth.localization_base Algebra.FormallySmooth.localization_base

/-- This actually does not need the localization instance, and is stated here again for
consistency. See `algebra.formally_unramified.of_comp` instead.

 The intended use is for copying proofs between `formally_{unramified, smooth, etale}`
 without the need to change anything (including removing redundant arguments). -/
@[nolint unused_arguments]
theorem FormallyUnramified.localization_base [FormallyUnramified R Sₘ] : FormallyUnramified Rₘ Sₘ :=
  FormallyUnramified.of_comp R Rₘ Sₘ
#align algebra.formally_unramified.localization_base Algebra.FormallyUnramified.localization_base

theorem FormallyEtale.localization_base [FormallyEtale R Sₘ] : FormallyEtale Rₘ Sₘ :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.localization_base M, FormallySmooth.localization_base M⟩
#align algebra.formally_etale.localization_base Algebra.FormallyEtale.localization_base

theorem FormallySmooth.localization_map [FormallySmooth R S] : FormallySmooth Rₘ Sₘ :=
  by
  haveI : formally_smooth S Sₘ := formally_smooth.of_is_localization (M.map (algebraMap R S))
  haveI : formally_smooth R Sₘ := formally_smooth.comp R S Sₘ
  exact formally_smooth.localization_base M
#align algebra.formally_smooth.localization_map Algebra.FormallySmooth.localization_map

theorem FormallyUnramified.localization_map [FormallyUnramified R S] : FormallyUnramified Rₘ Sₘ :=
  by
  haveI : formally_unramified S Sₘ :=
    formally_unramified.of_is_localization (M.map (algebraMap R S))
  haveI : formally_unramified R Sₘ := formally_unramified.comp R S Sₘ
  exact formally_unramified.localization_base M
#align algebra.formally_unramified.localization_map Algebra.FormallyUnramified.localization_map

theorem FormallyEtale.localization_map [FormallyEtale R S] : FormallyEtale Rₘ Sₘ :=
  by
  haveI : formally_etale S Sₘ := formally_etale.of_is_localization (M.map (algebraMap R S))
  haveI : formally_etale R Sₘ := formally_etale.comp R S Sₘ
  exact formally_etale.localization_base M
#align algebra.formally_etale.localization_map Algebra.FormallyEtale.localization_map

end Localization

end Algebra

