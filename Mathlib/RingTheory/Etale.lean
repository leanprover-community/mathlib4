/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.QuotientNilpotent
import Mathlib.RingTheory.Kaehler
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.LocalProperties
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Flat.Basic
import Mathlib.FieldTheory.PurelyInseparable
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Data.Polynomial.Taylor

#align_import ring_theory.etale from "leanprover-community/mathlib"@"73f96237417835f148a1f7bc1ff55f67119b7166"

/-!

# Formally étale morphisms

An `R`-algebra `A` is formally étale (resp. unramified, smooth) if for every `R`-algebra,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
exactly (resp. at most, at least) one lift `A →ₐ[R] B`.

We show that the property extends onto nilpotent ideals, and that these properties are stable
under `R`-algebra homomorphisms and compositions.

-/


-- Porting note: added to make the syntax work below.
open scoped TensorProduct

universe u

namespace Algebra

section

variable (R : Type u) [CommSemiring R]
variable (A : Type u) [Semiring A] [Algebra R A]
variable {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B)

/-- An `R`-algebra `A` is formally unramified if for every `R`-algebra, every square-zero ideal
`I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at most one lift `A →ₐ[R] B`. -/
@[mk_iff]
class FormallyUnramified : Prop where
  comp_injective :
    ∀ ⦃B : Type u⦄ [CommRing B],
      ∀ [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
        Function.Injective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)
#align algebra.formally_unramified Algebra.FormallyUnramified

/-- An `R` algebra `A` is formally smooth if for every `R`-algebra, every square-zero ideal
`I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at least one lift `A →ₐ[R] B`. -/
@[mk_iff]
class FormallySmooth : Prop where
  comp_surjective :
    ∀ ⦃B : Type u⦄ [CommRing B],
      ∀ [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
        Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)
#align algebra.formally_smooth Algebra.FormallySmooth

/-- An `R` algebra `A` is formally étale if for every `R`-algebra, every square-zero ideal
`I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists exactly one lift `A →ₐ[R] B`. -/
@[mk_iff]
class FormallyEtale : Prop where
  comp_bijective :
    ∀ ⦃B : Type u⦄ [CommRing B],
      ∀ [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
        Function.Bijective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)
#align algebra.formally_etale Algebra.FormallyEtale

variable {R A}

theorem FormallyEtale.iff_unramified_and_smooth :
    FormallyEtale R A ↔ FormallyUnramified R A ∧ FormallySmooth R A := by
  rw [formallyUnramified_iff, formallySmooth_iff, formallyEtale_iff]
  simp_rw [← forall_and, Function.Bijective]
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
    (h : (Ideal.Quotient.mkₐ R I).comp g₁ = (Ideal.Quotient.mkₐ R I).comp g₂) : g₁ = g₂ := by
  revert g₁ g₂
  change Function.Injective (Ideal.Quotient.mkₐ R I).comp
  revert _RB
  apply Ideal.IsNilpotent.induction_on (R := B) I hI
  · intro B _ I hI _; exact FormallyUnramified.comp_injective I hI
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
    (f : B →+* C) (hf : IsNilpotent <| RingHom.ker f) (g₁ g₂ : A →ₐ[R] B)
    (h : f.comp ↑g₁ = f.comp (g₂ : A →+* B)) : g₁ = g₂ :=
  FormallyUnramified.lift_unique _ hf _ _
    (by
      ext x
      have := RingHom.congr_fun h x
      simpa only [Ideal.Quotient.eq, Function.comp_apply, AlgHom.coe_comp, Ideal.Quotient.mkₐ_eq_mk,
        RingHom.mem_ker, map_sub, sub_eq_zero])
#align algebra.formally_unramified.lift_unique_of_ring_hom Algebra.FormallyUnramified.lift_unique_of_ringHom

theorem FormallyUnramified.ext' [FormallyUnramified R A] {C : Type u} [CommRing C] (f : B →+* C)
    (hf : IsNilpotent <| RingHom.ker f) (g₁ g₂ : A →ₐ[R] B) (h : ∀ x, f (g₁ x) = f (g₂ x)) :
    g₁ = g₂ :=
  FormallyUnramified.lift_unique_of_ringHom f hf g₁ g₂ (RingHom.ext h)
#align algebra.formally_unramified.ext' Algebra.FormallyUnramified.ext'

theorem FormallyUnramified.lift_unique' [FormallyUnramified R A] {C : Type u} [CommRing C]
    [Algebra R C] (f : B →ₐ[R] C) (hf : IsNilpotent <| RingHom.ker (f : B →+* C))
    (g₁ g₂ : A →ₐ[R] B) (h : f.comp g₁ = f.comp g₂) : g₁ = g₂ :=
  FormallyUnramified.ext' _ hf g₁ g₂ (AlgHom.congr_fun h)
#align algebra.formally_unramified.lift_unique' Algebra.FormallyUnramified.lift_unique'

theorem FormallySmooth.exists_lift {B : Type u} [CommRing B] [_RB : Algebra R B]
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
noncomputable def FormallySmooth.lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A →ₐ[R] B ⧸ I) : A →ₐ[R] B :=
  (FormallySmooth.exists_lift I hI g).choose
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
    (g : B →ₐ[R] C) (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker (g : B →+* C)) :
    A →ₐ[R] B :=
  FormallySmooth.lift _ hg' ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f)
#align algebra.formally_smooth.lift_of_surjective Algebra.FormallySmooth.liftOfSurjective

@[simp]
theorem FormallySmooth.liftOfSurjective_apply [FormallySmooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
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
theorem FormallySmooth.comp_liftOfSurjective [FormallySmooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker (g : B →+* C)) :
    g.comp (FormallySmooth.liftOfSurjective f g hg hg') = f :=
  AlgHom.ext (FormallySmooth.liftOfSurjective_apply f g hg hg')
#align algebra.formally_smooth.comp_lift_of_surjective Algebra.FormallySmooth.comp_liftOfSurjective

end

section OfEquiv

variable {R : Type u} [CommSemiring R]
variable {A B : Type u} [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem FormallySmooth.of_equiv [FormallySmooth R A] (e : A ≃ₐ[R] B) : FormallySmooth R B := by
  constructor
  intro C _ _ I hI f
  use (FormallySmooth.lift I ⟨2, hI⟩ (f.comp e : A →ₐ[R] C ⧸ I)).comp e.symm
  rw [← AlgHom.comp_assoc, FormallySmooth.comp_lift, AlgHom.comp_assoc, AlgEquiv.comp_symm,
    AlgHom.comp_id]
#align algebra.formally_smooth.of_equiv Algebra.FormallySmooth.of_equiv

theorem FormallySmooth.iff_of_equiv (e : A ≃ₐ[R] B) : FormallySmooth R A ↔ FormallySmooth R B :=
  ⟨fun _ ↦ of_equiv e, fun _ ↦ of_equiv e.symm⟩

theorem FormallyUnramified.of_equiv [FormallyUnramified R A] (e : A ≃ₐ[R] B) :
    FormallyUnramified R B := by
  constructor
  intro C _ _ I hI f₁ f₂ e'
  rw [← f₁.comp_id, ← f₂.comp_id, ← e.comp_symm, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
  congr 1
  refine' FormallyUnramified.comp_injective I hI _
  rw [← AlgHom.comp_assoc, e', AlgHom.comp_assoc]
#align algebra.formally_unramified.of_equiv Algebra.FormallyUnramified.of_equiv

theorem FormallyUnramified.iff_of_equiv (e : A ≃ₐ[R] B) :
    FormallyUnramified R A ↔ FormallyUnramified R B :=
  ⟨fun _ ↦ of_equiv e, fun _ ↦ of_equiv e.symm⟩

theorem FormallyEtale.of_equiv [FormallyEtale R A] (e : A ≃ₐ[R] B) : FormallyEtale R B :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.of_equiv e, FormallySmooth.of_equiv e⟩
#align algebra.formally_etale.of_equiv Algebra.FormallyEtale.of_equiv

theorem FormallyEtale.iff_of_equiv (e : A ≃ₐ[R] B) : FormallyEtale R A ↔ FormallyEtale R B :=
  ⟨fun _ ↦ of_equiv e, fun _ ↦ of_equiv e.symm⟩

end OfEquiv

section Polynomial

open scoped Polynomial

variable (R : Type u) [CommSemiring R]

instance FormallySmooth.mvPolynomial (σ : Type u) : FormallySmooth R (MvPolynomial σ R) := by
  constructor
  intro C _ _ I _ f
  have : ∀ s : σ, ∃ c : C, Ideal.Quotient.mk I c = f (MvPolynomial.X s) := fun s =>
    Ideal.Quotient.mk_surjective _
  choose g hg using this
  refine' ⟨MvPolynomial.aeval g, _⟩
  ext s
  rw [← hg, AlgHom.comp_apply, MvPolynomial.aeval_X]
  rfl
#align algebra.formally_smooth.mv_polynomial Algebra.FormallySmooth.mvPolynomial

instance FormallySmooth.polynomial : FormallySmooth R R[X] :=
  FormallySmooth.of_equiv (MvPolynomial.pUnitAlgEquiv R)
#align algebra.formally_smooth.polynomial Algebra.FormallySmooth.polynomial

end Polynomial

section Comp

variable (R : Type u) [CommSemiring R]
variable (A : Type u) [CommSemiring A] [Algebra R A]
variable (B : Type u) [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem FormallySmooth.comp [FormallySmooth R A] [FormallySmooth A B] : FormallySmooth R B := by
  constructor
  intro C _ _ I hI f
  obtain ⟨f', e⟩ := FormallySmooth.comp_surjective I hI (f.comp (IsScalarTower.toAlgHom R A B))
  letI := f'.toRingHom.toAlgebra
  obtain ⟨f'', e'⟩ :=
    FormallySmooth.comp_surjective I hI { f.toRingHom with commutes' := AlgHom.congr_fun e.symm }
  apply_fun AlgHom.restrictScalars R at e'
  exact ⟨f''.restrictScalars _, e'.trans (AlgHom.ext fun _ => rfl)⟩
#align algebra.formally_smooth.comp Algebra.FormallySmooth.comp

theorem FormallyUnramified.comp [FormallyUnramified R A] [FormallyUnramified A B] :
    FormallyUnramified R B := by
  constructor
  intro C _ _ I hI f₁ f₂ e
  have e' :=
    FormallyUnramified.lift_unique I ⟨2, hI⟩ (f₁.comp <| IsScalarTower.toAlgHom R A B)
      (f₂.comp <| IsScalarTower.toAlgHom R A B) (by rw [← AlgHom.comp_assoc, e, AlgHom.comp_assoc])
  letI := (f₁.comp (IsScalarTower.toAlgHom R A B)).toRingHom.toAlgebra
  let F₁ : B →ₐ[A] C := { f₁ with commutes' := fun r => rfl }
  let F₂ : B →ₐ[A] C := { f₂ with commutes' := AlgHom.congr_fun e'.symm }
  ext1 x
  change F₁ x = F₂ x
  congr
  exact FormallyUnramified.ext I ⟨2, hI⟩ (AlgHom.congr_fun e)
#align algebra.formally_unramified.comp Algebra.FormallyUnramified.comp

theorem FormallyUnramified.of_comp [FormallyUnramified R B] : FormallyUnramified A B := by
  constructor
  intro Q _ _ I e f₁ f₂ e'
  letI := ((algebraMap A Q).comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A Q := IsScalarTower.of_algebraMap_eq' rfl
  refine' AlgHom.restrictScalars_injective R _
  refine' FormallyUnramified.ext I ⟨2, e⟩ _
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

theorem FormallySmooth.of_split [FormallySmooth R P] (g : A →ₐ[R] P ⧸ (RingHom.ker f.toRingHom) ^ 2)
    (hg : f.kerSquareLift.comp g = AlgHom.id R A) : FormallySmooth R A := by
  constructor
  intro C _ _ I hI i
  let l : P ⧸ (RingHom.ker f.toRingHom) ^ 2 →ₐ[R] C := by
    refine' Ideal.Quotient.liftₐ _ (FormallySmooth.lift I ⟨2, hI⟩ (i.comp f)) _
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
theorem FormallySmooth.iff_split_surjection [FormallySmooth R P] :
    FormallySmooth R A ↔ ∃ g, f.kerSquareLift.comp g = AlgHom.id R A := by
  constructor
  · intro
    have surj : Function.Surjective f.kerSquareLift := fun x =>
      ⟨Submodule.Quotient.mk (hf x).choose, (hf x).choose_spec⟩
    have sqz : RingHom.ker f.kerSquareLift.toRingHom ^ 2 = 0 := by
      rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square, Ideal.zero_eq_bot]
    refine'
      ⟨FormallySmooth.lift _ ⟨2, sqz⟩ (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom,
        _⟩
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

section UnramifiedDerivation

open scoped TensorProduct

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

instance FormallyUnramified.subsingleton_kaehlerDifferential [FormallyUnramified R S] :
    Subsingleton (Ω[S⁄R]) := by
  rw [← not_nontrivial_iff_subsingleton]
  intro h
  obtain ⟨f₁, f₂, e⟩ := (KaehlerDifferential.endEquiv R S).injective.nontrivial
  apply e
  ext1
  apply FormallyUnramified.lift_unique' _ _ _ _ (f₁.2.trans f₂.2.symm)
  rw [← AlgHom.toRingHom_eq_coe, AlgHom.ker_kerSquareLift]
  exact ⟨_, Ideal.cotangentIdeal_square _⟩
#align algebra.formally_unramified.subsingleton_kaehler_differential Algebra.FormallyUnramified.subsingleton_kaehlerDifferential

theorem FormallyUnramified.iff_subsingleton_kaehlerDifferential :
    FormallyUnramified R S ↔ Subsingleton (Ω[S⁄R]) := by
  constructor
  · intros; infer_instance
  · intro H
    constructor
    intro B _ _ I hI f₁ f₂ e
    letI := f₁.toRingHom.toAlgebra
    haveI := IsScalarTower.of_algebraMap_eq' f₁.comp_algebraMap.symm
    have :=
      ((KaehlerDifferential.linearMapEquivDerivation R S).toEquiv.trans
            (derivationToSquareZeroEquivLift I hI)).surjective.subsingleton
    exact Subtype.ext_iff.mp (@Subsingleton.elim _ this ⟨f₁, rfl⟩ ⟨f₂, e.symm⟩)
#align algebra.formally_unramified.iff_subsingleton_kaehler_differential Algebra.FormallyUnramified.iff_subsingleton_kaehlerDifferential

variable (R) (S) in
theorem KaehlerDifferential.ideal_fg [EssFiniteType R S] :
    (KaehlerDifferential.ideal R S).FG := by
  classical
  -- obtain ⟨s, hs⟩ := inst
  use (EssFiniteType.finset R S).image (fun s ↦ (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S))
  apply le_antisymm
  · rw [Finset.coe_image, Ideal.span_le]
    rintro _ ⟨x, _, rfl⟩
    exact KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R x
  · rw [← KaehlerDifferential.span_range_eq_ideal, Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    let I : Ideal (S ⊗[R] S) := Ideal.span
      ((EssFiniteType.finset R S).image (fun s ↦ (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)))
    show _ - _ ∈ I
    have : (IsScalarTower.toAlgHom R (S ⊗[R] S) (S ⊗[R] S ⧸ I)).comp TensorProduct.includeRight =
        (IsScalarTower.toAlgHom R (S ⊗[R] S) (S ⊗[R] S ⧸ I)).comp TensorProduct.includeLeft := by
      apply EssFiniteType.ext
      intro a ha
      simp only [AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', Ideal.Quotient.algebraMap_eq,
        Function.comp_apply, TensorProduct.includeLeft_apply, TensorProduct.includeRight_apply,
        Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      refine Ideal.subset_span ?_
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨a, ha, rfl⟩
    simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using AlgHom.congr_fun this x

theorem FormallyUnramified.iff_exists [EssFiniteType R S] :
    FormallyUnramified R S ↔ ∃ t : S ⊗[R] S,
      (∀ s, ((1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) * t = 0) ∧
      TensorProduct.lmul' R t = 1 := by
  have := KaehlerDifferential.ideal_fg R S
  rw [FormallyUnramified.iff_subsingleton_kaehlerDifferential, KaehlerDifferential,
    Ideal.cotangent_subsingleton_iff, Ideal.isIdempotentElem_iff_of_fg _
      (KaehlerDifferential.ideal_fg R S)]
  have : ∀ t : S ⊗[R] S, TensorProduct.lmul' R t = 1 ↔ 1 - t ∈ KaehlerDifferential.ideal R S := by
    intro t
    simp only [KaehlerDifferential.ideal, RingHom.mem_ker, map_sub, map_one,
      sub_eq_zero, @eq_comm S 1]
  simp_rw [this, ← KaehlerDifferential.span_range_eq_ideal]
  constructor
  · rintro ⟨e, he₁, he₂ : _ = Ideal.span _⟩
    refine ⟨1 - e, ?_, ?_⟩
    · intro s
      obtain ⟨x, hx⟩ : e ∣ 1 ⊗ₜ[R] s - s ⊗ₜ[R] 1 := by
        rw [← Ideal.mem_span_singleton, ← he₂]
        exact Ideal.subset_span ⟨s, rfl⟩
      rw [hx, mul_comm, ← mul_assoc, sub_mul, one_mul, he₁.eq, sub_self, zero_mul]
    · rw [sub_sub_cancel, he₂, Ideal.mem_span_singleton]
  · rintro ⟨t, ht₁, ht₂⟩
    use 1 - t
    rw [show t = 1 - (1 - t) by ring] at ht₁; generalize 1 - t = e at *
    constructor
    · suffices e * (1 - e) = 0 by
        simpa [IsIdempotentElem, mul_sub, sub_eq_zero, eq_comm] using this
      apply Submodule.span_induction (p := (· * (1 - e) = 0)) ht₂
      · simpa using ht₁
      · rw [zero_mul]
      · intro _ _ e₁ e₂; rw [add_mul, e₁, e₂, zero_add]
      · intros _ _ e; rw [smul_mul_assoc, e, smul_zero]
    · apply le_antisymm <;> simp only [Ideal.submodule_span_eq, Ideal.mem_span_singleton, ht₂,
        Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Set.range_subset_iff]
      intro s
      use 1 ⊗ₜ[R] s - s ⊗ₜ[R] 1
      simpa [mul_sub, sub_eq_zero, mul_comm e] using ht₁ s

variable (R) (S) in
/--
A finite-type `R`-algebra `S` is (formally) unramified iff there exists a `t : S ⊗[R] S` satisfying
1. `t` annihilates every `1 ⊗ s - s ⊗ 1`.
2. the image of `t` is `1` under the map `S ⊗[R] S → S`.
See `FormallyUnramified.iff_exists`.
This is the choice of such a `t`.
-/
noncomputable
def FormallyUnramified.elem [EssFiniteType R S] [FormallyUnramified R S] : S ⊗[R] S :=
  (FormallyUnramified.iff_exists.mp inferInstance).choose

lemma FormallyUnramified.one_tmul_sub_tmul_one_mul_elem [EssFiniteType R S] [FormallyUnramified R S]
    (s : S) : (1 ⊗ₜ s - s ⊗ₜ 1) * elem R S = 0 :=
  (FormallyUnramified.iff_exists.mp inferInstance).choose_spec.1 s

lemma FormallyUnramified.one_tmul_mul_elem [EssFiniteType R S] [FormallyUnramified R S]
    (s : S) : (1 ⊗ₜ s) * elem R S = (s ⊗ₜ 1) * elem R S := by
  rw [← sub_eq_zero, ← sub_mul, one_tmul_sub_tmul_one_mul_elem]

lemma FormallyUnramified.lmul_elem [EssFiniteType R S] [FormallyUnramified R S] :
    TensorProduct.lmul' R (elem R S) = 1 :=
  (FormallyUnramified.iff_exists.mp inferInstance).choose_spec.2

lemma Finsupp.uncurry_apply {α β M} [AddCommMonoid M] (f : α →₀ β →₀ M) (i j) :
    f.uncurry (i, j) = f i j := by
  obtain ⟨g, rfl⟩ := Finsupp.finsuppProdEquiv.surjective f
  show Finsupp.finsuppProdEquiv.symm (Finsupp.finsuppProdEquiv g) (i, j) = _
  rw [Equiv.symm_apply_apply, Finsupp.finsuppProdEquiv, Equiv.coe_fn_mk, Finsupp.curry_apply]

lemma FormallyUnramified.finite_of_free_aux (I) [DecidableEq I] (b : Basis I R S)
    (f : I →₀ S) (x : S) (a : I → I →₀ R) (ha : a = fun i ↦ b.repr (b i * x)) :
    (1 ⊗ₜ[R] x * Finsupp.sum f fun i y ↦ y ⊗ₜ[R] b i) =
      Finset.sum (f.support.biUnion fun i ↦ (a i).support) fun k ↦
    Finsupp.sum (b.repr (f.sum fun i y ↦ a i k • y)) fun j c ↦ c • b j ⊗ₜ[R] b k := by
  rw [Finsupp.sum, Finset.mul_sum]
  subst ha
  let a i := b.repr (b i * x)
  conv_lhs =>
    simp only [TensorProduct.tmul_mul_tmul, one_mul, mul_comm x (b _),
      ← show ∀ i, Finsupp.total _ _ _ b (a i) = b i * x from fun _ ↦ b.total_repr _]
  conv_lhs => simp only [Finsupp.total, Finsupp.coe_lsum,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, Finsupp.sum, TensorProduct.tmul_sum,
    ← TensorProduct.smul_tmul]
  have h₁ : ∀ k,
    (Finsupp.sum (Finsupp.sum f fun i y ↦ a i k • b.repr y) fun j z ↦ z • b j ⊗ₜ[R] b k) =
      (f.sum fun i y ↦ (b.repr y).sum fun j z ↦ a i k • z • b j ⊗ₜ[R] b k) := by
    intro i
    rw [Finsupp.sum_sum_index]
    congr
    ext j s
    rw [Finsupp.sum_smul_index]
    simp only [mul_smul, Finsupp.sum, ← Finset.smul_sum]
    · intro _; simp only [zero_smul]
    · intro _; simp only [zero_smul]
    · intro _ _ _; simp only [add_smul]
  have h₂ : ∀ (x : S), ((b.repr x).support.sum fun a ↦ b.repr x a • b a) = x := by
    simpa only [Finsupp.total_apply, Finsupp.sum] using b.total_repr
  simp_rw [map_finsupp_sum, map_smul, h₁, Finsupp.sum, Finset.sum_comm (t := f.support),
    TensorProduct.smul_tmul', ← TensorProduct.sum_tmul, ← Finset.smul_sum, h₂]
  apply Finset.sum_congr rfl
  intros i hi
  apply Finset.sum_subset_zero_on_sdiff
  · exact Finset.subset_biUnion_of_mem (fun i ↦ (a i).support) hi
  · simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finsupp.mem_support_iff, ne_eq, not_not,
      and_imp, forall_exists_index]
    intro j k _ _ h₃
    simp [h₃]
  · exact fun _ _ ↦ rfl

lemma FormallyUnramified.finite_of_free [EssFiniteType R S] [Module.Free R S]
    [FormallyUnramified R S] : Module.Finite R S := by
  classical
  let I := Module.Free.ChooseBasisIndex R S
  let b : Basis I R S := Module.Free.chooseBasis R S
  have ⟨f, hf⟩ : ∃ (a : I →₀ S), elem R S = a.sum (fun i x ↦ x ⊗ₜ b i) := by
    induction' elem R S using TensorProduct.induction_on with x y x y hx hy
    · exact ⟨0, by simp⟩
    · refine ⟨Finsupp.mapRange (· • x) (by simp) (b.repr y), ?_⟩
      simp only [TensorProduct.zero_tmul, implies_true, Finsupp.sum_mapRange_index]
      simp_rw [TensorProduct.smul_tmul, Finsupp.sum, ← TensorProduct.tmul_sum]
      congr 1
      exact (b.total_repr y).symm
    · obtain ⟨ax, hx⟩ := hx
      obtain ⟨ay, hy⟩ := hy
      refine ⟨ax + ay, ?_⟩
      rw [Finsupp.sum_add_index, hx, hy]
      · simp
      · simp [TensorProduct.add_tmul]
  constructor
  use Finset.image₂ (fun i j ↦ f i * b j) f.support f.support
  rw [← top_le_iff]
  rintro x -
  let a : I → I →₀ R := fun i ↦ b.repr (b i * x)
  let F₁ : I →₀ I →₀ R := Finsupp.onFinset f.support (fun j ↦ b.repr (x * f j))
    (fun j ↦ not_imp_comm.mp fun hj ↦ by simp [Finsupp.not_mem_support_iff.mp hj])
  have hF₂ : ∀ j ∉ (Finset.biUnion f.support fun i ↦ (a i).support),
      b.repr (f.sum (fun i y ↦ a i j • y)) = 0 := by
    intros j hj
    simp only [Finset.mem_biUnion, Finsupp.mem_support_iff, ne_eq, not_exists, not_and,
      not_not] at hj
    simp only [Finsupp.sum]
    trans b.repr (f.support.sum (fun _ ↦ 0))
    · refine congr_arg b.repr (Finset.sum_congr rfl ?_)
      simp only [Finsupp.mem_support_iff]
      intro i hi
      rw [hj i hi, zero_smul]
    · simp only [Finset.sum_const_zero, map_zero]
  let F₂ : I →₀ I →₀ R := Finsupp.onFinset (Finset.biUnion f.support (fun i ↦ (a i).support))
    (fun j ↦ b.repr (f.sum (fun i y ↦ a i j • y)))
    (fun j ↦ not_imp_comm.mp (hF₂ j))
  have : F₁ = F₂ := by
    apply Finsupp.finsuppProdEquiv.symm.injective
    apply (Finsupp.equivCongrLeft (Equiv.prodComm I I)).injective
    apply (b.tensorProduct b).repr.symm.injective
    simp only [Basis.repr_symm_apply, Finsupp.coe_lsum, LinearMap.coe_smulRight,
      LinearMap.id_coe, id_eq, Basis.tensorProduct_apply, Finsupp.finsuppProdEquiv,
      Equiv.coe_fn_symm_mk, Finsupp.uncurry, map_finsupp_sum,
      Finsupp.total_single, Basis.tensorProduct_apply, Finsupp.equivCongrLeft_apply,
      Finsupp.total_equivMapDomain, Equiv.coe_prodComm]
    rw [Finsupp.onFinset_sum, Finsupp.onFinset_sum]
    simp only [Function.comp_apply, Prod.swap_prod_mk, Basis.tensorProduct_apply]
    have : ∀ i, ((b.repr (x * f i)).sum fun j k ↦ k • b j ⊗ₜ[R] b i) = (x * f i) ⊗ₜ[R] b i := by
      intro i
      simp_rw [Finsupp.sum, TensorProduct.smul_tmul', ← TensorProduct.sum_tmul]
      congr 1
      exact b.total_repr _
    trans (x ⊗ₜ 1) * elem R S
    · simp_rw [this, hf, Finsupp.sum, Finset.mul_sum, TensorProduct.tmul_mul_tmul, one_mul]
    · rw [← one_tmul_mul_elem, hf, finite_of_free_aux]
      rfl
    · intro _; simp
    · intro _; simp
  have : ∀ j, x * f j = f.sum fun i y ↦ a i j • y := by
    intro j
    apply b.repr.injective
    exact DFunLike.congr_fun this j
  rw [← mul_one x, ← @lmul_elem R, hf, map_finsupp_sum, Finsupp.sum, Finset.mul_sum]
  simp only [TensorProduct.lmul'_apply_tmul, Finset.coe_image₂, ← mul_assoc, this,
    Finsupp.sum, Finset.sum_mul, smul_mul_assoc]
  apply Submodule.sum_mem; intro i hi
  apply Submodule.sum_mem; intro j hj
  apply Submodule.smul_mem
  apply Submodule.subset_span
  use j, hj, i, hi




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
  ext : 1
  · exact Subsingleton.elim _ _
  · exact FormallyUnramified.ext I ⟨2, hI⟩ fun x => AlgHom.congr_fun e (1 ⊗ₜ x)
#align algebra.formally_unramified.base_change Algebra.FormallyUnramified.base_change

instance FormallySmooth.base_change [FormallySmooth R A] : FormallySmooth B (B ⊗[R] A) := by
  constructor
  intro C _ _ I hI f
  letI := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  refine' ⟨TensorProduct.productLeftAlgHom (Algebra.ofId B C) _, _⟩
  · exact FormallySmooth.lift I ⟨2, hI⟩ ((f.restrictScalars R).comp TensorProduct.includeRight)
  · apply AlgHom.restrictScalars_injective R
    apply TensorProduct.ext'
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

-- Porting note: no longer supported
-- attribute [local elab_as_elim] Ideal.IsNilpotent.induction_on

theorem FormallySmooth.of_isLocalization : FormallySmooth R Rₘ := by
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
  refine' IsLocalization.ringHom_ext M _
  ext
  simp
#align algebra.formally_smooth.of_is_localization Algebra.FormallySmooth.of_isLocalization

/-- This holds in general for epimorphisms. -/
theorem FormallyUnramified.of_isLocalization : FormallyUnramified R Rₘ := by
  constructor
  intro Q _ _ I _ f₁ f₂ _
  apply AlgHom.coe_ringHom_injective
  refine' IsLocalization.ringHom_ext M _
  ext
  simp
#align algebra.formally_unramified.of_is_localization Algebra.FormallyUnramified.of_isLocalization

/-- This holds in general for epimorphisms. -/
theorem FormallyUnramified.of_surjective (H : Function.Surjective (algebraMap R S)) :
    FormallyUnramified R S := by
  constructor
  intro Q _ _ I _ f₁ f₂ _
  ext x
  obtain ⟨x, rfl⟩ := H x
  rw [algebraMap_eq_smul_one, map_smul, map_smul, map_one, map_one]

instance FormallyUnramified.quotient (I : Ideal R) : FormallyUnramified R (R ⧸ I) :=
    FormallyUnramified.of_surjective Ideal.Quotient.mk_surjective

theorem FormallyEtale.of_isLocalization : FormallyEtale R Rₘ :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.of_isLocalization M, FormallySmooth.of_isLocalization M⟩
#align algebra.formally_etale.of_is_localization Algebra.FormallyEtale.of_isLocalization

theorem FormallySmooth.localization_base [FormallySmooth R Sₘ] : FormallySmooth Rₘ Sₘ := by
  constructor
  intro Q _ _ I e f
  letI := ((algebraMap Rₘ Q).comp (algebraMap R Rₘ)).toAlgebra
  letI : IsScalarTower R Rₘ Q := IsScalarTower.of_algebraMap_eq' rfl
  let f : Sₘ →ₐ[Rₘ] Q := by
    refine' { FormallySmooth.lift I ⟨2, e⟩ (f.restrictScalars R) with commutes' := _ }
    intro r
    change
      (RingHom.comp (FormallySmooth.lift I ⟨2, e⟩ (f.restrictScalars R) : Sₘ →+* Q)
            (algebraMap _ _))
          r =
        algebraMap _ _ r
    congr 1
    refine' IsLocalization.ringHom_ext M _
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq,
      AlgHom.comp_algebraMap]
  use f
  ext
  simp [f]
#align algebra.formally_smooth.localization_base Algebra.FormallySmooth.localization_base

/-- This actually does not need the localization instance, and is stated here again for
consistency. See `Algebra.FormallyUnramified.of_comp` instead.

 The intended use is for copying proofs between `Formally{Unramified, Smooth, Etale}`
 without the need to change anything (including removing redundant arguments). -/
-- @[nolint unusedArguments] -- Porting note: removed
theorem FormallyUnramified.localization_base [FormallyUnramified R Sₘ] : FormallyUnramified Rₘ Sₘ :=
  -- Porting note: added
  let _ := M
  FormallyUnramified.of_comp R Rₘ Sₘ
#align algebra.formally_unramified.localization_base Algebra.FormallyUnramified.localization_base

theorem FormallyEtale.localization_base [FormallyEtale R Sₘ] : FormallyEtale Rₘ Sₘ :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.localization_base M, FormallySmooth.localization_base M⟩
#align algebra.formally_etale.localization_base Algebra.FormallyEtale.localization_base

theorem FormallySmooth.localization_map [FormallySmooth R S] : FormallySmooth Rₘ Sₘ := by
  haveI : FormallySmooth S Sₘ := FormallySmooth.of_isLocalization (M.map (algebraMap R S))
  haveI : FormallySmooth R Sₘ := FormallySmooth.comp R S Sₘ
  exact FormallySmooth.localization_base M
#align algebra.formally_smooth.localization_map Algebra.FormallySmooth.localization_map

theorem FormallyUnramified.localization_map [FormallyUnramified R S] :
    FormallyUnramified Rₘ Sₘ := by
  haveI : FormallyUnramified S Sₘ :=
    FormallyUnramified.of_isLocalization (M.map (algebraMap R S))
  haveI : FormallyUnramified R Sₘ := FormallyUnramified.comp R S Sₘ
  exact FormallyUnramified.localization_base M
#align algebra.formally_unramified.localization_map Algebra.FormallyUnramified.localization_map

theorem FormallyEtale.localization_map [FormallyEtale R S] : FormallyEtale Rₘ Sₘ := by
  haveI : FormallyEtale S Sₘ := FormallyEtale.of_isLocalization (M.map (algebraMap R S))
  haveI : FormallyEtale R Sₘ := FormallyEtale.comp R S Sₘ
  exact FormallyEtale.localization_base M
#align algebra.formally_etale.localization_map Algebra.FormallyEtale.localization_map

end Localization

section Field

variable (K L : Type u) {A : Type u} [Field K] [Field L] [CommRing A] [Algebra K A] [Algebra K L]
variable [EssFiniteType K A]

open BigOperators Polynomial Finset

theorem Polynomial.eval_add_of_sq_eq_zero (p : Polynomial A) (x y : A) (hy : y ^ 2 = 0) :
    p.eval (x + y) = p.eval x + p.derivative.eval x * y := by
  rw [add_comm, ← Polynomial.taylor_eval,
    Polynomial.eval_eq_sum_range' ((Nat.lt_succ_self _).trans (Nat.lt_succ_self _)),
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp [pow_succ, ← mul_assoc, ← pow_two, hy, add_comm (eval x p)]

theorem FormallyUnramified.of_isSeparable [IsSeparable K L] : FormallyUnramified K L := by
  constructor
  intros B _ _ I hI f₁ f₂ e
  ext x
  have : f₁ x - f₂ x ∈ I := by
    simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using AlgHom.congr_fun e x
  have := Polynomial.eval_add_of_sq_eq_zero ((minpoly K x).map (algebraMap K B)) (f₂ x)
    (f₁ x - f₂ x) (by convert show (f₁ x - f₂ x) ^ 2 ∈ ⊥ from hI ▸ Ideal.pow_mem_pow this 2)
  simp only [add_sub_cancel, eval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero,
    derivative_map, zero_add] at this
  rwa [eq_comm, ((isUnit_iff_ne_zero.mpr ((IsSeparable.separable K x).aeval_derivative_ne_zero
    (minpoly.aeval K x))).map f₂).mul_right_eq_zero, sub_eq_zero] at this

theorem FormallyEtale.of_isSeparable_aux [IsSeparable K L] [EssFiniteType K L] :
    FormallyEtale K L := by
  have := FormallyUnramified.of_isSeparable K L
  have := FormallyUnramified.finite_of_free (R := K) (S := L)
  constructor
  intros B _ _ I h
  refine ⟨(FormallyUnramified.of_isSeparable K L).1 I h, ?_⟩
  intro f
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (f pb.gen)
  have helper : ∀ x, IsScalarTower.toAlgHom K B (B ⧸ I) x = Ideal.Quotient.mk I x := fun _ ↦ rfl
  have hx' : Ideal.Quotient.mk I (aeval x (minpoly K pb.gen)) = 0 := by
    rw [← helper, ← aeval_algHom_apply, helper, hx, aeval_algHom_apply, minpoly.aeval, map_zero]
  obtain ⟨u, hu⟩ : ∃ u, (aeval x) (derivative (minpoly K pb.gen)) * u + 1 ∈ I := by
    have := (isUnit_iff_ne_zero.mpr ((IsSeparable.separable K pb.gen).aeval_derivative_ne_zero
      (minpoly.aeval K _))).map f
    rw [← aeval_algHom_apply, ← hx, ← helper, aeval_algHom_apply, helper] at this
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (-this.unit⁻¹ : B ⧸ I)
    use u
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_mul, map_one, hu, mul_neg,
      IsUnit.mul_val_inv, add_left_neg]
  use pb.liftEquiv.symm ⟨x + u * aeval x (minpoly K pb.gen), ?_⟩
  · apply pb.algHom_ext
    simp [hx, hx']
  · rw [← eval_map_algebraMap, Polynomial.eval_add_of_sq_eq_zero, derivative_map,
      ← one_mul (eval x _), eval_map_algebraMap, eval_map_algebraMap, ← mul_assoc, ← add_mul,
      ← Ideal.mem_bot, ← h, pow_two, add_comm]
    exact Ideal.mul_mem_mul hu (Ideal.Quotient.eq_zero_iff_mem.mp hx')
    rw [← Ideal.mem_bot, ← h]
    apply Ideal.pow_mem_pow
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hx', mul_zero]

open scoped IntermediateField in
instance FormallyEtale.of_isSeparable [IsSeparable K L] : FormallyEtale K L := by
  constructor
  intros B _ _ I h
  refine ⟨(FormallyUnramified.of_isSeparable K L).1 I h, ?_⟩
  intro f
  have : ∀ k : L, ∃! g : K⟮k⟯ →ₐ[K] B,
      (Ideal.Quotient.mkₐ K I).comp g = f.comp (IsScalarTower.toAlgHom K _ L) := by
    intro k
    have := IsSeparable.of_algHom _ _ (IsScalarTower.toAlgHom K (K⟮k⟯) L)
    have := IntermediateField.adjoin.finiteDimensional (IsSeparable.separable K k).isIntegral
    have := FormallyEtale.of_isSeparable_aux K (K⟮k⟯)
    have := FormallyEtale.comp_bijective (R := K) (A := K⟮k⟯) I h
    exact this.existsUnique _
  choose g hg₁ hg₂ using this
  have hg₃ : ∀ x y (h : x ∈ K⟮y⟯), g y ⟨x, h⟩ = g x (IntermediateField.AdjoinSimple.gen K x) := by
    intro x y h
    have e : K⟮x⟯ ≤ K⟮y⟯ := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact h
    rw [← hg₂ _ ((g _).comp (IntermediateField.inclusion e))]
    rfl
    simp_rw [← AlgHom.comp_assoc, hg₁, AlgHom.comp_assoc]
    apply AlgHom.ext
    intro ⟨a, _⟩
    simp
  have H : ∀ x y : L, ∃ α : L, x ∈ K⟮α⟯ ∧ y ∈ K⟮α⟯ := by
    intro x y
    have : FiniteDimensional K K⟮x, y⟯ := by
      apply IntermediateField.finiteDimensional_adjoin
      intro x _; exact (IsSeparable.separable K x).isIntegral
    have := IsSeparable.of_algHom _ _ (IsScalarTower.toAlgHom K (K⟮x, y⟯) L)
    obtain ⟨⟨α, hα⟩, e⟩ := Field.exists_primitive_element K K⟮x,y⟯
    apply_fun (IntermediateField.map (IntermediateField.val _)) at e
    rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map] at e
    simp only [IntermediateField.coe_val, Set.image_singleton,
      IntermediateField.fieldRange_val] at e
    have hx : x ∈ K⟮α⟯ := e ▸ IntermediateField.subset_adjoin K {x, y} (by simp)
    have hy : y ∈ K⟮α⟯ := e ▸ IntermediateField.subset_adjoin K {x, y} (by simp)
    exact ⟨α, hx, hy⟩
  refine ⟨⟨⟨⟨⟨fun x ↦ g x (IntermediateField.AdjoinSimple.gen K x), ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩
  · show g 1 1 = 1; rw [map_one]
  · intros x y
    obtain ⟨α, hx, hy⟩ := H x y
    simp only [← hg₃ _ _ hx, ← hg₃ _ _ hy, ← map_mul, ← hg₃ _ _ (mul_mem hx hy)]
    rfl
  · show g 0 0 = 0; rw [map_zero]
  · intros x y
    obtain ⟨α, hx, hy⟩ := H x y
    simp only [← hg₃ _ _ hx, ← hg₃ _ _ hy, ← map_add, ← hg₃ _ _ (add_mem hx hy)]
    rfl
  · intro r
    show g _ (algebraMap K _ r) = _
    rw [AlgHom.commutes]
  · ext x
    simpa using AlgHom.congr_fun (hg₁ x) (IntermediateField.AdjoinSimple.gen K x)

/-- If `B` is an unramified `A`-algebra, and `M` is a `B`-module, then the map
`B ⊗[A] M →ₗ[B] M` taking `(b, m) ↦ b • m` admits a `B`-linear section. -/
noncomputable
def FormallyUnramified.sec (A B M : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [FormallyUnramified A B] [FiniteType A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] :
      M →ₗ[B] B ⊗[A] M where
  __ := ((TensorProduct.AlgebraTensorModule.mapBilinear A B B B B B M
    LinearMap.id).flip (elem A B)).comp (lsmul A A M).toLinearMap.flip
  map_smul' r m := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.flip_apply, TensorProduct.AlgebraTensorModule.mapBilinear_apply, RingHom.id_apply]
    trans (TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := B) (M := B))
      ((LinearMap.flip (AlgHom.toLinearMap (lsmul A A M))) m)) ((1 ⊗ₜ r) * elem A B)
    · induction' elem A B using TensorProduct.induction_on
      · simp
      · simp [smul_comm r]
      · simp only [map_add, mul_add, *]
    · have := one_tmul_sub_tmul_one_mul_elem (R := A) r
      rw [sub_mul, sub_eq_zero] at this
      rw [this]
      induction' elem A B using TensorProduct.induction_on
      · simp
      · simp [TensorProduct.smul_tmul']
      · simp only [map_add, smul_add, mul_add, *]

lemma FormallyUnramified.comp_sec (A B M : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [FormallyUnramified A B] [FiniteType A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] :
    (TensorProduct.AlgebraTensorModule.lift
      ((lsmul B B M).toLinearMap.flip.restrictScalars A).flip).comp (sec A B M) =
      LinearMap.id := by
  ext x
  simp only [sec, LinearMap.coe_comp, LinearMap.coe_mk, LinearMap.coe_toAddHom,
    Function.comp_apply, LinearMap.flip_apply, TensorProduct.AlgebraTensorModule.mapBilinear_apply,
    TensorProduct.AlgebraTensorModule.lift_apply, LinearMap.id_coe, id_eq]
  trans (TensorProduct.lmul' A (elem A B)) • x
  · induction' elem A B using TensorProduct.induction_on with r s y z hy hz
    · simp
    · simp [mul_smul, smul_comm r s]
    · simp [hy, hz, add_smul]
  · rw [lmul_elem, one_smul]

theorem FormallyUnramified.bijective_of_isAlgClosed_of_localRing
    [IsAlgClosed K] [FormallyUnramified K A] [LocalRing A] :
    Function.Bijective (algebraMap K A) := by
  have := FormallyUnramified.finite_of_free (R := K) (S := A)
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  have hA : IsNilpotent (LocalRing.maximalIdeal A) := by
    rw [← LocalRing.jacobson_eq_maximalIdeal ⊥]
    · exact IsArtinianRing.isNilpotent_jacobson_bot
    · exact bot_ne_top
  have : Function.Bijective (Algebra.ofId K (A ⧸ LocalRing.maximalIdeal A)) := by
    refine ⟨RingHom.injective _, IsAlgClosed.algebraMap_surjective_of_isIntegral ?_⟩
    apply Algebra.IsIntegral.of_finite
  let e : K ≃ₐ[K] A ⧸ LocalRing.maximalIdeal A := {
    __ := Algebra.ofId K (A ⧸ LocalRing.maximalIdeal A)
    __ := Equiv.ofBijective _ this }
  let e' : A ⊗[K] (A ⧸ LocalRing.maximalIdeal A) ≃ₐ[A] A :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e.symm).trans (Algebra.TensorProduct.rid K A A)
  let f : A ⧸ LocalRing.maximalIdeal A →ₗ[A] A := e'.toLinearMap.comp (sec K A _)
  have hf : (Algebra.ofId _ _).toLinearMap ∘ₗ f = LinearMap.id := by
    dsimp [f]
    rw [← LinearMap.comp_assoc, ← comp_sec K A]
    congr 1
    apply LinearMap.restrictScalars_injective K
    apply _root_.TensorProduct.ext'
    intros r s
    obtain ⟨s, rfl⟩ := e.surjective s
    suffices s • (Ideal.Quotient.mk (LocalRing.maximalIdeal A)) r = r • e s by
      simpa [ofId, e']
    simp [Algebra.smul_def, e, ofId, mul_comm]
  have hf₁ : f 1 • (1 : A ⧸ LocalRing.maximalIdeal A) = 1 := by
    rw [← algebraMap_eq_smul_one]
    exact LinearMap.congr_fun hf 1
  have hf₂ : 1 - f 1 ∈ LocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, ← Ideal.Quotient.algebraMap_eq,
     algebraMap_eq_smul_one, hf₁, sub_self]
  have hf₃ : IsIdempotentElem (1 - f 1) := by
    apply IsIdempotentElem.one_sub
    rw [IsIdempotentElem, ← smul_eq_mul, ← map_smul, hf₁]
  have hf₄ : f 1 = 1 := by
    obtain ⟨n, hn⟩ := hA
    have : (1 - f 1) ^ n = 0 := by
      rw [← Ideal.mem_bot, ← Ideal.zero_eq_bot, ← hn]
      exact Ideal.pow_mem_pow hf₂ n
    rw [eq_comm, ← sub_eq_zero, ← hf₃.pow_succ_eq n, pow_succ, this, mul_zero]
  refine Equiv.bijective ⟨algebraMap K A, ⇑e.symm ∘ ⇑(algebraMap A _), fun x ↦ by simp, fun x ↦ ?_⟩
  have : ⇑(algebraMap K A) = ⇑f ∘ ⇑e := by
    ext k
    conv_rhs => rw [← mul_one k, ← smul_eq_mul, Function.comp_apply, map_smul,
      LinearMap.map_smul_of_tower, map_one, hf₄, ← algebraMap_eq_smul_one]
  rw [this]
  simp only [Function.comp_apply, AlgEquiv.apply_symm_apply, algebraMap_eq_smul_one,
    map_smul, hf₄, smul_eq_mul, mul_one]

theorem FormallyUnramified.isField_of_isAlgClosed_of_localRing
    [IsAlgClosed K] [FormallyUnramified K A] [LocalRing A] : IsField A := by
  rw [LocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
  intro x hx
  obtain ⟨x, rfl⟩ := (bijective_of_isAlgClosed_of_localRing K).surjective x
  show _ = 0
  rw [← (algebraMap K A).map_zero]
  by_contra hx'
  exact hx ((isUnit_iff_ne_zero.mpr
    (fun e ↦ hx' ((algebraMap K A).congr_arg e))).map (algebraMap K A))

theorem FormallyUnramified.isReduced_of_field [FormallyUnramified K A] [EssFiniteType K A] :
    IsReduced A := by
  constructor
  intro x hx
  let f := (Algebra.TensorProduct.includeRight (R := K) (A := AlgebraicClosure K) (B := A))
  have : Function.Injective f := by
    have : ⇑f = (LinearMap.rTensor A (Algebra.ofId K (AlgebraicClosure K)).toLinearMap).comp
        (Algebra.TensorProduct.lid K A).symm.toLinearMap := by
      ext x; simp [f]
    rw [this]
    suffices Function.Injective
        (LinearMap.rTensor A (Algebra.ofId K (AlgebraicClosure K)).toLinearMap) by
      exact this.comp (Algebra.TensorProduct.lid K A).symm.injective
    apply Module.Flat.preserves_injective_linearMap
    exact (algebraMap K _).injective
  apply this
  rw [map_zero]
  apply eq_zero_of_localization
  intro M hM
  have hy := (hx.map f).map (algebraMap _ (Localization.AtPrime M))
  generalize algebraMap _ (Localization.AtPrime M) (f x) = y at *
  have := EssFiniteType.of_isLocalization (Localization.AtPrime M) M.primeCompl
  have := FormallyUnramified.of_isLocalization (Rₘ := Localization.AtPrime M) M.primeCompl
  have := EssFiniteType.comp (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)
    (Localization.AtPrime M)
  have := FormallyUnramified.comp (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)
    (Localization.AtPrime M)
  letI := (isField_of_isAlgClosed_of_localRing (AlgebraicClosure K)
    (A := Localization.AtPrime M)).toField
  exact hy.eq_zero

theorem FormallyUnramified.range_eq_top_of_isPurelyInseparable
    [FormallyUnramified K L] [EssFiniteType K L] [IsPurelyInseparable K L] :
    (algebraMap K L).range = ⊤ := by
  classical
  have : Nontrivial (L ⊗[K] L) := by
    rw [← not_subsingleton_iff_nontrivial, ← rank_zero_iff (R := K), rank_tensorProduct',
      mul_eq_zero, or_self, rank_zero_iff, not_subsingleton_iff_nontrivial]
    infer_instance
  rw [← top_le_iff]
  intro x _
  obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem K (ringExpChar K) x
  have : ExpChar (L ⊗[K] L) (ringExpChar K) := by
    refine expChar_of_injective_ringHom (algebraMap K _).injective (ringExpChar K)
  have : (1 ⊗ₜ x - x ⊗ₜ 1 : L ⊗[K] L) ^ (ringExpChar K) ^ n = 0 := by
    rw [sub_pow_expChar_pow, TensorProduct.tmul_pow, one_pow, TensorProduct.tmul_pow, one_pow]
    obtain ⟨r, hr⟩ := hn
    rw [← hr, algebraMap_eq_smul_one, TensorProduct.smul_tmul, sub_self]
  have H : (1 ⊗ₜ x : L ⊗[K] L) = x ⊗ₜ 1 := by
    have inst : IsReduced (L ⊗[K] L) := FormallyUnramified.isReduced_of_field L
    exact sub_eq_zero.mp (IsNilpotent.eq_zero ⟨_, this⟩)
  by_cases h' : LinearIndependent K ![1, x]
  · have h := h'.coe_range
    let S := h.extend (Set.subset_univ _)
    let a : S := ⟨1, h.subset_extend _ (by simp)⟩; have ha : Basis.extend h a = 1 := by simp
    let b : S := ⟨x, h.subset_extend _ (by simp)⟩; have hb : Basis.extend h b = x := by simp
    by_cases e : a = b
    · obtain rfl : 1 = x := congr_arg Subtype.val e
      exact ⟨1, map_one _⟩
    have := DFunLike.congr_fun
      (DFunLike.congr_arg ((Basis.extend h).tensorProduct (Basis.extend h)).repr H) (a, b)
    simp only [Basis.tensorProduct_repr_tmul_apply, ← ha, ← hb, Basis.repr_self,
      Finsupp.single_apply, e, Ne.symm e, ↓reduceIte, mul_one, mul_zero, one_ne_zero] at this
  · rw [LinearIndependent.pair_iff] at h'
    simp only [not_forall, not_and, exists_prop] at h'
    obtain ⟨a, b, e, hab⟩ := h'
    have : IsUnit b := by
      rw [isUnit_iff_ne_zero]
      rintro rfl
      rw [zero_smul, ← algebraMap_eq_smul_one, add_zero,
        (injective_iff_map_eq_zero' _).mp (algebraMap K L).injective] at e
      cases hab e rfl
    use (-this.unit⁻¹ * a)
    rw [map_mul, ← Algebra.smul_def, algebraMap_eq_smul_one, eq_neg_iff_add_eq_zero.mpr e,
      smul_neg, neg_smul, neg_neg, smul_smul, this.val_inv_mul, one_smul]

theorem FormallyUnramified.isSeparable [FormallyUnramified K L] [EssFiniteType K L] :
    IsSeparable K L := by
  have := FormallyUnramified.finite_of_free (R := K) (S := L)
  rw [← separableClosure.eq_top_iff]
  have := FormallyUnramified.of_comp K (separableClosure K L) L
  have := EssFiniteType.of_comp K (separableClosure K L) L
  have := separableClosure.isPurelyInseparable K L (IsAlgebraic.of_finite K L)
  ext
  show _ ↔ _ ∈ (⊤ : Subring _)
  rw [← FormallyUnramified.range_eq_top_of_isPurelyInseparable (separableClosure K L) L]
  simp

theorem FormallyUnramified.iff_isSeparable [EssFiniteType K L] :
    FormallyUnramified K L ↔ IsSeparable K L :=
  ⟨fun _ ↦ FormallyUnramified.isSeparable K L, fun _ ↦ FormallyUnramified.of_isSeparable K L⟩

theorem FormallyEtale.iff_isSeparable [EssFiniteType K L] :
    FormallyEtale K L ↔ IsSeparable K L :=
  ⟨fun _ ↦ FormallyUnramified.isSeparable K L, fun _ ↦ FormallyEtale.of_isSeparable K L⟩

lemma _root_.IsIdempotentElem.map {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] {e : M}
    (he : IsIdempotentElem e) (f : F) : IsIdempotentElem (f e) := by
  rw [IsIdempotentElem, ← map_mul, he.eq]

lemma _root_.IsIdempotentElem.mul {M} [CommSemigroup M] {e₁ e₂ : M}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) : IsIdempotentElem (e₁ * e₂) :=
  he₁.mul_of_commute (.all e₁ e₂) he₂

universe v in
theorem FormallyUnramified.pi_iff {R : Type max u v} {I : Type v} [Finite I] (f : I → Type max u v)
      [CommRing R] [∀ i, CommRing (f i)] [∀ i, Algebra R (f i)] :
    FormallyUnramified R (∀ i, f i) ↔ ∀ i, FormallyUnramified R (f i) := by
  classical
  cases nonempty_fintype I
  constructor
  · intro _ i
    letI := (Pi.evalAlgHom R f i).toRingHom.toAlgebra
    have : IsScalarTower R (∀ i, f i) (f i) := IsScalarTower.of_algebraMap_eq' rfl
    have : FormallyUnramified (∀ i, f i) (f i) :=
      FormallyUnramified.of_surjective (Function.surjective_eval i)
    exact FormallyUnramified.comp R (∀ i, f i) (f i)
  · intro H
    constructor
    intros B _ _ J hJ f₁ f₂ e
    ext g
    rw [← Finset.univ_sum_single g, map_sum, map_sum]
    refine Finset.sum_congr rfl ?_
    rintro x -
    have hf : ∀ x, f₁ x - f₂ x ∈ J := by
      intro g
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
      exact AlgHom.congr_fun e g
    let e : ∀ i, f i := Pi.single x 1
    have he : IsIdempotentElem e := by simp [IsIdempotentElem, e, ← Pi.single_mul]
    have h₁ : (f₁ e) * (1 - f₂ e) = 0 := by
      rw [← Ideal.mem_bot, ← hJ, ← ((he.map f₁).mul (he.map f₂).one_sub).eq, ← pow_two]
      apply Ideal.pow_mem_pow
      convert Ideal.mul_mem_left _ (f₁ e) (hf e) using 1
      rw [mul_sub, mul_sub, mul_one, (he.map f₁).eq]
    have h₂ : (f₂ e) * (1 - f₁ e) = 0 := by
      rw [← Ideal.mem_bot, ← hJ, ← ((he.map f₂).mul (he.map f₁).one_sub).eq, ← pow_two]
      apply Ideal.pow_mem_pow
      convert Ideal.mul_mem_left _ (-f₂ e) (hf e) using 1
      rw [neg_mul, mul_sub, mul_sub, mul_one, neg_sub, (he.map f₂).eq]
    have H : f₁ e = f₂ e := by
      trans f₁ e * f₂ e
      · rw [← sub_eq_zero, ← h₁, mul_sub, mul_one]
      · rw [eq_comm, ← sub_eq_zero, ← h₂, mul_sub, mul_one, mul_comm]
    let J' := Ideal.span {1 - f₁ e}
    let f₁' : f x →ₐ[R] B ⧸ J' := by
      apply AlgHom.ofLinearMap
        (((Ideal.Quotient.mkₐ R J').comp f₁).toLinearMap.comp (LinearMap.single x))
      · simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, LinearMap.coe_single,
          Function.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [eq_comm, ← sub_eq_zero, ← (Ideal.Quotient.mk J').map_one, ← map_sub,
          Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      · intros r s; simp [Pi.single_mul]
    let f₂' : f x →ₐ[R] B ⧸ J' := by
      apply AlgHom.ofLinearMap
        (((Ideal.Quotient.mkₐ R J').comp f₂).toLinearMap.comp (LinearMap.single x))
      · simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, LinearMap.coe_single,
          Function.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [eq_comm, ← sub_eq_zero, ← (Ideal.Quotient.mk J').map_one, ← map_sub,
          Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, H]
      · intros r s; simp [Pi.single_mul]
    suffices f₁' = f₂' by
      have := AlgHom.congr_fun this (g x)
      simp only [AlgHom.comp_toLinearMap, AlgHom.ofLinearMap_apply, LinearMap.coe_comp,
        LinearMap.coe_single, Function.comp_apply, AlgHom.toLinearMap_apply, ← map_sub,
        Ideal.Quotient.mkₐ_eq_mk, ← sub_eq_zero (b := Ideal.Quotient.mk J' _), sub_zero, f₁', f₂',
        Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, J'] at this
      obtain ⟨c, hc⟩ := this
      apply_fun (f₁ e * ·) at hc
      rwa [← mul_assoc, mul_sub, mul_sub, mul_one, (he.map f₁).eq, sub_self, zero_mul,
        ← map_mul, H, ← map_mul, ← Pi.single_mul, one_mul, sub_eq_zero] at hc
    apply FormallyUnramified.comp_injective (I := J.map (algebraMap _ _))
    · rw [← Ideal.map_pow, hJ, Ideal.map_bot]
    · ext r
      rw [← sub_eq_zero]
      simp only [Ideal.Quotient.algebraMap_eq, AlgHom.coe_comp, Ideal.Quotient.mkₐ_eq_mk,
        Function.comp_apply, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, f₁', f₂',
        AlgHom.comp_toLinearMap, AlgHom.ofLinearMap_apply, LinearMap.coe_comp,
        LinearMap.coe_single, Function.comp_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.mem_map_of_mem (Ideal.Quotient.mk J') (hf (Pi.single x r))

theorem exists_isIdempotentElem_quotient_eq {B : Type*} [CommRing B]
    (I : Ideal B) (hI : I ^ 2 = ⊥) (e : B ⧸ I) (he : IsIdempotentElem e) :
    ∃ x : B, IsIdempotentElem x ∧ Ideal.Quotient.mk I x = e := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective e
  have hx' : x * (x - 1) ∈ I := by
    simp [← Ideal.Quotient.eq_zero_iff_mem, hx, mul_sub, he.eq]
  refine ⟨(x - x * (x - 1)) ^ 2, ?_, ?_⟩
  · show _ = _
    have : (x * (x - 1)) ^ 2 = 0 := by
      rw [← Ideal.mem_bot, ← hI]
      exact Ideal.pow_mem_pow hx' 2
    rw [← sub_eq_zero]
    trans (x - 2) ^ 2 * (x ^ 2 - 2 * x - 1) * (x * (x - 1)) ^ 2
    · ring
    rw [this, mul_zero]
  · rw [map_pow, map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hx', sub_zero, hx, pow_two, he.eq]

@[simps!]
def Pi.algHom {R : Type*} {I} {f : I → Type*} [CommSemiring R] [s : ∀ i, Semiring (f i)]
    [∀ i, Algebra R (f i)] {A} [Semiring A] [Algebra R A] (g : ∀ i, A →ₐ[R] f i) :
      A →ₐ[R] ∀ i, f i where
  __ := Pi.ringHom fun i ↦ (g i).toRingHom
  commutes' r := by ext; simp

structure CompleteOrthogonalIdempotents {R} [CommRing R] {I} [Fintype I] (e : I → R) : Prop where
  idem : ∀ i, IsIdempotentElem (e i)
  ortho : ∀ i j, i ≠ j → e i * e j = 0
  complete : ∑ i, e i = 1

lemma prod_one_sub_eq_one_sub_sum {R} [CommRing R] {I} [Fintype I]
    {e : I → R} (h₂ : ∀ i j, i ≠ j → e i * e j = 0) :
    ∏ i, (1 - e i) = 1 - ∑ i, e i := by
  classical
  induction' (@Finset.univ I _) using Finset.induction_on with a s has ih
  · simp
  · suffices (1 - e a) * (1 - ∑ i in s, e i) = 1 - (e a + ∑ i in s, e i) by simp [*]
    have : e a * ∑ i in s, e i = 0 := by
      rw [mul_sum, ← sum_const_zero (s := s)]
      apply sum_congr rfl
      exact fun j hj ↦ h₂ a j (fun e ↦ has (e ▸ hj))
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, this, sub_zero, sub_sub, add_comm]

lemma CompleteOrthogonalIdempotents.prod_one_sub {R} [CommRing R] {I} [Fintype I] {e : I → R}
    (he : CompleteOrthogonalIdempotents e) : ∏ i, (1 - e i) = 0 := by
  rw [prod_one_sub_eq_one_sub_sum he.ortho, he.complete, sub_self]

lemma CompleteOrthogonalIdempotents.bijective_pi {R} [CommRing R] {I} [Fintype I] {e : I → R}
    (he : CompleteOrthogonalIdempotents e) :
    Function.Bijective (Pi.ringHom fun i ↦ Ideal.Quotient.mk (Ideal.span {1 - e i})) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    simp [Function.funext_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
    suffices ∀ s : Finset I, (∏ i in s, (1 - e i)) * x = x by
      rw [← this Finset.univ, he.prod_one_sub, zero_mul]
    refine fun s ↦ Finset.induction_on s (by simp) ?_
    intros a s has e'
    suffices (1 - e a) * x = x by simp [has, mul_assoc, e', this]
    obtain ⟨c, rfl⟩ := hx a
    rw [← mul_assoc, (he.idem a).one_sub.eq]
  · suffices Pairwise fun i j ↦ IsCoprime (Ideal.span {1 - e i}) (Ideal.span {1 - e j}) by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.quotientInfToPiQuotient_surj this x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨x, by ext i; simp [Ideal.quotientInfToPiQuotient]⟩
    intros i j hij
    rw [Ideal.isCoprime_span_singleton_iff]
    exact ⟨1, e i, by simp [mul_sub, sub_mul, he.ortho i j hij]⟩

lemma CompleteOrthogonalIdempotents.map {R S} [CommRing R] [CommRing S] {I} [Fintype I] {e : I → R}
    (he : CompleteOrthogonalIdempotents e) (f : R →+* S) :
    CompleteOrthogonalIdempotents (f ∘ e) := by
  refine ⟨fun i ↦ (he.idem i).map f, fun i j hij ↦ ?_, ?_⟩
  simp only [← map_mul, he.ortho i j hij, Function.comp_apply, map_zero]
  simp only [Function.comp_apply, ← map_sum, he.complete, map_one]

lemma CompleteOrthogonalIdempotents.lift_of_square_zero {R} [CommRing R] {I} [Fintype I]
    {J : Ideal R} {e : I → R ⧸ J} (he : CompleteOrthogonalIdempotents e) (hJ : J ^ 2 = ⊥) :
    ∃ e' : I → R, CompleteOrthogonalIdempotents e' ∧ Ideal.Quotient.mk J ∘ e' = e := by
  choose e' h₁ h₂ using fun i ↦ exists_isIdempotentElem_quotient_eq _ hJ _ (he.idem i)
  have : ∀ (i j : I), i ≠ j → e' i * e' j = 0 := by
    intros i j hij
    rw [← ((h₁ i).mul (h₁ j)).eq, ← pow_two, ← Ideal.mem_bot, ← hJ]; apply Ideal.pow_mem_pow
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, h₂, h₂, he.ortho i j hij]
  refine ⟨e', ⟨h₁, this, ?_⟩, funext h₂⟩
  · rw [eq_comm, ← sub_eq_zero, ← prod_one_sub_eq_one_sub_sum this]
    trans ∏ i, (1 - e' i) ^ 2
    · apply prod_congr rfl
      · intro i _; rw [pow_two, (h₁ i).one_sub.eq]
    · rw [prod_pow, ← Ideal.mem_bot, ← hJ]; apply Ideal.pow_mem_pow
      simp only [← Ideal.Quotient.eq_zero_iff_mem, map_prod, map_sub, map_one, h₂, he.prod_one_sub]

lemma CompleteOrthogonalIdempotents.single {I : Type*} [Fintype I] [DecidableEq I]
    (R : I → Type*) [∀ i, CommRing (R i)] :
    CompleteOrthogonalIdempotents fun i ↦ (Pi.single i 1 : ∀ i, R i) := by
  refine ⟨by simp [IsIdempotentElem, ← Pi.single_mul], ?_, Finset.univ_sum_single 1⟩
  intros i j hij
  ext k
  by_cases hi : i = k
  · subst hi; simp [hij]
  · simp [hi]

lemma bijective_pi_of_isIdempotentElem {R} [CommRing R] {I} [Fintype I] (e : I → R)
    (he : ∀ i, IsIdempotentElem (e i))
    (he₁ : ∀ i j, i ≠ j → (1 - e i) * (1 - e j) = 0) (he₂ : ∏ i, e i = 0) :
    Function.Bijective (Pi.ringHom fun i ↦ Ideal.Quotient.mk (Ideal.span {e i})) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    simp [Function.funext_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
    suffices ∀ s : Finset I, (∏ i in s, e i) * x = x by
      rw [← this Finset.univ, he₂, zero_mul]
    refine fun s ↦ Finset.induction_on s (by simp) ?_
    intros a s has e'
    suffices e a * x = x by simp [has, mul_assoc, e', this]
    obtain ⟨c, rfl⟩ := hx a
    rw [← mul_assoc, (he a).eq]
  · suffices Pairwise fun i j ↦ IsCoprime (Ideal.span {e i}) (Ideal.span {e j}) by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.quotientInfToPiQuotient_surj this x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨x, by ext i; simp [Ideal.quotientInfToPiQuotient]⟩
    intros i j hij
    rw [Ideal.isCoprime_span_singleton_iff]
    refine ⟨1, 1 - e i, ?_⟩
    rw [one_mul, add_comm, ← eq_sub_iff_add_eq]
    conv_rhs => rw [← mul_one (1 - _)]
    rw [eq_comm, ← sub_eq_zero, ← mul_sub, he₁ _ _ hij]

lemma Ideal.ker_quotientMap_mk {R} [CommRing R] {I J : Ideal R} :
    RingHom.ker (Ideal.quotientMap (J.map (Ideal.Quotient.mk I))
      (Ideal.Quotient.mk _) Ideal.le_comap_map) = I.map (Ideal.Quotient.mk J) := by
  rw [Ideal.quotientMap, Ideal.ker_quotient_lift, ← RingHom.comap_ker, Ideal.mk_ker,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]

set_option maxHeartbeats 400000 in
universe v in
theorem FormallySmooth.pi_iff {R : Type max u v} {I : Type v} [Finite I] (f : I → Type max u v)
      [CommRing R] [∀ i, CommRing (f i)] [∀ i, Algebra R (f i)] :
    FormallySmooth R (∀ i, f i) ↔ ∀ i, FormallySmooth R (f i) := by
  classical
  cases nonempty_fintype I
  constructor
  · intro _ i
    fapply FormallySmooth.of_split (Pi.evalAlgHom R f i)
    apply AlgHom.ofLinearMap
      ((Ideal.Quotient.mkₐ R _).toLinearMap.comp (LinearMap.single i))
    · show Ideal.Quotient.mk _ (Pi.single i 1) = 1
      rw [← (Ideal.Quotient.mk _).map_one, ← sub_eq_zero, ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      have : Pi.single i 1 - 1 ∈ RingHom.ker (Pi.evalAlgHom R f i).toRingHom := by
        simp [RingHom.mem_ker]
      convert neg_mem (Ideal.pow_mem_pow this 2) using 1
      simp [pow_two, sub_mul, mul_sub, ← Pi.single_mul]
    · intro x y
      show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ * Ideal.Quotient.mk _ _
      simp only [AlgHom.toRingHom_eq_coe, LinearMap.coe_single, Pi.single_mul, map_mul]
    · ext x
      show (Pi.single i x) i = x
      simp
  · intro H
    constructor
    intros B _ _ J hJ g
    obtain ⟨e, he, he'⟩ :=
      ((CompleteOrthogonalIdempotents.single f).map g.toRingHom).lift_of_square_zero hJ
    replace he' : ∀ i, Ideal.Quotient.mk J (e i) = g (Pi.single i 1) := congr_fun he'
    let iso : B ≃ₐ[R] ∀ i, B ⧸ Ideal.span {1 - e i} :=
      { __ := Pi.algHom fun i ↦ Ideal.Quotient.mkₐ R _
        __ := Equiv.ofBijective _ he.bijective_pi }
    let J' := fun i ↦ J.map (Ideal.Quotient.mk (Ideal.span {1 - e i}))
    let ι : ∀ i, (B ⧸ J →ₐ[R] (B ⧸ _) ⧸ J' i) := fun i ↦ Ideal.quotientMapₐ _
      (IsScalarTower.toAlgHom R B _) Ideal.le_comap_map
    have hι : ∀ i x, ι i x = 0 → (e i) * x = 0 := by
      intros i x hix
      have : x ∈ (Ideal.span {1 - e i}).map (Ideal.Quotient.mk J) := by
        rw [← Ideal.ker_quotientMap_mk]; exact hix
      rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at this
      obtain ⟨c, rfl⟩ := this
      rw [← mul_assoc, ← map_mul, mul_sub, mul_one, (he.idem i).eq, sub_self, map_zero, zero_mul]
    have : ∀ i : I, ∃ a : f i →ₐ[R] B ⧸ Ideal.span {1 - e i}, ∀ x,
        Ideal.Quotient.mk (J' i) (a x) = ι i (g (Pi.single i x)) := by
      intro i
      let g' : f i →ₐ[R] (B ⧸ _) ⧸ (J' i) := by
        apply AlgHom.ofLinearMap (((ι i).comp g).toLinearMap ∘ₗ LinearMap.single i)
        · suffices Ideal.Quotient.mk (Ideal.span {1 - e i}) (e i) = 1 by simp [ι, ← he', this]
          rw [← (Ideal.Quotient.mk _).map_one, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
            Ideal.mem_span_singleton]
        · intros x y; simp [Pi.single_mul]
      obtain ⟨a, ha⟩ := FormallySmooth.comp_surjective (I := J' i)
        (by rw [← Ideal.map_pow, hJ, Ideal.map_bot]) g'
      exact ⟨a, AlgHom.congr_fun ha⟩
    choose a ha using this
    use iso.symm.toAlgHom.comp (Pi.algHom fun i ↦ (a i).comp (Pi.evalAlgHom R f i))
    ext x; rw [← AlgHom.toLinearMap_apply, ← AlgHom.toLinearMap_apply]; congr 1
    ext i x
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.comp_toLinearMap, AlgEquiv.toAlgHom_toLinearMap,
      LinearMap.coe_comp, LinearMap.coe_single, Function.comp_apply, AlgHom.toLinearMap_apply,
      AlgEquiv.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (a i x)
    have hy' : Ideal.Quotient.mk (Ideal.span {1 - e i}) (y * e i) = a i x := by
      have : Ideal.Quotient.mk (Ideal.span {1 - e i}) (e i) = 1 := by
        rw [← (Ideal.Quotient.mk _).map_one, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
          Ideal.mem_span_singleton]
      rw [map_mul, this, hy, mul_one]
    trans Ideal.Quotient.mk J (y * e i)
    · congr 1; apply iso.injective; ext j
      suffices a j (Pi.single i x j) = Ideal.Quotient.mk _ (y * e i) by simpa using this
      by_cases hij : i = j
      · subst hij
        rw [Pi.single_eq_same, hy']
      · have : Ideal.Quotient.mk (Ideal.span {1 - e j}) (e i) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
          refine ⟨e i, by simp [he.ortho j i (Ne.symm hij), sub_mul]⟩
        rw [Pi.single_eq_of_ne (Ne.symm hij), map_zero, map_mul, this, mul_zero]
    · have : ι i (Ideal.Quotient.mk J (y * e i)) = ι i (g (Pi.single i x)) := by
        rw [← ha, ← hy']
        simp only [Ideal.quotient_map_mkₐ, IsScalarTower.coe_toAlgHom',
          Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mkₐ_eq_mk, ι]
      rw [← sub_eq_zero, ← map_sub] at this
      replace this := hι _ _ this
      rwa [mul_sub, ← map_mul, mul_comm, mul_assoc, (he.idem i).eq, he', ← map_mul, ← Pi.single_mul,
        one_mul, sub_eq_zero] at this

universe v in
theorem FormallyEtale.pi_iff {R : Type max u v} {I : Type v} [Finite I] (f : I → Type max u v)
      [CommRing R] [∀ i, CommRing (f i)] [∀ i, Algebra R (f i)] :
    FormallyEtale R (∀ i, f i) ↔ ∀ i, FormallyEtale R (f i) := by
  simp only [FormallyEtale.iff_unramified_and_smooth, FormallyUnramified.pi_iff.{u, v},
    FormallySmooth.pi_iff.{u, v}, forall_and]

attribute [local instance] IsArtinianRing.subtype_isMaximal_finite Ideal.Quotient.field

theorem FormallyEtale.iff_isReduced_and_isSeparable [EssFiniteType K A] :
    FormallyEtale K A ↔ Module.Finite K A ∧ IsReduced A ∧
      ∀ M : Ideal A, M.IsMaximal → IsSeparable K (A ⧸ M) := by
  constructor
  · intro _
    refine ⟨FormallyUnramified.finite_of_free (R := K) (S := A),
      FormallyUnramified.isReduced_of_field K, fun M hM ↦ ?_⟩
    have := FormallyUnramified.comp K A (A ⧸ M)
    have := EssFiniteType.comp K A (A ⧸ M)
    letI := Ideal.Quotient.field M
    rwa [← FormallyUnramified.iff_isSeparable]
  · rintro ⟨_, _, H⟩
    have : IsArtinianRing A := isArtinian_of_tower K inferInstance
    let e : A ≃ₐ[A] _ :=
      { __ := IsArtinianRing.equivPi A
        commutes' := fun r ↦ by
          ext i
          suffices (IsArtinianRing.equivPi A) r i = (Ideal.Quotient.mk ↑i) r by simpa using this
          rfl }
    rw [FormallyEtale.iff_of_equiv (e.restrictScalars K), FormallyEtale.pi_iff.{u, u}]
    rintro ⟨M, hM⟩
    have : M.IsMaximal := hM
    have := H _ hM
    exact FormallyEtale.of_isSeparable K (A ⧸ M)

theorem FormallyEtale.iff_unramifield_of_field [EssFiniteType K A] :
    FormallyEtale K A ↔ FormallyUnramified K A := by
  constructor
  · intro _
    infer_instance
  · rw [FormallyEtale.iff_isReduced_and_isSeparable]
    intro _
    refine ⟨FormallyUnramified.finite_of_free (R := K) (S := A),
      FormallyUnramified.isReduced_of_field K, fun M hM ↦ ?_⟩
    have := FormallyUnramified.comp K A (A ⧸ M)
    have := EssFiniteType.comp K A (A ⧸ M)
    letI := Ideal.Quotient.field M
    rwa [← FormallyUnramified.iff_isSeparable]

theorem FormallyEtale.iff_exists_equiv [EssFiniteType K A] :
    FormallyEtale K A ↔ ∃ (I : Type u) (_ : Finite I) (L : I → Type u)
      (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i)) (_ : ∀ i, IsSeparable K (L i)),
      Nonempty (A ≃ₐ[K] ∀ i, L i) := by
  constructor
  · intro _
    have := FormallyUnramified.finite_of_free (R := K) (S := A)
    have : IsReduced A := FormallyUnramified.isReduced_of_field K
    have : IsArtinianRing A := isArtinian_of_tower K inferInstance
    let e : A ≃ₐ[A] _ :=
      { __ := IsArtinianRing.equivPi A
        commutes' := fun r ↦ by
          ext i
          suffices (IsArtinianRing.equivPi A) r i = (Ideal.Quotient.mk ↑i) r by simpa using this
          rfl }
    refine ⟨{I | Ideal.IsMaximal I}, inferInstance, fun i ↦ A ⧸ (i.1 : Ideal A),
      fun i ↦ Ideal.Quotient.field (hI := i.prop), inferInstance, ?_, ⟨e.restrictScalars K⟩⟩
    rintro ⟨I, hI⟩
    rw [← FormallyUnramified.iff_isSeparable]
    exact FormallyUnramified.comp K A (A ⧸ I)
  · rintro ⟨I, _, L, _, _, _, ⟨e⟩⟩
    rw [FormallyEtale.iff_of_equiv e, FormallyEtale.pi_iff.{u, u}]
    infer_instance

end Field

end Algebra
