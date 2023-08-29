/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.QuotientNilpotent
import Mathlib.RingTheory.Kaehler

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
  rw [FormallyUnramified_iff, FormallySmooth_iff, FormallyEtale_iff]
  -- ⊢ (∀ ⦃B : Type u⦄ [inst : CommRing B] [inst_1 : Algebra R B] (I : Ideal B), I  …
  simp_rw [← forall_and]
  -- ⊢ (∀ ⦃B : Type u⦄ [inst : CommRing B] [inst_1 : Algebra R B] (I : Ideal B), I  …
  rfl
  -- 🎉 no goals
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
  -- ⊢ ∀ (g₁ g₂ : A →ₐ[R] B), AlgHom.comp (Ideal.Quotient.mkₐ R I) g₁ = AlgHom.comp …
  change Function.Injective (Ideal.Quotient.mkₐ R I).comp
  -- ⊢ Function.Injective (AlgHom.comp (Ideal.Quotient.mkₐ R I))
  revert _RB
  -- ⊢ ∀ [_RB : Algebra R B], Function.Injective (AlgHom.comp (Ideal.Quotient.mkₐ R …
  apply Ideal.IsNilpotent.induction_on (R := B) I hI
  -- ⊢ ∀ ⦃S : Type u⦄ [inst : CommRing S] (I : Ideal S), I ^ 2 = ⊥ → ∀ [_RB : Algeb …
  · intro B _ I hI _; exact FormallyUnramified.comp_injective I hI
    -- ⊢ Function.Injective (AlgHom.comp (Ideal.Quotient.mkₐ R I))
                      -- 🎉 no goals
  · intro B _ I J hIJ h₁ h₂ _ g₁ g₂ e
    -- ⊢ g₁ = g₂
    apply h₁
    -- ⊢ AlgHom.comp (Ideal.Quotient.mkₐ R I) g₁ = AlgHom.comp (Ideal.Quotient.mkₐ R  …
    apply h₂
    -- ⊢ AlgHom.comp (Ideal.Quotient.mkₐ R (Ideal.map (Ideal.Quotient.mk I) J)) (AlgH …
    ext x
    -- ⊢ ↑(AlgHom.comp (Ideal.Quotient.mkₐ R (Ideal.map (Ideal.Quotient.mk I) J)) (Al …
    replace e := AlgHom.congr_fun e x
    -- ⊢ ↑(AlgHom.comp (Ideal.Quotient.mkₐ R (Ideal.map (Ideal.Quotient.mk I) J)) (Al …
    dsimp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at e ⊢
    -- ⊢ ↑(Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk I) J)) (↑(Ideal.Quotient.m …
    rwa [Ideal.Quotient.eq, ← map_sub, Ideal.mem_quotient_iff_mem hIJ, ← Ideal.Quotient.eq]
    -- 🎉 no goals
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
      -- ⊢ ↑(AlgHom.comp (Ideal.Quotient.mkₐ R (RingHom.ker f)) g₁) x = ↑(AlgHom.comp ( …
      have := RingHom.congr_fun h x
      -- ⊢ ↑(AlgHom.comp (Ideal.Quotient.mkₐ R (RingHom.ker f)) g₁) x = ↑(AlgHom.comp ( …
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
  -- ⊢ ∀ (g : A →ₐ[R] B ⧸ I), ∃ f, AlgHom.comp (Ideal.Quotient.mkₐ R I) f = g
  change Function.Surjective (Ideal.Quotient.mkₐ R I).comp
  -- ⊢ Function.Surjective (AlgHom.comp (Ideal.Quotient.mkₐ R I))
  revert _RB
  -- ⊢ ∀ [_RB : Algebra R B], Function.Surjective (AlgHom.comp (Ideal.Quotient.mkₐ  …
  apply Ideal.IsNilpotent.induction_on (R := B) I hI
  -- ⊢ ∀ ⦃S : Type u⦄ [inst : CommRing S] (I : Ideal S), I ^ 2 = ⊥ → ∀ [_RB : Algeb …
  · intro B _ I hI _; exact FormallySmooth.comp_surjective I hI
    -- ⊢ Function.Surjective (AlgHom.comp (Ideal.Quotient.mkₐ R I))
                      -- 🎉 no goals
  · intro B _ I J hIJ h₁ h₂ _ g
    -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ R J) a = g
    let this : ((B ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) ≃ₐ[R] B ⧸ J :=
      {
        (DoubleQuot.quotQuotEquivQuotSup I J).trans
          (Ideal.quotEquivOfEq (sup_eq_right.mpr hIJ)) with
        commutes' := fun x => rfl }
    obtain ⟨g', e⟩ := h₂ (this.symm.toAlgHom.comp g)
    -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ R J) a = g
    obtain ⟨g', rfl⟩ := h₁ g'
    -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ R J) a = g
    replace e := congr_arg this.toAlgHom.comp e
    -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ R J) a = g
    conv_rhs at e =>
      rw [← AlgHom.comp_assoc, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_eq_coe,
        AlgEquiv.comp_symm, AlgHom.id_comp]
    exact ⟨g', e⟩
    -- 🎉 no goals
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
  -- ⊢ ↑(AlgEquiv.symm (Ideal.quotientKerAlgEquivOfSurjective hg)) (↑g (↑(liftOfSur …
  change _ = ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f) x
  -- ⊢ ↑(AlgEquiv.symm (Ideal.quotientKerAlgEquivOfSurjective hg)) (↑g (↑(liftOfSur …
  rw [← FormallySmooth.mk_lift _ hg'
    ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f)]
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).injective
  -- ⊢ ↑(Ideal.quotientKerAlgEquivOfSurjective hg) (↑(AlgEquiv.symm (Ideal.quotient …
  rw [AlgEquiv.apply_symm_apply, Ideal.quotientKerAlgEquivOfSurjective,
    Ideal.quotientKerAlgEquivOfRightInverse.apply]
  exact (Ideal.kerLiftAlg_mk _ _).symm
  -- 🎉 no goals
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
  -- ⊢ ∀ ⦃B_1 : Type u⦄ [inst : CommRing B_1] [inst_1 : Algebra R B_1] (I : Ideal B …
  intro C _ _ I hI f
  -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ R I) a = f
  use (FormallySmooth.lift I ⟨2, hI⟩ (f.comp e : A →ₐ[R] C ⧸ I)).comp e.symm
  -- ⊢ AlgHom.comp (Ideal.Quotient.mkₐ R I) (AlgHom.comp (lift I (_ : ∃ n, I ^ n =  …
  rw [← AlgHom.comp_assoc, FormallySmooth.comp_lift, AlgHom.comp_assoc, AlgEquiv.comp_symm,
    AlgHom.comp_id]
#align algebra.formally_smooth.of_equiv Algebra.FormallySmooth.of_equiv

theorem FormallyUnramified.of_equiv [FormallyUnramified R A] (e : A ≃ₐ[R] B) :
    FormallyUnramified R B := by
  constructor
  -- ⊢ ∀ ⦃B_1 : Type u⦄ [inst : CommRing B_1] [inst_1 : Algebra R B_1] (I : Ideal B …
  intro C _ _ I hI f₁ f₂ e'
  -- ⊢ f₁ = f₂
  rw [← f₁.comp_id, ← f₂.comp_id, ← e.comp_symm, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
  -- ⊢ AlgHom.comp (AlgHom.comp f₁ ↑e) ↑(AlgEquiv.symm e) = AlgHom.comp (AlgHom.com …
  congr 1
  -- ⊢ AlgHom.comp f₁ ↑e = AlgHom.comp f₂ ↑e
  refine' FormallyUnramified.comp_injective I hI _
  -- ⊢ AlgHom.comp (Ideal.Quotient.mkₐ R I) (AlgHom.comp f₁ ↑e) = AlgHom.comp (Idea …
  rw [← AlgHom.comp_assoc, e', AlgHom.comp_assoc]
  -- 🎉 no goals
#align algebra.formally_unramified.of_equiv Algebra.FormallyUnramified.of_equiv

theorem FormallyEtale.of_equiv [FormallyEtale R A] (e : A ≃ₐ[R] B) : FormallyEtale R B :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.of_equiv e, FormallySmooth.of_equiv e⟩
#align algebra.formally_etale.of_equiv Algebra.FormallyEtale.of_equiv

end OfEquiv

section Polynomial

open scoped Polynomial

variable (R : Type u) [CommSemiring R]

instance FormallySmooth.mvPolynomial (σ : Type u) : FormallySmooth R (MvPolynomial σ R) := by
  constructor
  -- ⊢ ∀ ⦃B : Type u⦄ [inst : CommRing B] [inst_1 : Algebra R B] (I : Ideal B), I ^ …
  intro C _ _ I _ f
  -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ R I) a = f
  have : ∀ s : σ, ∃ c : C, Ideal.Quotient.mk I c = f (MvPolynomial.X s) := fun s =>
    Ideal.Quotient.mk_surjective _
  choose g hg using this
  -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ R I) a = f
  refine' ⟨MvPolynomial.aeval g, _⟩
  -- ⊢ AlgHom.comp (Ideal.Quotient.mkₐ R I) (MvPolynomial.aeval g) = f
  ext s
  -- ⊢ ↑(AlgHom.comp (Ideal.Quotient.mkₐ R I) (MvPolynomial.aeval g)) (MvPolynomial …
  rw [← hg, AlgHom.comp_apply, MvPolynomial.aeval_X]
  -- ⊢ ↑(Ideal.Quotient.mkₐ R I) (g s) = ↑(Ideal.Quotient.mk I) (g s)
  rfl
  -- 🎉 no goals
#align algebra.formally_smooth.mv_polynomial Algebra.FormallySmooth.mvPolynomial

instance FormallySmooth.polynomial : FormallySmooth R R[X] :=
  -- Porting note: this needed more underscores than in lean3.
  @FormallySmooth.of_equiv _ _ _ _ _ _ _ _ (FormallySmooth.mvPolynomial R PUnit)
    (MvPolynomial.pUnitAlgEquiv R)
#align algebra.formally_smooth.polynomial Algebra.FormallySmooth.polynomial

end Polynomial

section Comp

variable (R : Type u) [CommSemiring R]

variable (A : Type u) [CommSemiring A] [Algebra R A]

variable (B : Type u) [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem FormallySmooth.comp [FormallySmooth R A] [FormallySmooth A B] : FormallySmooth R B := by
  constructor
  -- ⊢ ∀ ⦃B_1 : Type u⦄ [inst : CommRing B_1] [inst_1 : Algebra R B_1] (I : Ideal B …
  intro C _ _ I hI f
  -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ R I) a = f
  obtain ⟨f', e⟩ := FormallySmooth.comp_surjective I hI (f.comp (IsScalarTower.toAlgHom R A B))
  -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ R I) a = f
  letI := f'.toRingHom.toAlgebra
  -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ R I) a = f
  obtain ⟨f'', e'⟩ :=
    FormallySmooth.comp_surjective I hI { f.toRingHom with commutes' := AlgHom.congr_fun e.symm }
  apply_fun AlgHom.restrictScalars R at e'
  -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ R I) a = f
  exact ⟨f''.restrictScalars _, e'.trans (AlgHom.ext fun _ => rfl)⟩
  -- 🎉 no goals
#align algebra.formally_smooth.comp Algebra.FormallySmooth.comp

theorem FormallyUnramified.comp [FormallyUnramified R A] [FormallyUnramified A B] :
    FormallyUnramified R B := by
  constructor
  -- ⊢ ∀ ⦃B_1 : Type u⦄ [inst : CommRing B_1] [inst_1 : Algebra R B_1] (I : Ideal B …
  intro C _ _ I hI f₁ f₂ e
  -- ⊢ f₁ = f₂
  have e' :=
    FormallyUnramified.lift_unique I ⟨2, hI⟩ (f₁.comp <| IsScalarTower.toAlgHom R A B)
      (f₂.comp <| IsScalarTower.toAlgHom R A B) (by rw [← AlgHom.comp_assoc, e, AlgHom.comp_assoc])
  letI := (f₁.comp (IsScalarTower.toAlgHom R A B)).toRingHom.toAlgebra
  -- ⊢ f₁ = f₂
  let F₁ : B →ₐ[A] C := { f₁ with commutes' := fun r => rfl }
  -- ⊢ f₁ = f₂
  let F₂ : B →ₐ[A] C := { f₂ with commutes' := AlgHom.congr_fun e'.symm }
  -- ⊢ f₁ = f₂
  ext1 x
  -- ⊢ ↑f₁ x = ↑f₂ x
  change F₁ x = F₂ x
  -- ⊢ ↑F₁ x = ↑F₂ x
  congr
  -- ⊢ F₁ = F₂
  exact FormallyUnramified.ext I ⟨2, hI⟩ (AlgHom.congr_fun e)
  -- 🎉 no goals
#align algebra.formally_unramified.comp Algebra.FormallyUnramified.comp

theorem FormallyUnramified.of_comp [FormallyUnramified R B] : FormallyUnramified A B := by
  constructor
  -- ⊢ ∀ ⦃B_1 : Type u⦄ [inst : CommRing B_1] [inst_1 : Algebra A B_1] (I : Ideal B …
  intro Q _ _ I e f₁ f₂ e'
  -- ⊢ f₁ = f₂
  letI := ((algebraMap A Q).comp (algebraMap R A)).toAlgebra
  -- ⊢ f₁ = f₂
  letI : IsScalarTower R A Q := IsScalarTower.of_algebraMap_eq' rfl
  -- ⊢ f₁ = f₂
  refine' AlgHom.restrictScalars_injective R _
  -- ⊢ AlgHom.restrictScalars R f₁ = AlgHom.restrictScalars R f₂
  refine' FormallyUnramified.ext I ⟨2, e⟩ _
  -- ⊢ ∀ (x : B), ↑(Ideal.Quotient.mk I) (↑(AlgHom.restrictScalars R f₁) x) = ↑(Ide …
  intro x
  -- ⊢ ↑(Ideal.Quotient.mk I) (↑(AlgHom.restrictScalars R f₁) x) = ↑(Ideal.Quotient …
  exact AlgHom.congr_fun e' x
  -- 🎉 no goals
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
  -- ⊢ ∀ ⦃B : Type u⦄ [inst : CommRing B] [inst_1 : Algebra R B] (I : Ideal B), I ^ …
  intro C _ _ I hI i
  -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ R I) a = i
  let l : P ⧸ (RingHom.ker f.toRingHom) ^ 2 →ₐ[R] C := by
    refine' Ideal.Quotient.liftₐ _ (FormallySmooth.lift I ⟨2, hI⟩ (i.comp f)) _
    have : RingHom.ker f ≤ I.comap (FormallySmooth.lift I ⟨2, hI⟩ (i.comp f)) := by
      rintro x (hx : f x = 0)
      have : _ = i (f x) := (FormallySmooth.mk_lift I ⟨2, hI⟩ (i.comp f) x : _)
      rwa [hx, map_zero, ← Ideal.Quotient.mk_eq_mk, Submodule.Quotient.mk_eq_zero] at this
    intro x hx
    have := (Ideal.pow_mono this 2).trans (Ideal.le_comap_pow _ 2) hx
    rwa [hI] at this
  have : i.comp f.kerSquareLift = (Ideal.Quotient.mkₐ R _).comp l := by
    apply AlgHom.coe_ringHom_injective
    apply Ideal.Quotient.ringHom_ext
    ext x
    exact (FormallySmooth.mk_lift I ⟨2, hI⟩ (i.comp f) x).symm
  exact ⟨l.comp g, by rw [← AlgHom.comp_assoc, ← this, AlgHom.comp_assoc, hg, AlgHom.comp_id]⟩
  -- 🎉 no goals
#align algebra.formally_smooth.of_split Algebra.FormallySmooth.of_split

/-- Let `P →ₐ[R] A` be a surjection with kernel `J`, and `P` a formally smooth `R`-algebra,
then `A` is formally smooth over `R` iff the surjection `P ⧸ J ^ 2 →ₐ[R] A` has a section.

Geometric intuition: we require that a first-order thickening of `Spec A` inside `Spec P` admits
a retraction. -/
theorem FormallySmooth.iff_split_surjection [FormallySmooth R P] :
    FormallySmooth R A ↔ ∃ g, f.kerSquareLift.comp g = AlgHom.id R A := by
  constructor
  -- ⊢ FormallySmooth R A → ∃ g, AlgHom.comp (AlgHom.kerSquareLift f) g = AlgHom.id …
  · intro
    -- ⊢ ∃ g, AlgHom.comp (AlgHom.kerSquareLift f) g = AlgHom.id R A
    have surj : Function.Surjective f.kerSquareLift := fun x =>
      ⟨Submodule.Quotient.mk (hf x).choose, (hf x).choose_spec⟩
    have sqz : RingHom.ker f.kerSquareLift.toRingHom ^ 2 = 0 := by
      rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square, Ideal.zero_eq_bot]
    refine'
      ⟨FormallySmooth.lift _ ⟨2, sqz⟩ (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom,
        _⟩
    ext x
    -- ⊢ ↑(AlgHom.comp (AlgHom.kerSquareLift f) (lift (RingHom.ker ↑(AlgHom.kerSquare …
    have :=
      (Ideal.quotientKerAlgEquivOfSurjective surj).toAlgHom.congr_arg
        (FormallySmooth.mk_lift _ ⟨2, sqz⟩
          (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom x)
    -- Porting note: was
    -- dsimp at this
    -- rw [AlgEquiv.apply_symm_apply] at this
    erw [AlgEquiv.apply_symm_apply] at this
    -- ⊢ ↑(AlgHom.comp (AlgHom.kerSquareLift f) (lift (RingHom.ker ↑(AlgHom.kerSquare …
    conv_rhs => rw [← this, AlgHom.id_apply]
    -- 🎉 no goals
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
    -- ⊢ FormallySmooth R A
                    -- 🎉 no goals
#align algebra.formally_smooth.iff_split_surjection Algebra.FormallySmooth.iff_split_surjection

end OfSurjective

section UnramifiedDerivation

open scoped TensorProduct

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

instance FormallyUnramified.subsingleton_kaehlerDifferential [FormallyUnramified R S] :
    Subsingleton (Ω[S⁄R]) := by
  rw [← not_nontrivial_iff_subsingleton]
  -- ⊢ ¬Nontrivial (Ω[S⁄R])
  intro h
  -- ⊢ False
  obtain ⟨f₁, f₂, e⟩ := (KaehlerDifferential.endEquiv R S).injective.nontrivial
  -- ⊢ False
  apply e
  -- ⊢ f₁ = f₂
  ext1
  -- ⊢ ↑f₁ = ↑f₂
  apply FormallyUnramified.lift_unique' _ _ _ _ (f₁.2.trans f₂.2.symm)
  -- ⊢ IsNilpotent (RingHom.ker ↑(AlgHom.kerSquareLift (TensorProduct.lmul' R)))
  rw [← AlgHom.toRingHom_eq_coe, AlgHom.ker_kerSquareLift]
  -- ⊢ IsNilpotent (Ideal.cotangentIdeal (RingHom.ker ↑(TensorProduct.lmul' R)))
  exact ⟨_, Ideal.cotangentIdeal_square _⟩
  -- 🎉 no goals
#align algebra.formally_unramified.subsingleton_kaehler_differential Algebra.FormallyUnramified.subsingleton_kaehlerDifferential

theorem FormallyUnramified.iff_subsingleton_kaehlerDifferential :
    FormallyUnramified R S ↔ Subsingleton (Ω[S⁄R]) := by
  constructor
  -- ⊢ FormallyUnramified R S → Subsingleton (Ω[S⁄R])
  · intros; infer_instance
    -- ⊢ Subsingleton (Ω[S⁄R])
            -- 🎉 no goals
  · intro H
    -- ⊢ FormallyUnramified R S
    constructor
    -- ⊢ ∀ ⦃B : Type u⦄ [inst : CommRing B] [inst_1 : Algebra R B] (I : Ideal B), I ^ …
    intro B _ _ I hI f₁ f₂ e
    -- ⊢ f₁ = f₂
    letI := f₁.toRingHom.toAlgebra
    -- ⊢ f₁ = f₂
    haveI := IsScalarTower.of_algebraMap_eq' f₁.comp_algebraMap.symm
    -- ⊢ f₁ = f₂
    have :=
      ((KaehlerDifferential.linearMapEquivDerivation R S).toEquiv.trans
            (derivationToSquareZeroEquivLift I hI)).surjective.subsingleton
    exact Subtype.ext_iff.mp (@Subsingleton.elim _ this ⟨f₁, rfl⟩ ⟨f₂, e.symm⟩)
    -- 🎉 no goals
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
  -- ⊢ ∀ ⦃B_1 : Type u⦄ [inst : CommRing B_1] [inst_1 : Algebra B B_1] (I : Ideal B …
  intro C _ _ I hI f₁ f₂ e
  -- ⊢ f₁ = f₂
  letI := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  -- ⊢ f₁ = f₂
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  -- ⊢ f₁ = f₂
  ext : 1
  -- ⊢ AlgHom.comp f₁ TensorProduct.includeLeft = AlgHom.comp f₂ TensorProduct.incl …
  · exact Subsingleton.elim _ _
    -- 🎉 no goals
  · exact FormallyUnramified.ext I ⟨2, hI⟩ fun x => AlgHom.congr_fun e (1 ⊗ₜ x)
    -- 🎉 no goals
#align algebra.formally_unramified.base_change Algebra.FormallyUnramified.base_change

instance FormallySmooth.base_change [FormallySmooth R A] : FormallySmooth B (B ⊗[R] A) := by
  constructor
  -- ⊢ ∀ ⦃B_1 : Type u⦄ [inst : CommRing B_1] [inst_1 : Algebra B B_1] (I : Ideal B …
  intro C _ _ I hI f
  -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ B I) a = f
  letI := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ B I) a = f
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ B I) a = f
  refine' ⟨TensorProduct.productLeftAlgHom (Algebra.ofId B C) _, _⟩
  -- ⊢ A →ₐ[R] C
  · exact FormallySmooth.lift I ⟨2, hI⟩ ((f.restrictScalars R).comp TensorProduct.includeRight)
    -- 🎉 no goals
  · apply AlgHom.restrictScalars_injective R
    -- ⊢ AlgHom.restrictScalars R (AlgHom.comp (Ideal.Quotient.mkₐ B I) (TensorProduc …
    apply TensorProduct.ext'
    -- ⊢ ∀ (a : B) (b : A), ↑(AlgHom.restrictScalars R (AlgHom.comp (Ideal.Quotient.m …
    intro b a
    -- ⊢ ↑(AlgHom.restrictScalars R (AlgHom.comp (Ideal.Quotient.mkₐ B I) (TensorProd …
    suffices algebraMap B _ b * f (1 ⊗ₜ[R] a) = f (b ⊗ₜ[R] a) by simpa [Algebra.ofId_apply]
    -- ⊢ ↑(algebraMap B (C ⧸ I)) b * ↑f (1 ⊗ₜ[R] a) = ↑f (b ⊗ₜ[R] a)
    rw [← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    -- 🎉 no goals
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
  -- ⊢ ∀ ⦃B : Type u⦄ [inst : CommRing B] [inst_1 : Algebra R B] (I : Ideal B), I ^ …
  intro Q _ _ I e f
  -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ R I) a = f
  have : ∀ x : M, IsUnit (algebraMap R Q x) := by
    intro x
    apply (IsNilpotent.isUnit_quotient_mk_iff ⟨2, e⟩).mp
    convert (IsLocalization.map_units Rₘ x).map f
    simp only [Ideal.Quotient.mk_algebraMap, AlgHom.commutes]
  let this : Rₘ →ₐ[R] Q :=
    { IsLocalization.lift this with commutes' := IsLocalization.lift_eq this }
  use this
  -- ⊢ AlgHom.comp (Ideal.Quotient.mkₐ R I) this = f
  apply AlgHom.coe_ringHom_injective
  -- ⊢ ↑(AlgHom.comp (Ideal.Quotient.mkₐ R I) this) = ↑f
  refine' IsLocalization.ringHom_ext M _
  -- ⊢ RingHom.comp (↑(AlgHom.comp (Ideal.Quotient.mkₐ R I) this)) (algebraMap R Rₘ …
  ext
  -- ⊢ ↑(RingHom.comp (↑(AlgHom.comp (Ideal.Quotient.mkₐ R I) this)) (algebraMap R  …
  simp
  -- 🎉 no goals
#align algebra.formally_smooth.of_is_localization Algebra.FormallySmooth.of_isLocalization

/-- This holds in general for epimorphisms. -/
theorem FormallyUnramified.of_isLocalization : FormallyUnramified R Rₘ := by
  constructor
  -- ⊢ ∀ ⦃B : Type u⦄ [inst : CommRing B] [inst_1 : Algebra R B] (I : Ideal B), I ^ …
  intro Q _ _ I _ f₁ f₂ _
  -- ⊢ f₁ = f₂
  apply AlgHom.coe_ringHom_injective
  -- ⊢ ↑f₁ = ↑f₂
  refine' IsLocalization.ringHom_ext M _
  -- ⊢ RingHom.comp (↑f₁) (algebraMap R Rₘ) = RingHom.comp (↑f₂) (algebraMap R Rₘ)
  ext
  -- ⊢ ↑(RingHom.comp (↑f₁) (algebraMap R Rₘ)) x✝ = ↑(RingHom.comp (↑f₂) (algebraMa …
  simp
  -- 🎉 no goals
#align algebra.formally_unramified.of_is_localization Algebra.FormallyUnramified.of_isLocalization

theorem FormallyEtale.of_isLocalization : FormallyEtale R Rₘ :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.of_isLocalization M, FormallySmooth.of_isLocalization M⟩
#align algebra.formally_etale.of_is_localization Algebra.FormallyEtale.of_isLocalization

theorem FormallySmooth.localization_base [FormallySmooth R Sₘ] : FormallySmooth Rₘ Sₘ := by
  constructor
  -- ⊢ ∀ ⦃B : Type u⦄ [inst : CommRing B] [inst_1 : Algebra Rₘ B] (I : Ideal B), I  …
  intro Q _ _ I e f
  -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ Rₘ I) a = f
  letI := ((algebraMap Rₘ Q).comp (algebraMap R Rₘ)).toAlgebra
  -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ Rₘ I) a = f
  letI : IsScalarTower R Rₘ Q := IsScalarTower.of_algebraMap_eq' rfl
  -- ⊢ ∃ a, AlgHom.comp (Ideal.Quotient.mkₐ Rₘ I) a = f
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
  -- ⊢ AlgHom.comp (Ideal.Quotient.mkₐ Rₘ I) f = f✝
  ext
  -- ⊢ ↑(AlgHom.comp (Ideal.Quotient.mkₐ Rₘ I) f) x✝ = ↑f✝ x✝
  simp
  -- 🎉 no goals
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
  -- ⊢ FormallySmooth Rₘ Sₘ
  haveI : FormallySmooth R Sₘ := FormallySmooth.comp R S Sₘ
  -- ⊢ FormallySmooth Rₘ Sₘ
  exact FormallySmooth.localization_base M
  -- 🎉 no goals
#align algebra.formally_smooth.localization_map Algebra.FormallySmooth.localization_map

theorem FormallyUnramified.localization_map [FormallyUnramified R S] :
    FormallyUnramified Rₘ Sₘ := by
  haveI : FormallyUnramified S Sₘ :=
    FormallyUnramified.of_isLocalization (M.map (algebraMap R S))
  haveI : FormallyUnramified R Sₘ := FormallyUnramified.comp R S Sₘ
  -- ⊢ FormallyUnramified Rₘ Sₘ
  exact FormallyUnramified.localization_base M
  -- 🎉 no goals
#align algebra.formally_unramified.localization_map Algebra.FormallyUnramified.localization_map

theorem FormallyEtale.localization_map [FormallyEtale R S] : FormallyEtale Rₘ Sₘ := by
  haveI : FormallyEtale S Sₘ := FormallyEtale.of_isLocalization (M.map (algebraMap R S))
  -- ⊢ FormallyEtale Rₘ Sₘ
  haveI : FormallyEtale R Sₘ := FormallyEtale.comp R S Sₘ
  -- ⊢ FormallyEtale Rₘ Sₘ
  exact FormallyEtale.localization_base M
  -- 🎉 no goals
#align algebra.formally_etale.localization_map Algebra.FormallyEtale.localization_map

end Localization

end Algebra
